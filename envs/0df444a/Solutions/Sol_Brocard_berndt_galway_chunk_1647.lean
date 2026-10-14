-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1647
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:02:30.383929+00:00
-- url     : https://prove2.me/submissions/4f0696b7-ba11-4b7b-addf-2a3d9dbd8053

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 296043165 ≤ n < 296223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 296044415 1250 296043165 296043169
    0xa0f08070e030f0a03030c11030a030522060606230f16050f0607081b09011107080109030503010f080c2101060b070809100e0d1e0f0807030806031612030e 68
    0x64121000f6491640900c10b86410154148152000d002d010310b040b0200701d03112144680c03a03105000c0814200342d260b601240800c080803e9101c40001002d48010381844549000b0001c0d041e00c1c4100c4012500302d030b098a990fa444440300d0b500c20520503110314075180e420b03010341c0419002032041e100100004540100090000c02180341c07a495000c008100f40e140c005001005207600600f0090507410720a10b1581c0340c03444c0000e0340c41c1041e003400c211103101011603095103011240e51200c00ea960900c5d420740b0500da0084001c606860300c2c2022018116191250b03155644e0101d1000c541252040c1d00d2041c0d640748904400f18603507055400859a5543c600b401c4000b42c01483c1f080d11004c90009090145160141103c43c590b0300c941001f042d200b1426001480c2c0b201c114002a000b50300702543e00200c2141d40c04940c120544c8100040c2410245050424003500013034012004104501c0214240f803500090800f9049108280d183d00306080c036402d5103a82084001c2101072000c00c1c1c1440c0390075 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 296045665 1250 296044415 296044423
    0x160305220f0602071407120206120406110a0509180f0c0d02130906081608070b070f050303041101020706030e123a0614060403080a020f0f030703080603030a0f08070e03 74
    0x58040d036017195020851486a41c10710000794003070400c880744010f8900c0181c5a0f0340545441c4840d03a89601942c3c0c1d550305240014018028074401000340c0043c0742e00b00f02c3d070040b02800640c0c42c1900d00000e44d016030a4828140f603001e64030380d51780078100d00026070b624040c1e100418050081ea1405030030003c82c80541c51365661940c0281102a80b15241032011803010449641d00c00b0343e402201030102e06d004886a2640e0b114025016880d40010f00c14040c88407001500300c01e20b41c010100d96076880c20341004103061586030203050041c01051070009400d0321900418100c0080e40c0098400700e619291009461380c0800c3d803e1410300e411160089001c1851019040107806100e82c24048821b80000d031070445e40d06030007641150b6036401000f81d0700d8583d6420744092f41c0c0d01c806406da580310808000da1905543c4d051081030b0740b0400d00e01344046d450100280c6015442903d40c591706441e960708146e00c0b40035540c0710f400002d0072030b032498001510035a8016000b4406040591b03000110310007003420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 296046915 1250 296045665 296045677
    0x190207050108060d03080610050f07110901050d080405100c060e070512070807050f0303090a12210f030c18120c21030806030c0d0605160305220f0602 66
    0x56084698200800d5820003441d65001404541c107180307000fa40c1e5009424101d029100b24040d02d03800e111041641c2c028000c4920005000f90354580783d642901c0c220b51400031003401c55004648117000012203041200e80d018609900001d42401d09042600344020019803104607010010b03e20b80200205c0c08a00c039007498603030341d0005001c03a18144020f0081008545529480350340c48140b040061a1000c41e2030400c0d54000c541d107003011204c02c00060316600440d08800d42c080b21201d80000e000c8079114a10354028411416800c03150418034091b2101040302c00d4041c00704407041a5002510304c42d42c0018825282410300b004040c001041600d4450341c240c00004a10200e0301101007444080750030304c0010818860342c0b140ca01141c004041c1208190500101400140c1000ca0080d95003884592039841014000d01c210131400c0c00c040014240550351030200d84003034903200781c00612a0142e20f101d5003020601d240c00100321035812100311011202a1580304072400c03c007001554900084c44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 296048165 1250 296046915 296046917
    0xd020c06070e03030423042705010c0306050f01052a011505040605010504170111130510020c220902030d08010e0115020a150b030f0105071b110603040819 68
    0x101e1a0810340038092424500c0941d109503c00c1c4020460301c859800c2c400185101d40e11440d090052101c080744c0503004050f00324150350492862410740d0040035031001c0503540510002c0c00710750b0320300105804a0390700c2e0081680002060404a40c1540105d00a0a0780c03009007004628130070251702604182c00340f08100c01c000365140c80801f902d88400410000c05007104880400087d403428001800500c100e05c560030842060101e0000d07658402e600c40d0710711403001c0d5207040d035400b200718507041e00c050f0324001d80c2d1154880301000d2110750b10004225041a2025107541e85042040070113001840d960900703100c100d9160300101d40142c0702400040f40e688900d84a802482d4105148158080d00503006001c0512841e030031032000d154002102403406801c07006034648060008540c1e009058603d46d00c581500c59040c0e010380211056210a100d5060340d41c0c2ca203019149840c103800b08009800b0701400100c04d01c0420902840c04000031504a88120811403a1905c9441d03c07030015201041504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 296049415 1250 296048165 296048173
    0x60a050910090203160612150b070f050307050d020c0a06050a080712090206040b0306030606030a030c0b040314030709080f161505040e1608010617070f091701021c29060d020c 77
    0x4d44e01c0c4245018000780325141b443c03404005400c01c007227041c19001c7d07540f011741540107050044090240a0045a800300d4204040d59001081c586001c0d6456400200c407a020303200c041c200081d818400c20903a9080c0c0f002d075843c44203903102c1000072181412200414010955030301c0c02440142d0f54a00144014040c0721605a1246810304c2003606000f00100494040d800c03155281e000a40c4c0514030422456120800c00042d0720380b82400c40d071305d103030030302c8641000c800010130f008035107070004018011150f0b400300301d43c14541e603600e0f21038403008c402050132080f801b03040e014404105000561102e0b0234440c80d2803414980d840e200c0b0104004140c802210058090007a040c2140d071003000180034000c0c5040c12200c4181640b01c4e41003804004007450100903005130084185c5205280000c020201181a4100f40d131060034094000d510080c96031002842c441011401c842190080d4900801c030000680640105d8180340301c1c2c4060b400c1c281c181d0002041044d03a8a200c110f101808403503480d44010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 296050665 1250 296049415 296049437
    0x80c0f16021f0f050f0702040e01020309010605100c0204050a0b03011d0c0406060804020f0a051225030c030305030a060f230a080d110a05100e060a0509100902031606 73
    0xb0102080068180744056080414502c0e40c09411100301c00f0008240e01e44280e0369901d9000d00709540c010700c68021350181c201042c1180002054010310f00840c2180020410940d0700c41c20000320403c2d0403030442c08507801241c660054a4603903c980e5108441410205020090f40300003030031035040d8a482040c1500d03000c2410030b282800c01c1310030038409080e10204415424580c01501505000f40001d205c0d02c0c141d842d5215039280c65101c1c50082a0141860369244101040313161550541550050800c2194517003041c45101d0380c4840301225040450041d80d00d080d0740f411505a03000030042c0b0740c0252a541d00007072004541c052600140203054400c241c1d4900daa2070b107050080b001c1c509910501015a00307000c6a030000c60b0b045004080e80c10034204214840d83c000b801c2c00d05501010301503003d940c0b12008030760030a421645107094410150b848607620108031008803036050380d030240340d58441d001c0084100c0315503000c1c0c018a400282141c030100700b01040c41414003880d42001c0c000a0184445c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 296051915 1250 296050665 296050669
    0x206070507030f0c080c010c15150b04081501050f190e070201140105040e100c140c030a090e090613030c2f0402070803042006120f0f070f080c0f1602 66
    0x244c040c0c004080500801103100b00020603030001400060810205489500b070300c00d5940d4484141d200d04102001d402668510004109412038030588006009182c1010709003d0240c895a06984005164040741e04501c021701240b40c2030345601b41900c411040b000700b00214141c05403849154036a0020030600c0038000c41c0c4030f80d414180c1c801c80c00fa900b03201d0040c015282c04501141c2d4503d1120001890909000e01107410151000701004001c1c0300082034982c0c1503020000f002e100c40141c44c0c0c103001607075a410300403007a40c0880307000f00d142d00041c020814000c41020205142c5009292482e041c0043e501c0390964900c02c0e142d006005000300d014107408211001c41010000d104031411801d001c00b03516209075038800104000d00038151440c1c850727132030802412600381d10a0094245610b80c1250b44c608600d0420a451840d81c1910000002d0a0306100101041c46882c81e80d542003048000e00ba41a104188040c2109015510901880e003040c01090090610750424400001042c429801 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 296053165 1250 296051915 296051933
    0x628020d0c0b06010c1b090f1103060a0e07090e0c0306040501080c010c1103160303120609020f07080a0e04020d20030103030e010507060b0315010303031802090604090206070507030f 80
    0x10200c041c07041c04034404021070080080e4a501200a00340481208076034a0f02c1c81c500c420305184c46a40d0040340001043c0681d207a444509041d5100e04104100b10310040313501d0b014002100c2955101a950303005218103103652016a0b0420082c2c01c103440d500323072648500040004229906480300c01d0200821040f460903000350b030b0050100074080c141116010000800c00300ca03000b005006210409042c41c41c81d201000340e940a9210140200300f81c3d030722850000c040900c420320084102d41805800324000c4468822221401c81c008101441d10041e5681d0b0011600706003030704010300000d00503454468441d400103120304040a40d000985c400000b15420481c9810860f5a48488080c001400000d40040d5034808039642400c041da21a401860300030040c180d07090100c0d405000300b081d0504021510440181a2071180d103052008030407081c003d0640d41c0400c1c4021f51b000001c2c20101e496420681d2200080e1800074014038507201d02d54031400e280045c1c9a10403a0115010002c150500c41010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 296054415 1250 296053165 296053183
    0x307060203040b061002100b1f1e0801050f01030b0105091201050709080a020603010e09030c01090b01060e01050a0c0209070c0f052107051f29100e011409062802 71
    0x1a4a80e005e0000114025624040c1d114024440d941e9101800c0355543c44101c85002038099040300094085800c000030140c0c2015500c03a02102200c18450500c140204c5c0c40340c1c142d401c05000404400769510045018040701000b21741440340421070170f0100d03141e80d03440100d842e0424002048a090500780207000303241643c4140c056410141c4544010307961308040340e0456100f10400f00054441d10300d05410740c8034a407004803940d031800764880304202c82d400249040740c020b5140c48001c0100c039401940c076485120b010900160121124030014a00b05007400c2e0041500d26009070080130564a20b0360500c0b0004050380d00f80e00040b01401400400d455002ca643d64042d00142099880d0b034480c2d81d81c1814480c0c08422002024205015107159405809920305003010814201c40380c4c8200041003404100140c02240b020301d01e07820380390168404001d8403c060751240741941700794130300c540b180e0000345c901ea9102c0410022803080c0080205041140014030240c00d101c964442c2002c0d103091012 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 296055665 1250 296054415 296054419
    0x1090209060702060918040609020108010f0b0a0f02160609030b060103091e0515130209070809071202030109050304060207180507120c0921021302030c0406120603050307060203040b06 81
    0x4228014a58075203a065070300e03441d4140c0d01140c55840401c0041c0c04519900c0101d00302c441d031441004140509030300700100141c001e0b242c4444c00e9817140d13059280801140039408840c5400c00003400260711900c3c05080032207440c4142c42d80d96001c1d40e607074011989142d0183c0c0000350707942c2050081c401d83c0300950b50494000d0a0803c124101540ca8000302440340c550070072030301c410200240c00c3c013105000d0f022828402c14501030241c9030412412040c0000c1d03507400ea01800403c8001980300f4044c161980c000c0c0900d20041c4161841d01d40d21106a0218000c120307050b5480d0b51210001440400140018001980160617840d050812100118034051240180c1703506003000e1044264020111404a042c0000c01043c500c07004201990411110b1348a034116424045444400200305911010308034403c9a01518039048207004400381d01054540e0401007038204820044617010b407000050007800a44d000c22460707500c0d26203509541003244140da44070b8001040004028801080a03484001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 296056915 1250 296055665 296055667
    0x80c03090114010f0e390d050115081302010e0d03020c1005030105032103060d02010e0a032405060a0506090d060f051b0a0210021b010608010c09080a030e09040804091802010206010902 81
    0x31082c5c41d801b01c4191540e6103000b16a1107000d21900b10242801c4030845007645401b4040c5581d140c1c601c01c6103a80c02d031640c0c00066000408100341082081d0400c01440c0c050755100c003241003920400200740d2098000300d0540c4501c05405109031034038005030708c0f5804180c84103a12585014140b41c24481c0455503c0f50b49003000c1030701c121240c01407050380d40141d01510320041420661006840b0b03000c0601441d40e00400c501400420010002160b5010a80b5001540c3c2210502d80011040c0c540030354082d81d000303044807010701190901c40080c2091040c001c29100d0f010086482e244c084401e007840001d2000e454404001841d201c42c0c0380c40303018115217403600d845c022281c0e40003904c44408242300806507400286804c03a401118802038000303212030008005940c4c0d0351000300c0c020714800c2c900c500482c84034040041d00e060045100b1401a8050f00d404901940304030030031140040062045410103801d0201041c1110140b25418407103403000704038416003e550001900c0d20074143e03c0b85241e940 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 296058165 1250 296056915 296056951
    0x1a010806060910090c111504170705070b03090102090612040201020d11100b0f15030406050c13061404030f1b0e070e060f07060903080a0c030606080c03090114010f0e 73
    0x503400115001c4403c14000052409800300301110701050131024186d0904c82c9a961150224891041e90f004910401c0001f060f2044802e411516000c0c14201a03e80e41049008221461119000f15031010041c00014a45403201d00010749035000948014142c1840301c0c100f00031540c04200421100110b8108504001e00441c28641e440354540d1100d08907a0319007508501c01c0d01c50019600b081c4000801c02071020081648240702a001210141e40c0c080c10f0002040d05504080103e5171410b2080c41080901410b20382d0940308040c1c12184500c2c0c03003508000000224410b42403a0b039185100310021401141d40112184004030720380c1024136070103070038000d0080082c1c0106c000759911409a80781511080302c080d0000c0603008001001d04224207140d441420981c0c01041d6611828800c4410021714540340c3c0101c045510900a02000c5003034000414210010315001d03540c450b0b80240045a0a5112501300384000e60070b078041880e41407958420b10542d4582c40003141c1c070118181002c01d40304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 296059415 1250 296058165 296058181
    0x8040303030f1b030c0e090702161d071409090c030a05090129030304031b06110d17040204090f0501020c150c0f0c030c011503021e0112020a05071a0108060609 70
    0x2424a0458090680d074103c001c040c06d000e107011002422006000914928100328065103c0e03804103688180c0071088100415224440ba20035101103000c015000c0403035641701000d480007410000302c5010b00400b48002d1491b50346902040c0d00c50040c40c0c1e44292030781011f603505000c1d07800141404010f070b418000c2c640f00061354410701c0c45186c2100d000c52081ea95807000413a003035101c0c82d080a00944075100c80c0303942505a4103d0481110043d544030040e0074100101681c95500781250b02d000190803005a000e0a003a80100c260043c0c00240300003030081440d40c031507001107000141150140d4002c901e505228034240100c03242444465074100f854a000781204d0b17810f10444e50701181620010800c0341c1e00c00700400907900c0b018100c8000b00401e071003000416944034014401240b00e03510342c1e02d24161610040c02001c14098060312044502036803a101c040c0690003c880003401c00600b800441c01007211503102c02c00d41102300c13410b13030b107030354100400d085c2050001072015002d2040581404948 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 296060665 1250 296059415 296059451
    0xf0203060907030f02090901030506040309080a03120f06080102030a0c08090c13020f1615061a091201151d0903031308090a03020a06020d02161202061602040908040303030f 76
    0x40102e0f454000343c048209003280000b0700800084640000b051070000c17040000010b030940c0100e004e51102e00c07865540c1c50351160341d011509030090005202d6286800f0402150b0081d08410844442c046103050300d50b800a82285c20444603440c00c0d640354802c500c961500308407441d800c640b02501514864080d01e0203e80f5118446e102104003960000d0041111f24030841910304810b458001032000c6101c4e0305100c02803010505e4035461407441c2c08000900c80000c240b0350b8000e03019490700142400307a40001c02078490030704a0f038105555243d005118020642183c28000b600d40e0301141c00074004801c0b81c20700400c50081401065501c03c1003440525096038406401c81c60b030002c03210343c2d181e110f00c1c00302d079403516a039100a40090320150080380058004c01d19000d048100c1e800c44d4114403000d0010a00901c031441206076103040d48907060003504000c8004c000038004d0480c01e010080c407507404070f13049503080081580c2c18034011070140209071f45402001d146602140007030103402401c8604000c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 296061915 1250 296060665 296060671
    0x7150501050f010912080708270415290d02130b09010203070236090c030703030e041a120f061005090a09020325090c080108100507020f01060b0d0f02030609 69
    0x214402e0b02242e05c204680c0b134048039070b01d03039000801d65210480ca25200c0c0440c1c03e140405840c01510745c092981c0790915104482c854030210f149034012525290f4003016104164003000c1030101042c03c006009150400103251084840d48010f96a00c00c003042c2e1100d15555802c003062071101004285226a400416150141e8040381c1d68405d8194450310012080904800302c3d10803030025403544451941c0303030103007071141568500351610304032070320b040549500b560302000b00804c882c03808036500d60400e0b07800b0071004810041c540400820040014596070b110018603c0240c4c01503c01c00c11150090110f2500100365804059045007010002140e40c03400402e40c9803426a60024181556420050300c040780708429921071503040100c501100707902650182010581c281100d00142e148912107181c100c4080d507014282010701c10402c980038040c0034185d50304510501d041c041500000b0310446008200a000d026650240401c10109850301d02006020f000c0c0f0510400526858070203015074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 296063165 1250 296061915 296061929
    0x250219060e24030a02130f030305030411030115170f1603060e0607080c070c03020d06050f0601020a050c19080d02061905010b0d33030618050a030804080d0207150501050f0109 77
    0x40c441b800003400c0d00484005038800c64000c0c0c021500003080c0364110380114011b83c080c122a0381500e5625044c1402d0756001845603099141d0031100f00301910340704100503603100e80c0030181d400c9509503071592461300e071000c40300b400d4a9103404810800c1080521811000401980140034079280407040078040d00d0000b0721418819000144000801004502d041c01465005001c412003408900380400181021101c0050005501020940c25800020200c440561040040403215120003e000840e2095040210880f03a0314502040e40c0c94140910007072184a5801461030745000030006462500126000030f8680c1b4107001400482d04850442c0c1c00014004004120190380384a40c006a8843c044540c44500c13001002007803d5407145e101500300c0303000c1c0c4000c0c001d20301d00214940c01d000c0c12090050450380102c1d50940002e026516403075000e800703480b10908201d01c1d90b07458010381e03200da0750444000d00502e0007405610b0181c1300c3c0c6405403106640304007000d217442001924070801740c05602 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 296064415 1250 296063165 296063167
    0x90601020a0c03030e1305070e040c02010b10030906020403020a180c262a0a0e0f18040501020405090705030123011202090a0902180102060c250219060e24030a02 71
    0x440c5c0c2d5102c2030500e8815003071000081084c0d103030a20009000454030744c85548030300d0400c0e200d001554414000c86030aa46e00803c4120010070f256030540040001c0382040307407266028013000000d65244c0f80310380020301c80705603801c4001c03140751007000844004400759800e000070b2000c1720182c0030000b4100c013400d03401c02c0558009a2514101070364442044904040025005a0b0b0388801c290018040c0c0b030044007584604910800c00d504201e251410f480e0142c0d00039008400f1740d08214844030105400c5030151000500d8641c41e207000ca0040d8604482c040040307580000100121800c00c01c100707600d04020b80505000e0329514000801100c071482100d40c05e10b4010492130303203d545480c0c3c0b80d07005110680b0115038401d000780705034000e02d109146990150084000107000b0703030303210740450391109a81d02c1401d100d40c030004980c80988400d000c050781c000c03040401c045c41c034501107010000902115180c40d8038011216003008030782c0c176004940032010115980248502c10002e025280c02890a203c05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 296065665 1250 296064415 296064437
    0x71101020301080a020d260a03060603110f0a1803030e0f01020c0f0f15040e15030f12030415050f040605070e03071412070f0e01090b011d010302040909050606090601020a0c0303 78
    0x107021500390117404010055147c1c003603600071603d400e0080420b0121518140000ea42d644010380031603001e00b40c258603c6104211000c54604880010b001040160501e9040e03280350310302034110702c50b0035041100414103a421119142c60100743c03aa404040900c000c01e074500c024404500100b0040504901684c901c40950200390b844950780d003800700e41320031031945556440090311500307402520809411050220f0030107507410040b8403030490282e404001e00600035600c1808859500042c0242d440d5019034007501e00300003860180d107000e00e07034070344811045051608014040700c1d4050017080034068111480680f80c0c8007c9211070448908a086940180c1e02e034021424031082180a00102d00070014003141450b5000c0080301560820038140c5c4076a81c807004101e04540490600c240804c0302e0420301540900290b20f02c0901c19410700d009400c19517200c6944060710200038080720740d908200c081066500344000c9680d4012402d01c0103100828080e210700c0140245800058208074000141c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 296066915 1250 296065665 296065673
    0x702030d3c0b1005090a06080103081207180909020102152208190203030906060a050d150905010f0b130605090c0a031e0c021606080718150503071101020301080a020d 73
    0x2c414041c05000d4881080c2902944005003258400c5c0340240c4070b60680d0790046100f174402c4034000d058a0f03200700002d1811110320015000c0140c003c06000400c0f40203100e61030320811800c0801e005020100011034111000d100190030400a8116000c022265004000918403001000c181c581200c08098190309110b08005d40688504207a03c611480c1070410912650350000081d0301c190850012340c0c0302500c410040040402807403190561100704400d812002c203503003030313040f403403c40f0003c800243c11101680c5590035078101c0b0300c6803a087c0360780b00b03c4040541000d84c243c0203003254001c000c2001604000001c0c0c82c182014062029581c008145010300d1030295006905100781c040700c84405c5801402108007030702c4070741308020050282507211400030b030781c19178500180d585036103441e1407d07560304100f240c500c91403041425103041f50110000d0040104032901d01242c02071354440e640c9107801c503009400c203400fa1045081c00d0388108010820800301203101000d86034110b412036601030b09410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 296068165 1250 296066915 296066921
    0xb03100612020a0b0408030901050c19050609011503080d0504020a030605010e070e12100b0d06020d060503070807060504090b010507050d020124030201020a08030c0705060702030d3c 80
    0x1089402203240000110381181c010a408568034822903200e80141c1d1115550f0302140590f10030414070b5030083c424441d456000350007400030b0320252021205013015151000803200121101541c07103800903030900950103403c0c0100790808442624005880b865a81d980e42d0612a40c442c581c4615030b1070003c5411992101e043d0300007150400300c244403d5846180c05140c00d0b6054600001046081c030402e4030307600306540812216050035016240f4800140f4194002e80148814103501c140d04940b100c0014480340301406021100001c001029400c020a1610709801d80e00070400300d82c006501044455400b200300c5003910300d0080003080307000f8501c0061303400d030250010090a6010700c25100b0f80c042d41c158044511a0b0075a00781d1320015001039400700210080d40006030058018144c104046101800159040b4017602e175070314940316040e118079080140c191200c40042c0c1000132940a8083c090081d429030343e03803602c000e0540540e24001c0b41240d48500350454160994448560004800741c4c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 296069415 1250 296068165 296068183
    0xf07110d020414040b0709061205091903050c010605090408030a09060b03250501091511070b04030b070f031b030902130501060c030e04021317010f150501140a0e01120f060311040e1f0b03 82
    0x55541d00303300c1d07403510703010309039410450b00d00340c4541c6040000580c80c03800104045c001c0360000003061941d29502624009030010707840584042e81c031081c080520340c81c1000f015403a142c000e003a1624204400002840c003400781e9201d01d0401007401070501c0320410030752407100c1c180300604210340d0068002012a0030a00c1c20344c4800750b6010045400400c0c40306042d6064840c00d6650340308600d003400580c0c01c0d411203104002d00300c080d4070300d1480000c14038060760181156600007089540e110f08142001802e44100b41c01a2000484519824007015000501e00700c014000f100c0550a00c10503660460880c8540e204025220b501010b0410f503041c020350000c60458205002404071009803041d803850415144903ca000609601007950f603119124142d0b00d60403016900c01510030221801168116000c450003000b0310303924240e086c0c802010f441510001d40c8200f2031000c001014000700300c11203500c40c008084036009aa071070614036040c1c483e10002c0342144400020b00c4450040442c0c81d00e4041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 296070665 1250 296069415 296069443
    0x7080405160f06020d031a01051305060d0915380907030506010f11060c030c0c0d08070f02030a02120c031e0d0e030f07110d020414040b070906120509 66
    0x80c410204031011002e01c68030a80c0c586800f110f20416070380ca41141140d44020800b00c1ea030701b107098104101d40c4107000419001e500c0303c0c030074030030f07a500d0740d0004580d82d0000402c0d0514540d5144c40c41d0810420f1400c0d008200c500103010400d014200d43e00c901c440c202d844006c001401e007004075007207140220f20718800a600150400045141411000e0014203040e2130a40c0400c02ca001031840b0b040c400d0100902c6018020003602954844000c2211150005400303210350020901040745528401c021004c00512207a5400c502e0b0306000c5000b9145d4a800050002150420000300c61040c1e00080c80c00c00c1000d42c040544e40e1801071310307605811401041d2010b002e64425003c26103051031444003410784d01140b940308101c1680012041d6680c0c0c0b1405600380c03070303850080c0003580104200788018000860043c1440000390103e0f8001021030f440c1c0c87c00501c044040a0510081c00351005420343e0140c000d0a041042a040040251107540e040310230418183d04c603070000d0520241030044451507446 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 296071915 1250 296070665 296070703
    0x906090501090303060b04030c0b03070302040b0c01140a020f0909181009140f0706080606070c06050d0b1203040b0f041d070f1409060a02010603050d0e0405100e07080405 75
    0x1203803a0181c040d01c8200002c2d0300282c01c005002c610746000c9070458080b20340c0b20000101e003038038001000c0c205410043c58401070503401d22000804442d1000140801c00041000080e88005561014644000644034a20342481030108110303c036100d0041b24090130707048802002c00c1c1e80720000c001144001d0320412182d030190346152000b8082c190000c07a0018070802c148201c4025400360356549401400c1e0021041d40001420000c2c603000702010354000030b028000c6441c0044507207405068070b440740d120400107240041c403251900414890754000b00030442d061403205419043c200e80d240941e02810500090000741d2203102000d0008440080461140c8000520003400075036400b0300c4102c4403400425001c42084028600c034500b074480390300c01140b41c03600342881002404010381022445030155943c4a00c0130000c02c4080081b041d00d08025580d40c03800c0c0801070144130a80700e0182c2003071800181c0c0042400910b074450b42c0b50340d1100051505c03412699940c100a450240c07026222010062 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 296073165 1250 296071915 296071931
    0x207170d0e0c090f01060813021509030c010c170a090305010516080903030105010903231608070905040b0408070c0e150a170c10020c031603030306062606040906 71
    0x2034200c800c0484010003510b18116180c000e20150800031a10202844512001409000e01683e1500d410801c60031a07503402d2412980464442c400d00c40342030f0003440c800b00b2070540e0b6280820280e03200807800c1c644521186115914800960851f800700b01240b100030071840c040780c1c482e03c0d5010080d50488001c3c00103044c40301c200390f0803940c0f0b51001000113403400006404910000200c80c1210010381d40d1441a900e1a150207018041d00800c003400c9880811030615001c0d41040340c4003040c00b851000000356403034501c0b0340c4d140c5501680304108042c14403082002192107280125070007070300a4607243c0d07204690324003a5a41c00c3c40340c21042c003020f02c1e041407002c28045680c060301070000941d1130005003501c4030002c01540c0102300103109258081c4144140c0b600784400e0800041210f40103c5442c4001400028140000b00030818680321483d1010003d050781400b880c0000c1295080901011000c08046026203000d00442c03191620001c0200d50503844640c040541690800c804005000d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 296074415 1250 296073165 296073187
    0x60204120c0b070807061e0912020f1204050904140304060324030203100c1112030a060e07120c090b18040c080c1b0106170a030810060c06020717 64
    0x503440d04400d484030880410007062002400c0c00700e6981c0343c2c200c8655420000550b0f40d10025081d40b056094003084030040429505c8040e010340718034640f050801090300460410000d190613682c43c492032480e8231500e0925420100c620845080e11016540d044840c9d5940c00e1001c0c0c1d220680d6000620f520000900042e0140d16a02c010544405103004030644003480d00508499402c40c08081d43c10340010300f013080551141d80c0041e20004890501560303600740c03041c6060800d4601c0507401d40710380002041210044591084401504841d0765881c1c05007000ca1000b04a0320000c0f800c2c08509a80300300b0803a08030b010b90300201c028030900003255940c2e100d03000b101c0d00c006868600640102e003420001001c59010f880824400c075601140d040c10310480d910000740000b01d00e50140029541c405020940c2c0c600d400d001d40c1507440d2480285034070038036440d0003403072160014141181d11400002c244242c035070003030b4034002554121801507200c0040b030034084400280d0700c5210340142c90024401c0d20301 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 296075665 1250 296074415 296074439
    0x9050409020604080a03110607020a0c060305250c0b0f01260f070605071a013209090a23120c010f0f0608010e010b0f040507050409020703030501030b13030c0308070507060204 77
    0x6111f40d800f920925201c450040c1d07610303241c0c1030000b4042c072075141e001d000007442584143c1d4440c114610140c1031403621140d6100d04102c200307104000805032864141030060708070340741c2e4011605000030980c1c0d40c9080c440c80c900c8802070801003080b2070b010f101645005420010901c00c1c41044095072003181d40c3d00c0024003507500c418400c40d0001d0f0b90250f1038002002020109040b41c81c03103404910303452425441e103988179142c1714001a040c000c250989856071900300b0b1240c4a800040f00802108200f0f08018040e880c0e505010f4009050010104945840100708124149407042c0103e80759000340c0340090251000c43c1641c10428501040d40c5545003503034000b40e0403290014003c1190205030f00807103090310761007020b054008051016050303281c105940701ca0760009482c94a5401c003078030381880000f40d0348900800d0300003a45400052061103215801c107500890800681030a070328030b036070303020382066080140070303062101550010720028000c0c42100c5030380354015021551651100d10140765 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 296076915 1250 296075665 296075687
    0xc0f0e0604140a020901050d020d0c0e0307080d0e06040e070801030605070e0a03120c0f110901090501080d0c050c18040b06060c03180102010b13230709050409020604080a03 76
    0x410420600403940a003014031664222140c180e01e8014a0343e1584001c0f0301950014600904002c4108150700c900c400341c2c40a0320364660303441d40218502c3e00203200241420350031a9a41d21039001b8110400c40c683c40010342c00000000b0b400c00000c004a060300146c810b01803070b0301040903c0321020800c8001c59100d03031000e06807481220f08002c80c0d2181c0004407071084030101036580000c080d01003800801e003041400d0b42400203510748003890483c540d48042c4004412201166183c0410031051903030724006046a004d4040c40c4004c2040c2d40c54040d03000ea50300403001429040c0501c0d14180800d00c241402804420440502445020300320005e245000c00d908a800b61820b4a0003400300c0c149207012400c4456a11146004606040c6904424200b0072954040d0506640d82c420318080d4503122108190450601043c0002c0c42a00098074803110041c06001000b8243c1d00108124050350050403200c107969042c0e40c0041c48001c6440450304622554010100318440c0c0365005040560203006409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 296078165 1250 296076915 296076929
    0x20a08041a01050a0e040521071a1003020105160212032701020a020603181002070213060b031302040f020309030405010908030705060c161a06012a0209090a0c0f 71
    0x207a41500094403a041c49000c0c0039865000c6045041001141a00c0d8856504240070b507068590000b440c08400004981035800c02243c0b01010030f600d402e002403807014000310f01045015560030310303044241184900c07407804000d05010000c05c80707992004034560fa45040a40c003030110350300c0307254406006641c0d8005102c004801940703162072004503020071200000f5280180c00a00240b11603600300003903508000d1218011000704019590200c0e81006100480d031100e12005980303d2840c01070000740c01407100350448650130003004000c084824021a64000840d98608540000e02d100090140c0109079100d01101e00210030702504610100040c002c030381003625086611a43c5400d0303983c583c0500701000c2d145400110000341465000d400803c0341d250503030541c0c03294100560b1210b08290300500d4150f10745503c0b4080000790758100750046100008503107072600c2c0c3e40c080c0814812811640800034000e41c07038280400c610307400801100000c5a80840b558146170744890104080002e2481028 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 296079415 1250 296078165 296078183
    0x504180c0b1b07080a030e06121504240b1602030a0b09152e0512010609060f290702090108010b031207031b051e0106150207150e0112020a0804 63
    0xb415440c0c0043c3e0002240c12040282100c070480791016960066150350f030542242d4204901c503c90449001100d00c203c03007401d00c60b51842d65641c2840206e590200c1003107030079900381d50003103161502800140222010a144135a4519034034860292103014468025014230403258040100006c000d4000d01c00d840b031004888150010345226560100f055400148180541d503180003002242200540e400c07141500a041c805c2d07644010a4042d95583c82e05107850750340d00d030103200800c0340d07000340c000400313103000b10085140c106030703580b0080118958100710541010a40308500c840301400d9529542d0001c002e24055a5142c010360302806912010764828010b5101c2031101c3c5002400b40e500890701641c2d424054982c1003008004010809015035903442000c0342d03680307414041040f02030310342c0070a00003166441c0b0744810f0380f07907002149103044190f401903081404061102c140c1003001d046a868840b00454040c80181c5200c55454a104400c2d4000951400c8060300101d08a02030340c0310354111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 296080665 1250 296079415 296079457
    0xa1d10080d0503011a3f0103060507080a05060307050409140715030501120c0e0a060503010e010e01050907030503030c0d09020d112809020c0c09010801150b0c070504180c0b 76
    0x40c615204071b03400840c2e4018846d00b02c00030310100c42915060440c000000401c40f1007002003040302030303409030b20454a40380c48808020a45a000c041c0d140c000d400c419040c0814181500040c0c0c4846486c02100d001e15a5084081c00388514401551507030004003041e10340f61621030144107040240901c49001082c24800001a801003032642500c0c0e0740d40040343c80a03500d0070b00255406400c405070052409646030800030655907420b1003108000c0e000400000340070140b07103441d142951030041c80700300310382c0059a08102140011044076400300805041e03a680c1c0ca80d062840b0020010200c004c0c1d084421b40c0340310070400100d00b4032410132580c101e50030040b84a0461a400c0009040c0962403a0310791090030401c00702856070090801e842604091324900803070ba101080800704243c2c130a0620b40c0d12626100c001140100e1071901418101c000306140001c20303e01265500424400e450085070789241d015a0500e0364961024201e038031503443d04000c1e40d11180d82107550003d0f400111050240181 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 296081915 1250 296080665 296080709
    0x10509330309120c030703300203060310050906040f0201090305030c03070b0f0403020c01030b03030d051e07080903090f0109080102190207080102070b040b0a02160b04110a1d10080d050301 83
    0x350754680c030b1640001d61820580d503404942d1150508c100030b82078a18140c1d00a100380c001070075407610395285c00d4016146d2900004041c50242156000c20f0418980020f1024610000c10080e40c0b160704044440c0140e0144e2004840b4805a5800944a070101140e00581c418000c001030500c1c0d402420f00700c08503100c0404007078003000142c4008003d0780c05100c0510081d4002e4102070a4000300038243d90601e52800e030700c241520001c41e10445c0e6807004048142d6120b548604840c0c200d4201c0c030303190101e80707442c10344944d0720f2041c1034030309108400e60046201d0780d038800d090302809005010029525041c09036030f01c000c0440c0042c000da001d409010030200e4079010510a4989854004020281c2a101e58480052411002e018001e44030380030421700c4440040651107104c151302c640e00c460010f203001d05001490b1440d100b1154400c0d900c408041200d070490421400282c1d10a507040c0c00a81c6600030240701036945035000c1306e03850007140c442003082604500514125007100b40e038108d9030113a5002c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 296083165 1250 296081915 296081917
    0xf040f0804060e041a011b1b120c0801110409050907051206091b030d1110020a08090601051806100216081f020a050a051308061303120b01050933030912 67
    0xd08a40040c01c3e11011002c411f00c24154a20028000d619030422079441002d0340703128031a2034000501e81022804010708200d94901c4640c0141507080c02002003515604005201e841188903200b003254451020850f04d800601c0402c0041c24028200e030125080c14469689550701218483c03a45d00030b1075550044142d100760a0100c2d2907004000d4604902c048005079505108801078034414400d910400d590f401c43c52005194155561b25072080c2c2c4e1a041402d02e16050b016040705010741900178015500390440113841e90054800ca680b0a501c000002003246811072003000c90181c80648040040c13404004540a10b2155402c110030013800c00c01c1441c0801d038800c81ca060000103608002400205100c0d201800f035040c10f002c88030710510f98504500e40f902005492414114101c00a141c2c201908481905000100703e0000e00c164480704001138424015012014000c070701150000007a1500d059040c1120520801c200d54450480403000b1184e0b0000c58694104e4441c81c503400081c41d00801c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 296084415 1250 296083165 296083211
    0x2122401050306040c17010609150207030f030509030109022d06090f01030c050d0507030c0306120c0303030b0609120109140712020d210309060b180f040f0804060e04 73
    0xa1201d03842c688540003448014240c0701070310820031580c0700801c04400304000e40c0b81d008000c2c582d0380305515800c1c030b5190745588001c20342c0041950b205003010400100488200c80e03816815081040c0c60b002c40c80046800340011000c000c0d03201300c444000454052060509041900611400088034060402840080d101c3c1c0c0c80c80355405180501e40c0e009540c803039046450f5040192a1850401c4010800c2c0d10555106603014230119032202c0f0b503903014503458441d0360001e01202d280c116001049444000245410703010140403d511103015180d04e8a13410200c80321030700040d10749107108503070107503241c000c2c90a103004a500314034020400e03001510010340c1c0d4041c0e0308940320701a0a0400c075800c01060ba10306040c200d8402900c2000c0c02001d0181690304495115903403804039101c01d01d8503080d0201c5a080040e42d104003410103448500c0418080d0700c030351242d43d580c480760490b00c4505050305c000d5161710740182070a400080114010354000301c00300308800240c5003880801007901c0340701d2a0000714 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 296085665 1250 296084415 296084417
    0x7110f0712020d0f02120d0f17070305250512100305060a020a020109060f0506030606010918051302060406090e0f0103082505010507052106030307080f040902122401 73
    0x9076807000945002c800015049104600da41141e0885502040042150960025140d00103c4210000c540c020802d41c04c5150540340440c045c0c1070541c0c1d0854080805808481010790f02d60008403803862220700c0181ca460040c103652060604004028419070140090314209000c1700301144880c80307403d80c44016680d000b8060180c41e0307158030f080750081d00030540000442d900d64000c480850080d22600400c0020000040b50514200013818504000586014104841d960b020050700031414031103070300c0384444040450b13641c403510b06800e4604d000c020040d50003100040e0005290346c100407814100c50098074035005da41e944180a00c0c0c603100910010303080f00303400c101d000f5440341000c0e10419500300010640c4142c2d4441e86881e400c40c0e10449007000070602c00aa03003d01611080260b403900b61809020303440516000b40400e4803030140c0e00000342540c4020601d040485803038415a005003a480d4001c5489480e8000260b03044034050f0b84451680031030780200c000d204c4010304503480305001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 296086915 1250 296085665 296085689
    0x1706060303041a0909010f15020a0819020703020405100503060c04030c03020603060612240a03020d02061c0212060f040c080103030e03011e0e010b09040b0601052107110f07 76
    0x2810344040001450800f80074071039201004001199611a03144602038540303e03006204550034040134a108025024400c01558810944040090180c3c030444054902c192007141008180c4002a0b280005980000754030504250070003200d040001c2c1d004045500440407125661100c00590f92540300707900000d0704803c1d000c0420301c0982028002160400d501600481c0b510f0240080a00c00c05415101070b4400e81d040b0034203403904141d55403000e582d984c080303564005091860340018020144c04000074040c40001c1143e00050103240c200b491444007030f40095540701020b01225000107000c949252041072400501091402e003403085c41d4140c00306456640301039085440a44410a900c294030381d0642d01e40403500c0308601500d5201580c0c039140740c03001c2000c0000c15405400e441c41ca0031042d009540210411002c58007074015560400c0c800c0c240288d03980790082506011048940d00541c00503000030902892650000840b2000e5040900340d03100d484004c9112a15124140300304020501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 296088165 1250 296086915 296086919
    0x903010c0f0512060d0515190e0327090403180e15040b0a051509130209030304090b0315090307050105090304080307060b0f190e0702060f040f060b03060a0204170606030304 76
    0x7621150f964104000504401504529554052401a0f022840d0010034103940c2030000740b8510030710b0704d50700c010704800501107000c91158280d40c90007030301c0c0490f00e200100c001c2030810400e240580031036540050000c00041c030b024100a4551150880104038400d406100010500d4071311502c9405005024541e1041000840c00c1202402080e032000e42d0081e000c08002406603030312a0400a0010038150203a1101a030700100910005013071a0301e4031941c01008150300981d0040101c8040d0381408500090f5a0101e0021030319110881c00300c00b028985520034046c07100350003c042c0084500c04c5c0b00a210300e682e041c60103501c03170245103c3e03035106074001d00505000039902d130032440c01107401904030540404820002040d05040c14a4010001416001881650701080400742c1c4a41e0a0005140c1410409403c0c091080018130180419100142e080108410b5800c2400601802000c0302c9050400d00503103c0298414450501c0481a2080d07080c8440000b0030944e01c51030f40140a181024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 296089415 1250 296088165 296088187
    0x81003030804141605040e0a0b01120c15030204080d020d140a1205070507050f0120090d020405040506060a0f03050601060c47240d06050c0903010c0f05 67
    0x40700190084a01c0640b201c0040340f680410400e8001d401e803108085010607190030140003c44018007038010041d0084e03810f42001c210390b0b580482c11203031034560005214481e82811030009410b9002800603000e1802c502c43c8280c1c1c1360300984152910b0005075209403000362816640d5000000718000495258006822880e40745405481c41c80b9250610b50035410075480120104d031002c9030b500001c290041200310038010704000710081c01100320020170080f00032600041005032480c4e0541040240043c0c440d03455111004190422f0303a024105000324105441c3c85602d03500c040f21018080d80241e407000410004c0341068200f12a000000380c0010303401e081e41110b00c04c204110036903000c40b91041c400b02464102140004641d40300181c050503e114203541c800450410400c0105070a61a00f40442000d00384111502a1150130307032681e0200300d80000c41d0314201074a0004d0170117461700003084600c802c224000c00410318110006c2101125050045e5918813906540a0014a0503c0000341403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 296090665 1250 296089415 296089427
    0xc061406040b0f033309010c140309150a0209060a032a170a0222030201120501050f040c1b14010b031c110a08030106020a052a01180504020c06070801050108100303 72
    0x41010390307640c5e0503884241c9104010703a01c26600400c191707654050f00c4106641c000002030107038001c1107134640b0714100190f100b5511600074595400540c40302c4041075035112698100e5815107800b40c200d40e10b40ca54404098000c00c05040c171960000ea030055100dc0b00080c01d000e1140801071900c1e111295810a0b50b00b980c000e40c000d096400f0503a00300603540d0709016800c224800c0204101c40b69524906600c00180304d0400f140c101d004023424200103000995940484803841e44054500154030210804100e4007805540c290b540d000d0707200c14540c001d01081820150300364040a00921602c00c48400b890751701d501011102c0200c074a242d09804400d0310034000c0303180b4500c901c411149d81e42c000d034071044a190320a178081800340c1e0103441c1d81070400005206445c00d0700c0b214074142d0241e020110882003606442c45280d410440b03100c1e00d0540d60303039400d000207014203005031003151500d5440c501c01c0da40d184152001c3c4049541e0100000d10b540c8100d10240c40780d142d01d10140f4038140345039000d4584c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 296091915 1250 296090665 296090713
    0x40b1204020d050f2401030308060603102105071a040b03250c0201030509070501020d030f020c061e0f0c09041a090705031807030b070e010c061406040b0f03 69
    0x1012440050070b101262040000390301807011600035244005124424404050301c2e020501040c070001001000840d41140585501400503940143e403566002c007007030813030409500141450107902200401a08a01440c0b0310654810700031940595102d184204000a4030040420175490400040c00800b140740095a0007801c0101488202d42a065020005014200003000003610195000c0c0940da410700800e074000142e03030050403049041c400002e440d40c2c6103103224010306888104040c20503405070304030303822a1450010f075111070400490003c01401c81d0082c0c2c0d0b218038410004207800c800d205090600444100650b035280210789424000508608569003148044500620941c2c0e00e418407441e1003a0255550785a9a1800d40c4030084c3c04101004203d203150300c040014030002c1c9814000c56005440760401541954240e8012551208000001009141060030601d007540744061040c2c01041c0032101800000c2d107420520282d042d14001c000d078141d016004900c0c1103a081486454 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 296093165 1250 296091915 296091919
    0x303030f061c080c1023010302041e050c04060f0212040306090f06021b010e0f0c040e010e1005012306070204050408041d09190803070f020a060e010b030d05040b120402 74
    0x2024212a4840f00181d4008684211554100300609684a2001e00c5204480c85103000420790401c00c169168000c0a0305003c0280590344d10000200341401004400340144044101400140743c6200400140e411501c501c001041d40c180c0b2480c4994000718425020079003c8480341c2c1081d156444d2180944100d503416104210000180c4010070310500040c82e200c00a0403a101c9610400c84805003114040c0042141e190030554074042d24001c00f00f00401d241c0000c0b5070100d05400f19035242030060100202407409485480000103607014282c00c4141203440c081d0200c4d0b1a400d01360f04504e0131200c40e00030950b005800300050b80041c070b403580c03001e50081d010f034a2490800ba00c450b0400900e20614100401509035201000082c3c030301002a01c0c9a40c00911104224a9003540c44100c0c0d804050689400e0260140b00c0d03040700b9100304a0a540a50083e0ac148070300d940b205c40d180d0003080c003080c40d40e01a0007103000310b4071068091412542202c844c04092460301103400f0b60041141c0b40500126 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 296094415 1250 296093165 296093209
    0x60c020105130b043e240c01020408030301080a030e04110d2004060c0b010503150f1305150103050114093703030203100e06030c0f0301140f01060e0303030f06 70
    0x800d4004c0314545403030b0a04041c41020300c2030700d000e15000301e0314420700c1c14a03841b882da10300103400240213003900f144000b101500e005454495600d50140039001d10b8200c402d03140b0000c80000766540b8001a403031201400307034855450140d00f9006200c1076030811950740d441d451041004142c1c1d68072650119070342c2c15501c0100365815102c10480d0700c0942c07040d0700c4070340062041103101d018482d05c2c9a4250041c40124000e01100c0c942d01001c29840303200900e01107540c00e07031000144188200c8072602013001d6208044e140391102507004207860307550a000c2601c482d8641403411b10f4288810407683d000341e0740301d401442003501c0c14102800148996102d0002020410490445045030705060740d4010302c02e460240c0c4901c0c00101926080c6100e9009016040c41c040074440d550310003084138074200c03100b9a420843e40800202203409041d083c0d404240d50000c010401000c000707001403490603540296913441f0440d40c20307030415603a80819503003800040c110350007040300c61070803021050796294016141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 296095665 1250 296094415 296094443
    0x20102190203130e0907120c090f0f06080102070b06041d1006151404090c03180f05060c181903021f030b1e010f0915030207060c020105130b04 63
    0x294844031039003900300540d00101c0d440074071070200c40680001e8000324040402074a40b030a90713155686005e104034940307000c800e0128030900c03c0c0050854040e0890300404e00c044540711002d003008018003100e1070700d12882c114002c650100c041c001c49110382c1e00003440402c2034503003c003013000802003455174081c400010b50101c503401c1720a01000326030102140700012211f1811810310800c1c0c00c804900402c101c01c0d06d010003543d00b91102aa400d60740020000600701030301090a4004214801240c1a980380041da00c9080280c1c0211010030103100700c00755041602c82e4000d00c0420b010708201c41c8522a00507001081c2820484245000302050004402c1d00369a01e402080219000803c1d094001000151880d25242c140c0290900d02c0b10548441c0a8000842c150b0800d52054014107810044e0944010041a2041e00d5410260146032820032400c4190000603000390300030801100c1c00f07810300001c1c480c601d0040c03003120310503d100e96080c94441e500e0b65500c107040000806c2281d1600c04d030144 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 296096915 1250 296095665 296095687
    0x6040605180d051c0b0d0b070509062b020307050409020906041d07020c0910061d040f09050111181003180b040b061e010309030207050d0f02131104050d0201020102 72
    0x141d0b2009a05038507019550040907562110007040b140c13002910b5401c1c400c642900e612401a0104450741015461041d6141c50004650074494850425802480820404449280d005420000544076544482803100c40511741040c4d0208680907000705105000c100081a1203130010300c21035030300802940c54a80c490700da00c080d4400036110303500414048410000070580420004621020480c1d07518000d00d8030184900c081e1025005550030006048211000c5441e505440070f40000300074414041509000f40c01e0004000c24003060b1825824441c02c4103c00f103041d42156086400c04208403500c3c0d2840003030049009051008408041d0381d004554031200007404036050f07207441183c5880301c90801c0d0506603403880700540034501c01c00090401800e4506800044d40c41880c0078240410008401c1c101613080006540c42140c0004440180c4410055074960340c4440a00c2183c8910030f541645400d10103c92540682070318050080100b0301452515602002c0c180d881480050b2500307a01c686 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 296098165 1250 296096915 296096923
    0x120f030307030912111b011704050f2e0c02031b0d030b010201180605181c0f0507050a0201051b0a15111312020a170c010e090105030604060518 63
    0x4207903000035600c030418401c1000c0500740c415042501c1c0341160348003d0701601140c446110390300c002e20000800c0a1004a85d0007981c045515805100141c42e0a15041c1446a11142c80110361501d0b4012410030a016540342c1c01c110215a6809071400410422848904001c100307200510f010743c4028042c290203504000c3e000b4102d0b1002c10090300501c06400006401d440c0040c1c1c40302c1c1075904002103c924800341c01100c1300c003690451004916a119400c01c842070640c00401c410983c0121007240307880c0c102c20100c407400001c0903950300e01c0c0320400c03400c115507900680b58010500d41180220318050361007031000d403800d196801880002c103100242c40382c0c502050031600326510305d46c0022145d0f0b00030451040640c3d00c50030410031494504076068501d0101c040d03000301d046a6140c40860401e54941c060300101510840110004803001d442a8a580f05c00c0f04038040d00141c91101440703110700b040403525040302c901800401c010385036075a491020b400001c2250003100c48004500c00752800400c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 296099415 1250 296098165 296098171
    0xc090d050102040e0f07051c0216290906010333050f07081003080f0f0408160603060b030c22120201031104120206030703060f03080405090f090c120f0303 68
    0x340005aa942c030300015001000341c010200c81820080b80100301459800c041100c00707105100c01040c400b1b0b98000c50311002805101600348040500c0da80180400030a00682e0110070b42c1c0c07a602c2c62a442d050306030b91b14000b104070f54070800d41c1c01c024010400a413a080c65901c07110000e00080d480100f0603a00583c0202012803449012a220014402542902ca103402d81155a0786824440c500d0046040d98000304035110080000d9000203054510f007543c02e09403040100c40e84c2149540d01d07640d4041660380c91507840c1c000000c2c0e032020f40028099020340b0940040322100e04001d400d642d24503a42d21019084480503030828015540007100d0480d940c050a005401b6160186042c4a203078000103003104c65000086030080c002f044240b240400003680c07141c28641c1281d500350399540e089411400390021f6403018040c4451400e01004000c5148050400d90320f081c1c0d005020b5581744800240e81800903545d140164015140c2c1003643c1c02c02e5841203c402c031101007140e01701c9482c040d01c0c61450f8811 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 296100665 1250 296099415 296099423
    0x80a080a3f05090a23100905010204240e090411040c0504060207230f0a030c09020306100c030905090928060b0a0b03071206260f010c05030606030c090d 67
    0xe20510704818041d104241c0c008005000621020344141c0e40c40700d071402c10007110000608000d1004581c120100200010f0080400702400a04070928082c0e010390401d000b242015202840f00000c04c03910859007145c02c0201d03640c0c1118465855043c41143d90b0040e00580c0c04140300b40030049662103078007440c9482c021aa40d0180c2d01c3c1c2c40e11310020301f041150381220844030061003e40001c440107084482060b501114044a1000d0110016a0325481035000500c2da04406000150303842071640551300c143c209891301f90100c418801c0c02c4411603a20403000307011401800e000e00103418100219580300a40d101107a079002c66803914014080081e120180031350380d407440c080d07040018500400503650300944644541c103091815028813404001c110104006080c40c0360007200150703820000090180054101e550054510f1070700c038403d030303a052403040c6100b4070304031000441c014418142d15540c00d85c0d80c941161555010429654400f41100d204154188105210f550342e43c48400d80f61446 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 296101915 1250 296100665 296100767
    0x8070f0509240c2104060507062a080417040b0d0b01020f0a061a060408060c091804150b0604050a0b09120706020f010f05060f040b0103110a0905040501080a080a 71
    0x54030304130050001810380c1803c40403078248002c015a58221003550401a8800310118080b5400410780d440030040642940002c010100f092142d5034001048a01560060504481013040c2ca00708040320b101d244181001c040040003201c0566026509c9645510f03014810b46041445400e680f52511740501e00c161202d5960764410350029511000314034035800191920b0703040504d0281d20300d868490042c08560800c400107030030440381e520f008080c8030b60114000000100e08186c1040340f0803049000c10918914a4100c4101180c9031000035202210345c000c1442c12801d061079010051900308140d803030740001188641014680f0140070106c0940401d90060101c03090300300c180340c01c0d540e0071115400c2452400050011a4031900c40742841c001041d03c010a01801280040b80105000040c0b03441803e404110b21801d00e83c0700100004441c0111020310031a600d0303c0e10b140d221841c10000408400c010401803500c41e0288005468200501102038017241c50541d100c80340382c8401c0b40b51058005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 296103165 1250 296101915 296101933
    0x25050c010e0a02012109290a050f071b020a03110306060a030b060d060b03010507030c0f03050105030604030c021801060206070e04020c060f041a04050a020a090506030c060d15031208070f0509240c 86
    0x3501042c07d070703009200e1402841030303007455800e4a400020240c1060f04000c3c2c0994030b41c0c2c09046003540300c10401e40c09002c180d5081e80e03d0900300992140d40180d54400c0c0100750204402e840d0041410040c0d0350802d1140703219813141001c0040700e01150001320384007a00d03801c900308203039804c2c400c80b4480c0d040b50b240800d141c151044001c10020500104c102858917043c010311154600040c01c035800307940b50400d0091030f4010300000e20402d08000c20b109184000030000324100d41d010032003501559094468000d4840e00208100587c06109602c020542c08100002c981d02d040c0c50056401a02952045c0c105155030201020744013803c40b02030326164480101401113040410243c00106941c1d8405c0181d41000400243c07100381c1114007520541000c070707446814010303035440418003100312a440725445680c0e00c1c20610110807003801d00049070010000406050240d11004000f495950f0303041d18010180041005410031b442035041c049921138010000c080c80a0010564005424000e1006003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 296104415 1250 296103165 296103233
    0x30f12060105030903300703091b180507180b071e0b060d02030304170c040f0203071b08070b0c071b080d03020325050c010e0a02012109 60
    0x241026000c10704000c2d04008100c44004080301362504200c02070201c0000050000040c005900700600514074180c0b4502880910354140e4024145a80300c2c0042400340b25a28024059041d0030340300b5082161100454040c0c504c045034001d071f9000813581001e107154043c4001c1500311420341d8001c000f10410004002c8280125280c1450740c100141602401c02d0486623a41c0302c2e000340203030800d4060400b00301c0003411560184140da002d03180c5194210720120064403803996600094808a005a292000c005503d09882c02101d210300d861b6103e1080d107182850511040d04407084090740d6040c024850342000606040740b0034012003558008644a240c1824070602141c0c0c02c881c06c1a107981820b604103d2408082281c105080d490f050068490340d0b0044201e9111208402e4018180c5031410031030705003500031003c1e002441c941d100030840c0040010403d40c1e00c101c0c9000c0079000c95120b500003e2a40140c071010402c0e400101c40110b151140307503451243e944510000c1442c00368012881d00303604 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 296105665 1250 296104415 296104447
    0x4091e06181b0507020103150314010606120504021c0311070e090f010605030c04090501020c0f01020a020d0219060903050c0a060605011403060a0311031c08060f031f021308030f 78
    0x1d804411003000581c0d0080b00a0720501c182031009050603200c59021005020b03d0011000640d00100307440b165691840303041780284454000c413004035200d5614480c501606102d8144a507501514101c8402d242c411017400d64a000d403812410403c104503450751901c014002d01c0010500c200081e0001d042070843d50382003003071a94000601342e1410208001503500000c140540300001e0710001039400c0603050142c068466049900b2481c401c11800d0100010158010800107406509496100307007100c90890305c03285030070440c0100310050702e52400440c0b040d80c0046075482c42410842d1410f800b44d900f20b400c1260901c41602c46030399a26003080b16503049054600a041464222803440c41c1039070000e01c10300c20f940405000407040c100c91519a490412107004d0724640f404a0400350f02c9046001010410105ea0503800b40c0c6892001843c542030002f5802d03811488114245841d240d44101c00000390461100d040da8120200c80000303403444288000c1410a00c0013500c03581e2071520311780000b10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 296106915 1250 296105665 296105681
    0x13091b030e070501180308040806060f0901060c06051005090f100603060819050c0904061b05030c071103190605220201090902070312020c0624030304091e0618 70
    0x14181008070345003140002090b01010340310709082c41e24148480407005109104180c100400d14500007801081d510070000e040c91255000702c0300d0b07252041d0500c2c01d0001200c8280301d0100440e4800f001c6800140c01d0390003140d0300c201c0306107810134520b46d51000079030080070030f0354018440c071901418030032118090300c54007025040d030381000d00045143c51003041c0e1f1500c09c030000007000c0320703045025020014284030b01021040b004060104600f01420440010040c80302d8507010381000711201443c0c80e0150041c0c03071040071020502400c1450075141c2d800704d485109510b07603150113081c0c481c1003124181c184c004412800707210001410301c1d01074040d40b40c40b540041940e2042c06039051200c0142e80c80440341c4107a8144107405600c410081c41d0581d088610f0071284440c042c0040f4440c5190080000e400e171190b20302a06900d10b4802c010b003080d0307404400d00d05454150700100420b0042c1951904120a4429540c1d00c1902c4d002c0580da900301101c040e0342014803131a108898200245e8440d02618031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 296108165 1250 296106915 296106917
    0x3030b011215050f150f0a032d022d090108011e060c0302030d060311130605010503011a2718090307060b030a0609080a030c1103040b030c13091b 64
    0x507081e4020341012491000f8801d042c411320100700071242589400130701810140c0f9280c0d225468503910000010b49030040346a01c00000e10b000c80040c100050170903c1c0090350320f150301c490105586d80300744901035032014080c00d40e1454200b20441e00700190f42070000c0044880e200e0b0341e4860002c1da000404860060384103d00118210842882c01c03030340c1150301d2040380c1060400741103c8881c2d14059055000c0c103c0032150803443c1c1140002405008191014900c50403500d8101d40d014001c455800c540a501070030b8002a4140010703c0301c64807603060b03c1550031f48079150303608082040d41d07904210b0b01c3c1014110742740798040f4a826540c0c1002c800340102010382103c515501d25180400540e01d016542c0c1c0944031903100e0741c1102554400744801a040e541103603040c00408224140251300da40319002035000245001701416400b0700c140009000581c0300c0d4003131490207281124101e020b8102801200000700200240b006007913000c200c000060035002004280e0841c1c606000040074544400b0078 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 296109415 1250 296108165 296108171
    0x7020d0b1609050a0b030f0709031b1802030f0a020c0f01091a0f09060c0d061805100503010207020105070f0201020c0603040501050105090a0506030d180906031a0108010b06030a021e0703030b0112 86
    0x405805c203050140c940c00044981d001c0020780c2c0710841111483c3c810350001e010420410b61508214000d06e0750101030301d2140b050140c484250000a108034441220740700c2d41d6208600c00700e003002d80c29800078200400d0000440d4083e04507644030f542141d42405c011510198002404500031691010540d4071001410740c505a61801008040c1c480704001c0000301031003000100000c0b144602d2340508081d140c04014203140d5000104044020581030b5040f0001c40a00c01c800038039031505000701c130003056040c0e60382c038103080495898010080c280b41e0102d0660186040b90280d50301c52901031881103000340300100b40783d45030000b032020800c80540801e820324104402c00009450001345c0c51003e42c600e140032042e200b113040810303041081070741180c080341c2e0074040000b00380040716154000849058181080c0c42c0d9868003a00c0c200e40c1c0d40741280d40c00034400e10004001084a80c040c0020207100003003500c00d0715105421660540c845403048001c00d5640340f510019592004007003181c044051010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 296110665 1250 296109415 296109419
    0x3010504050a1401090c1d10060e121c0c0b01080d0504150215070324061e090504020f03090d08011a070203010912021e07140607020d0b1609050a 64
    0x103a0701c450702e28402030540c0720045001d6100c00025486803042a4101c117000c1c02e11a15442c25480600079130314000c408440410104810310301441002088840300e4480d88030340e0200c50203010780703100c041d41d540f0316500404000c0d03083c03002205480360803002ca680e107520301503d861510318104001a00101815405800c031074254541100c100c0c1c2c2940c442000142c00c00c1305100c408c03850010604245005d04da074660601107200d4058200ba1524038400c0001d90403a1801080c5a032080c14074421100001e500d030b14405985c00c408800707004401890310b805580507854501080583e40b1085546840000000070081c07070b07500a00c04050100210303c0d144a0551500b04050300d0481014441c40380010005007101c110b540950086410940c4a0713940640c00c2141103000c2d4075045c400c2d081c00c2c6210340c034582c06035004c500401c040090315001d07039401c10b8035072100080c03014070741140b2001c9070403140e060711080204400540043c4980490704549110300c2028400404490155120500030f4032070b4041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 296111915 1250 296110665 296110673
    0x503030307050903011b11010605010201050609070f020f0a12080a02031b0310050a0f0305010509030a09060c031b0b060a050f010504030206130b0708093a020a08072303010504 77
    0x8036a008074062810315110305180000a0040c4070765a4110000c2d84008101c4c00c103240c0280e0441c0c000c0c6080f200800a55071b9417401a030980340201c502d40d034454400000200d1442c0245681c4668242910458100d40031100541c1d2400d80e000c142039540f50354110085419680c4008400d901000c41942035003981004202c00703c4440110508042d14040440000e8000345180307490380040800a001d9105942e450890540740351041c0416078041d400c100000b078401200100f00c030b000400683e50030481c42c0c54900e0440d402540410110200200c50078000c250490b02006a00fa650007100038070003c1c200007040107100d003c26480240565000c3c0441075084c0e80010507103003202e4041d00d010b99907001c1c0c8041215030b00602d420403000140042010030074446a030015000d015419503011000c00300354843c2d0410030b1051048400d01e080188610000d83c4c00000800d103800d4070180241b00440d49540e07003181000c980c0d4200030510058010141e0440805070390003401244168002c108904040c0c03a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 296113165 1250 296111915 296111917
    0xf02030105060109050f040c03020d0f1a041509020c0312070509011e2007030804030b01031a19090201021501230402190f0e041b120506030c01030c050702030109050a05100204050303 80
    0x840c14031540c0c0e2400103231840f60181d0120303151041450380400c01c0e42c255600c848020185c0400f544045a40301c603d404281c1424030941c1080903070030180758503191a0080d940060b50051041c8901e0307000920035444070280303180d4250700400c0c4a840e0144c403010054001400440c0c001003000350b40300171219841d0307650381203080140c00c41c0c4030103c4a80c284049910081c504078150784000c04803440002d00005000c141038400341624480c1c0c0103d50703400c40012a820752035500f03540c10002e01104424071051003c0b25072021040c2c1d84180162000303007100300d403070600c942d500340d01c007214480758404420080141c000300301c020903a08641c00c5061101c1a52030941200103000c0c090b040c4a404021041c13218016008000c080f030004200380400e2660800d10114104200e07172810200301c2c1ca40e94a222100c050080b180307d880050000c0c18140309a100443c080c10030700101e0300034040100840000350700c0a008116031140900010501014640b80c614a41050400ea09800ea0300c14001840540e070084 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 296114415 1250 296113165 296113189
    0x50609010311012d0206011d010311061c0f0509010b010311070209220302030415020a020906060a0c0203010f051501180e1008060709080d0e0105090d0c0e040f0203010506010905 78
    0x7191030310713100074040003016016411598000306000810b00c120000c5500050280c10f03540c5008c50304002d04030607220210010020b0000801c171800040d201404e234100200600303100034180390f0001403624a081064201c804142084140c00c2e219810405078020034000e400300240207203010003204444402c1418503009901d002841985840003250101c01948820080c01c0100b4481402e42c11a924019581c0e40c030521071030031410000b4000326041d03400818060021500606203060983d0b0f04010000305a02140f4901e003800352564140c409618244600511003c0c0340d500001e15040c110004030b10094501c28540c104907074402075913450910240300c0b00c2110341d0107440314403980f2a4081504611266000407459208e40d900308240d013030780035070000103c90100041c0d5022042e6540121040d250f45104c4a02041d000c1101c11901d041001c0180c001c1e60007401802c0d0720f01d8945208007000c941c161400d07940008040990380170b503d400c1c03203030350b4110909007040c2c0d40061525000c140c447d0200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 296115665 1250 296114415 296114417
    0xd1103010e0a15050705040e150a1a03040b100f06020c0f04021c0509011811010809120f0d110304050d1b0c030206090d020907020a0c08011116150c0c0605060901031101 74
    0xb04c0c041400b035030080e82030b18040d0100042e0480d441c036025502e80c041044441501c4d1168112030300005030b18000901c981b00f0031030910441840d5aa494542015454000d001140d0b807402c24040011010814806c005c00b4264580c040c01038480804100b1144203c403c0082d8441d0344100294510030301607682c00208014064400b25041e561a10700310b00500f928450100110315640c3c4000800000c04040708881c4404d0721644482d464420030f00d030313881201d090700c403258038810065844540ca446025210070310081e240416030010300c0d003049029802c2520219202da00010b0b80f0384090b50800030746225106006400c512000146d16240f00606040c44041d0041000080502c102e0b01c0e02c442030191550064902040e5042c40030f4001d6440602c0b41d800d5582501c03000c400b00d11014180512851089140c103c03d00303180c103d6188000c440c417034940c11105140d0a0581c035405640c035020310340c0311101c95207810b0031131038140c203164081e035500802c190b20854443c0d00600000e40315200229140e042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 296116915 1250 296115665 296115671
    0xa050d060b090a020703020d031103011a0403050a05030310080309090106030903031407020318010c12051b060108011509020a12020f0c010e0105180d020c040c0e0d1103010e0a15 78
    0x10381804801004041c424540110100d001c000c9100d035580c005000e0548242d0031a101d807844034804078119203006190030100d46003040100301a09100c0919643d00103000341c0070389040e0362035403100d1505000c1c00044601341c0001c400c002001c011440c021008081201c09149803140800008244070014011001410740d103003031480a03d480780d80040c2d8080728104814805052010019650f03400a681c00c0d110008002002c80c06544520410782c480d40c2d04c0700e0b240b2101c2014070819201500841428010940103001c940301019080000c14001c208500000070030a06503182e400b001c0d4290b8101c40b100d240100310b1541503c0d400a4490948400c4040041c0c0b11040c4c2c95512a80c0e21455402c0319a0b50b0030035603481500035040d80254010f00222a85084e1140c8001e4141d454000402d045809604041480b40c03039030401d5048441c131380f0391510f04984204020000100c3c4050300c40c030242c0c1e121214a02c040442d060034825007100d64030303c10091801101d030390b4900c41c40943d80c000c2200c0c0561 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 296118165 1250 296116915 296116939
    0x5041a010e1e0c070816060c090305070b0711090a051f0806061311070b062103030a0e0a0b040302030c060a0e0304093b19080910091e0602010e0c0a05 66
    0xc1d850141d80420380c0c400c49440d506c164842000f00c05002040e0305644d194504010700c400a405a45034100701e03a4403401401e0898502000b00c0c00941000c2c4068a0b8411800b050012a64594046520484500303c000681d070408640c403a03c01b2031018680c4031410300300306091100c820000303120b0b5404201280c0081041412040440c0034141003280d00740c4842e070118001c810844024011442400c09940e0323690004480303150081c1030203200d2016100c542040010030107142264019248481c05101214400c000c0c0d50b41d42c2410b44030407102540141c1000c250380d01150018805181c10404180050014050400080d900c038400e501c20740041c965500d540c00a014064201044002d080701c030f9014104914400351206003403482d00f1802280184a0306000342141900c4c8a094180c020b403040307042030303040340c1400f0800c45c58210b1001802280400040c0e03e040b020151190303000340e55a2503d0740c61400c080030782910194044980b894202116500268071118030b84000c8440c11103045d080301d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 296119415 1250 296118165 296118181
    0x509030315030105221401020315120109020f09071e09060305150901120f05070f06090e0f040204091407090b010207050d02131e02040b04060806060304231005041a010e1e 75
    0x306c0380c0c3c1181c03180d81d4008400c01150350380d52402103a8040003030310003104850f0a035078102e00b210400d6070001d600240c888296400c0b41004060190711103543e00342103800d40d100d46110440301d1503102107040090782e04070b01808070030343c5801402c1d007044c544003458140a40f494002545120705008000010580c1040d1034144010006188050f580010913141480e86519a0302280100d501418011402c00c00000407a804041002c034407401318401c00310305941b01c590801c001b03000201025910108400380b40305000b0005d0040c00000d1031507c20014056411074006420502c95606c424810140b0b11007000141e100c604904514030004180010014451030000322012480300c11040041c1c40440c010410a401c0c50082c400d0301c416413244902c0ba55402e040126074401150000d14030103440f511a640600f41c0d00d064040c003603101042d03510007aa4a0100c40c1141c404440c240c42850950456040e850551344940d4003400c12003c8800f401e00d41418402e511202c0a03143c881a02c40010000b0540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 296120665 1250 296119415 296119433
    0xd03050918010e0105090906010b0307120e010c03090201080c0c07030f0204090b0106120f0b01050901110f011a0f0a1508060a030c030f060c05030106120f020d050903031503010522 79
    0x40514018801c160350f1110008560880709004007405041d5203408240c0385440003586904031040417100d58590b0303840441c02c03240c00d030181401c0382c181074450064001c58402130007100e00c0103803a039a000603400034034000105594000751505003105002c0001e89008140811402d003038a8000341100004280391010500034486d6590203841001c104001280c215400b80302281c80d41d4503021b00340544214040d220781101c003411132040c08100100706840e083e50007000c00401c2c0c0d0b101c51082c0c91420141480444c01c4d584190f0364400c01d420007016444480c6002804c40300161810394002e040d10341010010101c00c1c000c102c12605100a000001707409035601c5070070102071503100061070240385c2d9a18092001803500380e000c03510133040103c00e01e442807241d01941e04880c0349170780e59107881c502e0b480b50000401c00701c281d2800301030702080210450481030041c40d0003605004000d59072071a100201c1441700100390141d40c0329904100c01e115450040c2c040402c25a8240b0203640c03500c040c186003100341 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 296121915 1250 296120665 296120689
    0xb1e210703030c030e03031602120a0c060306060216080303060919090b040b1b0a1112031f0f0605040509070516050304050a0e041205090d05100b1507020d030509 71
    0x109109203080402010f50000003450b50034801d45509101c4403a05003056200e000c0c070420080288000290100035182c038a02100d2118203141c142c881992950701c540c003a40ca00c0ba0042c80110341c8480d400c00c2591b50400800360707800003001e40b09200740c0c28034070000d40f21320010300942c7c0310b0209000071560300d42110107840081e50f145881005084803503d0030710014001154282c502400550004008080040c21004803211080540740342c00040d0700141c401d108080b0358568540f0460b651000980c11010065025168410804116885041c03190640030b0310381d00440300054880704100800c641150580381584d00480311403030241e988640c112111b001e142a0482540c2180c000007052150100c0200705070f41e8207807030608031540c8659540910300c0c002e50b4000c190303140031035403847c43c03174440e00240546050003010203a99001c561103007442c100f8a2040d0b0341071580c0d2981124910b1410f00101022556030182c084c0c10b06c001900011405443c6200150a0160000341c49031555145510042 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 296123165 1250 296121915 296121979
    0xa0e150f18090607120e060106030c03020915070501110c0a1707060f06050406150c0f02180a0f140c0901120f060e04060b0103090f030f05040f06020607030b1e 70
    0x84035151030b82030a0740d984002d0300e81c41c02049003c00000d0301e0300b9440c000c0141220302c403801080c0c141d2030580114010900c00e6540300816600b0701041e050350b940c2d4018401501c080c5103003a519048141400c2d0300311808404001c0e0b41c01d400b00300034a081c00000c2010310b40c080d001205083d1031038640424150a22803020001c002924040501000710345650042007921420389080020075101c2c2d5082e69280d40000703a60001c5100b4a80d90f000280c4c099441b084094400b61030801c418404501d4100000400d80f04240384980352a82400e6190052155440b01054050503100608124030f44603450701c035166800741004400c01340d40c14110400d4104120b00301065000700051551410004180942550101c4107c0d090003403c0000c0e61007030140300c07103d603004446034007000000e64003600c89c28800c00c41e20b800c5c40018080060b4500d6111078a60051090ba0054492440c21150040442d20382d02541403060340844102144120207542c3c5404542068550f800e8200640300d244da982d07140d4036a008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 296124415 1250 296123165 296123209
    0x80711011506020102030910021e1804024302060a02010e03040803071e17180913142e0603020415150c05030d050c130906050a0e150f 59
    0x241543d070550007103100f03902c1c00c07099a4840d441607000e201a807060b200310f0540180020b400e140c19103102402401c0580ca0120904451701404022505980107014a412904c414802e050340d20581503090040c0d01a0007210100398800c821829280c0c6480741c040680200348c00f0807a006c1c0c8038001d62000100c42c0f00c607400c513038845940d164100c1d0380350302a00c03084405001c40d051000704071929001a83c51682e010958481a800070100c45440350000003913146000d0b00130700b0002e1151580c0c1c02103400350466070030791200340b002402c080d090303100900c051050961207030014071903d04010009803001c00c0c0225104211510310910343c000340502d0342020b0350252424a44980d00c6280200318801c44080405e100c0410b03280074000e0780c0703085042401a045400030855140c2d4041154070a80d8000c60078183d80342042c0c416406480700d05429007004207410754030681803201d80303010b0784440300508012951404510701903404102000424111078061020340165401d60707699082402c81d61650000c1ca0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 296125665 1250 296124415 296124419
    0xa02030c071e0f05030705121005040305030103110d030c030318050f07060912170f21070e04020a0c0f021810060801060309120f050d02040806250807110115 69
    0x502800101080010382219040d00700140080075440f12508581c0300a002e00212403a020901c00c0010a0060f001414040c801502150380140d21807680294007a507206506c96045107004400c100f05454490310580c00c5090b2240041c1c0d024002a4000c0d5251502086142e02d0202c0342c40325600340f41c0001e101d80190320095200e000000307410000c440050399411030055403202102030112403040003810324080e000040801441000c000c02c1508039000c1e545107095a100350012a8244883c210000b01d90f4071018013010507403091038280e061008403403c520300a030228000e010008110802085038102a108200359501d0b07000b10b011100e6440c020051307915042906e000d16051078010741010820b01000030035100d200340b00700d0f401c01d03502c890b00d001c01a0113a0400d5030003854003252081007001c00c01c40e81e1750603032650015100401c002001013003507082c012081c04010854800c605618641e00003892091030780b09007504d030401c6107800c0c0242d5404030b03514902e01400034550f1072200307007501406c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 296126915 1250 296125665 296125679
    0x60714190f06230403050a0e1203070b241c060c09150203030f070e040902120313051207180207020d030804050c091005010e0d021309030912170a02030c07 68
    0x107000240b4421002000a4401c1c00c41c04100b00c041d40e920b07440180c94820002e00002e025200a100225046c1041c3c0540ea00643c0013803020380c02c642d049662030b0804141075040001076091135400880c0f11a41082d00c0000340c207005204820304496500c1004156100c9601918088581002a4004400b4400504c2055015003800701034459444e1240161109502042c0b021098a004084d901005585a240c503401110503071800e82c001a401940d6890000042e0780d00110b0701045151703100915101c0901102c50b00034810503030b000314040c042c0718088844110000c1965001d407050703080180c0000c0145501403000b40601c00c002500150035100c01c800b81a04000c41c1407085200f04111010401c0d8841804a001000e42c0c0000b1f410014050500c510f40c083e0030300e41040300c8041c0841030342070380c00d40018514035020028907034041d55640b901400e140e480044000540f030542c1c0c5c094000c1c8800d46d18181801d05405242d01c003004013041e1480910310a200b00c1d02034040001c110303408580c8030f01c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 296128165 1250 296126915 296126933
    0xf0d0902120f0a0210110f0709060609030804060c05070909080d0608010b01090e060114030115020601150207030b0402210c1009031109090102071208040c0b070206071419 75
    0x410380c07080344101d03014801c5110014401020201550242c10704450702c0c0d00f0f02c004d4440b41c06901c030500600d04100c00640408000780d00b0070781159001045c0652070312034201c0c2100c044d80c004104004101c00b0034030115100608580483e1564904020781314084d00303040c0c1c03c10045801400100e802c189164080c010280088d21048140220400040b6910301d48036080343d242e640841d01150105d441041120000b08009510550604100c6c440350984101514170394800d03000b002c905002c131070f660400142c0c100b10713030b602500440c0900b280c12400b2141c007035904c8800c0d1000908881030030b800582103449041840d0703041c0f1401c0700d0392048542c42400054941d1150b451160180c510400d2080801c0e116100c204116030704064046090700384030017030080d10b4600170441e000664017040113070300190000d000d004440003140c0ea00039941c141841d0248481020360302c0540030a105000d41c0001d40d90709012103070010740c060901d118401c4407860240c140100c44007107481202c800303a001c50501102d99 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 296129415 1250 296128165 296128181
    0x60a0c050607030504020d0b04030201060b0c0303090601060906140a20061e1e06030c06130f09090b0c07051005010803120f101e152d0f0e060f0d 64
    0x40c003941e180380e0700d20504608840301150040e5021541145030340105825004c0190810701034400455203a031140130a8016921484034010b0a038000003c00c2034101060003023a016080510344498a00d29080d0b0041035880f03504c0d4040450342000a400d00e03080c0c00f41e6125414451000001080d0000c81d010701900ea0700e086480f10350950340c120f04410603080e180c0e6558803540c6c0300800394581c80c120618001c8000001003c440d0548508174042c041c0d5924100a04030191a08007801d92560801c0c0102e90350301059400680b02900313203200700c0b00251006c600c899000400d0202c0548414250038100e15005180b04c0c0740c501c1d43c0c64203002094024010000785001e243e11440c0e11440d84902c09040410705044440340da441543c03100500c48800882d42c0c02c0540803589110a101c1034658140030320f01034451603018042040020911401140c98034819900607490308440e0303400407001405071015425400240802c58104c68034100340c0e032050142c1d050080003119403529590344250010007803d101e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 296130665 1250 296129415 296129423
    0x150b04080118080a031113080c01091502070611030909240a0f36140606090904030807050c06190e031e1305120a1101030c05031305010605060a0c 64
    0x804603940b01c00c0c0708242408160340203880b41d10b4100c0303040302100104051a002c0c1480202080b11944810011840030040e12850f00506a0100c0906c0003402421041d4041414005615a524200340d0045645402c481c5079040c03a070010b00c503c40080cad0451066410859020100b003060020f010003101c558041324120310400d41160062108102c411502441504040340b10700790300748608603010a44040e85413401d035800f03541203514030086400300ba645005203070140d81d40c000c483c40303000340c0800c0c02d4126600741c03840c0740b03040c01000c0030489504000340301405110021000c031f1a414401c8017100c40301c00104059640038203112050045141400c6580c5403402d0412020351127002010088a02c0100c00350510004129820020007041e00001c0e150f4266424001d030000da2629440b81c140c0c411000d07103001d081400c01b10301d8030f03d40070b06041404504062a04620081040c1c02c201202c1d0000a50b1003040a0101c4500c2c00074003508060700459048180400c0140c02c590f00200c601c0d400c180f003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 296131915 1250 296130665 296130671
    0x405040f0c0e010e06190201090f0605060a0e1e0403050f0a020109050607050301080304060c0c03020904030522050307050112091a0709080c0a030f0c0b0313110a0302100f0201150b040801 82
    0x1a00b0b004542421880000700c2d4000410005c00400b0a10210b90310030070b5210740000315243c0901e0f191407413403100003071054400c0b0762590104440b5181c00503548000d0000c180c542d1415040c80c0405503d001040701640b442041000046001d05003c0c1042d200a6240c05c4005a52107440850003406055075140486e06441801c001c580c03070340d00035030603641a188004008c500b8549000b00840300090008429604a02c1c040004005a1a22450b582c400c0d4025181d181c0c1d603600c1d841c5c400301042c4100004400e01600310b4814002950007088841c08c9610920340490040302030b0640a0042800c40001000300c0160b4040101d444a1007603485e100d004681c0710114426900e088150b01e0f10754118019a0000c0c11441c05d00008641d024610740007405150cd0352503454072405420f2aa90055070024400111052100d0420480400e0407000240540311354001c02d25641c04030301d034441c10000d0399041c01260b0b400c0309042031003503002901c3c1625a90200250f02da55480310714081c0d00601400e017465003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 296133165 1250 296131915 296131937
    0x8031302030c042708040807030c0510031a010e04060506030709150903050d0813170301050a0909110d080f120a0506120a06050c0c060103060b031c0903170405040f0c 73
    0x500f61041c030026410314000c140040440094070940301d8100101212000014000801d07802c5040140902461150700c1c22411a070504040040403c040300446081504000409449044000301019240003e003841003600e42034900103006440b00d5000710b5003104000c82040300541d880386100b81103841c030401c0c0d1305401c05024070403601044180000f81c0305030b10a03214021218400c0c3d04c103590000f545450543e03481301598070400648040003a882d00744c1b5011006010f41d00d07000d00c0640c020241560b08110745034060b034841890704003c92115214100011000c800d0001030000c8400170494003008654442c0450204102c0c2d090035a145806030f403418000400e01c3c281124241c0944802c5001481107004a580d0517000c3c050041c405601e8110138840c0200d800400c21640703001c1e600ca01d001003070a404410506142c08482e00110340150245d22408a80725080710340349060303039000a01c01c0c0c040721124103941c3c000c1c419640603e030403038542421044844481e40c04644101c101c0d80d21041000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 296134415 1250 296133165 296133169
    0x5070311010c08032404050f01080f010207031d011103031003110d240204090e07080d0503070804110406030209040809030709020f16170a02030a080601081e06040908031302030c 78
    0x101d082e0710018000d00e030401c0820305066401e43d44920104c40340c070160110303880c03070300215050b6041612007820300e403150340040c05403203401d1180c3c4402d0329001000b1420280b080d100204841a10121050110344001d50501664412004026480084000c6a40e28246200e01840f224400c0c8020f64041040182c0e410480c9080702110070001d80040b0000c020400c60500c91f002044000c000325292582040300244c200e8060148940d0488090003406e025440c00300c605003030107100da10a8007040401c008000800350030072811070304242c10043d20b5402e800f0010201c1c00600d440c0e000654001d145c082000200a0a00000c0c07901040a42c01d0310039841e51080700b00e084e80601c07000401d8020085c0b00442c01da05580c1098804a03020702c888071489045003c0a2809900c001007580068100040c4540e101d608042116040342c03081ca0711060030b280101c600040035001c20750800d46881e06c080840c1c01a500d58200d00822034019915550340c0c00d00c11089481e1020010f0220b009003c0c11400300854 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 296135665 1250 296134415 296134427
    0x210092924010504140f0405011203111519090506010b0c0d030c0e0103110910020109020a0e010501050304030507060e0d030e01060806010f050d03022b110f0a080a0309020d0507031101 81
    0x503406840c1d00b4101130403d10f801c2c94488210b2220341e000b2646c501c4481c266903440c0134150007032402c516001400c50550034000c00841d1041d10008030303a405085ca00240003481c85007039031301201400d10000308400c20800e5034082c040d4010041c2a92040d8000410b080000d4130051180b20304400c11030784086c004200941c150742d0100903030b46c04904080003000403540241c01028000322000b0405142c54000400110304101180c0c1e8400141c0d504c90b030040c02c60400c4540308000d044000e50018656140ca40002c00511000308014108480840c08904019150300051045504841518030b4a20312000047c000c140c02c1142d80c10540c2030000c0050340c4900400c003203042c0c405265080202d1400d09080c03050301900303403030100c0851160248508009808002801060b0210508603040d00c50b40b040060009031242e4280741d80360002c1d4130070522104001091441c0960240109843d86901a010b4008110030807001c1d4000d9010761070f00d000c11030003140103410f89104d88032580703841300108011120 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 296136915 1250 296135665 296135731
    0x706020a02150106020f070614040b0d050f250c0201121b1e090302040914070f0906150e090411031e06010b07030504170703060e01020306040501090c02100929 70
    0x350f5000000284241407155070002790660f60048514981a9603410012495001c070080d28031907507803581800481d0001d0381d40290080c000c59081807080f412910200c1601118a088105110304580154116401a07400c92070380d001c056402c0111041142c00500224096500180095540c13000045030b0b040350840202c40301e82c5a0b0701d0011080c00c4d94240700040824038002d0300c0d01809440e40c1040484c042101201403c5007c0300400c0c01450034280300c0664905421886201902c9a11580401d0340101d44180ca09000c9a50301d64645840c113212a5201005450b07581600444100000c1000c0c00300200103440c01040469010341c1c4d840d02803404034003403820b00400190b000c00007004180911034540c0c041c0130400701a1102940e03295101400c0b80c01400c510741d603c0e5000300070040707585011311400303004100c168400d0082414003c40203448940c84031303280d802e8a9070f60b8031a1303003840f0b502c200000364126442e00e82c15107100290550300200c0d8040300c28800c000c2000c0700543c8101d40441074810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 296138165 1250 296136915 296136943
    0x310020a090e1b1c0c210510080d0534080d0f051003060e06011412070806070504031209051818160609060c1a06060706020a0215010602 60
    0x142440c1840b12090003600c01401e48511100c58031104412424040000d00301159110a1007582c40c08903154402900c48040381c800a02c0404070744900038005002e8a44504450354070700051035070791126070543c9121a030300850703841e11843c00700d0303040e40c1e821400602c40c4041c03110000800c91030301180b12001d00c80340d180d40708600310704c04070039000070b010f84018220005c0102c4004c41d41c480d04414440844600301c449074680448101d0401c20305c032070f5114400500b84108007410341c541c1812114000007803081c0c03449000703404900c0c40e03651000d01800184082c0c5800400d5402074181040b0082c984d030401d004c151000711a6500301409180250b8481d8101d5101030550403115001e003d658803405401040120440c19a0500c0c00f5410b00501948501c1250041004517081c1040fa0060200e03402d9041541031103c080b6615012505c4070604110590804c00d015801d6502c4c0000300c1d0303043c0101c900c0100442d00104089264a8010901580b480101416540c180eaa0b4010880c0e030f0314260280a8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 296139415 1250 296138165 296138177
    0x5061503010b160f0b15100206062211030109060e0108240a0908160c0501030e03070212030f1204120e2d0a031a01091407080a0b0a140310020a 63
    0x1500d101941601c0c0f400581c000c20b407200380424503481c0d021284004542d0f0f0305810000c02c03030b00315a918004510845281c058030042c196464400041100c0c4054a10005070019a00104144031081d9421003121000e502240c551a135a41c1d48103c0003a022a0140d44842c03000c500000c504520b0004891912005203140300e070310180f24255016140001910140c4000e0703c450080d000302d130500e00142590404001101d04100319400c0010341051560846810176040c4104560310030000070586100d2501190714132095200c4040c503900d0343c841c005041d0104440401d10002c40c18010725240c0c4205e0007181c2054840401070001c40b0615406809581c2c8070f40c100c1d9044502042c602d99a4102615840e4001d511081110000d080880c541d0f1003120f00321800314402003140c0400440500401404205118010080300e00315600c0c10028407920030000541d0000e8200d80c419007145242d400c0c044c24441086854900030364a050b041c00e0481d001e0310440040d1520300809100b21103104829680b51 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 296140665 1250 296139415 296139427
    0x12a110604080913050108030d0e06090a1b0f080706020d030207172d0403021207051005030a060f0f03020405250c0609020907020a02010813030f0f1b0605061503010b 73
    0x10701550703006a000d240d0032031648082d00c0102c480d41d00c03c1c0b9010b00b00b850002e45c9c44105401c045030956201d200501c480b50408000d000c410078000500d030144039440800e6200420110005000c0703104540d000d07450800052030300292902012549509848295007a5607070300340441419402d9105945c00103015004aaa507410140e191802515a140c0e8a01e50041e01c1c2c503031240c1c220f002204030399125604005c002410004c42c41e118004007c3c05240c4406400c030705191400242803c0500b00d020700600c600003000a003003080d20381c014009028240a00c2d0001034550003558017203e907501080b8095842c110200d13000e00e40717001d280440c105030204071041c44240304c0411246240c1c441d10442e031041d1a003c000b00140d58008142d0f11446241c0d0041c155109540001400c440b0080c14030601700b00045a080c1c0820361010a00702080c58504003042c0d11207807080100d4542d902410019440e0440034541002c100044c0c000d1800361800b158083c485c0d64070190303840c0c0603100078860030307020210030824 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 296141915 1250 296140665 296140673
    0xc0201050a0e09071d0f030312040c030f05010501030c0501032d060306020315030625260907061101020a0912030c0507080d0210050f1314012a110604 66
    0x10700070840340c0d241801400d0100c01c046088824103580340c101007610350115040c1c807242c080007440300e414101c5200e401e804e0304101180d202e02c505654400b100300303110009070501c26a04a8080103613072003900072100048600f46a4000c0c0030038001210a070040c0759000400d58480d015143d146115070f2000030b082030302008201b040782c004a0301c5042050315080c0001c00b05519102562241c40e404819009d490900420103040c040c00030442201040007071403a140c200519040d144a4124a00305000d45c1d00c0441203604a02600d4030041070145a400c0030044100030108502e01110030070b442c1c10803d4078948640909030702520418030001902c05000b000030090300d10384445100d010f42080500000c0540f04c450800c11950072990305135104410780440c150b41040b1110700074184c00c03810405810180c3c0c1e0320400d5840a054a50081c1981124209200500088150107200712000300a450f482450401c10200380e00000381c1030012184411800d03900542442d0142e500c0d902c0606040d41e12032b0b032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 296143165 1250 296141915 296141917
    0x50a03151e0c030b04150e0c0703091502101d0307060f0609110a0e0d1203050601021e0703110d0803190207020402072a030201140c0a0506040b060306070e010c020105 73
    0x2940640356480e40c44410300045041c400c200200c1110f90b8003007661607501040c441aa00300b00c1003ca01406507030001c000c0390200707400e00e80d04000304400290b03446071282000c885420071904800016030310440010800303500040c5250308000300440500500c89501041c40000f08041c8010031160010458040000d0307240d4003141c40702d00c0280c40080c40301d886590a100312101030440c06405c020008941c4031b555003202c0b6440462904807404019050176135035056500d98061100d00c00e042d200d0f0007054850303009106492913400350080146580e4100010255550321a04c410780d45103008a00c10701003403c140c400251020340062031035203143c0301d03c0a240344a2840f00c001540082c0d09102e1600141d84600050840038003071201d104c048401c003241124030283e0704140c00c0514101c00810030050744c100741803104056210301065124880c81241c58100b500040005145000d0030080008021030301080c940160019811140c09a68580f02a2103206075800c0d01d40c080380480d11007038010b40c0300750 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 296144415 1250 296143165 296143181
    0x60528021b0a080d0906020708010203161d09040c050103061406160201050c030d0506040b03030c06010e060d0b0c07060b01050a0c0b0406020c010e0105041209030b0a020f090604060513050a0315 85
    0x5419850b003156200c001c1420704000c801c44000098a4290422000f6810005603000c0c0ca41c10b0001c43ca141001000c90302c0c04643d460024090015800c03ca041020003100009141c147c050186512403070189488061240103001e03030341c0420301c0c0241c00f0941d01d41d94501c0341c59451014041d0340c60041c0784c0002ea0602207101c04100c0c1000300801085900307c0040c005001e00c1200a080420740e03040039400c1000340e0f20320300030060081d803090000c800c6544001031a40e0444149042d1002c003900e0301c001244001d0881076010b0f10041500b802c0c03241c40440c0d5401030502d9402020100b24095903a40111203074410b8014400000d01c549001c1c402003401c07450f500760060701c1175400501e0034910620031070075201f00b41c410745001d940d6442040144034401d01e10f00703035240719464002441411a030303a0042c0c400001c0c014541e140e901007146180410310008540c404036004005035181c0d40c3d60301000b40150b2000305001142c01d0414000900da081c200e0909054075844030f4060f500591195002c40108958 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 296145665 1250 296144415 296144419
    0x50d0b0406030f0809040c0e010203121504140415230a020d050106020c030d020303071b23070611030403020d020d0c23090f0105090403050a050c0304060528021b 71
    0x707a040080003c1007152880d0b042841682c1094460b4411400c12040301c8088800d0f4050055111400d00da50780e01108a8001000c04003042256441e030050308003485a584030000e07002490221091f540981e0000420700c07491045283c0b1300ca0741102c0030000140c2d403680703420314820141d90704400007821150f841243d01034103010f00182400d551200b80426070b1002ea11403c00b6821102000d0401d0078148140429500a40000c2d440e43c00c1c00100200b1000c980c043c1e17428803648020a410401010410020200d43c030089070f0140c015940f0302e80c94448805102d0000403c41d010184002034001006490480303800501000700b42c41d0b984c0078400309140040b01121030140311500803a40000d046c4c400b8140100785191021008031070401d0209c0d03050007801441c2c2d0f6070400d030f00401280c0d60b143c2203560301950618010f1b8850080040a40d2070b80100c040c00070481c08007090100708c150303010b009890780802d42480c4204608060303640b03440c9902d8003050940141c01002d0b94205400810200445240c80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 296146915 1250 296145665 296145671
    0xc07060c050a0f060b180408040501180b0a021c0c110904020d0c090e0d030504111203070606180b0d11010806060408070311030d090b040e0705041205160f06050d0b04 73
    0x190b900c500290000f62030483d04195141d070491000c0c01c2c490b5181d20140448008000e20f0306043c4c40b801040c0c000c80c40303643d04001411011802000d5002d10352801482d061680a403074903129080030f03440785400e000600c400c19006a446040511031603400e0345d6103811800035001610340c0001c1c42031043c4002d00c1aa00320b585503400d100054100980745001f07141c25100041c1d0070745410300081c1803560381941c2000701400c0c001404017080790309201c180150360444200c940318107074007109821801003080c058a4103151483c002a0074480041501041040d2501000580f0b09241080000c5070410005001303400400030400c501d5000c2c1808541000004200b9420695204012858030000c3e810460306070010803220400c0d41020080080301010380e0030049151070628581500e89c0c000d52081c0f001800600002c070318414005e070304803000ba201c568000084203480d802c00564405800341d401d0707042001c5020000b8003000d2410b04070300342d41c0d481c2d8400e0300c2c1c003c031902e080d0040c100c03014200f030b8099a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 296148165 1250 296146915 296146933
    0x3140a15200a03060305010c17132904110d0503030610231308010b1302030703090f050c010f020c010207140307080316110402070305070b072102120603030c07060c05 73
    0x700c409040c152049960100c0e80a040d0f04e4100d0a4070103000001e03080c0000ba040c0510006e181c1a001035101948090105000c055070405140c0c84124a212b00c0e0f03e400c400040c9081402101d02e090300c030324010003840c91868260350903c2140c07102410003410580083c00410f016241005194440e0650f0303142150040f40102e0f02c203207822031851707086200840001079072408268101c030400010100c00c07000f04024107145006c12001c40000c0d10048200b940000024002130095000b2840b443c0c01408410b4510328910b405541d55082c040321501040e6860382c9441d8a80c40018006a00101a4041e0407284d10300721000d81e8101c2004540c60703150040701d001045081007000a4600003200481180d00c000090070849203902c07201010034011401000300c1808a90450200c800da150702030351803c3d0795910b00b2812140742c880c0548251030310b12036030461000600b03184c01402e8464403035000500d09131030340c10030160343c0e11034003e402ca9070b50080030080104601035140285058011816106d07201 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 296149415 1250 296148165 296148221
    0x240103060b22021309110f0d0216030503061804031e020f0d030c0f0e0328020d0308070f180605030c0c0d0c0605061014090402040e0c030103140a15 65
    0x4150241c4502d10b07541c007060180000842c00c1c100d400030002c00c501040411500d4084c4260741c442d684c8141803c4000061448034181b00e541182c2d000b2001e4031030b65030504861f24009020354810b403510307441030030040c04007003c00c113500d0a26805a54103407140010768030804c600c01121740c00c050285003523001d1110b13500011031052004095250480d5030008000701402c0000e03000e980d850304101c04000c010440c0e002142c800040081403940b01348880000c0441601c0c4421000160071002504224181c03040710800d41c104117003d004202ea921030240044007079008880d554000c001c078144001d8880000c01515005000030743e003010030f81d070310706250480c4c00c0c001034070b4045405004400140203456500c244822882520380110f03085504500d402801140104000c0e504480d8245019001448800030350311507040300c004004072081e400481ca0283d0941031550403d1000713072452144403141031990200414404c40a0341d2001018000703502101104002707280d1404462010a0400f08a035600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 296150665 1250 296149415 296149459
    0xb0d030305360d0c151119090302090603031218070807061806030c020309040e030c07031505070203040803030f090703150c02010b031606050c01020d110705240103060b 74
    0x141906044000c80710490114a00e000e404020f03c0c420082c10510580004000f000d4009501c00405004107404d503014005d040c5030f1084d20b140c1c83d118410b02149070213094001000d407089034021946010782c0e58855042c140c5034402d20341191000803901380003c07850140c1c4030360030408440050031240d40e152100c10003803510010f82c1006000c69880c410303015100001032140c2c40648024501480f00015180c0e0181d9640a0992514420360312003c0c0712000d14002c105071241c040000c0215403007141c3e42d0a00300c0018218195050825003048001411580000704039822500317101c0040d485e40d91500c800740c8013034001500c08006802820310000c04104c903040b10101d25034200d0400200c2030780c00040642101c144030000e5000b42c00500c038000c881c201e08404001107944a060240d940d05580105500a20824a030043c1882c50101700000400c9c0d2007020384400782c1703e60200d40e01404212480017a984840055803016100310300140b00086558018250032000a0071012581090b88031174020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 296151915 1250 296150665 296150731
    0x30307080301090e01060302210a150e010609090c0e100315051f08031b030c01050117120301050a120201020c0d050606011b02030706080c0705070303030c0806040b0d030305 76
    0x14140c008070050103458282c0c41040d89980400008005091a50780070070300580308403410310081c0a002c00480501081440702034007049d849182e044ca08242e401990b00244441140d040b820b40c030300500400d8500d007904c108660ba5800402d841900c03441d10401c000c0304c480007000d070140200070010000000d01140c00c0c0b040e03841c0140c1c20200d041d01e0aa421840072601c1d446009003b41d5103001d08100c0c50718044105c0c0c20b04148401000340b0010100342051840c800da510f04040c3d50300e0074000080c00c6500c0c0c03c01e0307072034500c074030007a201e00200c14401e69030140000e00889031701c1012008100158051803504203401403060041e5106003d0b0340c0c0025880403d482e1040e034103900560200005980d0125800400c6115407440c0380b184881500130a6031a40c050064900340403811000c201d08628850640e50140e40c403d007107490032a00ca24004024025240321a0701040b11800443c1091a00c0d0144142614015010101528841d20200c014001c041d20718800042c2c04000b050041c11044000382c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 296153165 1250 296151915 296151923
    0x90f060c030a0503010315090308180106033f02070902070609080a11010608011107080c150109020c012702130b04020c0708100b0102070e04030509090f07090609060c030302030a0209030307 83
    0x40c136507156040042407030602804030001c8a151050010000f40c02110454000e400e01c1d2003001100040d5441500400c243e0304007600c0b04800540002148103480308040c9506484249a08062101c3d48028a80015080803001581009105018846250b03000e003501900500c40860541450784a0344241da05c0610050300050b08802c403a25070003024040c1c40001c04a5a000300a90740c136240250415000e5800000c100b01c40000c0c08200b01e2034104102440c91441d81c00c0c03400741c0c0d40e40350300600c000c1d030000140030400d5080010400310305c1c0d84070003c403800500100310950745c442140d00308005811820750241036165109900040c989840c030150006605c0f0900410a07a414810b42c149441040c0d4241007980e42031040e03100c07590344d002c61a441141c1607440c0c0300c096070b290362a0035502d50003905500c0350007162080402050030300b818007040c000c04080d101e00d1495600c1b240c040307503106414003072031012409240d00b80d00028400c0c0d00456110081000c01403c1c203154000103800c507400380000b60b03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 296154415 1250 296153165 296153167
    0x8060613090e152707090606020a0b1312030c02100c090608151c060b100302040e060d030f0e0109050301090c05210601091a19140604030503090f060c030a05 69
    0x1034501e00701000790503060100000b9980051614251264558007861329080081160341c0025075022070402050006c0e103281c15003444031544500d00250b030381c1c201410955140341c035040424901400c03000394640064104038001020002e030f24058000c0c1445062040462040050580c26071255110788203059115075180f0081528080f0020205d070409040c1c0541c0d042c030b0b00b2100314184d4491000c202540d0503020542003403c11424200001d0200c0c0c0f401c5030f044203105047c0d002c180e6160b4020000d0340c081410351041a2221400d20544000d4101d00034040b0300038441001416001308061203032004145000d070102c039200c40200c1d0075500092801c69640c85a03c105100510300580d01d000558030008815001038801ca202a541e041c040c8103030090b0780e961b07560801e0b038002079020500c1c8481c406008402140100c01f50600c0001c400d11031884880d51010714159a8503019048804403a000001076003071003000c00401c50201140030116074010405c10600e11020001d0001d42001e2095803141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 296155665 1250 296154415 296154431
    0xc01110a0909060b0706180510050103020a1202100e03120c031908070f140706050405070e0615070210050415030b030106090e1f0b06040807080d0e010c030806061309 73
    0x1e04020141e800020300d483c2000001d2110582031002e803018960054000300c2c09030010400002014000e1001421501858804020040c21504018100c034420740750f0155007a078440c050280c0301c100e111b00035408886d001c0c1d0300d99080e105248402c542031009007a6068050341d008041419071007403204000396040850380e49045804403035001d01c8a030340c03410003440b07524115000a00b003407041c1e21544148800c924100e03091017562802d40b07000652114007040030342000e04180e035503617241e0f1080505108a1200040d4542050251010050307100e4007440c0c01c0c0246070f0700b0002d10003000400c4400b0440207200015001c0e040c002080305081c040e8400003000880c440c180740c25240c50fa0420800c403401d010418159030300c0002d5140b9440c0e0180c0c2011030a0b400e026012001d407001540c0f09522031808a4049040700b00469000119540603017150010007841c001519071324020784029000c9103100c018040401e004412141c1d00c4070b0001c1c2164a054040b1103480c9824415810041c1415030721003a03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 296156915 1250 296155665 296155667
    0x7030806040507020705100807020106090204090207110a0f1a090603070c06140f0106180f06120609140c03130602030109051f0b030114060903070b250c06080c0c01110a 74
    0x40d10b41143d040c0c8090801a170800c0007192901403600f1000040002c0030b0700183e80d43e4400c0d4005000303020b8008042d99155990120900a5005040d00f5101d00061009488a518080150104840f6420700c04001d0f54940f4112003000880d0048904421000b00289201c42c0d440300000c41c400c02440d111105990b40604100007185d922000b0042144984014401c940034214141c0781101c0541c60204076258558051098080c0a5800201c07901c038640800b240c1581c100c0001004441442410001655035042c010300740c82c9022030b803c03101449000031880340d800b0080259800410ba40052040c04010795400f000c0740c0c02644a03551040d950350522502c02c1a1403801c1c20140e24400d03c1d11035541c1451a0b60816220610518102e0072255030440c01d56150401a2891070400405a902d0581c1c0d400421510350322020403e01e80e60b0482e680440120303107440d0700e8084990000c60050800e0b04084041e58500c801800c401c111413014800300e0340c0c0c0e540c24010b000c0320007450751417984c4500c18058 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 296158165 1250 296156915 296156921
    0x21b0402190930020f010318200603060d03030207170705010c09050d0b07030e0c03030f09150a0f08040201140d0608060612120708070b161205090a061109060703080604 74
    0x456852900000c0150340440f04a1200700d009183c0444100c030030502900d0042c0c1c003c040f42c82c06800c15018818445051180e000141c80048014200900c4141005030810072140700c11594503903c942d00b44d08680101e072003030340a051560302c0355030041040000360030b83e0000ca0f000b02808843da070703440b078140380305082e8056900c80080c08241d580009160444e07403045480b290042c201403c01d6a44c088603440014200300240c0040c03800b40989688001c1039440d51040d0340220302080c003c100e2440302d00b00c0c24003480c040392002d1480741d44040050359041c2c000c03035110f00d003d4020785c100000c0355080d02103082c5042c01055440d0303421074005101450040d9103070030000020036042c4142005070760301324800404034487c0004000300d002d01e40d0350300d4075241c043c0c118040c0c45005486040c017042044010b844004040f01c050100e6250760850600384c004600075208101d510520703035045015110001013964204498030b12032625803608007107007000401c80da0b4201e00d400b80e0000d9444814850b107410644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 296159415 1250 296158165 296158199
    0x15030604210c1a270703060e0303060907030c1206090906050601091202271e01050306040812060f040c03021305030c0f0d03020a0204050c07061b021b04021909 70
    0x704040c0c0b010080e603160f041c608003208898020103021000010300440000039503c000c0040d008402040c0b405500c44156100200d020807210b2030702c0e103440b0039546c610000c26030340b1490004224400039a40c80e8000c801801c09229090705201140981e021150480d01914002c2d0260b00b10004520615041c440c027540d401410b240d060002e17480c82401007101a504540055405a4104404040c5400e500c134240144c09442c4403403081e50000d10012440e903000015040303843c2d44142540341d80391000c0585500d1309480003421280104906110403140705446a40400d0003441a01000c01103404502910034802d185030001e0350014909144c5c00140c15154040d15040d401481c019840a0204500f4104203440c58071a407810001441010310801c03644410542c06403051205040041424000d5000030328100c40d01414454030800c1c1031041041c0e03c000d24003e5005200d41c043c280190350074489500c0480d608140c0030030404008005002c40702d04891396559034201c62a10303011451600d14808 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 296160665 1250 296159415 296159417
    0x60c0a0c020a03082706040b07170c060103140c010503070e1305090f0f010e0c060f04080d0306090f090b1b04080f070510050a090e06040b1c05010507090501090b031503060421 77
    0x103a00da159042d2206c00c20703501074441d02c00c10a030f920800d900b41081000c24240301c40074820000146543e5002d00402c0c514102c038418484c1c0221a1501103c0545070f510311540140051030520000d125507108010740c4003625030161101c40b100600d0200d0400342e41040b5040c50140c0e000158200811004204d01400056044001c100b20194010b00640b11985000310390320806001c203c403026600050210380007030003104110b07a00721070314010250292941d44103031045139103411a8003020741410b000b5024001c0e4040350703110700d80d902d9100c4c40c5120581350540381c90b10102488041031032001004160750103070022005210f11481cac4020868081c0311000400c00300b01341030020580d1250400c03596030648000310090b020998501001c03500400415424580c010403403c2907a00c003050341d141020b0341c503008900030700483d40c8400d0140c0d010140c030300c6010300180403079000b049840d480c8070107150412031079800000010b80e9030b00001e28140d0140ca099500b14410003e2a0b180048900181200d6202d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 296161915 1250 296160665 296160727
    0x8160506160203070b07051b1501050f09060111160e0103021f020d110127030315060f1101091b0f150c06020c071a0904060f0305060c0a0c020a0308 65
    0x50003500c90084010040c1201030003401b164580380104103079002014030400600e02c2d0740441b05215a41c85209104514560020300049901d0034254060b04203c04090568055038607108011100c1c1c24500980f0041801440d00303502d120030340041030b0700003041590300052055041d80104048055807081c0302205241c00400d200c0701607000b2038031404d035120364102242010010f42025000d80309548031001030780340d02840c1d00c0c0303014168114130750260301a5600300700c62031020b90741c246404446d015040c041007507842a0741c04c20303100b00659000c4529035000411559001c0c0d4440507006c81c0384c0314088144448100c20300580d403506012200030580403886001130780701d18a006d0311104680d0405007409400240580b003652040001ea401004014203288101c950311400c103100380c00c40340344d2521981c140000003a100e54060342080580e60000007500e81500e400545940b550300040102041c4403513108501c016036210b100004c000c500070744020b0345e100040302001012022807907010600c404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 296163165 1250 296161915 296161951
    0x6071701051e0f150702010e1e220c0503070e030c0102030d0f090f05031b0307170c0f12030105120705102706210c020a02120f0604060e0f0712020609010c08160506 72
    0xc240c840b0100e0700b000550b2b403052402020621100d0000312a0041074000e810118461809523001005500c590300a5a8010b11445031a081646a170809003400c1e006900600550b00c00d00c0c82e0760b110b07203203c0101e1800000c070b4980d280d0303e4405030740c804c080c19101ca070400f1901c00492034921801c158100003030809580350002954501481403010034000000c0280802c00700c0d208070041000048040301001140c254030349007040c40c000c55109004040c001e45400d00c20140c0e41c200015908241d0708024402a8254084807044481c061100055100f000c0d1203520b0f81c0e004c0c207081501c44064655a91940d8507054030101001e10344036002d540010307407450521408142940405e880c84026030440705010481448501c039880c2c07a45011740d08400b07008d00c60a02040129584c040d0946060f5441a104600d1041076030035201d941714444c403030208001544820051408074002c100800c0b05040c070131550142c076210420140c00c4180e4514035100c803a0210f07000e0080801c0300d154810b92910105040304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 296164415 1250 296163165 296163199
    0xa02150705030f090f040f060303120915090602070804080705011815030e01020409062d080d0c1e080c1204060c0609020a050607030206071701051e0f150702010e 71
    0x40f142106000321030342c02140c8541c9a07035071500261300c4010000d1041c03280c651814140d100408003844110301242c0e8040b03802d120201c07540580d04646401c1f034820301380b001d4a5034920003e009402001c403040d9500700413020004450700003400c051300e075070402090308900300340000d403d210301c0302c4c81d11240ea0024a010044e4201c54403a1f403030030140525020800d21010380b07006001e8003a0340c00001d121404d00b00041405c00a5030000c0c00006446060070040005090a03000c000119000b660301d581c200c4000c0c10070041c0100172500c0355078032920b880804003008491002c1c00185008048800c00000960f243c209181005810071200010507080d25252408101400c08001ca803001450b8548981d40c0000b0f554405451100819010300907d546501c0380c90001c0d2228400c542101c08200d448046001e082200c5102c1811703250302509805401c80d00303445519403007078414034481c0d0200001e51541c41540b221a042258400342e84e10180d02d60503103100140000c0701e0b000c23060780030302e0b1907003c211011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 296165665 1250 296164415 296164417
    0x6020105011e0b0901110f01020705150702060c0a2609010b04050f07030f09120e1008040c05090405160807080f1504080a02030c1204090615090b03060d0f050a0215070503 75
    0x243c0303454100c16640c0c02103100682d4810070a01d00d10440f07000c0d03100601b0782042c041d001405264850380c04c4d9208103003c01c04400303020100340e41d0200164044400581d4080d118030041c08036480d64180700000442c49a0040f00d000b0b2031085003c1002240000c0c806a04400d00420f40e0094045406100b00c2c6004d04001d03c901030018544020941c80c1c0e00b0a4044001035885406402d03040f2410190683c0d0512020f0000ca0348400440d000751400c81d84008020b2099042c203004683c0040d402000a2802c0d040107690030000d04162070724043c85003144100020400040010440c50001d03220311440c00c04d940c3e06245410070f80810741d80044400135210181c803007825034040d030b001042903101d15100204030310318024248411528410072450980701078162010308120b640c0540b09204080d2629066082c607410a222040880c068402c1030010480d0760010b107910013001f40c0384910001542d15082c40f9919942410b50707642d0003000c1403600794140b140f10011a42000c40354649001c56955800d552 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 296166915 1250 296165665 296165669
    0x90c010906020a03021c09030212030307090509150d0201120c0c0501060603060b27060318060105040e060403080615040b120a06030221100204172a01030e030409050405030406020105011e 82
    0x46c42c0401c04110a60181c081000a19005440308402e1642e000803e541c0794016580b4034082102050001170714034120900c1072080404d0116000c80c080800184403800a0b40e050481c10b00c940380400003003486840c400c200709410155240720304407000d820460300b141c81d5030f0408010142809018004104044100c62101440100029034410390f0140d01606d00c086912659020030000f003800030400c584608103000700390500a030790140c0da9400030030003240c071195104403007600490009008a0702421040d85d0010018080b1b220300c984072100a0000d51090b00501901000481e000f12520442107040354810700203c402c201642c11a000541d0392010405a4003143c01d03038030280c8410100c207215400e00c04031000700641d140c949401e1461100600c007000044a8425110903890007021a400c140c2442001548940301100740700045014101c04444c41c80c5605c4100000100c4035220701c5402e124502420145468a00f0042c4c000e081d45c0060f8003042c5400d1001080d88012800f019407141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 296168165 1250 296166915 296166943
    0x1611040e061605030c0d0c26102d1205011808160c050a090b040b01030b0906040e011b02030a0206010807030201020706030f09060e0705031e03190c0506090c010906020a0302 76
    0x2d105d54900c2e00703481142c40f40500e01da16060800d542c501c21560014801b201c2c0004042d001510201d00340302440001c10115169010100201000c01007828080c003100c441d015980d078841d00100c490020341041c0d0089a001e652903e41f001d26034002d000e07081c42182d81c804045078030801e012100c0d8032070902a0140d40b098000c0b8801594060303041001e40340600c402440c0c060b01c07400100755180c0c2000000c0204542c040d00440c104521403806600c64400c103406218004c4c08010700f61910000c2c80010801e500c0783c1c070150f6690301d4207200e038501c1500a007070025201e03900641e40d42441450003403c004c0e040e40610b02962040d4001e20050ba0003080c85001e9170b00e1442c0016881c22003040310301c0640000f40000d080c0e14540342e114504001d0105003081500d4054085480e882440d4040703803041d03a201c41c8240d1b0b840e003050145080070000681c80030344a45003854251951803564a810b030030984141c8100b5121b5005484152540d6080325101d002130003240042e110074a05610302030740f0b907254007034207003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 296169415 1250 296168165 296168167
    0x20903060114010207092307180b0a030905160504230c0a0c020d0302060a0612030c0204020304030504180506100e01021518120c070b04032103021611040e061605 71
    0x484264800c20080b0010a5a03440a1101d10487c1701180c0d90814002c14441102c0b41510006e040340f4098800000e01030780000449407042d03c0d100c0030342c07070f00c0c1c00420741c0b4020151100540e8000c5802080001c00305140c0b02c240070740c61803510040000311b580580e00d41012881d100d183e480261204006c3c954040394920583c0d40e01d40210408075044032001000039407001d10340301751205050b40080c4942c401c0440d100e00b04545a180d80040c05c0700014a035000380014000003a4100505268019540051090808600341615800c1602410111848050051f6a03174070070404a03240c116226000c0d24046c0c2040d5100f402141c0000751580046802904100c8001c1d02045e02541d590042601c00b40701d68090300c91184032441110007960000401803001d20078500046640100c00e02150100c951084030000c0c42d01c0102004e20700514061988000d25609200101141030010b041c0c2ca840d0388101a140c000031002c40800003101d003d6a000343c210ba100000301300100070f041c800143c00d000b00d81081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 296170665 1250 296169415 296169449
    0x703030b040b041e050f01150c0c09060305030c120304080f1b1e0c030309030715030902100f02061015050d0906020c0d110a0c0b09040e0f1e010209030601 68
    0x115020380040c2c100719410500d0860030802c099000304c0d440c1c24900151100340990b4664041a412220080c080c02d0109144a43c21491003400b6011043d525481307200c040c10309580c2ca00101044480944c03065845400c001458507030180107021119a0f100034094003820b42c203050326038bc0e500c1c1c00381200c17690007004000364510010084200800d0380703800c03070340403104090f1810b801d40c050b80486031440100380c03055600d084850710f00842565a030350009001021280d01c3d040980700c118a4440c0e10030305255072056140c01585a2110f4042072400c84c0c0c80703001d0f240310050b500070302c2d005006200c1e02030b01448110038401a0450300c2d0341d0141c40e6032807410035120210280c0f404004e2025900003410540b0014941440c04c07000b08d08000e400d03140c0e8541158803416104a103403102c0036884000c0174000400790034010801484c001d4444070401800001c0c9010810400030700d404207081100282e54403021428050584421280e010120185d0003503040070701d401c0100e642c40d103040c018101500511001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 296171915 1250 296170665 296170669
    0x3100f1206020d090506011e1a370302030f060301150501050c0c120d0e01020604050604200607060f0e07030804031104091a190612121e0806040612080703030b 70
    0x11007040700b178010069070f1032941d546454004041129407402c00c11150b421000480482c0d1400003101001038803025490401600620810780c401803450b2064912420707500c24104034507552011000e4802c1c0c80c01656400c0a121051801d800100b002d071080c1c1c10540191241001030b1070100403514207003002c544034880c82c0035090070001a00c885079000098201e2421207042c2c0052090400482e0b900e4070400c4800c00701c0126100d4a0454020b0041ea04c808007080019605003a0386c01101c0d883da8100e900042c140c00007820907405118180c40c1c282d1100c000c8001400b6603c03031424041d00d080300611440341307503030b840017014040c0f44009440300400980b81000758503660000345500d40e01ca000c0314004401e10121440c000415240782c01d4030081c811140c0d08a42951280109455645000348441c003003d80c0c41e020038411000b9440f00700034601c414545072024214240928560b1a20b4507403d91a200003403100700c90b0f17070342d1059001201d14415080812400c100300d451964062801060384c1d4600c00c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 296173165 1250 296171915 296171921
    0x2010203090d0312020a0c060c0810030f050703060207080d0b0105040807061202040801020a120f180602091521060907081b0c03030a0605040b0306220204060e040803100f1206020d 79
    0x1038184d6241d40001003401116900c0364640b03c402c1e02c200d604009001c03894108032160841281d26101045072524107001150001c040c8089007803040742201c0c1c03543e403650303640e4040c1d0700034800031184608003185032101e450070340c0903846400100f07103441802d09150009007983e8415500c211810300644461224880a5580448019244c80c4009640e6901d02c804018644d00b0404d03000303a8035502d8102007510200241c00382d0403c5c024081e070b40f00c1c10000d1984400009521901007250f2201c88200744547c03110322a40079281404034000c4a103012003601080c5c0240b00300c0244a0f80c4184009000c0012007070308081120b40040131450300102c05c0144060010892107801403180c0217110100c1008035402d0903801c41000c0c4d40342950103020501091046c96641c10081e1111514240c41026143c106082070780c600c1100c0e80001e001180e0140e54500c0c503812601c0a51342600c0124002040041851445d260000103000a11410691034500b2142d20342984a06500900c00350300040c0c801801400c81e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 296174415 1250 296173165 296173187
    0x60604150f030507080d0318030518181b09031b03070b07061a03010b01091802040b072306011409040f122309030618150c130e0402010203090d03 64
    0x908074145079500c0341070140e0b480c1154071035540c0c0781c854010810000c40c4680140714600003107818544014210755401c0d541034020403079103e040c00e680c00c0c0c1c260a40c0d840c0c03503104481920380000c500d0326040011744d071081da000241c004041488104030510440c0c5001842c000c0c05600705118628603070707410002030f01309003140d48580c43e410780116501d42405103c0d44030380c0b0704c4041040e410b40d2042e00001030600780c50510010078081080301030b0402c010381c3c0d809140780b0803111040005284c0342d1295180b0300150809a01900e83e1007811681c81c400c0e90740b10400b8000d4004080040c1820340c90244102c1000c1d000c0c115407401070782000d0100302000032009191880c0342e071016100708c88254548000741101c03000190801a8801c00b40c1d2406a44101d01c02c40b074090f580030300a81065600d584051080d8080c4640d510524030038603130240c0d41d0207802e01999010b10341c580105036445c03001045004107a0785c1a04440001d20995080c8401030380c000088640d000350590b1078454410446c24191000c020f14 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 296175665 1250 296174415 296174429
    0x30b06041502031911060f011d062106040c050904080703110c100c050d050a0e090603030c0d0c0303200304030305091507020a150209060405011b080a0302041401020c010206060415 79
    0x20840c0c40450300d0b00890207058280c03043c801c446c0940d440300c61503401b4240070f11640200f58050610005c4200214008079486030002c0c0c4250060f0110f00200e882c180104907071040c2e6500b108051108120841c8100c1000b02012158404a802d150f25254114816502d00034240302158041043c0040c0920906001400007065183c0900c2101d10180c000b542c0b502c0221264060612400b140394003600641354001c40c1d0b0f60b1104001c40040d010311002c41c0d8041c4c1042c0e8544001c2c802150441e40030230034005518110ba0b03807c2011a228640034060342e69071220110400d0620075034030107a0f000c40052766401a0186000326003510b89030145410030080c071400e42c031b150a1000821862a80010304070f18032074440d003100c140b18491103200e0002ca004043e02c4582c0300108000400040d842105050a1211105aa01402c0c402d41d91195929842a9410b20109401140800031501402d0492030301041c00c0c00542426880040000e482d401c004203000e01c600c0d581c040c0400c501c0c1d0180c5540019000d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 296176915 1250 296175665 296175697
    0x1204030c0606091a10020705010f0512181c0503041e050a03031d030c0c0105071a0a1a030c030a06110403020a090b031911091902030406060312030b0604150203 70
    0xf61800500a060110301e0015025200241c0b07503442d0a1020301a0700702e2603035078081c0000d00d0809004548a208504695080002c144400409482910b0a41c4d000e008100340f95101c40d20403203e428200007841d00c21074000d07a100c04044a94070341040880e948142c2c889151004008104c00b0a000741140c00c002800510800c044103003010b40582c070550380d180c141042d601200ca002801a0341d0f034030802000320001d42003c1c0c01150700354041d001824429101e421003284424100303544011b10b51048542c81c58003511080380c524a00c5488800d42c0b030801007030340600103038a00500469610902d503e03009201d2036942c0f9000601224000079200503540c010420241c8a07a100c5a5101511420307100d94824014151a25001c4618204c4102c2c001c2d404007401c03070308401c464200400d40c0c0c0001c0541403082c074101058040980c00b44011880b8a11694000511600f1410040a21a0b034a9152000d140c9807071341101e4a69518002c0e00c00b1506550540351031100d0900b8106d086014084064000c0b2403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 296178165 1250 296176915 296176919
    0x50102070f150b0a05060c0f031216050307051210090c08011a04030b0c03060d0606030302031e0408030904090204091a01092d0926040311060a02031204030c0606 71
    0x20764200000caaa002d07103407429104809407424002c440202040c2c13640f03c2640d0504000506110300904415101c8001351503981482c10002402c552110400b072031540450382c20003a03001c0640c07142011404451411900354613190700090551b10855481500c18001000041c1103111800e9240d400b170061600c040c1b1640184c00809007001400380541d004c40384244110390b19480724681518122600002d803aa01da403288001248150300140c1020f401043e189201c030701040d82c0380583c0000710b21035402941d80c0c0905030307511140c1104030f85104840600800041150038000000d44441c00d604442c00901c481d95031000800401c10010000d2001c60310070082109164040c0c2041d04032840100144004040340c500300079007038a400304420041c5101c26160703582503007980c841011244600016903020302d2480712210940d03071500400703941c0b450001d024000c1203001807031410fa682003902c6280c14503004420103500c0c0e0145140511264910f400042d052502c51058080b455800000820030a6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 296179415 1250 296178165 296178173
    0x210921050406080c0a1b06060e0c070219030b1512060108161208030c030408090d0605070f0c05030301030201030c1e020106030b090604200402070212150105010504080718020705010207 81
    0x1c1c0280c03040101090761400080c084c000c18108460000794180d50350600b00300c0031000040000614003082d45c0d040d03501d000100320300380d001050718050400c0401c1141c45205c10b10400c80c0b480300c44d505001c40b42080c004200001100c61000940020030540040055010100410700c030000c0040d48580d01c0c450700d400000d1550001c26900c81103103045030040d6400b5103441c1c803032000c10b10181c1d000700f90701070420020348004000f41c061074000c0c1c8145001403426601c0c500040ca00a4410001d440740b60b0750f502840f40482d04244809002105130400c00182d40d4551107258482c041444080c0c141500e40d0140b6034810b10800c0c030012058640c104020303050400400c024000c0c4441d010407941e4148840c003040c1c0d801000244148100e501640304070041e0040e2000320300201e12030020039002a001c2c00590300580e584a41c400f2a43c4c1c2d550014100c205130803644950308101070b808203062240401c0103120320a00840e0107015140e08149034541500200c800d40c009100382e104c090000d520101e03c80c4108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 296180665 1250 296179415 296179417
    0x70b2706041a01050a08031207110f060109060518041205090910150806060a0c030306090207150c0309080a0e0f1201150504110a030b0a0e012421092105 67
    0x2400c0ba2601142c403a80e210001e03c5135070b01d028041c048540d803060201204440a04164075400456071a0400904003250310140c42c0c604146240c00d0b00e60010302c010b1100001c40c0c82110000c00082318003003801c18081c0d542c4a00319002a201410080340031030b81400301030242003101c0c20420050032030980351909071000e406401c0103001d000195058000515465481140031600616005180614150341044140d800c010307402400c074141170300c2c1c0b44001b034502402d00c050124503001d001e01c0d8807002e210800c28804c8503001e80202c2d0601d40703802060740214003507205882813942d8038140303005140750010004043c64078400e203044c1d02103403c100d0710b4080701041d041121128014829240507545640810080d030b1403c0792415410a414052103008501c00c2e0030041000e00007528140280f91650032000481c8800d0300305920303c1c201c034584a01071105d900500c0030f184201d0301c2c0c02442440010028014120601440d03c4000c0c2c03150301850520a0364000a0150510501c4e140c41c1c2e054015405029 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 296181915 1250 296180665 296180693
    0x20112091e11030106050901140409050106091a0907080117030409060611010b042013080f0102120a020702010801030209040302100903080601091e1509030c030b150105070b270604 79
    0x4000040c102d103090a05050040e04155031006221804583c02d00d54103e90388036100c5503240d44140c4683c8800089202880b03101d001d0b200b0fa15001c9041e040007085000110384d420f40b407078065a2484100090568131000644c1582c0a940780c100c04003c0c0c1c0f8a40624600881d0098149140790990004160360003003c21108054040000c0c0150a0301e00200800c03600110070040552040900d58400d01d19020000d000030842966842c8100d5155184245405a10804402c02e41e50014100020342544026240d0000070443c0a40c40c2010541c0028010b20301803000034000d180c80030104040600a109148200c21000c00400240c6064100245604001d507034148c00300b1424400483c025000e404031440151061900000491410300d0300142d912002100d08200142501c01200107000020100015030003101c10b000b803801c10b004503118008403000c100d4140312081110400194455000f00d034000300b6001040012103a290a08000d2000b215240801780203210812007000105004e01c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 296183165 1250 296181915 296181923
    0x8030a0810080304180b06030709050f040207051204050108090d120207060212070309020a06020c180403030b1305072c01301a0306040b150607020a0311090c0405010903020112091e 79
    0x6c4110500140080c5100944444001640d692420301c01410014640d018844001d88014500304e803a49801d41031034000010303450a041c00040812803980d01044071a001605800540010003220307030050019500701402000c142d40104508050040c4d0303070305541c11513541c06002080c91034045030007030042c44c0d0700c0c038101c0c07040c2c50701e040c00301b0f03190300c0007a500d07410580192494603085010303420000c100b10300500c1201010789603100c0024a8552030740c500c08a040601c00801d00d4140040c1c041c01624607680d8842c28103500001810008019000e11040344400b0700301003505000c6500b07044c40754048020b075400310a00e001c16043c41c1050350f40c403a403070201020034010a02480c00701055203c071400d03a000b4120140e410040b400e65004030154416802000340510720302001a40070030b400c0c600662094440728a40790b01022541428000316510511641403149800d041c080041c0c801046804080e0406c41441c03083c91008004d40d005880c80d50300010f004240c101540146c170501021020202c0f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 296184415 1250 296183165 296183171
    0xc030b01110f030901110c040603050a03120c050306101103030c0703030e070b091002030c010510080f0c01020304150306080f01390807021e160602030408030a081008030418 76
    0x441d01e0840828101d032540c0c2e0450146150241107001140c003282d43c01000142e9003e074004800032595107101c1c1600646c440e101410485400741800f4011181014080c3c400d1401c0280c0c941280780d203c0d040300d50250f811601000c450001120031941003c15690306e4016100000074040004040f40203481241d200b65814482c0200500c41a9181c03186846040002d210a1103994002c0c5421941044d000c04070b0b01c100c1c0d05003012184422f007034070000c1ea25140c100545102c1401041c105008105518118a00070043c201750203000039075074400e030b1094021040320a070862024620907007202c8020114502141d950079a0030010500800c002000c41c0201c8005441440d680c0800d547c0c1882a102c15014500d4108850101510412030084c0b0080440c080c481041c150082c00010554000d0401030090010503000d0007807244801c40740d0403010640d030080c04200f09c00240041180c040341010b142c042c40a480d0310180c00c10041d03980d00314a145000c0800c0100d4010403400c0c40306c8080c444e0380d40034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 296185665 1250 296184415 296184437
    0x71b0608090f0708060105150f0414130c12020d060e090d0206060a030f0308060103061e050f060702060306330a031a01020d080711100f0f02091807120c030b01 70
    0x1035035550f00d0070304c074403085500100c0c0100454503100c3c10103c5c400014039842490109052030b0100d195110b40c02000d2401c885203208440c2d401c0510300307402c045405000030407401d50700400160003c1443c0d03011208207900015201c000f91042d4100e84018410914014036031700303041c0380880d00d07481020361400040c030070303400007600510342070419000301c03070300b141c1c4c0c03901b40201d02d40701228103100c01004107041c5600d4000004800d05402c0040c0c0c4829000400500c1c401d092908210040a0858120348908003d1100310050303581c00e411250400011a004141088541411480d89224104064a5000b03050300103140904000042c1000d076050369042000c80d80303c1d01783d4059541000540d60060b4007002c83c9514450042c42d040f0740044203404c0640300b0402ca1241246442c0003624954401915040c80210f691983c2c040d5101b2485900380943c01c02200e000481c41c035010080c1d02105980e0888003141a071801003451264040c40d08038140014040d4120150281c0940c1c162030340000c0c059020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 296186915 1250 296185665 296185693
    0xf1815040b0714010c0c03032003011205070605130b07020a0b03241c06020a03060512010207030201110304110d06020f0d0506192904051002060103021309050a08071b060809 76
    0x1703d032554141a140d040140c1c8603914210001c001050984d07000712a581c40f82030010304500051402801e5820b0707008000702c02490001c1c201141c660004040c030a003405254002044030074840300782c8034a0f511060300c480b01d500000e0f04c5403220780d2054024080000c14070501540d5107210000c0c0c83d24201c002d02c8000e150b00b05101c1c01408490302c5901d801d00f000045000200c084c4c005280c501143d1501040c1151900005004458090140000c6a40c00514041019020700641d2410000000a54190704d801e4642c442d0b46640703402000e1140c01d4103d406810041103a045d100b507480040b0380951595984030715000142000d45d61207100703803002c0c40710300c0c0004032041051060740c2c485544501c031207210032420244030130002c0041c114444103001c0030900303842d40d980c06464220ba550042203a94554018080d00c3d03450b03041c031801c5941c24007038208042100000d1400780302c2e5101700140e0b0b0310b401d54104500703101031455515054900189000488a40c030a4013203001d072411800f503407500110002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 296188165 1250 296186915 296186921
    0x30318080a0302030f03070e03060721020306030d0804030207030b010f0f090b1f020304030b040b071b0c120807020301021303030f020309091302030a0506070201021c020f1815040b071401 82
    0x30740240182d10803c05404800c00c0070b0041d603000042810540c6401d0f1580780007908215080310a0000558501e0441c40c541c8514403504800c03a03400700c0c046145040c001c001c01c0c1c480d074401485105000c0780030041820544208134442c0215005210700b0000e503114038400340a507001d4411050401c4400c1000710710381c40c1903c510054110000c04003440380300d20003c10030000e001f4030300d07031800d6020a22000021503c41054503100c0d910811100e06645080800500b4900450881c00c3c106103c44a03d080060740840c0e19030192410301700003600e03022070382c6408a00c038494207500075015400030501c80c0051104400100a43e8481e8484000c41409610126564012a0b4042e40e01441250104049088003406d4120860000c0c00b500d020140b50b440f110b16048045e130781c00340140c0d070004295030300680411041d032409020050940ca000b600132000741c0303503000f0900564a40d00b1900e1b8400d550b5541e41c850503203020f0078401290b0701c8642e034a4128142703030412001034640246104000c01086410b00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 296189415 1250 296188165 296188183
    0x4090606050a0e0f030f1615090e0403050d0615080a051b0405090c070804080d0e0a0e0c030604090501051504110306030601060503040f1704081015062102030103031808 74
    0x10f034408a41c0101e00c1c0400601d1103c003402242c050140c41480003070303040c00b40b00c182c80c1504001c00a500d01c0e441c003146c0010502e0030030b00007420081021020702800c105030110716040754140c070304141c0721013441400d000188420f40c010341d41011082c405410382500200d440e403281030640010049603640c000e04405848420340d9101009004010a20062a282500c1038000051140c0c1c2400d0005550f90006907900c15080002c1079409589000d080310343c07011078103d401c00c0c240c13403140c0d10b00d249c010102c0e07100704003030702821100c01d02000003051600c0d1a0b01124566400c44028011070a14541c0c0e601c5000c1d114807154040d40c1071130140c011b01c0300d031902164085c40c030140003010589e1800e1011252074202510440b40241100c0f13008011445c80c00c50100100c046c1800309646601d4411041c0c90942d01d0301c4406030640c00d200010382100100c00d000412a4070a0501c0003000080c1d00d0344071900844800d040810510210004c802d055000300c05951076011400d143d01c03071540741c00503545e64418403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 296190665 1250 296189415 296189417
    0xd080108030904020705070e0a060302091b0d0e15040c2903010e13081201170f0c0f0102070b03091c08010f0303030207080c010219030b102c1504090606050a 69
    0x2c010496040c2419802001d81600640903200925141c010a03c0311640503204027118607103078801401940b070604d03904e98012500210148400481030281c1c5000e000e0075041601e541c2e035468043d000c0c01000d014141c1c881c43c1e0841045c40706c1c40e0a141c0701048081900581074145100c01c0c01101c3d00e61100c00100b800d0b01d00d440d03c1d500350b07803900054200181d00240304070a40d80407000c0d4400001c0c2c020025240c240b80b83c0700ba17801a503040008000d05208507441e050510750140c103400d444d0160119001c007043d00142c50484005a03010010713450300c042540101c0911800204103ca140c5000c0b4401d03c1010200081c100908814403084070401401e000e810000c074002c00781040040e0295000317002c8170740301e04000e60412000903205822a04000c0140e061200805400a800d640c103220399090110704a83d0210032200b80d0f40e000740520b0070000302d4041c410140a184403403079a41d0020740b10400c002440b0789504001d081010f02c640d00948508030525040c01780101d50b2a000c0e01c2a10952482 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 296191915 1250 296190665 296190667
    0x7050a0203030c1803120304060b0105180d141902101e0c0f02090114092508060d1e0309060801120f0f060204090911040218091b03040c03050d08010803 67
    0x1d0a2040b060a600280c04c800c0a120075122588180c1c5080c400c107110110703010a03441d1207140a01742001581c820104840c108141040140d11151000b068070071400c000340d903199420045461700104000400303102e44420300c11500c0368842c01c031003490110301552098455412a04a1b190300782e41041c100300741c1141c000c400e105442e0100c0c2c0b00e1808007500340d0041100110082c4141c0114500c110f00f07030450511080c8401210180b401c2014099030040941140040ca0404214817482c0358000c80042c4c40c04c200038a804150159550f00310703162019002145844205011003c00c4002001d945d030840124599803000550340d40591181130484034004500100d80c1c03140d603280b0868060a6000303c400450310700604010072400e1025102034122041d00141501060920f0f20019584542c540c2c8980d004124080b03800020700b011090b20074007a0382d40764981d2181c6504ac68600b44044040e8107100d0084104030034030580a84a4040303030700034815101007004400c1c007110041030034003c0c0b5150b540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 296193165 1250 296191915 296191921
    0x1a04030201080702072c060a0b03010b070206092112030103030804020d02040219050a0e030319080603030408030a020c012705240d0b0315040c0902030a060b070507060807050a020303 80
    0x40105403681d8001c1c3c0718810b88900a446400c41003103000302c0c00780d00c000c4140780411050f0180241c1d1019421080880f03c0000040c075001070b804052005000c1c0040680c0042114030031074039000c0584240d0800100700480e02010340000005075001060441710a108103a40c60040f1648141201c0c180d07070300340e03480200c195115002d010b08105041002ca81280c1e0800040031034003100156a8112101079075000e94a004070303100207200345030b12a54107100741c0003000700c1c89100504507180c00800c0c0313440c140000b0694910300024217500455000030440e0100066408425a001c2105d10029200340c0304c100d801e81c03180f0039016190801d01d00b040c10a9510510a00a03441d281c203981e01c3d02500e40c00114422004900c01c80810b4208188582cac2c842d48034540049646014088074005080c4a0380e20302044c6070944410070008460f2080c0090386500001081d81b01c1c07001d03080500505003040c1029900c2d4003a1030480e41c1c400d964480c4200042d030200101d0481481041190001c03440c0d0f43c010740c01d5031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 296194415 1250 296193165 296193167
    0xb1806070f05120a0e0709020f1b0304080f0a0c24110708070e04021305070c1202030d02040605370315051f032703050307020109021302070c1a04030201 67
    0xc01c2100d06028420240704120351801c0803d651407040f03400030f1020900088075000c883c6442280c2c1c001d404203078014400100803001c50400d460003503108580c074404012a641c0c00d43d00310701c5284c1011000d4003411003c4c0d2020702d4001101c1825620603044032291030b90b03500403500c0300702d4104a141c520060b61207401074058829180340d1060a490f00030b55030480c0c2e981010340d2514030503034030402c14001100f0411055203070048a07501141e0840601340105e01c2c00043c02484800c0303a89005000c1d01205021415082c03080080e0f89a841600800315038039502c2d100060100e4020383c0b011149013084080c48915409034040402040a01001030030000742880001d80190901c00010142482c050500154a13504c2d8000358290090740b10480b1100040c11740006c007511040044000c1c10781740d0480065400380280018080d068051500948035298181d0480c0504400c681c060361200c01c1c184c480b09008410360090117043e1048001c040c18990b035000a000c100c55078060509410f405100410140d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 296195665 1250 296194415 296194427
    0x80f1207031b030306180e011505092208400b071a0703020a0908070501020718020903060108031801020105040f120512040f02010905011803030302090402250b180607 73
    0x42c503ca0308010502d192520303160300b03042c041c26402c0c0c0e451a41750601c00110300f800780f041c4040c0081603813040c4026414040480e103e804040c080b0501070026088607003003181c100b44c08078007843c0d000d106c25075940c901c1d940d00f8200400480751480701c0c40d0355941504800e1000011751100c0103112607450b8500e46400a00f01460300142c0066440d181842e0001a6000e000c4607642c0c4507140d140c90051316030701504c2004151880a81200303140d076025100030720a584e0001000801c40340d0542560099580c4035040700064002e03050038030b41522440380045001800032010b0414802c0d020351424041c1900d02c01282a03d400b0760b8042d00c0ca208400414000c12644813807020541c1690812902c4d00702860007408020300102c1e02514120141c0076080c045680c8000058000c01c400d28041000910316500da503403558180c400102031585c005003049884d00c8503016100f00c0d1515110500c80141d407010030391030800300240111042881d141c0054800c82c082841c0d424480b031444014445540c0c0c1e130b9400d40302 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 296196915 1250 296195665 296195717
    0x14031f020d0b1f03050603031804021b15040203010e0712170408070306051b07122a06090606091509021e07060c0f0e030a020f1306080f120703 63
    0x3110b4884440d5846500d5028807000c01540642c0840e40c404102c01d8010203e0f075018105d54402d07003080214180640040141c40d540031808c88005a50300e0b002100c0c4018100080407115050040b81c00e8455100d050842c8244618020f40c001d02c00c41c580c5014003a129092801100720a94040d0315070004140112500341c00c1401d12a82d95140070340703926440b450110f2542c011146d40e0b40f40d070200141c0380c2013401c00c0c03141d000b80318a01505007641c968512031506410f514042c10098249410b212400c44001d8002c3d00e8003285000d03000c14803080c10003901030b1140392025600981040e0300056030000c240b0078402c109540c0804007055506080104000e503000c1d00302684840140040705e401944040001c250b101e100d02d1000401010111014000055502d0741c1c105005003000c0e030280f1600c01081c0c4040c46503040703400c14040d03020000040e070328030010b000703562055141400205001500041849107401e0010032206440f13010184c24005114400c401400103045030b0070a000284200c0e91040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 296198165 1250 296196915 296196937
    0x1008070f110109081201090b0102011e0b04062303060907030b0f09070f060c05010e06100b0f1902010509120306011205060d06090305220b0909040201020f031314031f02 74
    0x620105144c0b2580902d422800007113443c180303103200420140f02e66220345207a080e4280020b000081c45440600014404aa121680c2580300c0c0400c001c950303920350180c0c019103050f03917104a03428020405d02106105094101d40a80310b60008940010700009208046079442001c461065895001030140b101015190450f64483c0120201e243d607415000e58000e0002c40d030783c800b940102801c0442c00c2d40d95604c2e503110541c101000303010364022186000d03400d98201c0030100d644c0d125540c1d142d401910401d96414032168007198500c200c0b80d810740005019004d403500300c540b5011030754400b2420b03200550791035001c038007a005a0340c000160354011a511a40041462001e00201c3c0c6400d801d450500034100e002550001b0880c013030086903102000840307803070700e80554044d0030030714200c1051288450a9210b060b2520028003160710030802c21120159100603261a20002c07001854043c6203800b844035840c2450b00c030b0083c40e040005a0080c02840305550f1180b102c02080300c07030000c0d401045091 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 296199415 1250 296198165 296198171
    0xf14010b220b07170d0e150c09010207050f1201091406161d0f030607030516030612020d0f081b01060515120c0904020a05090f040e150c040504090b061008070f1101 72
    0x440c0545601c155100105884058560b405040031f540e42990001082e248150805002100103a6030009130170b01595416a0101a1440d100780081c0c50301c42100441c0a030766003400c0310300003000801c4951441c5c0f00c112a0440d265602d40d90294403c1000c0c0d0035841d0700207040780e040030300d5103070310185c048842c3c0300080c1001720440810340111303041400440b06e20012030f841d00c0c04d1058140b0243c2044c850301d0b4079031501700074003410f01c007280165000f41c40d40a40310740d6260344079170103102c0410080303000a1350100a8a035101d443d8413040c0098603252121f0040c0d5444d1610010f8207007402e13030800c0e0590201905c00c91600710f812001030b50074140502840003a11003404002c41e2038680d480104400100c548409450b007411804000c509154070303203098041c90a02000c80c21800c40001c02c0c0705907080355800440c0680e1100d8002680340642e40c82503511030304208480043c01410003003603015040aa07000c0e051882105404d41e100c460598a541c00151480e400d14941445203810340007541c4400008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 296200665 1250 296199415 296199427
    0x60306012c06070605040201020f0718021b0a05070603060518040f050106170c03011b050307080705070519030810050f150708040801060f0f0e06040f14010b220b0717 73
    0x2c1040740d08006011100c81307a0320b805100c150368040000d50030519840c030081c158a0700b060150f055004480b01507103d0242c002c40c0c140d24100c02d80c036552038051242c01c00c40c0c150540d0f605189550304107900c5481d011902e0080041141d0400700d0044c1c00c02c88882ca660700707950701c0e203a0324500200502d90081d5101e560b02e25000c1441506204580e141d006460018044d0000e040c08044c00c6400c412100c0020b5030345264142c0380c5a07088425030707604c00040e05101065969401080d074162040002c001c0c09402211400a41c0c4500750700c0002100b40a035488540a07550507050300c0e1841c549000300d540c4902203c003010070b5841c092002d101ca50503416001400c040d010360754184140c006802001c000d0b5180d10b014454907ca00c040320008000742c1c50110071481c9801882c10480d81c01400081c0584e842c0c5203540020281034222144205101c0c10b0110747d0340c2c1d51a260356a0350031410f8142802d946140a950900803880301000031340700c040400a00d0001290380c2c07007814440c140c0950744d0001c400d03c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 296201915 1250 296200665 296200669
    0x2301030b030a0b1b0304390906090c02030c07090507020a0b0f0108010e03251a07020f060606040e0a0506121c0e0d0b0f041b091a060306012c 62
    0x141004148a1040c845007801e0886400741800a070484e512401c030001d004001c0800c90309085201c0d45800c01c1d10002024510303950f0041c04060000e82030400c2c2d0402d0b40300052a200b2030303019400f01c8210980411400800c400700701d0b145e225031040d40e56107601642060000c4d13186a40840c2d04004180101c0d61007085980d1400b089203000c990001b1145420401008113090a0058908071030b2080007442c0382c41d000ba0b113220b4101c004c0081501200c101440e01c101040344051008031103804000500703220303107090800250b6400f060460400b0b50b0081d100495910705049041c1d4054030b01512a2001301d9480c04074003801040c00410140c0d01128181d00800c006034140721886000040304a500340480d030420018000381e01c1c021310f035401040503100c46000b051943c0c000d6a000403100820f806c9640351810301003c03192325240c0c0310601b1541d498000a0158a6620044e0f4002004804107842202c0d2410440103005c01c03201d83d030103d104001140c81001064404103044444190138000315510a00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 296203165 1250 296201915 296201923
    0x809070f060903050c09040b041106090d08090a05010905031203131703090607052502010c211101060e130602130b09010315080c0d0303060e10050a08072301030b03 72
    0x440761002c64104081841401000e109241d1a141c0995525900703003060390317a540b40890010030142c100030304841c5c046001c0c0e650000721445244007c08145510006003081c4001d90300c01510f562050030055400100365020b0042d02c41118402006010f0079180303000040c1c9150f10040c4410780316039070801d40b10b0002c1d410348440480a0004403540341c40385410418145810310141c41001401014010301d9032a1407080d800864005214200d40c04800c82d42c401078078030011400006141000202c4816040403c1d545444001d02d07141c0d9520b6108036242c034a0500b06c5945003d08850400c03450300182d945080c07103031104109442820018a0200100c400100100c0d05400081840d803002400a94969050041d0180d00c1c0b9988503400c2c04502c3d00b0241a0f580302c9000800b070040020500d50014580203601c0a0000c10003a503e0390710034980360385c1700398405600f8001d0703034441c403890000410309107000038103001524000090102d4428a02481007405c084c000000c80c10103485010480507910244 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 296204415 1250 296203165 296203169
    0x803010308040807080f030901030b0105130902090406170d08040f0501090501060905011e061206050a03050105010e091b061614010506010e01020a0b0f060609060a020c010801050d120809070f 84
    0xc009151180d00f00700c5580d0401390194440210340d80160920210383c00040300325900d10304242000203a07a90804016100c6000d081188004140300b16400903c500043d001050000000c8408015a5485030b0f0001030031a4aa80c801c885688000b440c07081c103500071040c0c15006802405c40e03040071801507592509440c2c04810889141e51190000c22001c0f46900480c3c0c0504000890641c06100958910300c48503004e1040d801000b414000c00c4003090503542c020000b17001d000d410862007584070f007400b41c064202841802007824145002aa143c4408903009010a50303420800c1460300b90b174003c00000c2d40001e1142044038091000b140001492001c540c8400703407201c4008076207803030b100001400032851003c031079041d074000d2214540040e141c600302e03e92002005981411503201c10002c10b0050280d5440e1075044800021081d0784160002000481050f0990f40c1c0c440c60303a01c5030f05001c0d0000c1307441d10060940c0001c90040181e90702030445560300c2100c00b07084681c0d40366101c45543c035240d419 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 296205665 1250 296204415 296204423
    0xa0906110c07030b06090115120204080304030b190623180a0c021204150810090903090e0604091106032a040602011505090403050708120a050a0e0105190c0c08030103 73
    0x502c000f0400c120076402c0c41e0358425805c40f80031130603604d821000f22010816011a004004001d03c00c1c5000d41010f0f13040d1409446107204494859899242182c07140c40b0596104010b4407004034544c10304c0344980100c0003541d00726040550340740740555001d04046407040209078451030005d41c00c0c09502001c0304c521320038081240d01090784440d2400107420540200480003034800204020b0000c4213501d0030422a40c4500c0c03425142d0380d51040c0904411031055000031034018140720311101030660129100059954841003010f89441e980c2c100811901031050081030740e00f04c0b01c002e0030a880c0880195030710070344510712202c50700589001507540302040301c418200c80001141c207020342136091040c4d0221070b007240344089540d0b040200040c1c003100000d00040c20007500240d03050801082c5402e985403600c5021460460b4101000d402d070240c1b004072203541a41d45031020710098801d05000d024090380d0505c0001041700303a500400d8010b0805891010f0510118105003000104440019030081d406 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 296206915 1250 296205665 296205673
    0x1d09030702041b0e040e21070f1416080703060b0105070501060e1f0e1501050d0507020d110313140a121109010e07090b0a030f020d0b0f0103140a0906110c 68
    0x1e1220f01800c562500608a8095490410001c0c115031002401121105002c21014015000c100800c0414450202c00601d04840d0f14042c1c5c041107080e140c01c04809156105441180b841a15655514a924410407005034046501000412100e038041c145080c2d06140191524816440d45400e540c0d0560180b82e009001e0000c000c0c200c440c88160308034003950684561020340ca0a0340000742000050003d14611002850708074480c1c0c011001c840c0040b440d08814003541c13512220107915501e019801c080420a44001c08080e0f40e00030084500c081c00c0c032101150350904158005d821800c1140d01560010001900410311402c0f016212094521840d600d441409202050003040e8606a125600048840040c420915042008802503c0030311150b00d45542003010100c2c060207043d490070803090b03c00682c0c00e41400702d03034009280d041c01c2034406010035032041e40110308450481155101c8400c0315800316041c0e00c0c0c01d400c8122000c0c050000400c0d02c00c400c001c0702d00c1540c80711002621583c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 296208165 1250 296206915 296206961
    0x50d0c0302090c0705030d0b010e03070e16030501150c020a0504090506100b04051804020402120106120621080c0a0206040f030507090504031407050a0c06030609151d0903070204 78
    0x1800d001400c2d0b005507003c040c0f42c2804142d5440d0f682e00d016984402486035110081010b0a900c01c4041407001d41d0010212403005559074481380030030509840c90454180306055103030101d8085d0040234101c40394080b0200034650715250444254041550803648210a4a40085e4507034503809414000b90240e03010300742c2d50801c40d04140d01c001aa61194811000a2104120b25540c030940240400d840624042d155900d42c80003500a1041e0025500d080c0d54510000c604030368440c4400c9000c4018450401440380c494201c481469001400d02c02c41f6401d80c02800000303490300000d0074044020404588000300a607002038501d41180e0003681c000a0000300410038854204400030050a09003420071142c20a2707200141080b0995941c0900e80e0300014002040240030130681d046940c00030700003100f094031003000401801003481100d4500742018103019040440c2d800c1c1e0812200c004104a02441a030410040321450040001000740402c0c0900300c056121030180040012180741c5040c1194 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 296209415 1250 296208165 296208169
    0x708030901120e0d0f0e06030c0703080609090c010e0d080c0309100c021302090303090a0b0c07090614150f0304060204031736040207050a06061a0409020a0504050d0c0302 75
    0x5207445010b2082c14100f02d03040e54040401c543c58411300301d281000e00d04800728410340d01d40c644160a15003051700001004580c1800303501400166200f6902d102c165229003080000004066415000640001003003203069070251074442c12009028000d80c2c4130850548588445800c500704402040e01300080d1040369140c4081d405017601c401b420003244900307543c0c0214001c00f903004080d00c0c285a0018104c07046550402c03c1d11b000040c0284101e6080e52103403106480c0e508543c00500041c030a8900100740b01005002d02429508000c2d00c41c4d030201e40160070030151000018400c15106800c1100e41080b91400300114403440c0640c8000d42e0b0365203103180014120b09441041d0580190a02074001361548021a03010a84469070960507030700c02402000021010140b42e1030381c402c0c4001201002c128003c90030200e25170180008200041d0b0b1031580c400320000340000b044284008020500c0302400c554041d01403a034070352800301c0c01d150710340000c602243d50218094030502c01c0d0041c100114 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 296210665 1250 296209415 296209427
    0xf080607020304031109130b0a060e0a06080c060a03090b092508060414010209030109030909050c04030206300702150a020c0a020f03280308060612040f0f02030708030901 75
    0x4003a910042d0700e414a035483d081a0086603c042c9445048074001080d4622581ca00b41a10180c20130040441400d00c880c0401c0105041d202c2d0414907450040002c007101c2081c4905002c4400100107803880003c45820808242d00c41044142815a00c030680408500c40100c41885204000018200440c80b60241044030640c410500b0f4107201804040c401e104000c03d010b40c006a000400050301101b045409000e030059038541c941541ca44608182071692000400088a24a1108000c16207035010011503a21550001a4210100300700140002c0411100c03a65500602000d5018840e0301550900d603105050710302c180103034000e10b1048070780b044483d02181c005140031005c62601200d22252500c5041156010b842580c0208010036652002c0c0401035404041218100c10040340700e092004107940c50f0700c107400050643c00003801504051080780c803a2101800d0702c94466442d90b585403c80500f000d4100e420071f840700b9903107005031803c04ca03c4000d80342210145031101d21401c001880 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 296211915 1250 296210665 296210671
    0x908030103080418180b0403090320011101020906041802040e0a0e010c0e0a0b0f130b0a0f020307031409061e091e2b08040303051801170609130209010f0806 69
    0x200c41d05e04111144011380300701c01580120752000550002e50351f02c2c00c0070382d1212500e5001401c1040160406c04d14075031401020410b901c400d03200d80c40c1d05266410030501f00d0044201042c1c0080c400c001c2030140390800101c005101000c1c18002d454a0b490b0312121010780d5042d01c41c90000c40d00d82c000c3c61111442801f500e030204900e4644030942c480d50400180b01440140304110540c20002282c0014140b141e080b01c40b8415040124904280d64440840a0307521150103000014141407036101c0c00c1c1d00c0401103030b2201d80c040c0c0e5415000c04890811801e1070707010319080b0b60f00140800c5001c1d9603040c0a10710300c0c41e22500c4076007130b621440c81c1418042a2a00c03820f8600e04c009100000c42400d80d035000200b021848819090462881c0700005080d00d41c11100d409001d0f840d0124000080641c8407009000c44201e0b007001e80c04c2da100440040d2583c1a4a10b044280606400c0004561b400d0030040c05900c81010541031000444035004902c0200013a0080c05001c02d10500a21240f2010026190 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 296213165 1250 296211915 296211959
    0x110a0501230c03091c0c0501110717030c030c0f1909080618060a0b0a120c090c0e01020307060b0a2105010605030a050d0c0309180f050601050f0901080a09080301030804 74
    0x4a180b40c032503091502e1781400000c480c2a05c07250402c521026119401d2082c429a1141c002c0080c0041e810011840742c0000104842c0c204641040400c44900b64041e28011403074a0000d41c01d6407540030707103c80f058106070403081076800c0500c264249850204e8150004a5154070f5072481ca50420361007504004006061180c1e001d200801d11000c1200040c180b640560002e80c0083ca12190f01c00080d0111684d03030009800030001d104001c14070406d4011030007111480e000c1000448031200c400d8841090901d0510b004d03800620948010038103580103400043d1004007000040d6445450111903400c105100d100321400020480702001024800e41d8040d110460040046e21f406940d0142d03030700c1c002070402c070411080c0d032440d03020540038240c038001808403030440c02401c120700c48018004200e032050100100d41880c0103c0d50650154046481003140e41c27078030b5860301c102000156540c07500034041c3d8011680e80c00ca48070102c1d03424006980030354450f48109680c2e52800301051101014140820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 296214415 1250 296213165 296213167
    0x50a051c05250f081009090311010507020105010e0f190221090c060f28030504020f09010608010605090118090203100609080c090a09140105010513050c0a110a0501230c 74
    0x9104203030000d403507418101c0f0b94540b49203199102072500107042d8a69001d81c8105d400d264600e41015000020942c00040540007001150784411003242620300a20441100034000c80210361120108100c2990280e880500503000d5404411500100e0b8804080c4007001c03014054460183c040310108260000f6070000140010720130540010b4581c0300d40d00070459041c0000a51001341d54038006800180c0f56041e80e00c9901e01c1c050b0310084c0241c1000c5034202d2249070003c101d01350381e141c0166014180d81d45950740f000a81e091038419205503020707209043c188060361194440791548151740c6405410040005610390a00b85115446400660408010301051110a006001c00003405c40e815a10071582709429880d2100040c0051052500181481541603500000d034001504418100c0f0810784110b1207103001009081304a0f07806941a105089080140c0c000e4a441402c00c03440030030081003034410454a5540302c6003180c2031100c10440c400c01400440c07000f0522080c000c1c0c0d0180c010f840381 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 296215665 1250 296214415 296214481
    0x90607021b0a05040c02070f0617072102130e090a0c05010507030e010e0a03020402180109120503120c0903060f0f2d0a0e160509060f0a06050a051c05 66
    0x280c003035600740101c13401295100364010700948200000c0005061080b8040b442a03110071000340003c00680c00e4030078030344050002c81c3c1014030a440380f600c00c41c044401b0200c0021154a0080030798403401443c2e40456003103d010943d5881c5040d2103005100c01e00003410301c02060701d846041d1031415400f80d4113204091040e00042070304464281c41030202482d00c7d20740d020b0310500080548501da080a034100e0700c08115030303551041c0749030300c001d40910980300da1000e583d4170800030f290a8090303080109641c109002c0145640d01915a10b030b008400c0a200c5403c165520011903d42041101c0c0180d01e5070100052001c003552b10a9000c0e0402080400c56070051241580142485880a0003001c40508100011551080d641c07000d45800110010356902d0010036084601d01091406a68032800300000400c00b203107840000c100d04010007400c8090200d141190554040c0c20001c1100140b007820441c584c1c2100200c21888004c1e5004003002600b41042c00103000c200a0205184000030500191 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 296216915 1250 296215665 296215669
    0x7140a1d0103121407060b15040501210207050a0c170c010512090a0c15080c07020904170d14040b0f0708060d0f060c210209010504030326090607021b 66
    0x410390569400200405481c2042101115403000c0b10b0701c103d814a002144600c20010356030440940c050341200d1120300080d001600c0012031049100310f6000c031320991150205100525840c00ca440307101580141406495204d01e4101503103c0011558020390074001c2c0080b0748144103142d004c82142c0c000b010342d62491000a000c1e03204402c1025001010a0300060b000102046800011644607100c484900d545409001c80313180c103107203101c010440c0540014211008041a19201c070740007001d1800e5904e803911841c100c1e0240c0340c200c090943c0108481c20201c0468002ca003100807043d03491410034a8242410383d0359000c0074185070340c154003620078894010361007036410303401800407038248210007028508041e920419401c0281018104080c003440340b0340018640c901c0c46030014900010010954610f0201e2040e502020302003070b4144024400b2a00c0349140d09401101005642006040500c191032046070840e000321065102004000a1030381c14010001c01440c0c410841104125581c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 296218165 1250 296216915 296216969
    0x40b0a0203010312050702030a1401020417060907060807021006030f031b050c040e1608100501060903052107050a0b0411011107030f03170a0506040c05040803070204091407140a 78
    0x88090104000406c0c80c009640d424400108160703844020741258004510516010f50800d01c109602c8901041c00d07181e00070b1340401c03282e2203086030b00045c081c4542041c4066a10010242c50842144500c0050140e15201d6214100c080c602940e01005264804d1070010407000f90140244001154040100002480081d92240300c1c24102d6001c174104041c1219203140c0682480c5c000c506100c001c900043d141c00114008105000210043c403d50b0707201c00301980c03a00d04e544802844d41c1e0081094019101ca150030300c50403040191000e83c40c12904d42c60b681d15005001c5001d8030080f803c201880204050324240000303030030080c01c06888031012149565281c0115100160444600203d503c0170144959440f0903801c500058a106e5400c0c450124801032a007140c400380950720303142c01c80000c240200309540032500d404004505e8201d0960034400a4904600d045545180c4c142c03103040038201c00d10490f4040c10580062542040080040000c1440c0b01c0e8445020b03142014002c040482c2850 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 296219415 1250 296218165 296218193
    0x506030609040314131a030103120e0a1205030a02150907140f0303030412080604020f03180705130c03060504090f020d11150304121706010c020303160308040b0a02030103 75
    0x40d580c079102d650b1400c007660700411400b5450070004000a0484000544020050584192075007280300b8011030780d1903031620310080c080035100c101903101140b4004c2c461102d0703480c816005018414034580c0ca0a0714030581c110280100c9060f040455100c403031302c4d410040d0304604034680c1365816042c1042c1400300e40b500068000c904040c0008540810b1988910801c0b0200b80405421242d9034902800c1005000b048040010001407084021805c01d140c58001d60340c614003401035003031441c2c680c20f0081480c0d40c0b143c0180040e90046003800640ca5441e81d0380c0c1200711341c111402103901e07080780b5002401c03a06e030364000278459840c110080300841c1142041328042a815560611090603505220801d01a400e460f290700121010844c0c5070b04100402440c00f4034440e400c41c8141013600c40e41501c00e100c2c4c005104004402c2e643c0090910b621410f400b200c81400601568030304800260280d00358601c1d010150041403410f024001044104448280d2001805504500303650550703840c2c00c1025042 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 296220665 1250 296219415 296219419
    0x1030210031503080414120109020105040e091e01050a0f090b0a0209220605040b041a10180b070201021c0e090a06090f0516180b0706060e070203130f05060306 70
    0x910364500544100c0c0420800b8580284041d9100c1c0d40c0d50b015168481d0041b04039a0046885030303504180c9180500401c1b04555058403a54201801d1465401d4542001000030300f0781e11650310b081e00704680c280d004000c8207040200200b214030b801c2c91030341c3c155589070000240c09480d1060b0600032425485e0080d40110380c0842c05607607078a105000034500d4062441c0ba00071015040501440d003120b551000040b541c050300c081c06189c0507030042004075080030842031941d90301a0341129041c03414541300d1340d510b141402d10f00359412100b52030340f01000703803900240000c0c01e0004402095607010024060100444c00e9010015001c40320700400400f807040faa94085c7c4814004107a48800d83d0700004050a1070007000c20510481040d020b014010558402e0700755030203804290741040c8030301c601140310b00e54030801d000b245207401c440c581c0640c0900c40a071441da680d400089a0490003100300e0340907000030303030040d0b40303401900c038100c40102000c0d80700ba4a0800c03000e01c10003054440b041526800030302 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 296221915 1250 296220665 296220671
    0x501061221030e030a0e1306050d02040f180b04211707021f02030403110304050a051905090c040e010f0513020912060c07140c0913030e060703170f0103021003 70
    0x1c0d050307016003515034104075640030120318a401142c0c0840daa4510660880707008148404510100c0101d90417030281da034110722001841009800c0c940c1005562204158000405c00166200604020251041221008480b4082c0014056920348a4610780c91b45402032a01030ac46400151070343c0b1100302188000c48113500003c4206d8003e12102c011030007020f4402c128203905030882002544120b9080f00400d08420000304242000000d490603182e0241468520500b400c00304801880140d488100200c400302021816440781021980075020300200683c940f820180141038000c0142c00a00303222460f880c0820082c0e403180e03605103070040449c070016036884208001c5985107020b07100b88032161296609100c0072402c0c250007024032500840010401c05401d50620b0b840b0036640c00700e82d03440744030100440c02241c80d418144070511720a007400c400501d81c51700400d209801440c800d401181c8030720240808c03444810101944840b407905540c12079810b540c0007800300d81510070040201a9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 296223021 1106 296221915 296221973
    0xe010b01050a0c02040e030a08041a0907050d0f231b030a03030203090a05061905090c010807050d0b0a140a06050a050f03060a0e04030c05010612 64
    0xa0507520585401010300e012075480120341d070705991090399140c40b80410f203410030003400d0290407515644450315107800c24021800c0305240c02ca40c55080e070020442800d0303002c0780403026507008032402d44c0001407506129040d140140130042032130131200304000010405401c940c1d42c00c100a0103c0300704420b08a00700784030300410b00c1586d4041d40700000f8030340000e00076009154808055030840e400701400d0385034289040b00644100300041441c0c100e90100203124003c0350b502600840080c0940c11809000815101006060030200720380130501c4500c04500d0b8002c0781c0120001030541d040603480341c02d4107214112641c5054071400f1142c8001038854007660613145005403d031105800c105a070056640ca40e0b20080c2030a40c08100c4c1c040111340c0030700780401d540c05203000350f40d8164903580900d000741c02c4a2160b04a074042c80c2050821200041c0541488800c1880101e520f4070111 = true := by decide +kernel

theorem cover : BRFrame.Cov 296043165 296223021 := by
  have h0 := BRFrame.cov_init 296043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 296043165 ≤ n) (h2 : n < 296223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
