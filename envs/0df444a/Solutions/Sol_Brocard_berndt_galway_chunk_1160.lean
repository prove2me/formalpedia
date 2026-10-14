-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1160
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:31:10.948338+00:00
-- url     : https://prove2.me/submissions/9c89a5c7-7d75-4c9f-a5e2-cb526923fccc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 208453237 ≤ n < 208633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 208454487 1250 208453237 208453277
    0x319050a0501050c03010305160e15031c1d01020303131b080304030302070f09020a0f03110f040e091c2c03010903020715090e0402040906020f07060f0b091303 70
    0xa034094140d51034207040c44118665a802035041e01e00403411912140340713041820328061b101d032161020078040b440204800c83e41b14000805c036000c006048444400e86000307100c00801d4280188404640b51103025400c0083c4202015036480e0240003540c25450b015405514102503c4402003080020300c05145186c1003091400300584142c2d000c40340c4454803403601960b68500ea02851408500c10744e00026014018003c4a100f4055690740c000041504101035019141c1300c12016045a4144104800c007040301000d840284000c0100c55890b0030100c0740715041013a0301444505814800c1c4800406a80007004024044031082c03480140349032508002c4103c039000213100790b165080800034802c0c036500091000030f98001942040081c10701240680d01003000e403043c070700321420050020340545817540c000b03e01e080c010200549414585140b0301d05540c440002220b103290340303112600c040000c43c462001c0d602000e0b15000a10300744280c211414a003945402410010300d007000103034802481d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 208455737 1250 208454487 208454503
    0x1e180f0b0406021e0a2c010f021c050715020301050901031b03060e0c0f191802090a12060506090c030414010e031812010510120302070b0a0503070e040605031905 71
    0x134010030041880c250b84c0c031034203504c43c002c0c100009800c04d002c1c038030283c03128901204501416201d07054250442005451808804e03041100798003940031008881b0717003540020011190709980d0b01e640c0b085980b0b003400044008951081d4002c0c130600041c0150784410b0003142c1500d4110116449115580c5500c10840c200c40e00000d000c2800c2c4500c219440d0320000e29121605c80440b410a4410744280a10100d404545180c40d05a005032100704a420400980f12004d9000310308050f207462884c202140c007881c6143d00c400d075a01c4a545814050208610603180c11143c00c171100d6185041c9402c4c0c03503119003c0070f000036100e41c00c503201e90540681e0950103624400101001c0d01c1d02c1d8400741418450b03040101c5110b9014107420142d0031044601032050340d201da0040100b103010241010085100301503402421025403107040b001082d031181407406000d80702425a1601c0e81d03071a0200d0000c006101ca002228002c5081040507c42d03564081401612498591003000b24003545090039844c0c0010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 208456987 1250 208455737 208455757
    0x20c0111011104060905030606030a03080a020c07031202070f09020a021513150b2106070e03030f04030516230402090a1205060106080f091b131e180f0b040602 70
    0x40010001601074002c0705c03070b4080740c000b10159121b59481c1403d044d2180340e4140002c00080c80c200009124540c07547c0a4110b6842502c01c6600280c0c403541c1c0c80002039807000c0d226000d80e0200c90200000d5008280003000b501d0348400540c10084a04000b80d40e694101094003402c0813038400150031400c01e500207108040e001019001c4071180035028030001c054040c089802940100300e1052040300980d2801800c1c00c25100405e2242d540c1c5a048450490312440035505020811001c0303640d200c03550150015600800c05400c00e000240c10740750030140b1981c850814120140e81104052025502c00c1c0781d182415140176035205070700e00004060212607000002010001c0c020517081c05000038909058555a894403000741e00e800c040c01c19504000c0307a0182c11540304452540e1501c00d0b261901d0303091304c1c1c0a8240b03c0c140b01001001002e90b100c000850702d220510302c0e04015082c0440c050b5055686482000d1000f10b40e9035103409140503110100079000144c00c102050030400580c0c12100040c4c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 208458237 1250 208456987 208457021
    0x30c050f1c2003160324050a0e04120e01031104080705032103010902070201032307140309030f03040206040e01120314040f05040f0e1e01110406020c011101 69
    0x29100081098440030456181440c012440c56044a002c2904640410503000c1c90308554460300782c00605007052048800705500c44405410444191a000d142101411410103245041000b80055000c01c1c2d8000d880c070341800300610002c250a502801c00b0005940b03080300401d140a401640076001020f0101034113a000200080c4882001c5000001e84401f00d0588101060313801510049620725080351622001c00c0004000326251a801449003a1044c1000b140039543d00388003440d400c030420042c04450004c90200020540d20004142070151986402400d600b8007c07492a603d000d05109a10700c2c0038004042019075441c4010380300100303040c10091029684030500056a0b02001400300c0110710200b41d401c24400460041d50242d034884054848107034540020003014085d8070301000c94a03652885030b085210310602508034400300300455404040307584d000340c0c1e00f100c00600040842c29800c1c0014050168080703000070300c00c2c00034a044c044840c9240340f00350050100c5014416888 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 208459487 1250 208458237 208458247
    0x81c0b1203070c090203040c06050c12130501020d0807020601061d0603010b0a1202070f022803050303070e180105210312070f0c050607030f140a150501090e040201030c050f 76
    0x124000001c098076846100c43c918010307915901c01d0b09902040e43c0c018035081c80b2990600a4511890281080400c10011142c10307282407030728820383e6441000c06030800819203605110b1940c0402541400d0340d50b515081e2403519180070000e49540040c0248810052410f81c80c0c0d041c5240c0520031903091900030a80b95403569118445803540d40301c0d081c80360226490b0000c00001048910964080c40d81000c544d00b80b5480c03030380c200446a02c0c0d0f00e4928081034025082121101036007072591000d54441e2006594074144620050800041c40108900c00c1c81f46141c03090410000303042d200d0440d141038580103809070382d50300c003000a50495400c000003880085802002010780c421100d0141c001c82c3c0740c2101e10140041c0407203921106d03007405420f583c080381c080b50303409110741e02c14585201d0b18a000282c088038414107461103c010381d06420019181c62055000c0042d45008800070074090070080425131600441c840201f200601c040c3c1450b0340d0304002001c40b4000c80441304090a40d800d060399034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 208460737 1250 208459487 208459519
    0x3071d010201020f0d05060a0b0408060a050a020706090f02011206030807060203181506010801120b060f19060305010e150a03060207151b02010e0c010509150c01060e01030506090a081c0b 82
    0x4100c115407552180d207230703850002060340005044409a51000d40513000d070740e5034100028068100071b0802e5000540c00c000500100e04d103407041c40d42d601d1003040340703448030400c030f000050120104d000c8620b44a803500c0c100700001040c00d812103041c90307030041e005a00c3c3d0350781c10703005041c1240c0310421440c5405030303010425000d26403030f0400d440340b5400d88039440a81d8855170618070120050302e000707014402000100301300d460201c04d650742280009040c000b86148296100c14915420790050380800d884900502c440004088220390111041440313441c005070410005403404071a1202903c26a40003a80d80144685068400106030036901c0a000001c4015030255103440c0c242040c4006510b815401c145429010a070962904816504d503403c0c0348001c0100588032840f041000258181002101c410f80001e0058000920003180c581c2550361442c2001360815000400d621202d421503424230000480c02c1c0251059044601c2501c0c03c1307090505d2960f00207203103600c2144d0b403041340410620b0b0380c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 208461987 1250 208460737 208460741
    0x11202190317041703131e0305100c0e04020a020304030f0c0306090c03061503020906100c060e011d0d0207180902130e010b1806010c03090e01030c0e01080303071d010201020f0d 78
    0x40f903800a26108100e0b058612045d16409040e868138509010301030100a00c03480c0c2800d840d80325084074440f0450644e2a0f0700c95103007118605410552586500103402051340003000076144110646040d843c08500a85c025202c1c440d034040104030041c2c1d40c4812052145ca0482c4401a6500c00d00030400b40e421414454031384010391204603816400c144080e070000403403400c0181103aa014180742c4940d242e403001c00c40d403c14269041c6042050420080e00400c00d140076041c4080060800000c40c0412910358240c207062102242d011717980700543c80300025900140c1c85c400c4030310804030b0301141002e03072038002d000d40300c81c0c1d4010754028082c500c00841a40158001380c45c9481a400800ca0030341e03203004ac809082c00c5001c1e1005510041000a038155000345010f0341d80078031030302c2c0ca0904180c440c0886080d1100c00e801c1a110303500b0000040c80b132032004403419030150180c40011170a40c80c040c1e10041900d185440c18103150a1325900024859000b50113541c03405410013156625200c4492040300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 208463237 1250 208461987 208461989
    0x308070309032901170c0301021b0c0108090d260a060915030308040f0614071206060e03100b0f040204270b031e160b0a08070801120219031704 63
    0x743e18103021004490401038150180c84071580000802526860a00b1403c00903402c40c9800f11980216994005696803c0c4010100041481c4103401c405004075013103490028200d140c5414080440284140c440e00002ca80c2c89810262420003600c0300040c58000c4180c1800c01481801c0d00514284440d0005a410040654a1030642084040001034076424003440b184000307400309040c03d02181c0400e030109204850729004000100b58503802030752403500601c1c1200c05800040c0108900e610005481c01400010100343c6000880c040043c000680c0301c00c600c04c0451404d55a030441c0800d903856104000e010f580000384215140c07550f0b0b2015580c0c481d68410030f84d040720030306203003601c041002d0300c01c0800d82000a0010200c02170302c0750010b2030f03411481036003241c2c1d0b100c0d40401880405009402d9005050b4820f240d075106c0004401c0603280080241c5100b040c0b00c0c90400500502d0248404001c600d1b80403690303601003440e041a10111a40b440d08040d15105044d1040d503031030700c2e40302d0042c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 208464487 1250 208463237 208463243
    0x6090303020a11010b060406080612030705070305010506060405010e100201110310180219120e0703030302120f0f1f090509030408060a0204031a0603150403020c0a05180106110304030807030903 85
    0x464020543c40716401c8034020020180d01410a10080c001280306206060f881030001c0c0c1480a54903512240340c0c07460304810011911688900c03024020060203005858110f00156125400d00d814400007a00b807074065045503016901510326011614401d41001030071188030304d0581c6d078030f00b4404207504541105004c0c4e90356520703041c8032607820760400d88215098000310341c0b6079400307116404c0c1c0100da00035030f200001d0140c151100f003200510351081c0004e2004500c261401030f03035095080c603041d40008000701802d82851140080004054041d5162540a17001c3c00c2621004444618040749945103504000d07090341c40c1c00200a6802c5002004209482c0c1c4102240c0c0c00d07940300760200c000e902c9075000050404280760031903140450401030b0360fa08020000c00760307202d0700c04840415455090444081c0c0060340007490300c0b0658105125000701802007030384e49148000c0b046621120a80043c0318001c20800440300b102c0c0070304424070548028560044101d0b032740300c4c5981001424820070740019 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 208465737 1250 208464487 208464497
    0x100203100e0705270f150f0307050c0f01020409111206011b0501050c0a030e061014011103031003022b080d0912020a0501050105091e0703180b010f050621070c06090303020a 76
    0x110b6171924004102094001d0003a50365407400003880154042c85d04050301c080203110301804031548402007844040d43c1e07003805100050326985085442030030386040450110031610304010816450071a0148030341d000c102030030120881001084c0c440c0700e09a0402c0701038025403901052000303e400c440018007620003140d409100380030300d402803951034403020b03102080d60a203580010800440c003040015001b201c141001c2404500b00e44180c4e09581c0704807408014000110f034144218030f0000001e880b01d000d660f40070003121a000c010108a144442e8003d0010000803540e00320042217a0400c010b075952000480300400c080080280d0303500111030007104e407542050004152400e004590034401c0501464028400d08501d5480000b101c01070480005c150300c0c1c00201124582c104e103808002c03480b604044400d5032404251800e103c10a0b001148502010041007031105800301844000c980a010094055280d1500c1600e0b84103490300003c0003182007045500505030035502030f06c89066140c0351 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 208466987 1250 208465737 208465759
    0x9030f030901080412020a08040905060a06030b030304090e0708070605190e0603071d09011805090703020904020613031a06103204080a08030405100203100e070527 72
    0x2040d440340104496580061503000029002c82c01101030004450018016610020100e4480201a5200e40c11880c0c1c01919001801000d080c41c0640304001c1c2040d1074200070140041c80001d8483c4128481d54100d5601d402c6400880f45085c00840000c003041c6040301c011a40c0c920015205400c00001d40712103003201e0129614203401200072000c8502c00920603480c503074500000342d424100d011180041c0074020030351160982c443d440854064080c3c080500100d010145102c810703a50000e00d0301140f03802c1003404100580b200c2d054990480d50481e0b001e500c030880442e0008401034203034030140045107030884c43c554400d03401c12481d0040307000303962900b80b07507405c148107945049031502c10150044000300d80000a00f0750031901101900041d60b010b20380fa607120340c0145001d58415083d99002000401d000403c04108086038240d02c6061082d81145810008203a01c00203a101b00703050000d4400009a12600c154100c07618151003005207400c0d0880440c10a02c00051607030801e01508085030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 208468237 1250 208466987 208467013
    0xd181203050909091e01020702150a051306080123150913090602090411120406020c0a0b0f01211703040303091505040b06010228020a120302150a0e15041110050903 72
    0x2315070040d1f801410718440070480191a955591241c5559402c000e8280627001c24070003000d81039001000c041e91a181030354101390204103400c803500c00306c03000b8042180b1a8407042d201d00d0347d080c0110f6038894209440b40d88000110b540c0210829505104d985000e044808100140c0d01170140c00005880410106009400d04281403250080200300070740d00c00001000035159800500921342c00e1410b5a44000c4650b58000130104251282c81401407448014040d404070340700030380340d4102450410600d2122175102d440e0001100c07080300d83e0050f00000040c00b414026001b502d511399214810005010411240d9002080c0907a41155445040008580b040d8030010b0b200c08c042c82c1c00c115001c24103800c40d048040503c008107080360811490000051001d0030303c2840040240a60058250741d09050b128030b00c103e1008020707540a0346011060000a60001030ba844240802c00304d41145031618100b804590000418050340b25400386000384095078442e01402815034145d01b29030341e0620400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 208469487 1250 208468237 208468241
    0x60d1b050c120711040f020d110c01150b0307080411091f050a0501050d1d03030709150219110d02042412020d02010f0e030a030e01020d181203050909091e01 69
    0x2040900403008000136100189481d0717000c103450945c0510010301d4a280000108182d40400e02c007408800c0b400705031100000028015410045045441200501d082c00c0b2100b0745400041c1845c400c12203000e000604000c24910ba12049203002040041e0b0780c540174105886081440400f8020341c0818100050f00d41032440321368040e948141c4030316080c861040021030051035024004581c0d188644020f826281050000b94019482d0b039503010f60081c01e011403804e008400320305003001c40d4855102c10030600ca00100841d0b425610400005a40c02030f000040c2e448100260003030741c064504410805843c22810494902900040060805599a01080221098148010b501310490b0005540150f219444540704902c0328102100d001c0d1500003c00c1c41d0130b120f22011070101e0842070781e0148039030301040301240715071041c98000403036400300c107131196584594440d02d00602c800320442000c05008006442003600040c1c44904189002d05169680c0ca0f0011a855000c110141d05009a01418 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 208470737 1250 208469487 208469497
    0x322031a184213080708030f010305120405090a0e1608030315030106030f0206070222050114060304030c11010908010f1b0c0f031d0402030a0903030c0c030c02060d1b050c12 76
    0x18a42e0060315544907840071609403600340c01100e041200f0000d40b80082c4258003d10b02803036a0307507141001c0d58114a449403a28211000341141410240020007065589620040e4011f50b0210003003803000240364505d1604451132500e0180d0024840040b81e480b400001542c8070350844400214003038100410b1500302d07030a50001504640c0500308007001360801400401c3d0345880070707041d40d05a000c3d454140040151100c5a20700303440c1c4071401004082603c071360a10016204071106460f504040d50042c003480c15059004140c1c49040032450690f038082c07101180244021402444000ca0000c0200c00038400c04689150010000807244022840f8a40d55900e1551003480c071000c2c010f041e02c0544200c2c0302e030390001d4035403405845207030700075200c50028501a4049074000b044050851a02400713039600b61800108000000c40c0c4840400d500102c0025459015112030b5540d07904c40007004064580d0050b805c0403aa124a100104664003000420003800f0300001e80d00c60010260b001c50a034424 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 208471987 1250 208470737 208470853
    0x10f05070605040c080601030c0306061508060d0203030903031216050a050d02090a05040608010e060606031504050903120403020a03020705060703050306040e070f080322031a18 78
    0xd02400000403001c0e0b01080d0000d02800c030480310550341707050080c40d200b0309800440311702e965848100204000c50084401409819400440b03030484040f0040c07080e036005103a00c0c0304045c889000400e40d2424030449014200c0a0156503484440c050617940c040f0081d9408215999100041e00703850b03200d84140d56580403d039407502d18003403400c0c80d140081c0d000125250340c41804000c000400340d54a02c14480180007003800418140208104c460500704018041801135204008010310b02c40006d054a4050030126000030344da4668032822851030140741500030319001d07100184402c0c541c000031601404d511030350880310f03d0364440c03040c440301c2c1c025400d0040c0411000e0011038058602608843c0019a010080341c41d026900c1400346041c00346903002c0c04a50f0000100d18401d0001901444441d251400401c54a14034681d156440c91a4003982c00100c0c0782c004000c00c0c003000d030b07103d070010744404004116204191b107410742018924400100c1e000c41e07000c0540600c141340e00e031600f104002d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 208473237 1250 208471987 208471997
    0xa050f09060d1e12170402100c06200903060106110a0605062e120e060103060b01090801020301150806010c0c1401020a170c0c0612040f0218090a0302010b010f 70
    0x21508188a02d0101d4248102c83c0300c0e01540528502121040c05100124080d540e4581c060320f0b4000e028001926180f80100520529010000540c6540b091407203880c007945040b0724580e22506008008005042d920703050b00034000e030303220000300b40000905520602141510080d0f66580380a8134100303800c000d9110550405c03032407400440d803558402c66111502800405003280303001d0b0200d44810f20403200c00380c03d190003125a420303a64031250400c840c0c403c036001002804445440e540c0c2e16081480020a520741f5600c9142060b4030a14052008200900096413a56147d0381c151b15210703d401440400a01030400040d29584540c040b021590f070003070044000d81c2c0c100018400049402d1030114113501ca18450000080c0502c180480c0c04030056031481c0e2200e81d00b003c40b505002d4010200c1e4440d05041c0708408081581a80040c3c000d81c0c805035042081140780701207501c9040101c07006181081140402c40c52107004110003110902c01c0e030007007104500380401510721003451101500019 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 208474487 1250 208473237 208473241
    0x80a0c050f06040503010c0c03030506030a020105030c0d02090618090604111918080f150103150b011403070c02040f0507090603110d05180d02030f07020607020d020616020a050f09 79
    0x10400c50348201d40c40c0000b901aa281c41d031150701103030070f4565500040c0d002680c004a5201410382c03500c55250805000c8000d00003040407078000900390301000e040420303040800524104524100e9044031410000a0800e40d00c8641560080c81036600710349050780600b0042c0005000761416106440034108680e0701641030045211741f101440104940c4401481066003600f400b060100a1040007000900c1c0201144c2c455035401da4101090a840d00c105000450300500c00184418803080703030403103200780c002035081100c03004964030041140c2c00141e984000082c130000560203059590264000d540a00001131189130410881d032040315184009240100103200c441e109801c91703a07000d0b010340074a0342090034540400d011564140c64019901a80e41d07c81101000144030b00b5160000c86d001440c10b14030350000890480c41034050080c400d0100269032411950303a4015199000d80140110b0703203070984428984110181d0310f0040c0d12690f02c40800181d140340091414102c40c80c041e100c4440c80d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 208475737 1250 208474487 208474489
    0x806010f1206050601090e0123040e060708070e13050f150a0b07020d0b070509030f060420041e02091918180b092b361205010501080a0c05 61
    0x90201404c1141041008030b800202c1c440c64139102406803040703070305201c80c901e01140200080700020141c1e40c001c5042006207200010049001540001c09040600c8542e495850444955030000b54881c1c0c80032060015400d0304880d0fa1040b032044800010ba0043c0c2c1d00c5811016481102100256901200d461000e220750101c4c2005092824805800203500b0362041d07451105070007048500c20002480411222207074902003050a100e240ea0401901850501da110658107031002501d00c8202e0360498108034050f2502d61005820280c43c000003140c1095078010390010b0750103050413921500e5968554603c8811615100c03080b940220708016080c42c410803c2d80140801d18001008540d00d0403140c0f01052206130351910919041d00a840c0d054182e038140b8020003000f0922800c2490624111a103040d0000190390340c3c800891040d4190b0504018003282c1c3d03d4010340243d011480303202c40050301c0c018a1202e03403110351080001b800a43e0300d816000c1d94440410101622108941c0703020440703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 208476987 1250 208475737 208475741
    0x110306090114032e11180f060705030c160510230702030a0f0605011401020312180a05031e030907031101020115170601080318010e0406030506040c0806010f1206 71
    0x1040c4010b415a0030403220340789a9016003d00e5141c4c2c48200038040c1001d0141009031003410303044420f9010311070a0000e030080205201440e018541c5c01200c1265544c0801d550318015902500d6000d42100c1e680c48000303c8c4640c0b40c0141d0442e60400b14980c2001042620708080e040d152540d29550311070003040c0703124803110b0555000040824a03141000300c40056101400700d40074450150102a00350080e80c03a019080301c00c164400441407890004a10b120b0303074041308544172500410120103440e03c0b044600000742502c5c1c64510040e106c3c0203004000c01c100070014009215031180045840e105500c8607001610007101c4078011508040c2c001d20005510050740700c103454040c4000101c403d4403003240084042c290b0004080c60000b00081400300101704286070150014101031400c145589000381c0c2004944105681844030311084400c2e40c3d03e440d44498021504001201e40700e00f0141402000105180540c40c0070740035150020034030501d4410803400b00c0303401c0507194401070f24540740c0d000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 208478237 1250 208476987 208477019
    0x6070204110d0204030506011403190305090a0e070207080c040507020d11070308030114130e071a13060c03110604050303011502010b0406090e0c0913020d0201210501091103060901 79
    0x624610309000b004603000d200d202500c0514800d0340103043e6075041036011225440003c480038441d41c00941e00500f110885030ba900c3c2059032504010b61140e03081d800183c600d407001d070440c0900c041014100700340b041d030000b01320003100e0038402510303003840c01c00c41800140d0f00102c5d0a400540d10003130069054a2081241c101d50304948010740314100d0301c4e80d40b95183c540c402e9100d418101c11030444481e081c9415003524096420b20041040b0340f100b001380c003036140d0000d8890320a445203d44110b441e070804e00e0085805164000c000d4405485d00c03a140a00f0511100c08181c0000d8140c0440700e8204000040040c050b540200055055030f2904440b6550510440300b00e50440d5200d03071440341c0e03e4031749000d4500074102c03c5201080d49000843d0702880c4c0b07054054541e1285202c8011300a0745410707054044080d64050f2946103410680c2e0006950402e12130020300528404645150780c44421680301034141d4000560030b20504800d0144500c603800306460082e40540c03242c1c01008140c180c000c0c411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 208479487 1250 208478237 208478261
    0x60b0c0c0922060b10020615060c010b030609010903110718020904020412030f11030a050711040e030307090f1203020d03200a03020d06080a150b130e030705150606070204 75
    0xc580c0c251080740c0b040d088010800b16040c2d40c8030146150f2500c2d11014a5010115a00c000c15a0386041d012840c0030a0003003011038003d0034009041108003900390061102c42d6009070490380903041010700030f8020406d81106900143c0820201c150940c1d0100e200001c84054040d90090901e41c6e40008000394025028140e12a030b08000026800300d001350540d03030490090304c40320070616104a001d00800314031444a00740350800c21008400c66001010781c1d80079038000c088020710003042c40109000304000440604140310100400c8641540718640400707403141682c403840c82c20b07503035290700300c40030000f072070040141c3c01c4074605403541e51290740f00060055124207090b504a103c1d60306440c141c2d02200c0c044001a80008401880100c1401118018400400104400c500710740320703030ba0400030050607440301da521000b0306d003220780c0c81210714101140d2040c0f0402c4140b1040380850764950047c1800c0b190380c0203103c80c40000000d8040c1c820310500001d448640b5004541c1d082000401450401c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 208480737 1250 208479487 208479511
    0xd0f0c11011e030c021506030a0305030a06030506010b1903050103020603040605060a0509090a0618030801260715030e011116080f030a151202010909020a0c05010f050a060b0c0c09 79
    0x85820808000340510040e0355140041c0c1104c442100074201803804400d010054003001c140301d036644000031001c0314103802d40303000c41d102c1e25072405003000303843c581e4400b500710300c40c80c8004100303110000b0080417008000c1c8800c0c0c000102031307002541910024400650f11050510004011071078640095900107070082c003030415180c80710005144041c0548100f965a03118007260820044a48188030100d40040d12480c2d043c8201e0b600100f100d07105000e14400580401d0941c102d00e4400702e140000c0e80e0009055071106505c03603e40341c001710304031050740c4006030074100001980e0a041c411254003c045020b12450041e8504400f120002c0a100c2254420010400d551a0750f440c0070145003c2d454900b80810070110800d80300403a40c00c9608801c030701d149621100001031384c0001c20b441c110b980ca010096210700d1000c00541d1310b1140240301030701c1303542000b4141c40e10000640c81144220426101007033a25103130202c9880c24040c6087d090a01c2e841030514010501d00401c40942c000000201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 208481987 1250 208480737 208480757
    0x70c0f0501050a0b12010207080433081603051902090d06092105030c070f020a030209040b1f0503070b130b070b151509010c0311120306030d0f0c1101 66
    0xa000d0071102c2c11100c0c540002c2da07403112042e842c07401100030040c02241000035400c03d80c0395124080e062040384544562140c046900d01404401c000e18041c00c5a4207114021414074000005410305004840c1d13841524a440c21210350b0340d01911840c0c0c0078108220202e440010f845500c10025800080d100381e112884079007460004401c0d02500c0e075100e01c00c00592515220040c10842c41c16101100300080c400244100240650340000399901c03690480c2c0c0307400d2214124000300d00520007940000e5040382c10b000801080c00b4018140901844e540d0207061540191300250482c6087c0c0d5001e49075154102080800c0080505005000d003410710b040599581070f980c001c01d052035407200d038040300d40d0302c505000c114202c03201d4204084d00d503a056401e00440c000e085003160b410b10814009070b040c40350420a92050510626004c8000c400e100100c80985840c0000080d89410440b4080c0c4603200c0c90b100c00050511070818170403071010301d4440c00a5a02c050360382910b405101d00d1118100246030364 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 208483237 1250 208481987 208481993
    0x1320060408010e1f0b010c03080606070f050a0201081b04120602090a0815010905062101061e03140a08120a02070804060302090f010c050c041e050403090806010617070c0f 75
    0x2c201c1000034a01c4000300b003038810540441e5a044d1003075130360900c05031810300303000c490340d80241e40322a400d54180740c03000440c0d9601d40040d03418011040d02800c00385805640f0f1081240014080640e40d000746c075001559070340c1c50780707030b0040000c00e180c0d6030420780e4240030401c01050010781032180241b20b10310141c00e0001000204d0301c244030541c0070302e030a03510058113558081100c01415001d04040d01092100d840c00d1400728007054070103d0003160310613000310400b03d00d04081d401100034010346013034070911021550003014000c1140c0410360314000c403901c006142e190002041c00034650f00403405410010382021616400c03000500c0351201503020450301000420000083c03000c0c05081e100162200b0700d01042c8052031010410160503c180aa0b80c10007040303001400d13071842d2000312001301d0030005c41c3d024402d41020006641c45124100b000384401c0503088484081030f15815002c03120580e0ba02c0e50100d486090283c0c0004032911880c0c04100713118401c00c403070002280074080701480300c0601d03a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 208484487 1250 208483237 208483241
    0x90605040308010509070306050102030304031d0901060801090f1b0c051203090303330907030603080403061d060f01211a09010b0f1e0a08060903030f132006040801 72
    0x803001c9000500550050019142c150501c07500080f491904025050420002035034a100140c030180600109410381c1420342c2c142c00b42b0000c210300181030304d005540d4541019111340e801b801403001d503905000c092910031003a0f100340c01c0c00e040440f180180c900c10100c015615000700c02002e41d03d034081c0c0c52985645260503401036011b138501c20003e503503034070b000c002c404242d4180c3d074450f03040030884121340c0301d403800c90b68001d2050040481d040540c0c0d88408000b50000c0c03126600050600f1000700300003041c80001d900c258214019840c12944204882d080742d0f48501b01100e91411084c800c0d801407054041c91021010b0ba9072403020401c10030002c50b2580c1078442c45038050380110f0800c480820090940a004160800c02c0a0b251600d5101042c00001d0f44c52480d6207003c0c0160214440764103242c0c2e01c0728034060081c072024003a100a8202240030b544c42c4e80c011102049011200d00200355201500e80403803201036006800820090340b0303545c01c443c140c1140c1c0401584041c00b8000070600c0c00c401c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 208485737 1250 208484487 208484491
    0x41a0d0b0702011a010e1e042405030a0f1e081810090f0311030a02041e11070b010504180b0907080f010c08010b030702100c08061e03100c0201090605 66
    0x140380561564940104001d080d61244e110b03003010004658400906130340c00c841c4046004004494034002045c940002c6420307000c840161b194080d003131018040f10030f5200c9003614141000815000101916017081c03680d281a03d100c020030181d0004c0d1340c0320104126200400044182510444100c1c1054442e040c0b150820f01d0051000c0300c00e58408003007450300d007603d10050442e0742043c610040c9456801034075400c0c6484060004c00d076410b0f80350070310f41e070a006040056500a104002c0507240304080c1251401e07540064247d240340110040031241c40c841070f540310f55070104648103560309140030f0102070001c40c400b400c4c0c041d000001103000107100d00f0410740700d920f52000400138103162201151501c04280b1090105901d42600030a803154000740c01415500600f5160345d607500ca80d0f5040b0710303005624940015040c84c0c41000d400d1140c2c050f040a000304801c40382401a504d41c40914910404440d03038150b490b51003e50920308032003607a0040b6420410380d000005039440d294407000d00351281 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 208486987 1250 208485737 208485743
    0xa02040f06140d03080a241e0f03020307030212031209010b01030b060708191101020c010b0a150f120204030803010e1605030f011a2a07051c02041a0d 66
    0x19450309100c0003440c2d4110b0422848122102d00c19148039803000741c000782d005040c2e0300d40c071a168029443c241a2800d140c1e49620074002c90010582d41e00ca00c0390f800c1c80200000014406003ca50018600008814a40540ba0024041c00c003041c5160700b00100c0e141051003019660005100d0400081d01c03030b01e84544074140700c40010520012181c0014200c80c444134240e84954014442900032800c107000381e6071140100c4600c41c084411500c8152414403911034171180b10b40c0002080a41d920064000100b411001d50390180c9040d2940001500000c3e01140130000400031640c21000034815844a0481a0310100042c9413035142c1e2980300582d4800d0b00409025a500420310461031134a8981d500c280c122450a20304504190303442c1d08001106204010380b048c1c0c0200340d624070078102d03000c49104010094050303001010300303003d038035017081c52119004080c0900710001840d41024802c071850701e6200381041030b80003016801c01004200c948030303104400920400c40400c503100c9640c1c42035281c3c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 208488237 1250 208486987 208486991
    0x61512180a0f0312180611041211090f36010c0503010e0705090901061d06040306090507060f0e0d0606050a0b25030e130b09010f0e090609060402010c050a02040f 71
    0x11a4100600100303046030015000f1850200d0705000c0d02403100320805510ba1100e80811b0341487c1c0314405040d40a180c110302700a18903024404108240d1408202d180340342903507903140359a0386144240582e4001c13201e1403451100292014601450112045a42c02c2c001d80c1c05c8645a003c06051030031540c0d2100000701080380040140a54507280310a0f90f070048031b13454628a45002e0102050810106100c0d0f101070000f4118468100314001424400b5194003034402c54840d80d9034103152010b000944025107080c003545402090b40c40c4100300d020482e02482c3c80d55100c00c1c10342c1d420712022041c540000e641050f51b4000224003595003410400040c1f008045e46030b2602d15441d05055451144003000000f80403040241002039008040107560400840d102d02910082d418100042c000642006508c41680400414141c1c418480902034441c541e840000f15940d2102459a8200c1a81c0044441e030110000800661050a50f412094410400c0d10076441455000c42e069a00c4803c290003420f03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 208489487 1250 208488237 208488263
    0xd0207060513020109030f151802040c0806011d0f0d0305030108070b120a05180a08190203040e1501182702070308060108060402040506030a020d05061512180a 70
    0x821035000d655007124003808050066a40caa002800072510352200819442051800e642404808207075207000d940c8050041c010500b0b4032040e4100981d1024040740b0941c50503958405180c45016003500c92401038580d020002d05218405d5a103015501d1102e03408000d0040c0b05049448000d44000380b2071190300d07256200d5050006003403d09005402440005100b8003411140c2c1414020041d0003031004080010243c640343c01e01409150000000c141502c03607035480c0700401c10030800400704400c40841d615030082c0c042c8400c07a102e00c0307a0712440402c801004089030700180055500c82801405040c84890304043d00241031180601e035102c00003040c0740d4a8a100010ba12403000c001c440c11041c800c526050345590090001c410190071a41042f0903600041c1d42900c960b412113014100007884030340c4034500b81c80040080e43c0003c4007135119600300b01c0814182d040000518500741c61001103542044c021501170880079100400c500380c2c01c3c2042420185606007030251960b10303802001055a44 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 208490737 1250 208489487 208489493
    0x1120b0a0e090c0312130819060507091d1006030e0715020f1006150305010b16020f040e010207020f0301060305030304030507020414070c020424230907110606010e0105180301060b0d0207 82
    0x2d1b0165002c260b60307400035030032075031805c00350301915040d030b540200d000031151500e81c01182c01004940100d52194848005101c40f510441d0001c4c6c81b41d5000c240c0c4104541c2c84543c1102507505407500942a680800020721962424070f07013800340d400e02881240c5845201c0350300b00b440c3c143c502417040ca01551317500042c4141a8078201c08800881a402d0901c40d9501d0030601498610410701ca008041202002d91404c40d6105156090802c10003002803111400c1580480e000303601c00e11040b48076405c80100e50b01103040600860301200c0e0844091030031640c80e134609451690143e0412a8882d41d40c6042c0041844400c1d4441d0040350150703a030001d00c004c5403040c082129520891419030017041468030910329940d0764100c0540300ea04030806164a2000c200c24221420581e6655014240100700314006034132001e14000c00000c80c0850300e15403118070066825400d02901d441c0018020043d145a6142d00e0050810400000c4d000048003541e80074403c40d140c102d0360300049803a80000302c0c0d00078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 208491987 1250 208490737 208490767
    0x161a0c07110f0d0b070c1b0602070f030302070b031b030406020c012307140c0706020d09440f160603110d110f130501120b0a0e090c0312 60
    0x910030141c80c2140d01c00e110b08005003600c080840004d04a444200004441070721500f003006c0d50641c010708021f641a5106007007044a005402801c0c01445503140004806202121010481e909a0050002e0b642000180744a5600003454400004652103001640490050003184194080c020050322056031400840c2034139018502ca00007258003030070820b1074000a941d82500308045007015840c8401558140259000f1060103580f20302a1721740009045402040320030480e1419542c140600d82c0b81c0ba1182c0000c2a48103001c2c1510003c4465900171200c803080380c0c04035545143c800003003019038090b000c5c900162303505200301c507030440c0225003110480b25142d10003518640c10701b4400085122082182d40c0680d0900c1d0301d4198459002c2418000c2c800308894000b00e19440d00c5641d12150300141101c0c0480344681381c0010740114014202404922038180c40c81c00040012143c90329001340c21403080130142c0341801c81c1c0600160840346550070404040c1245440503402d45801c840c41c2a411 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 208493237 1250 208491987 208492013
    0x604140a033008091005070c0b0f01061803170706020c01090c06030e0a110402030c0912061e01120303090215040608010524030420090702010509010b06040b161a0c07 73
    0x10503c800795050008143c004180d502c034003400b00d64001100d0341c500f4000ca0ba0151300c03540103404100403209010f2034101e115902e9040c0d0303840c1c0d1a510106503211144415001e41840043e20880040103511052101e4400900c549802500007506001d07000454508482502400301c07500c4c0844d090400c96185c2500079141c03840c01d00d078054001d01d049511018108810744103820310590740040014441e44510055508001d8040d0401d40d0210320340302c22580c0c0700720a40e02e80c0070800341240d005842c12010101113050b00e001052b460314040d0142d60035809061140001c0713078070040e420115240102810040c00003031005503104c200952501d0140415114041c980d1614020350304031040c040c020140c01c4a40003940541c29801555017100a117102040c100341d110784c4003c0c2d80003032100d01e80d415049240245c20040007005803c1c1d460040081c58481d500c92140d00900038405007480400008441e45884d0255101c0c0c407414a40c0540b41e100741800712142d081c0e8042c0032030504240700300c0b072403614 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 208494487 1250 208493237 208493333
    0x30a1d070503030936150301270303061707030201140705030405060c0304092903070510200d030c02060906060901030b070c051c031a0604140a03 64
    0xc1607041c10042510382c8070b04141c640c014080b03501c0d00c242c002802000c03014a0000e01240e551450113012400ca0307000000d407121910f031000450b03a940c040c6030610544035101007025803006403045101081110281c1094180e050550300c2e000040d441c454509400b45004080b0041d001031815403002415080c452482082001010320240000910000c200c1d000c7d500201c0d0601c1c0c444200d18070041c0b542c4243d42040c0c856904021080c5c00005079400c0c601140b8030419041c0030409802c50616541e0105841801e512000130f1110034511402001c0341d41504402e1713003407900700c040070004262a05440c0070400c40080d58550050030469818008a81c0260b12032001d421103040040010b4188003043c000035000481748030124407160301410795540c01135413004c01c0d143d6031022000c080d00030700c1c90031a0701c0020904080c0310039504060001c0b03111060000070111401c003814194540c11606800b445103820001052001c40880d007800e20030500c0c07103950342c2d41000c044040f500b1820170303840f110240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 208495737 1250 208494487 208494493
    0x50d0f0609110120060601230d02030f090f0606011101020c0a050c1f0e060f121f0f060c110301061701060602011d0a0b071202041d070f02060f0705040b030a1d 70
    0x180714050303408503035250000000d20385404c2c240c43c1d5408c0c1000640c0e03114621000c41074000742d0740280400c3d03a0091031240524103010f04040d52080040e03500d48202d0300324900740303410803030020f6119809148401d554800102c001802c0c000780352950752a011141c1025255540b00407150381040c5404280150010244c1101c500d41c0031031020064104a00008028810f8101248508524148070140c454265510200c440c0a0034001e03608046c501c21040d0300c2c440da1314890310124000449901c62012a8410303500c513400052103464400c031807841a510300c2d9155403142e000040314018071101c0000304500700000248540b820b44040d0851701d40344064850b00041e04210504003c0104401c00059041600c00105e6500d1400c121000da10184500202d54404980441e00c0307100800000c4c120a40c00b514a91562100041035075182c0120719110010b074007100008202100100c9407507040315085c10007a0800d81c686174500d406810480f04203080c940e580c80d4400c00311104219000d04420701e2005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 208496987 1250 208495737 208495787
    0x21b01030605090106050a0c12080402010f080603071701020f210603190212120406030207020108220818030d0507020316030803010b0f040f0914010e0c0301050d0f06091101 76
    0xf264010005205d044180540400c038218050f0140010144203503001080703e5440c00c09910140140c1000d4034240e000800d2503000c01c407054060081c0d80d0050000900418103186001c41020000311000700115055409011041a02c4541005002c00c91303a601c09800f5100e041008003070035450300600709482648180c03a00012401444840084160192024a01071218213007482c50502880015422014005400104030b54554041c1401510036610003407603880e800740421410082c12204d4580410070a80440066000d0b030082401e20007a404460041c4400380000b41802031007100350010400c002020720440c40c00f44506141080240c0c6956412401d5071075980311400140241ea580344030000724107107020000010b403401010b85450f912440303038a07101b441020781071090154051035138031800841c9500d141e10560707200755110702c0d166085a10b41800c100a0002911081d90982e05800584000c030b03400b4010210080e01442c10306480800400005000c0d0140c40c2400e80c1080c8070240d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 208498237 1250 208496987 208496989
    0x6070806180f0412031407080106030c090e070c031101140105090121030f0201241403061911040302040e010e0c030f0604060b01050c0a060e100e0a15061203021b01030605 75
    0x2c040e40d0002d070051490440d0f6204c0728819001048150025a144507031003082200d9030740d20113407540c140c0d034681c5d4051107003072f00c19074080d80ca0075858000c041c40e0341c3d403280001e6981d42c410082110f0050280c5004181c07060804d03243c80c01c462100115072241403000c0018045410f11421450040404580645021019986082003580c800b44000c0c10005500051802d0510175000190400d1406600c03000302c03e620070a120f000c8800d44500d0030719040c0210240d0030b500c2c01244142c42616109200071070039508422040c0206856020080082424880400903031120300c156241c1180600c00021800c0304030b00000d1900c04d005a91612950000100c81000d981c0407d01d540c020750301c101c0c0441c0614100300140c1d0a130041c0720554465120741c1d4015001e12400b40c0120040d200c1c207805403440d440c0d00e014440c080e540e0030131200e02180c1c0070031004400035070f440d488502c3d1010031240002d41e150321601c0440054282500523070041e4001c1031001d420700c2d181c0e03461005203142406c0401105250070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 208499487 1250 208498237 208498261
    0x110a0806130c080106060c02120619021309020a020a03090503160e180a030512010807050a030b150a06020a020a0e0f01060f05070b0103060c08090a051209010905030607080618 77
    0x500007100c50048007580c0d410031840788800005032400c00000c0c00090f865400c0100031b0b8098842c10780c815040d4180d82c203285940442d2560080b8050744c0700009a4001c54443c2029601072880405c4846000f80002040f100600c0a884034410343ea0150244d440c03e810300600c00390440c0c00c0031384aa00900e524400e4008440c696004540d0f44444e004a19a10b001050340ca103100407a00e0400c60148401060816900500070074400a105100ba9002d90325583d0341ea40d01e910300d00415420451090090022841e085421503120007244282066002c400300843c0d040b001c01e0f4402c0002d640203401c464110f02e040040c0a01070550301c00103c2c0c052138508a00140f9040c1031040005221805012664840c8034004660009401c10303c0340d022560b4034680b040c020302c05100190001210f010100d60b03803403404100503100716049002008640b15040d4515402d41c00030222905000c0c000710006120386041c0b00c9c1030703c5030300f1980b100c450b0741c41c00e031040c04148889035840040346c0004904120002c4200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 208500737 1250 208499487 208499491
    0x140114060d060608030d0e100203061804060b0d061e02070c151403100f0b0a020a0201030e1f0605042403120c1b0915060806190f090603110a0806 64
    0x8940280c1408150b00300080180250381286905000029451520b00740d40d0f000b490040343e181045421001e01d1524044c03c90006032484c0b03038040301600311100108820000960098004c00001410710403803000a0300e03181c03400b50221140ca440c2c46c4401c0441480100c0310801110700c1d18254540302c0340396503180c44070000d80208409191b10403140c0b42e8651048500803140055112120b5480c20880303103104000116104603024402c0c4030308041103400318002980c03c08612074000385101000c950040d00548000002c91281c1d01c948001d0390039a04502c0c1c508500d0307443e0b80f4000a0301da802c200602082d2490007050512480e190041070b0900c0310291001821242c01121060610058400c11904641203a8000d0600f08951502ca0705102c404001e0b00121080080204188032480c07101603200301507489200c02150407500013800d03d00b01030645101454003055107204003a180c15189900e0380c000e4003c241d080382da8040600401c03504800c6c502100e0710031184080518075029100307680d0080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 208501987 1250 208500737 208500739
    0x403080c07180b09070e01120b01050c2b050a0207090c051303032606030a0b0a0b060304210302030c030a020c1002030a0c090b07021f0c0f0803010314011406 69
    0x400215829120030500000c8081e0101402182d00208007a482d50080d2207003100d894030130340c60440843e0309940110219040075034180c641d030890f511040000401041100c0009040c41000c00c000740c0040d00034408041c60f0080490203007032528050480c00405400301141c40184482001865800e07600000e1000458041c07643c086034aa030000700468460147c82c94450080202c0720b004400c0580088010078010300202c110916155082c2004280c41e900385c6032030380c041d000026143c01040004504641c442e006000204040c1074175008109240d108035802c0d81d00003050782d030742107031500780490740f07943e00b02c3c1031070b0650a40c140651281c1442c40f001e015418941d60004502c0d84d24803043c0504801803000f03040443d2130340350541c121400b0b0182c4402035800142044008120038000383c0981c1e65441d005065210444144062803800c142d080d800b050601c81e01911850000345000300e188031880c4603090154813035145240049200301c01038450011641070200013820b0080305504e6540c0868 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 208503237 1250 208501987 208502003
    0xa1d150c16080d05040506070807050a0509031603080901110f0c040504020d1205030109241a07050706030902210c0f12060a020702101e03020d02090907032403080403 73
    0x344000d0708150645841c0c000400c104008620301c030704584554413440c0b1490140050700c0403076a41400032186028211001c00c00b26000b44014441c07030380b040014100f540c2c000b800712054a22a1500302e03894600d141d00071160383c0800503c103001540d00c00c40b050b05168402d0010201644030f80d003102d844000070710710180100d540b00c00080a554034220302e66011a00079a0005902c01c000200400c3d0360300900603000003a04203d14005a41501040d8491141c00c41302c940001a0416450880180504078a07112140042c880078003c290140301260080555850000d40044030b4814448080d40304840060403600c405c2611098170000b00f1101282c0d8000c542c0c00307200c02d00350800507201c00410801006207100c2c0390208059200369034010004036000311018520f000503200100c0710480300004030781c091074414142010f014041e070094034402c04d403104054108035000000c9200984c08880324030000780c8070f800840340541505500c0416518070440841c03102e089d0b0b00e40e69014841c07407100501e004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 208504487 1250 208503237 208503247
    0x1020406030e03070f060b010e0d03030b0108090705031216080f0a0207090b030604110418061e020310120809041806050903030c0708070804050a1d0108070f0603020715050a1d150c 79
    0xc1c1c800d010349c580c01e210040030705503103c8003410020020010f002d101404121501c0205281e9200001e640040b00c9000f001030030400e502c0100c001d8035400504a5031a680360318042400000c0110700900120340c2c04500c420b0b1030740811100245002015072129491514000d9069150386001c10210b52060f0028000344c81940c141c004500101148504003022909114000003004015042242030204200e00a41000e000780d40c0b0308100e101c10f6840b829080b5a40c5410000c0e0511112160000340c013030315000d42000d400a0115003918100d00c0030140007484400d001080008034803031107801844840003542185840350400701107100701034000d0800400030800300c04000c0900308840150002401110f211641c84541c0ba604002c003420495004881d24008140010700050f024100ca150a030a5500380b464010160001c1d1300c00d5505940c8803924541c0a00011100d00807280103084041d00002c14200c2c131030348030030700c900c4c4241d400d01550841c48201c503c14420a4140d6000702011808565503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 208505737 1250 208504487 208504489
    0x501060512060f09330a170c04111207020a1e02060c010606030b13020c0613030c05010507020c030c040203040206090603060303040e090a020a0603090b1609051201020406030e03070f060b 82
    0x582c500d02c3e182d07600c0614041013010390f10b50044412840d1100c41540406410a142d400c3d000a528042d19504248021000c201000c07402d41c0882e2400f69401c251081120b03801d0206003030325004403803a940c0d007600260241080400410995010145102506000c100d42d55641c5014440e420540c0903111036030481001d555520040b1040a80000000c004c81c41e81c503100030b07000c0d00c08460240d102d25491480b40c0c0801c092402296030f084c070b003031010b0002c40e41c4283c84015410f03001482a42002000241400022403d07c2410b00401443c0c00900c0342d02d8441042601d49400d41d1861030041d8018810b10005841e60001e9501242086450503126552a80401d00e1030265a0000c05800c15150600c141c02c50003041a01180d4000d40c2c00c45020382e25804260180c034640c03000180340111180c0001c242c03080026117041003515a2170f08904240e95400020240303905413450800c265030001e006c03c1016010b1003103584920b80400a10704106184e1102c43c103e18950501408054481000e0701c15 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 208506987 1250 208505737 208505749
    0x6020f060c031f1403061b0d0f020702030307030806090601020102070803130f020315190204050906010c0204150803030603060709081b01090e0711060a06121407080a03021609050106051206 83
    0x50304080740e07514007141d070384200b00949a02132600c418003d01424011840794844c048400145120040350545085c55a0041000902c0440c5000c0c1d010340c2e0a1240d00b0043e9810700062601e1400703980c13050003904141007004000d940150015056a20400000000038030a6050301d50090740f814040f1108002c90030300740d0140c20000300095240c02481c800c18042c18400c130b480c602980c10b004402200d5200403040070228800c600980703501c199003800151541d885141c0c2c5003980f520241c00400c00040080d0369502180b080e4115128940010040000c281010018158041098503203400706900c0c1c00603c0d51103105202c2c214412840c65500c00040b079002d00c00da200200143c81d40d0300c040745813000000b09130407003408924181e40510300c040341424049000b92000e0b54181101ea42c120340e010303540e1a1040b450000300c01c81d0f0f40503c2400050413003041c0030381400390f4040d0b005461009103024031a90070481a41109042a1070400180700080c0d108003a21580c0c040410b180f40503465040010305 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 208508237 1250 208506987 208507021
    0x309080702100203040609080d050403060f0b030d020c1302090a06050d0e0d0c050d020d02060106030b040e030c0109140109150207060b1f09050f060d050c0c060403090e0106020f060c03 81
    0x2412121034160b6a41103980080200308440d0300e6070f00c90040c00d0311342e80c8064540640d003154800080d410301090000c106c2e2a4000d07000940003140004407403100c5400300e81071501c003c1842002d03030007110505400d418030408010f0800100c1d04110b2928a5101c001075000e00333540101010807201144c49050340441d64028016a15200e0403550582c2400100404036a01104202c849026026410380b00c503000060f24001020290007a1050b46c3c2003240480c000c00c9500c1c0000d60140d115001d00b84568014001007606002450020600c41614117101c501e0302041d400f500ea135070385400c00c03482c04036104842c0e039101340c851104e0141e565000da08112000e08070010b11285c0c8000c01070034034480c03281509250b95004c003842d140c98a240d6074840070466500c10070312001d038000314200010244203006511980e405280040040d040c1a690b0070100d00c2e0402c00c40c0c0860125070140b409000c2c00c4c2c0c203854500e00402c07562005010b01001141007584075403014000c10b00350302d0048081030a006031152504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 208509487 1250 208508237 208508239
    0xc05070b0a02030c011811060703090614040b070503040504060b0a0503040209040f0203010c1817100b01090812040f0e0c0d15122006091012020d02120a14090d0309080702 75
    0xb020403031184501a00e10101d449003151f40c0410400803c07201d00f0300c40705850581c1d806844450f0782e41e03d090402d0b11100fa9a2034a00c00d264801c10010039075a003d100030f4080c1600440055403a1400c3c241800700301c41140e0084c4923440414400b10580b950b102040707a034071170b5040d158003e0320340300c9180c1030f5810b0300c0c0020001c2d415400e10207401c3c2e000358010b0442c1c20b403a1070303640c042c01510382c0c40502203000604440c81a405070040070313100c503050225802402009030b0602d441c6108640d140b1040b400c2400640e280080090001000c00401003c21a81c00141c010301c21411a18100308401b07504c42c0c4220400c06100075212a490180c5541c10224107000f440e0100e41440d01c4401c2d803600c0400724030b11005822102c40380265200060074050306980c003010000d0004070359040c485905503100c845140b1008500c98003007184041074406030016005c840d224000c08411400d00c035201d02c0075102100341c04803e40404c5820442c074040300141000b1049064100001ca81a850509890310300c82c0200107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 208510737 1250 208509487 208509491
    0xa03032c0d0e0604061b08070812071103030c0d0b041d0c03100603030807052b0603050c010c2d021c0b0c0906041701020c1b0f010c05070b0a02030c01 66
    0x84060100072640d20001c0381165103500465105104000803400785005a10004850310600300c2e5a100c06a4000740d000d020310b08141c180220740d40d4100165101000e1980c0049001c0141315609070003440e41d42901420502031425854040000d165601542c007145003525120f14881002784c480341c2c4140101e00c4401005d03203002c01c0982465030b4800d14105120b0080c812008240c045422a100e90320903203506580b4180261200c03a821511600808014890044a42d014000070300091400079102d00c09110302007011859800d00320b040c0400c94203000d05024107840240001140461040e103054a00c850a01d4103800c1141c5040702808042d00c020b401c071401c04800f1194101c4403039080d07452442813498880380e0369042c0a00b020350148060050300600140300034018a50000a03c2c030170080040001401c01d00c03600c83c1c0c3e6207481c203030311982d00c00440c0022090301c950800b82070082c64400203080004100301e0315510303da036680c81d91203514038511010422a540034428400c031400761001c0310007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 208511987 1250 208510737 208510811
    0x70618180b04020c01090803100b090303070f03120510030c080c130c03140a0213050315070806180a09060b03010b0a0b07030201150311031b0108040314090a030303022a0a0303 77
    0x81901503202707075903c0850275004800018200b540404650f00c180014010b1401c016643c1d40719000c84240b580f0450520100c210031905800031880b0f0280b00d41d50300201818001d245003000e020410007900074503610341101c040c102540e02c60002d0f016146140780c40c005038005446400f28000e014074001d05400d134941c8000d0001030000764015082c540001914490b04654500c10141c2e43c43d20b83d00c49480c60140b51300000c00b0360380900100c580c0b100b8081c081c001d05601c1d1403a40400d03010700312026441290781c0c440d40c205200c0c50748203482c1c0406c1c058008100812500c0001048486284100350f000100018001e04140c402e400c83c800941e81440d0950840380c0341c2c60590009600740004600900c0340c5d806040c03144480209036030382740708180c4402041e61104d4508840e40e49101201400740389017006409280d0302c0e2000d420004501940d40181c0358100b450500760540c6407684800b501c0194540015000800032503003401c03055143c1000550400300ba186890150f0302c00385405003088080398 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 208513237 1250 208511987 208511993
    0x122e0608010f0e0f241215010e0c07020603100e040c0806150f0907090b0a02031b0c011e11100606021006030b0703020c150108070618180b04020c0109 66
    0xd50941a1202c040c0d070b031940c1c1c9403280701032144143c00711401807841d1135580100f03000708104446a98822815500c841640d294500410030000801d115101d03283e20010b944104032040c1c042040c094608400004024205802400b07013a00828402911a400001c0440c3d82e101c15411902c4c000c02c840082481d0904d01070402c9082c0400601c968640d50160000248140c1803041650700c40b60801800141ca6040349030601600700801449142401020140407510b49500c5000d02400c0d0f24a6009640e64100c04851050440d2451402686507104420761082603801c007000c02d030a4258004803e542401000d007c50b810192440c0038509030199040320710b018035050308648195241c94084440840890540d40221801ca10002d482d90710050040f440d4103110307070001c100300301d0f46c44201c0b401c1c0d45146401442c261002e900c103c009074003003c02045040c0e044400c00306407a184109082001b40703002d40b2204004417220300d05da0580d90300c070406005580caa6066034507503c5640002c02038010585 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 208514487 1250 208513237 208513247
    0x80910022506080106030e0a060b011115011d040b0408031b0d02032e0b030a02070204020d0204030b0121030f051204050601090e0a0c050d0c15021c05122e06 69
    0x20103544001800d0f80b002044103030081c0104183c41185100a1010701d0302c0e516148010640d8480d00c0e810496031180c00510030303108208045940c112000c43c1c00e00d552500000c0b8070b40b001c2c960710120440310304000f0040820946070320aa40079810540317165807503541e005201d80100304092031200101c0b0224142c40007c0710b59018611604440c08840e0741900f85003129a040f41903440e00d01903428000e00300f13010f03c001c140e0103103400c003811260250034240c01e0303400101070b600003201400b06240d01090410600c0110b4540500502c4250b140004030051050300b810340341005000641400a21801c02ca540c92040c01121900c2012420101071801c05241140d2184000e100c0e0a00140c1007400381c8058a0000c84c00c150300c26404503081da80d15151000f88a80810728a00a40780810b01450000c0e04500b18009408807005941c05005140303c4043d50580000f4408040403c01806000c0b40180c0c000404155810442190714103500d28000d818845000192908034030a2074640307107001a1381d64001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 208515737 1250 208514487 208514489
    0x30316020307090513020111030409020c0109020a0f030309090c09050907050a08090d23040918030207090203010b07060b0409080c0c1302030c0319020c0303040c05090609040809100225 81
    0x72402c0d00c28180d52003802400781e51041e030b000490071031010403c400541c01461405d41003d00c0c0010b49003055600c41c4048101c0e0801d480454959445124031811427508081c150b010b081c05c0310b0301d904130505541b80113003a40c1c1c0c02e0181c40021a6560030a6003004e000d0741e420030003040004d000e00b01c0b510b022600200160440a071180c089135514001c110461808501c00c64903050030ba845030564a80340b481c40004451102d02c2740342a56040001240c6070019020f00300220052004c803280d03000b110b1400a1900345580d00c40003000d441800103008021100302203d440c0fa4000380041881c14220002034010129050010506003001a012010000c01301c0e000310421400c45001c079101c148011a030381a1b10007150140c81c120010000990710b2800300c0042805400280401403c1c25000200b140c5147d02c26641503c03501c111020411035441d007041210792098081c0c1d20781d1030b00c2c01c20341d0f64002d69000d80030450344650240c4007010b030110b04c00c114022030140c41d007810081c01840410055241021 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 208516987 1250 208515737 208515739
    0x60e060d2705010c030c051804090b0108030c1603080f221707060c021c05190809150c06070f1110051f060801050f041d0d0e0d08250203031602 63
    0x2051004d4251034040d11400400321429240c844c0b4143c0090301c43c0c0d160400c442441d03a0300c40da4a20403070010568880c0c01601800c0b20100540da07801804c408035145c121105295206501c0c4030b07806200154011013562040d1542c85809501d80300d81207010003041d20949213120b2194108100024a0f094401e0304215240414003541c5d0310341d40342c4408031450340728041c010390000c00c00600d900e0030303c03a0031204103082c03070054040d42c025480c9441c442003801604042a40e00c0d5201060900359494a0070000780b030120b44864031460500400c0d4205e880340340040c2000103000100f81540403040c004c8822042d9001c40e8002d40790703900c00310104a070042005588000d07421758610040d030100801004c14005440d900d46412208ae840d2a041103103400040b649660030030340302c00340100e101b08402411400003c825001d803160005282c00107106e00340004d100c80c07040707400d503041a0124070308804032002d4601c02d074000145208000c04584242e514110001d41612002a001242003440c074500d03480a84 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 208518237 1250 208516987 208516991
    0x70807030b2e05010e0103090f0f020301060308070807030207050904030f1d1003090b010b0301081209010c0b0a0911030106141e120d0305010e0c030a09051510090f0501060e060d270501 81
    0x164400c011000c5840703440d00145095546274242022490f030144420070144010300104075240c03250346e9070040f0b41044008030744004001c162101015010f00040740940f40541c3c10051614060310014500010311541d8000d000908503288450b80c07500b07414121510010340507503855a8030f06001001008005410356802c1072260001c602d00c0340600891b41215030610041640b85c0361004180c4413070307000f98038540c14030226098420001d4401054107109070400c0d500011480303040e003002090580010140c0f4481d91400360140001c02001c410351030303646001e03034031205400e80e000100d1020b5240b6518943d40203a203040894a04200090820040b80250341c052240c0d982c0c46c0c80d10350404409440c0b0703400804003800040c1191070305600031084e40d40a10111215156400c880b074030041425101001005100076040c045801c0f04e0050080074040d03d001000f2541c54040c00078520782c032139030b903885c03003264002240300c20500f040d00300e0341da90012402500d4154550004040f0680002d00007121254 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 208519487 1250 208518237 208518257
    0x9021504032003030405060a09051c0b060429060d15060f02010c080601030b040209190915030506010e040510050708070f05030609180a05030d09050f070807030b2e0501 74
    0x1070345403203079102c041d00041c0040d07040c0350501040007400e4000702403400c1000401d00d800100765807410100220041c0c0d0500d2140701c100c00741040c00a6500c0185428004c3d42000c0c40141e01c2501801c1d80c9a0050040301d00d403280701090303000030304a441892241020182813000c0d000300010082e440d81d00f107441c240c94103a412900302905900380d4018080d88400f01d680480001c1c2030b5406074110090f00b61000708014070741211540050540100e8085003020000c1c109400d2040c0c0d0200d12484c0036406400805205071441c40d5500c555038101405410340e03494a24010030100001041500c2254203034a606012a01d403100d0300030405002222200300049509162000740c500940840340103080c042d055001030360301c421030700d8641c41400b07480c402c00d4454200c4407030205005002a0200c81d4040c0c0000c0751880c02410701038941918601d500c8080e42240b24100b02da4040000e44900b20380e404203603420302d507944c01800882c0d03005030210f02d500f442450301e07540320400001010009691090321208a03079 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 208520737 1250 208519487 208519523
    0x507080103080403110d150e0d1701090209010323160c05101116030e040b04020405030d0309050709060b030603011d030a05070204090c1d07020d170a0902150403 71
    0x95428800905072000c10001400401d050308411500404c010f4142805400140e8a07060440110907203810550313900c1c014100030384806c1c000803c085400b4035089521141d95441440050710600c280e0a4481c2d0000d4890f41c0d80e4001d800c54422102c1c1d48049a030032201c4c0032411628101c007100e41d580c0103d0303c0e22000082c58081e02200b039040e50040004c00103138a40c2d044d00310046c44459100c6103d188213003d00084801c8556a03924481d11a41d110f1200032440c0c000d00c003e540311a030b8080d02c91801400700b407160391000102003058403450300c0d011030424003d0800c03071f040c92804e800c038900c02824101d0100c2c40c89109001180180c0c070640081090680c1221141e50203103070f07500e014030380d80c0007003007128040d61146001d0000a40003c00000b000c10350341c2d5424180c0c000c140d10040728210013564911051036018a45076000c0c1c1c490000d8920340075076200043c41440230301c00e007850790035000011485204041d802121550b0380a001800341e42a86920030003503821912040311420403013034150110b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 208521987 1250 208520737 208520747
    0x903070303140f040b090f030406020705090901110703050d0e03031302010806030c30151f08151302100e0f1507060c02190305070605010b03151c06140603010507 71
    0x4644030540e603c48040d281d5950f0501d08a6018081401038480c0740f0352940c020300184010002003a59400a090311840e01e4140701201ea8014945036061f450b00c140c502210007890100c845060381803a1040e5180c030304950810040001c0125039110b0302c00481000445180d94411602240c002d8880d00f4466459004042d51035001c109103541000c54040f800301809a401c85210042d03414010140284100c84c034080d1a050b0071804900d4401030400900460f40107482d06440031144428207040014248007882d036650464111103610502902d00041201d851215484c0c21158000d1000601d0b0018400040055400d0300e811440380100c01c800f0480384c5403e034008118448441100303402c00030f076600e480c0020004203007500c0641c002d0213100908034150035958585c903031094448585130758a0b4200315046940c141c0201c1c00d018020400c0c8045158030380c030303421500c100c00c9540e010084600151039250f4060080d000348a1414580d0556420901180d4244286800e9008211135620318508a0b0303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 208523237 1250 208521987 208521991
    0x7211e0203060a05060f070f060903110f030f160204020307090603060b070b0411030c0904260309100c0e1011010e150415060302060d0c0305010e0912090a0509090307030314 76
    0x3070f01c02c041e00020043c0342010300151101c500c0781d1503035905240f4280c40380c0c1d038400b00742c0c1c5049038410380d105603400030185c1040400c080c0d5071000300102240e0304071101d015543e1003650203681c00e0850120740c200310308a02d50320300307141d09501500c00c0d5101c0c2007224000c0c0852204ac080d0710013203070030110086802000070013682e01c0c558101c02818043d80f0b554a40180c040c410030206d81e0580508219200aa1070345500c081c01180303d8003482400142d148254001000800802c210981b010018003100b6000000c480040300e0b05814001501d44241c14140d40c5020781c40e05417500a2035100f030206880d6008140600711580400007880f40c00b4841184641b81c5041c1103404400e0070588c00424007085011080d01142030a125000034466206d0700010701035005008191900c03605c403ea00c801c4544e02d805114014000d808c0c3c482d1480c14981e00c05501c0701442e0809540c0c010011420754455503506091a000f07080162048078141422241192250310104058002c17906181d0300c1482004403120480c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 208524487 1250 208523237 208523239
    0x206090d021009111804050d030c2007030606080a050c0d02010507080c07180902011704050709110d020703020102090a0e150f0301021c0e0111090a0b0307211e020306 73
    0x254030409000b000248604041a42c0c44140320000030702d682ca440a1404001c01c05200394192031a26251092400f01d01400c1c210400d4205050303211a1500803030104030407900c51000d4482903003040307403ca00c0d100481e840509050305110380000c000601090300c1035181d001e40e054030030074803140c002e22140000e403841c02800100208820030106419030003900e400101282940d481c580d0b01c02c0703035610059917424400305172961101c00713000310760300111003040389608001c04040c00d24058940a885502500c1804c4480340c41d4008801040f442a08a50721901011821034444035103041c024001c1d040b0210f001c1c024140ca09000c506504c24800b528070030040c0401626490f04084140803114a118480a170590340a0000c0f1409045427500034084900e0000700281030b0403c49001070a4414844581000480802c071080d0b0703d03207503006024262080440300543e643c4691008803032561544c0181d10a469815401145110040d080002c4640003200b02048241c0152641812440191042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 208525737 1250 208524487 208524493
    0x304050d030e03040909030e01030f0c0c030806030106120507030c0b0c03030a0209040608010c0804201509010908060406150b09100f1b1a1302130b031002040311010206090d02 77
    0x503022403003904810410303041803040d80d003400d41d20190203040e5985031800700c011442140314440196414800e1800d11818a00107000030000c0440290001c0031a10010b000c01030140001844e0345c0342500b080340241090030a05c500c0c0062403c007a9103400141c04100c0382015081d07000204081d0700c40035542000101d40103186180c030b41c04951002544540d0100b43c000392075580c001841c040a2007410b0003180f054483c11142d10305407520b5500700103039030840c0800d244550403601d5962038012001d81c80800c51414181c0d03c600300c000503100c009250b03004180394401d62003001b00300010794004003152103c110a201e44036880e46140042c1e4051040382a030410700300e04108000d00e101c1c402c2048001c41c24113100c00c4030348007450380c104008410401070711500a03426002440752039404416600c80c5c080c050751b2000c9c0c04264001080000105810402d141d103510320151581e40512101c0401c1d4540c110840d03689a903440d04e550303032600c000c8145001d4055074000403601000800d41c4207401e4415800703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 208526987 1250 208525737 208525753
    0x61b0903060f090a140d0e030d020304140d02060a022a010807050d0b060a0e0f0405010e040b040c08011505040b01020a0b190902040f1b031107172a070b030405 70
    0x180282c06002050f80500e0701c100360100011940801900403034024401c040e103020190ba5901070480d2101001140c001c0c0e0262150803600340c0c3c04000e407001c0c0d40c1480b410a03c100d50315000140413140000010703500500c001410452a6000183c401c4c42d000d2403c40300088800c100e01c11040c3c80382c08440940401d8402c1c0000b00c0f050f00c0b480041604200f083d00000e1000c10500100340740340c102426840c04505000c0c00d08805143c10f40d0491840d540459082c4010b41c10109482065400584000c10012812002c1010021140304090151806200030060640040d1144801e0000c49c800e6602941c80c00c0c005628652020403104065600900c006825890b540c41e0014003420400f05040204d540f0400c0800694907406002d10a103910790340841c44a55a0012030740030107080c1603401c10715141c4605c105054070003100360341219402c00980c0503241c100c5010500707280b103441d09d5690040d15084080a016940c8000b485040315211300302e0f00001d0300c1b040c00034418030041d01c0c060305079071107005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 208528237 1250 208526987 208527001
    0x11070206042c041208130606080f16081e030c01050403120e0a050a0821010803031b04080d030b04110d1506031e0b0111060403110c01030603080d0b060c03040305061b090306 76
    0x3d0b17a90024082c20480c00c002d0110b0b2501400c0f80e40319000012030750480c1b000a104030500304000100d0f00310441d0108241031400820030342e1821040c081c2e00300c5403041c00501004200910507030312254000f4000b0b00c0a460a807400030150b880030000360752010f1a01000e1106120009555003000e9400340c000c1c1140c84d6140c40b841c856401005070700c01c9191590b07000d514070401c2203003024001c0880701e000b0341d101d00780442500940032504a01000b5040700307100401204d07c000881410201e028100007602c07044010218020340004450813418441c001400303101c854507030780034015941402d4843c01c42c0b00e4580404078103840020103107040e5039561035566403140d405a8424191002c0504002c20300d02900c08600b424003104481c26004248942d120705004441407080584800c0d00746020883d07141180e441945030302603441841105942c0d104002c00b15100e42048030f14a03428003042300d80303840c4c1e82e12b020f0760fa542048a40d0080c0c2a400052440381031009426103100c5d00c80100a401c5943e41e43e1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 208529487 1250 208528237 208528247
    0x15060f040504051c2a0b0109020703020717160b030105060d05102409050d0309032a1404060504090203070302090c1c2703090911070206042c0412 64
    0xd001995039008180e40494140c0480e2078013046143e05849880c18010744c0701d03504100601e00011524028000c009a038000786248040605440085900603110003050504a14000c0660842c42160a100f1070200d40c0c1c5500040d0b0402100000c0700b0082d089031100740c4808030b800284a141d0704444140301203150204c050300220740c040c034081c401d42d80c0d9950350040042c189900100500c2070104414540034503692001d03041e800340509480040c280c24043d50300420031416484043d01219181c40c1c4190b0b000403141c09040040200000042040d03210113180c070344540540d902c0c501c110b02d4004001420706080c05404c46154008002e8002c403440d540900000d00d4004201e448811070801c0003144840344085641488003070080c000411a808540520044c030400c01d0080d401c0354070300344400009500c403841d0402e446c1440000b00e000e031003020759410300703000d60040298481c0c03001c078012610030314001c0f0a150542c07150112006004c810081e88414800698014115031302040e14140d40e24020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 208530737 1250 208529487 208529491
    0x2073e1e040e0114010f06020c0d0b091905030309070816030f02060f0d0501030309081b011803060218270403050a090305060a140631090c080604030215060f0405 71
    0x19101190b02c1035038240e030500311030f03082083c5004008070100600c00c1040f14903801c80901401e000409104044000290703e440c08820003c03e15035003100010b0030484c0600c40b800886c0380004038024181c0041c6030042d160b8004a0f0f0044480c40750b03050020b1140b60000f1030407005940200c400b550507046896041404004200c107a070010420410880400c03042030040050001881c0d0026095045142c02040c45d00c85900140311540800011131501c0d00342c5449048501d02420821101c1780d500040300c0d800507980c0d10203001588007082109410886190f003080c503031f00840e142c58a660071620609558110300d041003009000200004000070b016034001c1020700030504080e0f8030f880d5603565483c54002c045030b07501c80c403c0d2203140d6407a510310400c0c0010703009842111842005040d0b40f150740c005140425441c03150b805441407008030000c0e10f6025900b000d41041e40108215201c1cac04070359170343c0700135601100184140040c111511144072540341c017554004200c101004441000c101c050000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 208531987 1250 208530737 208530739
    0xc0d020607081303030504030b06040903170711030c06010305060c0304210504050a1203020c121b0d0b010303020a03080603070e07050c070902160309090b2202073e1e 73
    0x4000b0910b40403c9403080000079440385d92520341c1c0700c3c10343c6060044d1107006002075000710700340480540029003050000318000307404c144940c0e2503a2000d030b040b2f8408000040c44886800000346816941c4c40104003076060f240114100e446503255009071404902c02120050009070701d840d0020211181d04209501040f954038200381001d48500c0001c003a8420343d4410541c0391440144d6408058050000a000090440e850394442d01450030094480c401361060000030f8500f00c150b118166515002c04560540051a00d00d240d030f1203281c0a503688400100540c003241e000c800023425490000b45290a0303860048010701103450310541a9801d0700000c4030340f81c9900541401084881080c400351002402088030003d2950301820041c2c1645080e4001c0000f090400c880c0c1030ba1a11016051400c4121249019090004502c0148003c0c05080d90040c00c0c070f401222200319030f00281440c410303014225108111074204800c2080e598071481d179001e5030814880001104003a495005040381420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 208533237 1250 208531987 208532003
    0x12060b030316081b0618010c02070503030a03202b051006030b1206040804090609060b040b0304080c15010603050a0207030e130e060a0609060803031b0f0c0307050d0806030c0d020607 80
    0x103d0708205041201c00c032103611b410001034411070b400c020309009400701071003240090409031b070400010036102d02c603080c40b180a16484071142c008880201101e0090109000c1185d601c8200348600080040d4541c0341c610410002c201510301e41c91850b20035540140403501420b20542d21301340c0154081c1210794401980f0900305050031590f043e051000d60f114070b20812809035100c3c1418420b8040395890b4001040261070030106104050b0308808039000c2c1c64040c118551280c1d204d00c0c1c244503502c50f0745a0321009018040f0200d4500d100031883d1410b03904543c405010655a03441c1e0380f000c900030440090005179102e003c0750600d00b030865510314070b0300040e030020640c030358501c2090385016025556084180da0310442006104413038403070302016001940c007440c514200146c1c8941d1214900032030b000903441c0020380d03490b890080f00c1100c2a000342e60041d644c80382c0305400c15903103599520301c104001c144000c0016460703117008240105d88050040030343d0400a000d4080c0180d54000d1281151241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 208534487 1250 208533237 208533277
    0x1a0c0301121a0907080601140303070803061906051312110904060f020408060405070501300902090903090a05060c070611070503060906070f230705070f12060b03031608 74
    0x1182c0c0d41c103108220a100404143d460701d46031600d07280050707000e50f50304240c1c43c4000c0a10780d404011101d10a8003c1129511303a110080001d40a00c03d541c0c07000fa04c02200e81e400500c00e1341003805070441070500307401c01142c2592810a0740402c10002c100030281120154640954500403002e203030080e004800004540750350f80c243c64200e074440c1c1c00041d01d5502c880c04101c01c02c00c0c10090f00c40502800e18001144141102c00c0d503040c52150030512080c90100c16107a992001c15901001003540c0050405102e800c2041d074580e10790703000307c0c4040d00580c816180810030703051400c00c4a000541c88030041046a16040c82200d90880150304c2c14418080c40074001601d6808001c0c650252501c040030700800c2c100000702409100c4c22082290070b000c0b00900c020080d108a20740e404444448004055441c159460a9411b05c181034108a000e00009580410401e141580e484002445442e0030054403225608044d900c0c044e0140d44854201c82440841c00075003494041e01c098011401010400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 208535737 1250 208534487 208534523
    0xc0c06020a0e15070209090c0f0d030e0301090804050102241909020d030e18040f0b04150e0106060e06040e070c0c091b030b040c0e011412131a0c030112 67
    0x200020f0340800318200010954000f5071410690a580000700d190080210340411804604102d242d196070b28070a01300124031100b80b500508a03540c8d28030004000700810529840c107001550064003407540144a640051424508107602641c01200c0803001c4001c0f81ced662603241c4005003200b0344902100e60311414090016101c900b10140c1d81071080d2038070340075440001c040c8011b21070380b004c9010141c2011000e100105a075110040007058204031140d903d5a15820304d04c000f0003c0b540030048003454120707038540110041d801403003511599560540c40022100421109010f0340c01203079503c00f981c40c00f250403d030180c5e102d903107e02d01c20017241c0c1103255200302401c00c50b002d1001c0d071051300407604078141c9010380c54400d000500000b00c4081081c40386101c0000c00314074454800c0381c18007415244600d103601c0d040084c1d0312070141011010140d443c00c0b014a440c0301194110031121085418508444c2e1221803e0b86803080d44c00e007403400d007560310f01100382c3d19200d01a181500c00d200b401c0501100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 208536987 1250 208535737 208535749
    0xc022407090503011a09071704020f010c0b0f0403020d090e061009170304050f0603011401030f0609061811030f0c13030f032303060f06070c080303040f05010605040c0c06020a0e 78
    0x103150b503100d8280c402d25404c05c00303005d80c1400084c00e040c02c2251440030303040c41855110100781c100750103450100e09481c1400060703074011220b92019148414100070003500322081d40ba00c52040e8460703030030345241e90311402c0241e0380c84919000b42e140e016009000500b8030304000003141c0003202c0d1481c003601c043d5540c410300d04012a2007407040c81c01d508001001d12882c200618009030101d8255405451507160005015a09400703400040c10540c8079502211090040d030442c0c4080c00d903114082040555403d1208610000080c18280070340c03c00084004044c080000d80e48580a00ca0640c20315686000012200c0e80c0403941d048030b03400c0c00000100105040c0c2280c10003c0303219444903d544e004052050b420f1142c204610f00c5689000c100700312813911080803c3c1c15000c0300351a1a40c407007826260441d070941c2d0300d402085a0340b00c048100010301032500d00179045980154000c0190986070001d010655070608200c1000c158550703034a4000400396030041c842150a481e00030038940c00301c000254 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 208538237 1250 208536987 208537001
    0x20c0c19260f0a02060702040c12020a050405090f04050a0b070c0c0b09130506010203041e0503030a170f0402010509060d1407090602010b01020606152107050a030c02240709050301 79
    0x4500c40340003001c440031031041040b03242114680006107110105640042c0a03403048841c000d0003a512144d440c50b140d07004050203600c00500340804c1d510b40030100c02c0200b0703a070810703c1030b90700c5100394402080040d401c0c2203403103000c0c80d000350207881e26440517240c03401462409401042008002044000411103007080c45025059003031600350b4805800c020040703011a10200540074a1a00050190580e0008101c0e82110003861582e000c01e550f54840380120b0340964003554040c0000540d00c03201c030741d0011010f9440c03120b00100d1491521421265804c0201c2100e00902041c410070009030940b0345140078082c3c40e145184080f40341000c41e0100485101e0541c2e0350300208581d404140f00598081c0a8450650003e01c0181080e103002c0340016030407201e005188081020000c0c00e0943c00110011040b0580511121301c00541040e20004016034400780c44a40001c0c9060098130049201103203a03060600d000c10113684c1883c035103da40b031002e640504000700f400500b12000915450030b0080c0d0f9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 208539487 1250 208538237 208538279
    0x10603060504030e04150e0601030e010f02030a05100e0105060d0b040e0c120102090f0402070203010e031804050106091805180a08120601020c030307150b0a1413020c0c19 75
    0x8120740c1850b00e07003d00781c04610810030f84501d083c048000e01c80c6a07520448000c88003000321540558840800581c014600e4000f00720555017800d0507121583c9180e00218080d90300003100f005107555030400b5000841040c02a2510440300400421262800d035002e0610445492000030310f032416a80002d04440000c441d00348185c20803c2041301c180351200851558400c003400943c90950b080d40024a40d444c0c07a00c2d100e02c82d66000c56014203640707096010824a61420301140d80c2c0380264840039032004050140d49114905140000c01c800f817041d84540116244441b1200c02402098580d03401307460000e04080840e105400e0100b00301c0004c02c198041c80d03001e980b04a5884c21250500303006800028241815076110081c01002a01c0000c00c0390200740c0c0081c1c460742081e00b1512200f0141031101c12140d84107005010106540f034211800e8446070300d0449412100c40c40503074480040c0d004a140c024104d03005411b00d0001810700c5104043c80c00303506412442c140c0d13103a141011032104564006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 208540737 1250 208539487 208539491
    0x3060914090d02070819080c030c070f12020f011d040501150201051308030115090509070e0102010f050f0c0705010b03030705010b010f021c030b01030b0a082409060402040b01050c01060306 83
    0x1c031400d030005200400c4a41c4041c40540b41140c1010003150b551810078610320750360100c034160034042c01141c0301696490240308007900c2d914041d101c43e20350b850649010f107003010300601400261010140b00601c40a42e4086c11110038201503000549000b1440104184070000c4088224002e645034131070079000c0d000710300c94428680c104100007400c64200800c24503810003440b0300301c004560107906482c110381400720441e0608941460854a046241d80419044082042480352041c1c100d117200e01002400e9008201c0881c29000003c00c1c0c600a03601c8410500c020800308260400510080160a01400c0007185096030b201c08240b03903501c89401641c0c165500d601c070452a41e4010941e0f41e202c0c4861004004410045600030844000700d0518820b155450030605001d901a1b00000e002c030301d004055201807a0b440395100d0315003100c4580e901c1e11180030300c1c0c902d451902e817400c440c0c0076101f8030f402400c0e40c0d680d5a00307000041520500341414000b05001e10074400209010b00405076100e0000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 208541987 1250 208540737 208540741
    0x21f150603060f0909050604080f04030501060b04241d030c06070c050306100308120601031d011d030a0905060a1404090b010221180a1e08070b04061403040303060914 73
    0xa4a210303500c075900714505150170810608046040002c4c00f40e04180c000b03240c3c0e0758070354404410701c01c1c6116541c0000c00b19401c0460000b800c00b02040130380101c4030032a2000818541c84810f501810041c2218a03010402c0d9003c20380f0301d003100c06040c010280303004e421a110349048100003a156008100c0031a51003105070002d0003242800c0c0b20403500150368543c0300c000c060940c1d452440a00405180c0070a850720b00c1c000981c0c0ea0b10a8001c16072094600040c660541035950415019082e44406c01050003811603500ca18848000704071051100d407650750a150504180030020380d0340c8058031071010001b09141c500ca0b8a01440020002001000000a1080c0c1c0c81000a4141140d416400541c101c400800e60400003200e0121175519000c2d4010300303504c802032400603c400803903400103d60f90003101c81c81e00d062125100c006040e60034241c2200c1c41d4542e214011400352245000340320001d440c003103d11054001f50409550024441d003400f040c10740d05c2e180e40c4400c540c84c2c45441200c215501007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 208543237 1250 208541987 208541999
    0x5091501200f010c0e090a05091005160206010503160501110f03030c0406090f030b010504050a1103090d1d0607140a05150402040f1a010e01020a1505010e16021f15060306 75
    0xc034400300d03800d05040c04001c621702c041c00103948940c01484140080d0700d41e030000f550a40b05201d9400e070b004c20240c00304042c0c01e000102c0013010b100c00300c4442c050301c244800821145000036084481c01d60f041100312480742008011a14000c030005403038924401c0a0583d100c0c41001d0014503c9009240c19103902c4900e0030400906190a96101d42850140d0910a1020451000000741074600644002c60162913120014000f048469018030052001200340103000f900440e1004104050359602e50710801e910144201d400c01400142d40d110208200110000e0000d441500004400384207036040c000e40303a21041d09010500c603200c0100c0341003404000c11458a8410b000c24040303480030801100341c0204403903c510f001241c0c1d250600400c1494021039a20070014158019849201c900000c0081d080d428043d200a0160010304100c080c00103428136010f010721000704905a00600c910507510001e01941403141c40c0e10b8403501d0702c8010006c0ca100780c0c144280000c10555a00041003442c004d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 208544487 1250 208543237 208543241
    0x15060102070609080c01030903050c01060f080c06030f07032c030319052a040f0b0d05010e04120e0a0801020a02150106090e0f0c090d08040905070905091501200f01 72
    0x10b08084248880454140480c00b400607040760440000c0c2000220110b0904058400d03000e00b8000248035130803c44003044d00402002d80401f02c07100b0070700711046a6000b008002643c00200d82e5220030707402550003e035001d8801e40094011072060340300d0003203030980c0c03144890025841d68412000c5074000000d0050f013801044d10340b504004202001c00c454149034410300d026800d09940c2070348114100c00700fa004d1424601c210380050034031420187d01d50b5901e035030711802500001c2d84030201c0f900d007100020300b10081c0762005110f02d61211007017000d0044000191640c012070307103a02b038012590020119000c03900744000c00341500c190300144182035175041c01d8068200160001000c200c1c00542c10803000c0d1010002c0354002040751800812aa00c450f805052409034080781a80301e0400c441e1030061041c040010015124020320a0016030703565101910f2200d0700c0d100f02500200854002440d224096455040f044014074201480c1030240f803084070350808000c4180300300e42001002112a02c424 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 208545737 1250 208544487 208544489
    0x26030f060a03050c090c13120b09030a050f0f0715020c07140a0608090c10090305010b0415060c060b040213050112060b0301060f090305030a0c031b05060105040906020405031506010207 81
    0x126500601d8a00715a01c0903190f10070b004846000303100071008107a48510f004251075110000020742c4690b20b039528180880d00040310700a42d5103044420202c0c203d01000300480d20300b10443e4075241c2c40e018101c55071404590000c01c21442c010020301c40301d8001403885c2c012195114003540301503202c4009092144c00d10041340e1000d003107001070300300c0c00717120780c0780e007610082110f40034104410960342c0e81440c0c908095070440800d0b84240c0c040b1010925540245600d810f42e8080d0000f04982942c0350140422107600603502c400e01c100901c0d0800005100d8800c0e6440e09200f0403000c01e421280d240402d080c2d03000400c6030301000750110414044c55903c001c041040c4200b0301000d0101c2403401c000e050f92032106005003001c004201d038508a980d80a9001400103584c000201c980c3c41a02013801003c11080c4002240054403140b2107032400c032850300290002035084009449030343d180c00c00300f000800600504640d000d400703100c00a80c5540901249000c14039001d0115401d00c1c0c490002402c107161 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 208546987 1250 208545737 208545739
    0x7090605090a0b01020d0c021c121706031e01090f060506181003020907170405010609111801120e060f01031110170403121a01031b08040f26030f06 65
    0x103480f00b240610382c0e00140004169041d070a09044a4000b800440c080030400502010000c0010890768104907282040480c203200941e26522100c1030f01c13510005111096498590690020492680d0b00d41d007001c003490168014800003910181e0313035480241407000c03e00d090b02c0c001d54913800c010160404050a903401c9501c900c00d404680342003001c10180003100d0001a0140b08407000042440d402030088480303801003080c0c1507810b407900345400350280115000b41070781030341013903d0307103005805410540e21503814401904440d541117000440b91080480344100c1540e0321800101c20000042c8070031402100002e04003803c541c110304005040410301d8265034010711081003030000780303548a03481c028900d0103444080d1440c5c449003801c81e00f071741d49184808072141c902000c6100455080c681c04007440400c0e2014003441045044525404640e1055080400c401cac0b000100021100c2c008504000d00c28000c045111070038040c001108111803480010119000081c0080c0c1403c040d081640460 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 208548237 1250 208546987 208546991
    0x3100b10170123060c1605090405030a030e101505150702060304030e211c020601151b0b09030706050606130608040309030210050d0609060b041703040807090605090a 73
    0x40016007000c00c24014400e0780d0040b402c48240301c000a015464044200034020503064654400d01d81e141c3d201c100c000e26150945044410000e09800c00c9a41c0c140700b00c1e00507007e181044621076041e009061288840c03c018011044450382c02100c1e44140e1105505428810030b40c98105010f100d400030006c920821680e0b424000c80c001a524007049a50003581403030011070802d1440007140303022441180c00f5040e8003000901784900540082c840b4940f42c0c01a68188804102c400181d80b00d20007801804101100e00004024560044417085401500c1c0314440c0a80701440c1c0700e159540c8020380b07010721a60400104d480a0001030700070030b0b0308004200c80480ca046e00640704440c0704401d038852401071140c45800a0141070003164a0001590060803a403010804104001c0940c1d00900300c000c45189003200119120301c0070b00c246402d41c0c080c68401841d0508280c004103808400105040c05803000f00404941000103010010080c903407202c010411074204410441015030003403810503070074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 208549487 1250 208548237 208548257
    0x150b0307180e28021c0b01091a09040c090b060706050925140918010e070810061203050c030c030a02030d0c1b08030603030c030705102703180503100b10 67
    0x200d440b541d039140d0382d411101d1030342d9080018a42c40324802010806071012111b5000091080d800341c101528118044016010030303071000080025004041e200503002e0004d910b024010414281d00c180440440107080c41d041440c07607914402038030310880e254426074129417420282120503820020120442d540c00408407402c20070189114004aa82d49100c6c0d28840701140c0750032030040348000c0480d02031000340400c0c420540e9141c3d07559010312a05009100304c2e2481b400300d038180c2c8103030004c0e1241c445d0144056291600c0854180d04010351591981c001001000d0b4014400c000400007101c20740c019540303501039035021204071400151644144042d0780111001c0c44c0606281460040c1e00088103901ea403201c0002c40d2442c0503204500041b4803000806005203e0700103140b03080300803a0102400346052031400c1628a288898441d507090901084a03400a0302034407501c82c2c103003500e252030754040f0360310b50002e498075114082280c18903a60b4042c0a9013030510b50701e003295603201810110400c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 208550737 1250 208549487 208549543
    0xc030405030a030b0f04020a020114070905180a110409090b010b072103020f040609030605151c020102100903080603010621020d02030f03030103080301090b0409150b0307180e 77
    0x80c030410211004050380ca91004c546592441ca82004002d800b5000b1900c650380100040e0081200307441015030707154441d001441c841d108003034100540b4000f5007030000106004041d200700d070760301801c00c020f21a02d903d0140a141401c00c0540020124600d01041d42c807443d06240302c403160103811210504908100f000085803900c040d410fa15407a2404441c21000030946c00c5000b4041c00c41100f15800c80000c0016419520920320000e80b4003e0f14204019200e0007055005c06120408080d00700078214081405030341010007000c43d01703006006640d902c0ea5800510011118545022004200c0f54401e01085080922501c405010f40b400347c890f10512002203817441c80c0d02d62400a01c11022401c240f02192000c5c032400307009031010307070440e84c880d40c503442c100d40580c009000d4900362628080c3d0301d060701e20f003d0040450313103a0001c07035400c0c0c0d2040500c410300c0640081003030035815214002d00000d496084c03d81070441410028000201072414114040c01c0a0b000c41c1d54060400c1482007403000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 208551987 1250 208550737 208550743
    0x90909031e0f03071805030607050a020106050f010c0807080903010603061b020705090612030f03010e091c05090d0204140a0c0e0f0f0d0c0e012c041a15090c0409050c030405 76
    0x41d00170f0034070b001081402c1d0320849071422070381c100a80500602090180b0240c110b005010145401d0300240010364452040c081d4061aa144243c0042c2e902030418000ca560b0000a1840c980100d900d00c0c9803501c00c40129081d1000761740100d030500d5076584414584114250301e41041151417000d011020700e0b02000a5070300c400500021310410707612050040002c82042180e142c00400003000341c0303039a074410048140040413110746665008451500c0b060b692022025000c000b07058603001d05048091080c400c5800901100705d0b0040c3c0d82e15407002d2a02154440c40b4820f05802002107090204003000514403407441041070b00a40c440092180c540e03603044440c1a00300c8040d2580481c40c0344d281000c11802045034040e21503484d0120000c84e50400c00782004075031034249840011105902200c0d480e150500310b40141541d0504202c1c0804002d9031002e25411180d815910421005400c00281003404142c4045950f240c3c002000c0044860500a10358400d0000d800c5c20304503d065200c03a51 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 208553237 1250 208551987 208551991
    0x11161a090a0308090102190c050102070f0b0f07020d0f150f09020604030b0c04170c0307170303041104020d0c03021207260403090e01180501090b012003090909031e0f03 74
    0x80074840125004684d644204001943c042c0d00840129403840c0604203aa03101409014960050140300008100d84000196a1040780d81d0154181d1400c500e00080c032205400010b0b00300d9020508004000100c2c1c801d46600307038058040c1c1d028142071002400b1907411030364030701c0c1421201c80c1045c101201503590380d400d48007107d03000b9203913200390390b01d504030554070f03100d107421841c0e40f0044010a6283c0caa00080d500348174000590490f1210f079207800080107100561544035566510810001d000240000d0120403a002c01600150403c9010031290065441035803080d8002030b4081017402d44140540340d070507005801800c0400001014000c2a5a000d22648100240c00c9a01d00400c0415200b10030036070007051941064403039941c4800c0c1c3e00183c0c94002e16407294140c207100c00403644100c0c0e03109003105003005844600c5016611020581d24104c810404401d0340001e0041500c0d03620b0310503145214078444405141d4035101054107503020713014182c40b1041c9081c1480708114105195044a03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 208554487 1250 208553237 208553243
    0x40501030504140303090a030f05180f0a0902040915050a12030503040807080a0309120f1b060e030a1107080304050a0302121e01060501030b010206240111161a090a03 73
    0x2291650b954203180c12084100c0581c005207100c0002085001040401d40160f001d00c01c0d51000c0d149075400c0c01c00c59444c0900201a2401d0542680d1200310b49003c800c03010a18501400b8400c00941c5c0d03408030406c81e0417a071f20070546203488101c07109540513840a044040d141c221000c44000d0f0400101c80315000c00c001c03005091000020108051041d07000c00c1d80e0000303a000c20140d59402c0c8180c0000c1c00340c280300c03e01302e441000d214003104e011030003010f1020404909541d0202001301001c0603842a0305141c10070f440309540e40c101d10251110070b0006000003051074440c44e11017100f2041040c07030224150300101c034580040c4010f00c540d50f40c0302651811a601140c090030172000170b00445040001d6205070801d81946001c200b030030000107401175000c80300c0980701002981410700c01680c41c1c3c1811100c035540414004034580000b2030400d030900c1c00c0241850114a580741c002101441d110210702014100ca07801c1404200040c0000340490806000d606298107003003881d00824031840e81c0c7c0c0002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 208555737 1250 208554487 208554491
    0x3090f0509151c060e010b01120b030c1c0212030304050609150a0c17070e151812070f030b1009020c1b1c081201050d081603050f0c0114090106060504050103 69
    0x1030702c81c1c1d200c3c224509207620382200d01003015610141c1c0490081c5400621540031660400300501e9207110b91041c201155005806414000c42d500d081008034400d500000c0e0514079000c5903880540c039441082d070401d500190085541e41840d0070b1962911200034040c1c91258010041c4802031802803007004c0d00800503603004900390080040580d40000c01e41c01c0382d5081010241008074040d408400d0250103801a5402c01d45406400c0d02c01030f29210354880d401c04401c50f407045048034109103007544214010030060300c80071600c41c541c00042551940c01035560a01e550207225505c600c114a04c4018268002c0441c80e02d2030016050b900c4034910481e40c10080007070700e014402619807864040007100708041881001080780340c80b181030b0300301400780310100e8a540000701d80c500384500081840c940000072107090000d4141da413490a40405000c030308204c000e01040c2c41e5254140e01030641c2c1403180001240f51030744005076031402c4100500189031070307040c8402040a1504001141c059880c20310380 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 208556987 1250 208555737 208555759
    0x8091501080a14120a030902150415050903100c020616091a13050310020d0f0c1b05010b090a06050102011b0f14160506010626010b0a02011803090f050915 68
    0x1055041c51904c003000309103403500040e1840443c4d85548142015482103480c0310808000c1d50702c40c0118025401212410704120b220301500a020701b014000d0000024116a00e45000e241940255040741e2080310260b4014001e03c50b068a02d403544241010301894200043e0345865040c844a4284102d91040384900003900c102d14a0010b6909000e0a00542222420300400980e640254040000c40c205d80c4d2803c80c2000061003103004030007200906545060b41803642c1c030b54030040c4140c2400111140e40d030359440c1005a0f11081d401c40d2042c0c6039030300c0002d2514a0080013900355004900c8100015100004070306240d500f204031031000701c1d1140b50038624056000104521403044450a0052100008190341003000004403281a102581d580111800c21b851680d10008c40711350340f81d01c00c4540c1c3c400511401c01c4010150121010390310000c1443c8011b03844240d0300a4200e1010f600040504105001600d60341c04d0321002084107491103131840c94036000c8a5115000786c0c040512401200c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 208558237 1250 208556987 208557023
    0x18070909050c09190e070e1807030b040c030209010603022a0a0c24080912090604120b010801050601050c0303040b06030a150501141509090c0c07030308091501080a 72
    0x4144101410b015210b0152401c1c1403400000f03001030b0644152203581009445500d40e1004180d0f1300032145205040c090369141c1d00c01c90b868445404a171201544604540000450300d0b0004441c0545c0c0941048038080d815401800000541600500145070041003075940d030102030004185d100064000c811214143c0280190030424400400382400b1080800030610450780c0c6001001c8085209010088103c0414169580c5908550780c41071500300c01a014548600a40100414070005005911306a2115508004501c100d00d054864006c40d10061140210134401c8503040751003400d180e4200f690300110b05560b8400140003d000d0141480840c089440410044940a511082030003000300b5030384104c0c0c0205024401c030094041c642072510070700d00346000178490802084c110b05150003842428082802c10280c101c61039400100701b0741c04100c90034070a2002841c404d40d5118914100001c2a40c0f8002080c0c40d2602409160001000200c0340000c4402041c0d91048041005203140a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 208559487 1250 208558237 208558243
    0x203150a0608010f0b041a1503041b080c090702030f070f0f050d020303041209060801030b1008030d0e150c09011d190302011101140601050708070507030f0b1807090905 74
    0xa4000c216941c284a80400794824070381000c004091700741d07800c02c1a003200c41c45040c1440e05080c003c9030800c074089005003242c100c5500965119024205070042601c4400b444449000698041503190b040300c1a010440d1078000fa038103030400300b58401141040090a2a41946d00c11540002c112500c43c218030020800100fa000b001550051f069408000c10070034040e41b00c0e4001c5404507540c481140c1c250000501a142c07a900380c606550710084507a0855480d1102c8000150000d11041c14503400001c1c040030400080240c402c442d080841c031a815801c800e850701c0101c401505040201d101000b21048840040c0c3d1419102443c0c4155015072000c038643c40ea404000c41180c00c80d4a403045040307441c10321102002140d1003a60f0b155038040d801d036486800c883c1c0c80702c9117081c884040800309501e98410006400068090341040d8a814559501c9070319103522a0b01c21211115000c41c04001e010307803003412543c8100d01c401d00c070b0582c200300180320b616150240076201c4c415948a20407004d0000070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 208560737 1250 208559487 208559489
    0x1209050f0703080c06010b0c0a020402032205030d0b0303310902131706040b01030b06011205010f0801050c1c1e021605100902030a330b0a09090203150a06 68
    0x20301512010740c0c0301c0c18188500e40c0046103488551080200010341c80040c1011500350743c0e189000b03042010a82d90822010351f1004c0c21008500d290304001102140020385030591481c8210021036403a50340d004034100f0344041e004024441d4005004004101a60382840f00c5503c0802079540c8020f0a02c2500ca00701040b20380148d070800b807011425804500000020000b5100e00202480404840b481402d80d201d8040301c0040c1030070f40b54801080010484070b8200c3e0040014100b550041500180d200101c2c2c0c0c0036400300340500d2a2704001c010443c003c0c030900780c020640c0c4100c03900c0c1140e0320310b071391030104c204090000101c1d990341d0140b0030080d9207a900302d84601240c1429507403200d0800b0000180301300c95134103960a00030ae20151140c95428030803403030941c3e4040c014140c42c0c121a160900703402c10111410966290500220345030b61b54040c880c0b00e11031130940c40002c0140450042c441000a16006400b02030729100200001d660002980c420b40c0c02c44001c4105d075561260f039000064005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 208561987 1250 208560737 208560763
    0x304170304120e040515150904020a02060a0c0207051e040f182a06030b060910180501140f0d06080303010f03061b09060507141204091b120905 63
    0x4040180010800844440d6007600b9655440c40030760b00c608420041100c80550700c0005a015503240c400290500000c0e0918190344040030303a060401800124041e80d02115000005070404010007000701e505114010034880b07544000e002c45400c05d808900ba650b00300300089030150303403160320383e0780c65640d40c000b200c8103c0d080c01c003401600001e41100c510340c3c1c0c0c021360840706504103003c4815842c030041c1600008040a640f039080a5240480c00c0c1e00501100c4102074014104100702e0001d501d41a4420368081d0703180d61030742c2d490604020340740e8110081d80c102e58101318a8181e1004841e9201c0c0c1503a50501c0c1c441005541c46002d0038541c4010402944100c405000200c0002803442c00420054206e901440d4207019980041c042d961801d21003d0804000c034120740001c1c40207901c110b02905800e4481c0d600000e80d0300c1e003085914a401032441c0032204c00352002806102e01072680c010310007642031340c030314409961616801c0901019400c422a1203400da0b1900094280041080700e0040d10381 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 208563237 1250 208561987 208562033
    0x29190503180a060522031d060405060309030304021309030503040605090c100201060503160509070c0312020c0307031e0905060a0c080309060916080601050d0c030204020a020d020601060903170304 86
    0x4140b03090f00150408803a40c405260089011801005000f5040d17a0250380c16601c0344402c0c00744066810361500083c541d40d400800901c4086402d4660308003e502608144008607164641407040000d00c01d100c039000000070741000000c03070004ea0001c080e40d03042940300704049035903510300b580c461409a05072106d43d4800d98a6105e512415019409181552402c1c2d0680d0070190440001480c030309154440e0702d8000a44100142c8014407070b81c00407403890700c2858900045207540000400366000282c00c0703000b9420010f6540b04254110366140c0d1f0310108100c501d8440d031408070002d0b03e61501c078858a0b020f514002060495a882450b0010b2181e81c010746041c1c40b8140002800d503101c008503100c030300038800d2201121040d104102040120348400008184c60707828001171102c2855020412241c2c41d11007600400181c1ea603002030316a0ba03c190780101240703600401d00030725003041a482070080c03180402d0180003040740c1140d1300b04101c003c00d0701640d030798a940c540080c12145071852103003d81c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 208564487 1250 208563237 208563253
    0x803070e03100c031a0307090c03020c0a0605070201050106091d0c0f070f050606150f091912020a090509070b1303050a03110d050906030a0b04090c2919050318 70
    0x1c1180e4040d10380e044250703604005c01070031303918070960856505e00050713850b038082030003009503003a10740280300d805050340f8025080220440080d4540340c406e00d402c40312151900104202a9424420359004100900c0c0c00700c00f01d4502480b1002e0245280404200c0d6154a03001450034003140044500c108200703181c4075580c11560030030b01001c101ea40750031601d82c0180400700c0d020b49442d9400743c5e65600000c440600e4400e040c080c142c8507a002c50419904603610101170310782e48400100301801003021401c010312409070b61040100321265600000700803403800c803e00203800f00005804055034208815250b40d40c407034a460102d0f008259000130100d120744003405080542c8484071003010410b6500315102501240000d442c03030b01514006039080201400020954680c2c3d41040505003c060400940078415450740624002da41c1c1002e01c2d113001c5a1186034009100b0355a614110860110b043e04080c010140c80b00c440169440d400d08004010000c221003030f098106004d04142614100e500b10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 208565737 1250 208564487 208564513
    0x4120606030b1801060803030402010e09071107030b180706021c030e060a02191b03200f1e031218120a0c020a06111c02070b0310140d0c030803070e03 66
    0x40f00c1e1042c0b54010b50800c1d83c00112580000b0075a40600d9051f120f0044c40d0f103d41c400c0c041c00d144020500b004020300f0910034031980c64144031101c041c1d40607520610b0f1901d040d00b0000815030350040341c60b1055100c080c0400811794046030300341c09811140d5000605203000d0307004602a0800850b0260725000d11004d2041010342035008000c02e050980002920350103150b002c2c2c031070304840c0006401110348002d00ca00080d20800b50402c5a801c001d041c01e50b07400401001500e8800d4013400145244c1c0f00b00d8103440400c00c940124848007003400002c0d4070703003040e10004000c01240070305991000ca5180c415854502024060340e010f0a0051581e1034555008580090034030030004001c3c2d015101941011400c03501c6aaa00c2480442d048000c12200e000000f10a42201c0540c000c1000c50123401d601182008201c00190302078032072512883d00090802d01c0b15030700e659444c0200c41c4500e60711806003001901c17021a600c2180d401002d003603140c0d91025010394101810796541c50f45401445407603101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 208566987 1250 208565737 208565761
    0x3050901022203110d0b0604110c0d020c0f03010e030d0b030a05060f04212120040905070314070f090308030c07120801081005040f080a050403060b060f04120606030b 73
    0x889001d1340b03038040c10f008414240f10100c131a620019048949650000e6864201a04003102c1103228101d054604407040d10400c0c2000b105902103001a080481c900015280807003c000043d402117000b08900061005081d40d24403034410700c4001503031030f4076102c50b0651381445403055183e0448252612450803030810000110111011980c84000e0360710071144060041242150903119120000c0002100c903c810960440c2c1296480498680e08aa00c1114202c000c0c00d0180b9038070f0b00302544840c10443c070306043c1c3d6401013800c0e082502e80815103e015100c2c0c00705a8000e402c900f0061010040300400310707510043c2d80c0001c1d007580c070000705001e00e030b80303815004009aa010340b40d60020302510203011a0388200c02e1165411541c801030b0360804061035544201d1700a0300c1048142003400142e610310000d40c1100c00d100c030101c0c2c00402c1c1001032240764082c0b001e0144c4100d40b00e43c1303002410045030565000d240130300000300001268020400610750300082c0a160804098001480c0050450103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 208568237 1250 208566987 208566989
    0x3010e101a2101061d040f1410020a02010f0207050706180f0608040210080f15040b120c090a060302100c030e030709020a0f032702010207030f0602071e030c03030509010222 76
    0x41d09601e440130024540348942c1c0985007200c42c0074580e0045840b2a100c02c0340c4402d0420f02600c1140010003035143e43c2804000c103517400859100007588480e09140f01030700316030030350f1407008046004009641c0014800b00d808405e40320581884604610030702d070400c41102850700450806a05134202003007807034020307e07568801d5200300d808200f021019842200c0b4860b06550070b0b010600042c001c100d160b440041071030070741c00e000303400042c3d03000c0c0344000503404050300560381000303400a51500405041801126a02c01d001d06401d1020700c1ca16030100c1c0e6104002412001003000075218001058440e41030502d124030b005003100c5495465280540081d484910300c000400c0300c0c0c6400e001654068013030035480c00e04030b94240402034038084e4410f00c01c04002400300e0445c01a00004400200e900e00403404160107904011f80b609107070303e041c50145550740c2c1c0c00341d007006102003a100003d5114580c0310200d42d15240204a58070384030411806070041540030103203042818055000241c0640d5510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 208569487 1250 208568237 208568299
    0x60f05010512010c17090c040510030309080a0812060a121112010608030d1802100306080c0f030309040e19031706060f16030c06020708090a0503010e101a 68
    0x28106040b101e901d03c2c201c659085011021600564090310321900d410b20700d0351301034080b200752041144481d001900b226000c460f5181d0310542d0314414418036078001055400ba02c00c01004201159032610740d00601d00072400011111503500c0001000c5c0c3d15400c26040080c19144441c41c40d0007404c2c41c1803500030703400742d0702540142203003280d2581d02d08050160f0301c12180d01c003000e54036108410781d81c18050010001224020480500400010303120b4807024840100c2c596800114541046600c60511680717820052041c607100c0381e182c03850754010044485c0740d141101d00150722011010404d041c10104070501060014007000c9805044d041042c043c0d038540b0840c0b240d2035a5840303d00300f184a00440c100c80700000e00a02c030411007101044c10781540140241004510480d6503528542641e04c6a00110744410000c2020a241d090070000d01e000f80500b01c00900c40c41c4481c1c0002c6503510315048405002c15103c81c0c5d030f040703010b500d1a000a5029030140440705004006007012a050042c10a46 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 208570737 1250 208569487 208569499
    0x41509030c11012a0813060801170a0804060503180715020f070b04060809070b030117100b13020f040306050c190206010b040b0309010e0708010f060b041202040203070507060f050105 80
    0x40c211a42c0f245151500e14141c0021640300c418041e044500040100c0404031008071781008244607001d820402070300100f1040d91190010360401030301f40b08029a9140b000810b0780075001140001d03015105803000d8407070901e0026100e56405010880550b20070b887c4505601441303401041ca01c0e0100e640d5100e0020700d07002c03070300c03003202c00254030744e417081144102d5030400c5061000340b01403441007031101e0f00240250100d5940c1500c0f286c00111550003a8041110502880071000c1460010301100030002e0f03503400704115030700d0a0004514840c4c0080c1950b2121a030000c1c001d98210414000d840280d038001e80100694508035400701101d0380032401c94a41814152544918680300151140c10b070f841c0e0350042802c161030001c0d04d4950b80c0026152181175520303021103410b001420000b0000600214001060999004550108982c2c0319080520404070400081c4244844541100901e81d4140d80050340caa07034140c8121014041e846005080a043c40d011b400c0400940c0c01181c1a03d00c00c48038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 208571987 1250 208570737 208570763
    0xa02032b0b090603060c09031e15010819080a090305070b0306030708031c02030a0e0a05100b01020f0c0d020f090c03100b0702010e010804050f010f0e10060803030c03041509030c 78
    0xc214010744111003c60381a489070b80050100115980604803154028040b00ca1144101d0300342103102c40307124115042070741300389034200052542400f000e004200001c06440803502603080b40e1440055108081c0103402c001410065103441202d158005642140607911b1080c0c81d01000480c551050300d000d0b1080c071412001095464000c03003254060103130380c101c10224046280803072001c0d4000514402020395580c03840024041c00780141d031803c1d84264041c284c50710300c04102004481c1d4000e01c09045501c1030b58088081580041d040403d1101140c80d6040c8040e9440012099030501690179008840e4509005024a40b240a5800b071040b105001040d50746485004405000d19a8081c3c0010740f440710340c203101d50044080e160054000c030240c0c0c814503541040380b0300b903902e20403000c80032940da22403900d4180414411101000c00c0c0d4203050100c245410015540d900016200c0e402101000011804006c51b0a903605445800d04906010484443c2005070280700050401d0342d06c1c56036280303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 208573237 1250 208571987 208571989
    0xa060606090b120415020a27051804140307120912080f0306130e0304090e070e04140a12050d0b0d120311250c0605030903040b0a02032b0b 61
    0x1807800c0039a040420b0241c202110490b000420800282055400d51074214503009907001a000a2111084580b40d40c021031507280c000c684030300d901e8048405480c0700c0b00010700c420341c0c41c00b1880a920800c038004009070388403802c000215403100c0c075000d5010301c00080c0000c01c10100b080c07541d0101c10725455160705165500c4102c1e501c041c0720f02c2c0051480c0001c1100214400110029642140c0c000e084c6010192644180d8011900f80e20b00c1c4003900da00204003080b00c04914001c4041c80e01e045409051718078640f00d90440601c101070401445004190600c0000c000200002c84005030003100c2400d54800f1160058500c1d80300034215065541491280416820604406120542c0c4200e00b14007120514004400034003104a084a4001003044100e0705000000c1440c10f00074144180100c204907580b50102c0841c01079880101405020f0007000a01030010081e01d0841d8025401d55647e1041300c082207046108171040f92040820903003000c1040c0148005034001c060500c081000360f525808 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 208574487 1250 208573237 208573247
    0x30c0603060602191a010315180f03051e0307090f150210020c030403060204030c0e01080a0b060915030d18050607260c030403060506180f0f07120e0a060606 69
    0xc0942d0025034000303000400308280481010f05030501550600c103159404041100c80782000303078030a44d034a07150044000d80d505264401e075007086a45108489080f003080e50b603c00d05a034000c0c0064103114021600382c24641e1409541e200c0d80c40c80440540c2d4a1030810006451900d590082c54444134a000020032420962146920990301e140c00800700e03d134448890301c020b90700001e0900b8a81c001400b00200255840c00500040c42c410440256164140980c1c80043e100580c460011544500b101c1004240c030320101a4100c00161506140b65550711910050090b40c032510b182c151040300d62160a1a61000100400c0088403185039616a903407410403440b07024402010b014441a030028400048080b0414031072122401c8100d418600e07901c00c0305045420962054440750b481e102000340c40d150203241c55440900b0100304003414140040d040b100311000034000d03200c120321360001c00c00c0e01c0c1c0140701c001c4081e900c1e240d05010400c00b1503045034030307404c2c80407080310328505280d40882d284d4014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 208575737 1250 208574487 208574489
    0x3020f0106061409040c0e061602030f010510090b0105091e0405060f060f160f0308070e0603150409140105101707080606060f22060809010504020913050c0d0309030c060306 76
    0x10059880c10f1070401d84c104002003480d400710009009105605294a0722680080c040b0142040b14058182503680149810058603aa0f020100e034500420410800c44a4210b00d0940d400d0343e03400280a8903550043e1000c1c420303100c04e16401025103441c00042c8407100110308013080103960510217501e035041408180c4000048241d070020b01400080154080c138000b1700503414000041c0f0700000041d45074070306031501850702038002580341820015416040002007814ad03600740c2e601c40c81c40c64541450341c140060305903001d201d580c440c0350107400d000207046003000d04c10381c15000304007a041840c0c10344800e0045110b2140454162190b0070300100020907004221500341018014031303520310040114940c0800c0e26092202800d20403425103024031203540601c0e00c0c0084241403614100100580320351001024425541e040104000050300c0304808a40c1103218030a104820414a240807030400114803001c603049036400c4004c00c245548403103d0340481e8001c810007282640c03902d10403000d880700703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 208576987 1250 208575737 208575767
    0x11d010501020c0f010e100305220c03080a12050903030702010e0102032203021c0e04050105041b05030a0917090f24070807080d090510060501080a1d060403020f010606 74
    0xb03035a00000d00d041000c14002c400d03405140440c0c540500307500150500007d10080f000003982c82d410060352080c0d407107090601c588550607440e541c40c41e5035680f100c46480c60000810070721010a200200d03038019014180b00742401070b424040b614040c00300d1544ea401c110340c0704c00158240341c540500c4000c180300b2070b402030f20942007a05d910204510340082c04410503000f00d0440c0700c0c200500718500c0b0500c00c5a181c16941359140080c01c00e0200402c407d656040c0c1045100c0c0f86010141d159a03908030701020444802d03030409a4883d81c550551300020401d0f424064034403011006081360858400300207141091040350001c10341c031080414003010010b80c1c1240380c0244451030029040109074409810b40b1032050318801c1c50000160754010664109605204200b5241c610100800c1b0041c0641c01c0070356001c00c0d0410440385400002409804041d00d03221059a03180c03a8019007807403c4040c03803894000362017165018180340c6402542c0b4811142e04020a510301030020405502c40d10034031520441e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 208578237 1250 208576987 208576993
    0xb01140f03040204020a111209010201060e070503071116060804020907030203130b061306090b120d17060604030501020406080f0907060807030506030f0607050c0106210807060605040f05011d01050102 88
    0xb072160b00340f20003580500400c0081c0314080f00d201000c05810450700032005d200540031501d542c1200006030a584480d001500c4009041c001c001c42950310105407644080d503454005650f070100c913140c03410701024485201d12440340280200ea00d6030080d140e640128803c0c0d036098420f42d9003103802c0f0304901082c4c0d40e00140103000c60240c0081902e40141e80e03084030b0014400d0b480090b01c8041c0100f160090790000700544d44800900e820751600d114900e1079120441c001c1c2c9600429000010a001d40c070f1104201e4040101001c29800e45449042d80d002c2c551200c004c56846032140f030090302c501000c46044440c50b0500e400152410000703e1a5012a0300a80340d1914644426100382e006c6c0c034000709825090f1044001500d00340004001c018000c000c65190f00c3c0e550608801c08500751403854100301070010301c5400c0040c10400b03508151041c40d80100e801d6455528501d8090040c4c6907540c0402e6006042640c0c0b4440c211081c2d2055040702e43c410f520042140404054441401c0c0034415140960 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 208579487 1250 208578237 208578241
    0x80303010302060405150f030f0a0515102f0114010602010b010503370b0f0402070507030308040212010f15060c020a030201110309121e0a050a0f080910030b01140f03 73
    0x30031b11041c002509201c0035102c0b410071040309440c031059017045540c486002d000a080c040007034480c0c4191340d00300c1040c180d005040d80b1b80401042419200750030742020007020120301001c08030540b0180501c05040c20740c0110480001c84498040c0850440c10049001c041e000062180d0051040740401c80301a1034540c150758800404100d1000242010000c1d504001035140131007004014910995441c5100000c1039480c180c240007903409818000e42c007030f510401401001c10710000e040c04c00c07290300d0300e40400581d44620100f8200d10a008000c8040c1d070802e900b5000c1d141443c3c0050042c1d04402c034600040595802c070071150301c208904040c0d0000039581d401c1c000b55101b01d054100b00041c21040340c1c54030b2200c1e4003090001080d15507111003030b0006444491100094110301650346584001071071041001c1e110192101c0b48400c2c01000380300848291010021300c0005d0355841000100140c0d11007080c9140640075000e0419500c0c002403c0c428406036030140700d0150380d9140800110b0034110b0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 208580737 1250 208579487 208579489
    0x8030a0504020a05013603050d080a2403080304020d05030c0c0f0405040b2403030409050a060f0303140a02160602060604060f080c0409060204120f060b090c07030c03110d0c0309080303010302060405 87
    0x134005551004002d1b0f1402c0740200c040303142001000034540c0c0c0d6580700d5460340380403940030040703c030703141d1341011012505c180305212500a45590b50a5079007181e807880e50380e1a5031000815403000c80d0740007411400b01160b2213a1801d8003140ea90000c0318181c07488440c0d841c00300d0800c02102d508640003450401c0d040d000c03d2103648170003d2515080080300022240c03012500029103560029032150115540303e008001d8020340900840c070081a4039148541c00c10701b1942d024140e03880c1e130000500810801305d0200810ba00c01c010341989500540301001d5071584507807000b500e8601c1140c4050049080107000101c1301441c0340c90100300c1d20355102034101d44200c5402c12000e004a0360055a00c01d40a01c0081500d400001c1c400205d20321545010100d5510751410405807484541d00b240309a56090400401c2d00004081303a00c00e69040c070301092042c03514507099500131580300700c50a040c4102001000301c50341255800400c2c0b4025184d5400d043d40d165009580c070f00c805d000080d048801400300b0070803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 208581987 1250 208580737 208580807
    0xb04080708150a05060d0b0c041404140708040303060306020a03060e13121b0b101503050c1e12040303051005030f03040e19020c01020702010f020607090509090a08030a0504020a0501 80
    0x81c011320441400740e181c2c51f00642e51400b46c504041d40f5500107401c00c9800c0820300c098500d0310301a201071046c0c07c0301d404100420b0400405100a211285001074101032195210402440d413042c021916090401c17401030081c06035006070b4044801310f0740071546042d0300d030300c01080507a1f00564003000c03403020300d2080360007901a06e000c40b8680702c000c0e210000500d6080d403140c4901d11040702c005110b403802d65546880030a440d042024186000244188400841c088441c80301b10f502c10b17032a5007101d5500517000352040581b02c0e0b4103c03428409100405506810042c0200248802900115100e80815455071458240c00c0324036402040701b04104010300c0c00301d540c4180c900200840204521001074241d910220640d802650f0020300790b0211b6030844502e00d00c1d900d1520090600b460034110150000701c86000da940310380d018900064022500704244044154404116500c0382041100000901400c0c0c800701d01c280c000100119855100340941d022800e810342c00c90703a0305841e510301004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 208583237 1250 208581987 208581991
    0xc0706051b06010815010e010311011b080c01090b010b0903100f06050a0f0306050a0b060d11162d0510020a0201140f1501020c0d0215130b04080708150a05 68
    0x8074900c0701c800450781500706000150003003286901070100540d045811114608050300080c440c03040c0c50b0018008612002d0416100c81000e090400581c004101c2109201d0a1000c000b0300120000a0014001a043d0015640341d849070424000c01d03601c4460f800900d0242000392074060f4485141e040c100c2c0324079003200030800403030000003e41544940100710315001d15046481d40301241081001040200c3c4141684240514020000011510006205449a4442c49046d1522001509501600c032800c403424820503c0503000496914074009403d14001c1e10340300e0b4120a00380b43d110b00c0b84040c803000c00c003056024010b8400c0001d003407102030080d004201c0d004110766880f1107413851805d070860514018080c01c81900a03520301400784005e05030440c044181150040c4c0c504031150b44070181c0d0500000d904a07580300c08503800d03103078841c000d005508500140c050110790014071210030038000c000396414203042e80c050545541c419942d89031079a40c4096032000e074800161146000c6e034044d42d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 208584487 1250 208583237 208583257
    0x140309162115020408030f1c0507080403051c0204091e020a0804031b050604060b090612030d1e060f03030219171818061801081c02071a030103060b01050c070605 71
    0x500701358803648110b181d40c02a103c80012000000ba01d85240000c02a03043c1d01040807040c284910300d001c49000b41701920180000b0207004c80452603440c0e118080c428841c07036443d242021903c983e074400e00b00000d020358855003003468280c8580b001d0880140d0003121000302554480344c00307580340c1d660101d501380b50f06000c1001a500300c281810028500340141c5000e14052070010551150031401c204112001400301d500c5600c41c1100415030010110569006c0701901c140027555811001c9902503c0c5800d50880d120702d454408041a040504410340d0180c0e4000d5080721001c00c41942544020708c4034180c007030203945d241004502c11347d0035000101a0030f070410303440c511f148000e0b60204000c0d02801c04c0c011071038400c26013049068204105000c9106280ea0300d5041a540b4000d00c0903200c00803004c020320b810303078400d2000010a00801c01e040052410058000c500070003850001a950028041284c078142003914800a9611413416a802c840805019040381441d1290950721540308800107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 208585737 1250 208584487 208584491
    0xf020109200a0e070306050a080303070909020d0e19060e060714090a12150b0a2102010207080a03020f011506021e07180f05160504060f140309162115 66
    0xc2410f900700903040e40200703070f0b07030b240819040e0500003040b01d014066001451103174824000c101540b80d21540101c122240140010380c0d5020402e02400070700310350403540f00c0ca0b05c141140c0c40c030094800180d0181290090b072003000f84101d902091521a030040d40c90400284244001c1110345440c040100303003e0f200280034010f101c2e51811101e9007110310b0f26050742c0f0240101200ea02c0182d550281079012142200c0342208203060840307840e921001c407121502c044440703540c15011a4020004040039002a02c200c41a40001746802581c456480c080da08065090116a02d000984407200509407031442d0041e20030800007448603410052500e40160341403041200001c1c1c401d6410f001405400594140070400748400c61400b070a9543c05086044c1200d051a0020802540942070301d05894452a014a0707011002d00e04580d031500c0100c120541c102c002003880000705001582030183c045024042e1400740e640c6070003004401d100c0100b100c0e01c8521240100000c5e00c0106050001c01440f400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 208586987 1250 208585737 208585739
    0xf0f0d030902100f1211090a09020a0f0302130f0803180a03020f010309061b05090f090c030f0a020405190303021b0307060e01050714070e220b0403051204120f020109200a 75
    0x1002056511034421107904500010b0703040310364102410301c023000d0400e0407415131500000f1200145200c4010512008140d80842c030b940318074068a00d22402004072010380e80000b61640107641d241c0c0d1120070304e046985900300c9404c1090401d4000c810491760000c0c1019000121a07006501410108604507041e59480c0c00c1204100c528003d0554040300d40d580705902c514000c0306221125502d400d0305403240c0840410002005da40c10200ea60201010800b4411074541c0e641500c0a170085170444c031340c003051002030400d4240303804007641c040f28001e500b203541c00e03080003890003030b0440140c04064050300f04403414040603000301d4000b50200d00c10326150340350022035140c800c0400001c000c0c181e030b9a0081c003400c0041c0411a080b081c0c0000303181c052410b400e424805002c03480042c8200040400002c90000f03001c0c5030148055032011001e40401c00b116141a14220081c42c803881c0c60700d80800c0601001d40c902d03510500c11013001982c000c0855500302c0480c0300700642004040040c551000308184 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 208588237 1250 208586987 208587017
    0x30c0105160f03050405030d020f06010909051c0309060515010804120e0909070905160207050d0201140c010c0f030e06040b04020f22061202032d0f0f0d030902100f 72
    0x600b14a20b40295113045d1501d007001304050038860b003a40c0c440c0841d0b00600c83d0708110a80802d64904640c80386a0018000d5034501e40141400109112002501c070604848100c06805400010755184501e2041002e55546c0f003613503041d180c2c0050700b540060350350390000d8001807e03251000c9041015003800c140194041d00040d2000000303c1c0e4501450304410f60410401b0311500a0307542040040340b1070200d550482400958518032489400d2081502191a00a590003000e030800410b111641d402e940303221015189000c0e1603000c04080000f2542c0c03841c02c50282c401d01c611501108040007810840d260b644903068035800180059030700458000307060555948010b401c18410710356840c508040b4904050250840340c0e55402001244d01c000018001681c000c600d0203001c00c0911006595401101c1601c00c00e102d80d0f501280541c410041c48400e2203800040d0300030b0b041021021105c200d025882c2c2281aa031000000079040807451a03148220b500031124141300880a21300a00320705400e003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 208589487 1250 208588237 208588253
    0x51813110a03090203010b030a050d05070303140a1506050a0903080c03160302250b040b03072003180a080606060a1101050114190605040b0f090612180c030c010516 72
    0x4001000c40c0d43d039502c01e011402c00b80a03500340000101c0c0074040816058a1b004d8507500220399510803c0320010744502014000e07400b28042c0401070b462202e2525191144d40010210300c0e2040f00480c00342d01c0b001507900c2c0700c2c004441a1010650301e0390000c03480d6580b00200364106009010316404180410842d10101765146c062042c02030703005058408034100d042d50b910400300695503005050007410310034100440112011034010319100c5070f0720741d10729400b22041004500c0070110101d04616800d101e0340d0000c003600b8020b10325449642e400c4e0402041001d07039811403055042c25006030001460783d1818901078800d404d1682041a00c0701c131005001400c6031000d8000c03920707503002543e1000c3c413410081c04c201000c03900d401d1044a81828044050903d005901c1852040e800005800d45224500402c1e602c036510040c1c000741e12044c900080f400e00d044200c8072164101c0e8200300b41114428002075252a070038010b406007604550020044400340d01c0f242c11003107801d85034401500090844 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 208590737 1250 208589487 208589497
    0x50706020409050705070b0702190209061909050a0605040902150f07080c0709060503010504050705122b1812020118050d0302250e010b0c01090c1e0605181311 70
    0x4d65202c907510b400600d020b1020100c003400880c1154010a0855a509000058140840d404031101012a9100000a103c0c20804030000d9440100b0240001e010301298025a000320100c810a10995466400740411518540b00180d40581500340003131003402c80100410b04688451006454510070f5180c0256992044440e4207150b17000c0c03401001800c013148a5103010f0441100244000d0519894043c1d8500003800307460320401e07011065203a00801044040e0020b40c1c030f03a403036049505440b100d00441594015908002c920f0f090018101c1607804044c1c07a00341c84510407001201462170300112203540e415042c1600110403454041801e643e484881e541a620035402040101111241511911100b4405001180e0480024080d08a15140190648110380411a01c600a46a030240903045802015103c80c01c90741d00420080e124045074101d41e104010000b078110341d182000c4900b07104d0700c1e01c3c040361b00039403054034003a9240115001209040c0400702050013900340755569519482 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 208591987 1250 208590737 208590751
    0xc060a0504090501050a030201120f0e0d0905180712020d020f0d09051b030714180f100b0f03180a0618030e0405010308030f070c05150106020f06090d05070602040905 73
    0xc0850200050744082c01842d003d031034141d0f000e000e00c0c2c2c074543c0082c00452010794500902921003046007520b00d0342c0d03404242c0303050b05081112114800500042c1c1050402d0250b03500071441032091000c0c40410010060050303e80d41c0c0c6402c1064010481c110094100d000d080d80055020000c0c1d841102e400405008007041071540000c040003036242c107a1a00001c440c01c451b207114054280c802c0755a01180301c1003180d402102c090300c2001d042c0006202061307401c1102c6a20140201030290f0040e0310855284100b820491448001d502c405240340304e8002e040a600200404100140b466060903c1882c000d8900f101210b0255106556040541c2e10f100010880e6042c1400c1107070505900940a00c1038140944d420440c55040d038590880301d1000521010246850f8004140311a105103510301405070410155000719140e40b00003000f2000070f114844c0148645481d5025550000c184d041c02075030b10800800d02440444000e0301d20340c00184050714010750030711001502044500071203100e50303d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 208593237 1250 208591987 208591997
    0xa0b090a0f0b0108060f07050405010318060906020301030c0812070623040503030601020c0d020a1203050c03070f0215090f090c07050715030e06011a030c07061a0306070f0c140c060a 80
    0x2040010b200d10302107000f0410146ca15001051102c050741160445059840a18001c5a000080c140c0709041d040080d90041800d450311684e0030a100307940e0f003e075040e244507503a185010780d030382c80d495507a41c215400c1e604940d02040050000007001948084202d295034211049100b600406500401c03008403000c3e2010740000040100c81d680c1484a031a80704c0c0202e451103240d5400c2d40128821000a00030205803201c5104803405050141055502a55404040780d0343c5e4100b03450306052030240d480b0103e0041704034942c0070140c1c20040055894000d0b0180064000304000000c1203649800508000d60789441044480089030081c002032001d00800c0c01d0f0700786900c08001000b002c59482406500c000d4101c000180441c0050040c0d50040c41c080c84842c540341d032512901842507100d4020b00608551a16102020b09200d0305c800300011030f0101c4c26035807155554107055440c40b07080c0c19840002a1409070940000d0a00902c0048090000b000c0300e0135811030f0400700c0d20b44d52114024102080c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 208594487 1250 208593237 208593239
    0x911010c2d02030609061005010f0915020307080f04050a1d040b04080d020c01061701050705030a1a1c0b1b040501082203090312020c0a091802091003060e0105090a0b090a0f0b01 78
    0x751b059007801000700401c0c4ac00c4581000c0d000002000e1021500443d071444005082803100140b08100783c400f134030380110a03035a4030352254840010503402445814001e0b92801c000241d168107042521102c543c8a82c0c580750940c1e569900d4411a5200420840d88101c2c144002203484c0d902c1d01c0540081c522100c0000782007402c0518072545c40e070b02070800c51100d038102001c01c0925540003059070340051011402040001451150442603c1c1078901c280c0c000c81d0340941d46107044003100701011a280280c1c0542c405455446003041c180a05000b41c945004040100300178551155172030700e910141c09808451000c031114000d01806002e42e0083d80000c030600414400d00104048546417281c00d800101000540100441c640d2000c1d481500d8485984100e201582c40400da8001c08141c0c0c0140301c0d645031b20b0841d132050700f0522140401d9580514180700c1200d02c0c0414401c4501480c032100c000c0c051004541d45100c2c41e5580209020002d002d0f03544600c00150036403098602e01440782400107519 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 208595737 1250 208594487 208594501
    0x100e030a020606040203060a0e04150c080a1a1509040908040f0510020a1a19141f050d230102030a140a1a12070f03060911010c2d0203060906 62
    0x110078050700fa42d01c03a6204000b0700c00c10f80d5840340e03041c08513003d1401d50000303941d5508104c040c20404460310804982042030f58001c0c1a44036a03a603101e04190300e0104500e03030015030084080c811102c4c0e0960007910590b00845901040000b070b106050340100089110303006070340d44860303540181c0d000059551003c0002c0c4503030702c1c0001100c02981c046100800c055100d0391a400840d010750b034008a80c01040c90007249c48004100c0c50303803000d00010f010a125540300c2207549001101c0417216040900440703200d07125120440c080c901300315040100759255400903621540031400e0f0a40040940b40e047c0705c030040c520b400a00280d40b1503c4070010000d03d42100c040321480f1078600401141c092031801100d1400d4202842c0b00080c040005d440c2c1e98810500712051500d09115600b20300417021440c1c10002c100040398000300801c9124140d02030240300c030640191100a03140c0b20040c01c2c0d042c60a0143e50001044070805803012a8030391840b128241a00800d0902d50150303004186c60300410204070709 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 208596987 1250 208595737 208595743
    0x40e010204090b010809100c0c0803040b0f070c0b06041112070801051801030818012007051f0206010902071104090f0203010e0c1302130302030f0d020106090507050a0309020102100e030a02 83
    0x3c44502820175141070f05d840c0032501d84a00a08901e03e032146d0b5202c0981c00200c3c030440c2031120407503102c1c0d21035550381464289408100c004440060b441c1c5d5141c03001403817951080060920440c3d00802d00c4046854640800024282030346e90301c1d800040074049180d4180b050880107005064a440c0c00d0f00c0740d4140014421196411002581d6100e0840e0040000929071002c42d02c403880c4000403500d10b0113080700100e680792544407080c0440600c285c00d00d0313200400403e01d9801c80309d04651210a0034868030702c08009072520703904440940c210302c0042103002d856400500080313100d0b2039038620b00021480094212440060190b03002140e8414030001c6080034462083e40380300c0e0000500500c110500040c080c1e1071a42c0d41d10301d9070b640110745028120521413061010355401425242c019a02035041030350b8030700d04800b00d40103600300030000545c550319200d00f5004110503602c551503c09218020340150030070100803411840f0f0208203150240340b42c0700d50702074801076401a540d600440e24000385 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 208598237 1250 208596987 208597001
    0x5010603060e1302010923120109031704080d06170f01050115120b0d050303100f030f0201050c0309210d051305090403020a080f040f06020a05060703050a0902040e01020409 76
    0xd141c981030040c010302440300b41d41580940c06824601a020603403004071054900c135444040204551810003030840b009000c0780200c2c0d1702c25910752074504540c0410501382c8214102c0900030a008040e04c404190008142980c0329014003006403604148555150458481d5400f4109000312003e0001d10f5000503c901404115008000c0c0242c0d41048030355110400c062110800307001c40e0040340502d91415420891100380020403d1010500a06180c0d40341da108890300c80100c1441400030401101c00e48206081c3c0e45c00442c2c5030800902035005648903803100c0f10002440c03009000d6032110759982440c4504c240c0c5000315100d03460f0701040d1000d18040042040d0700074800140644c3d40014030006100086038021506001584c440f400e080c5d0030884111009044004002130814052402078014801c0700e82c0c00040c40c00065440d1303c200d03208c408107e001001c0e5084032000c100e5442c4a904100c0d000310881400260800c01640060120790100c10010f44503500444c0c200a94229845200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 208599487 1250 208598237 208598249
    0x7240605091f0605220e070e100203030a050408070f0515010b0a0c060c170703020301080c011d0f030705030a031110020906070b07051b0610080d0903031d090f09010501 74
    0x441d00400a1464202401060140c5001c0000c00304881000052400d5942100c2407140d000800c541d445100748088881c6c00c0f10300c5000314031000d542208908008118a0741c0600780d502941c10340d222503c80308007502c8042d01c00c0d01d4200b0184100404604070300c0d0340a150714411001008502c00c1d00040060302e141c1607104aa0703440042c400c10744125081003ca400c070310340c4900005841c461041d415140d540710203031044d80d4400303880c0403c28440c1e0983d004506030b9600c9011641d0300c0040a0044a619001c20030b0211010300c042e00c40c4003142411904104440c500906131210b654a81c804a03140010050060300000c860310300c40c44864030240000c0380e4421405006520b4a00c00c0c4c1c021411a2051001c0107040500b441d002072000c030b11070b0f429107040c0c94801d0313100d800300f10400261650f148000d403056008000004400a41100001780f5080c607110541c0364003191528580701924064128140d40501110064141c0c0c0c40d0740d180600c2c207128000c1004240820300b0104115402c51314140c100ca = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 208600737 1250 208599487 208599511
    0x22020703080601030b030a020f06040e1306060503060705040b160503190305010e09070e0903040b0703050c010507020706090b09010908010504050d17040f080a1101060b0418051501050724060509 85
    0x201759585020076070010064040d00d04480f855480004a081c0b407085a02030040c0070b015009109096050a8100340c000340a0041400078640754001c06481c0d00c0160790343c0002c01c9040004000001e1100044d16a40c1c044269400e032000403900ca180c01d40d03101d03c0c000d089540300c18074003000b0a6014403806d8007400c00d10399900c1c050700d00380b4012565003100f401862034506604000444900c1d0800440f0064142040380783d4551541e1300d40036000e600006141e45c3d655084c00c0004190510002d0848215a0181c1d10543e40c1c4c0d1900352000302d19404042c009040008011000c22021024003032075009500c030320001c010394035041c00010b00d10400c104119151450b4001031002060b100040320b4504c03600001c00030703902c0041110a80342e40b10362142817000ca50900400140300f40c4942c000d40308855406080d58070010f5110701e800d04481044940c034125140e0180c51690a5118a01402c4224400c04982d48584801c02840c008001d55542c50400640c036884203202d141483e050064100320b1200c85 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 208601987 1250 208600737 208600751
    0x50a080f03030c03060307030f051e0102180f06090301141509011419081f0e0d170403020102040e0a06060914090406200a0302030a0e030a0219022202070308060103 72
    0x140a440b880083d100d040b10301c101102084c1195018461080150f52001d601d44420410f0b02e003860312404e030f240d007021150b1391a00032945504030600032142d4440e80c41806c4104c0710056000c001e8860711030003078130b9000201404010802d4400348240303450340940c50000d11440c07030200c001c104108940040203000d0300011004200d600302c2c3c00810818000100ca902ea0b18441d1609403100c0c010721580080d0720351081185860754210900001c4c0900ca60320300b028081c0c625812810b55039144440515000945c04580c00d00c0c40380e2a00c055544c2051081c40003520701551100c6000c0c1c0c0f0700065030720100542e501c00301008100d408c24401401003002d40542e444c6060304078006502c4002c000d101070f00098803020314418034083ca6005586540b152061180c0fa2203070050014002c2d003003242c01c03001e000d2818040781d0300c0f00c0d0000161407039100e141d40208520340e200440b00c80519440300003280c2004403e5960000e46100b40680b00c00da5027080c0c40141c0f11711071414000c21001014100906042c82d00c90 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 208603237 1250 208601987 208602013
    0x9020d06240305060d0c060f0f0914120c090c19020706050d090c03060221010503030702060a230d0c0e010e0a060c210e0a0b0f04050405060d0203010c09050a08 70
    0x40105000036150070300180c2665080c005c00c41c82d060b09800140105010000851055000103600002c80d007e50780d414030024016000707441a422501a0b8a940541c031400400c2d81d1808001c990b0004121b201a00c032200d042402080700402c09441001c4d143c00d01184507040c01603000300e010350110703040c401804460300d4003202416074071490b5100701d031894444c00c441e410b1000313404c0c06070021039021908654484075101c62504054206219004024901000007014a40001510103540c2c008015074500242d00c1029951b6004042d0030700d0061801004c02102071607444007621001010920228500c3d005ea20014540f00b000e010321410302040388168140d9807030b13924076042a11418240420b00c46500c2c100001014410022080a51660b090392411558005240c80400c030083e10001081910741a201c00c49005041c00441300f21021f2008020601c5d01340c000035080700028102c0c4000c8012500424251510002210302050140004014504018541000404101000c3c043c1c90320144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 208604487 1250 208603237 208603289
    0x7050910020309030a03030b0a06052118030f071a091507200106240c020d0212160510110a02060f090d050a0b070c021807021609020d06 60
    0x151824010380c060418000450300800489042d1840241114241501d51a004025009540318107001d00076140000521030b004005842c580303001b0400d9442c9200d151211800c00d02c0300100072000c44052005104042c040500c002c0000307902085044e503650b500fa0920f00700b4040388800e40300c0e4201c04c160030403801e4030001c40c1c20040c90524040c5201c5680f141d4100700c58900840c0b503598103030480c003402d1844180d81540320074100c400784207440b0080d03030f0039071140c1942807800801039011540d004184001072a1080510144030306c01071030085a071003454a070f68900750b0206103110141c029103c080c449454410b400d2160054079280080c221503640d41d9807a100d01d600c503c001d000310030200348103490f07801050039654050b00250000c1c0980c2d603e03082540da00c10080300e050f180c8100e00790128008a20410415882680141203440f40d500e8020040440140042c00342c000c5004030104c1580c1005c4e0307050260300410004a001d40c42c0c82181000750100c41d455030068445002018a5003860a600e03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 208605737 1250 208604487 208604497
    0x7020414160c03030b031002090415030201090b0c0109060e0d11030c1b060403020409080a1403060916030b121b120c01080702070b03100303030b040903091e03060e1e060705 76
    0x82c940004410311034030781940640001d482d03165060141240111205210758041c084001d8215018070005040003000901c000d42d500029002035100c51041c014400342000400f0810650400001c80404640b00c62044903200001000f69800848200300c289603c41000c0c040703541450091840c080190380000e42c0c1d000c0f500d205000040841481080303070b0b911001a90020354028100340000f802e149004880d0740d01005070368010444a400401801c462007003038134410080544100700a4072905114403451000d84114002c040e200c00d00886543c80710241008141aa40c0013000d844024441c1e000b41032800800c128058031034010721520341c000000c0e0541c100842820903484584031050101e080920540080e039041c00c000040c0166200390740381c1c00045074001d50301007052149074000c21007910f08201028002414242e401c0c0b0000280d5004562201102c106c040502e5540ba61600151f80c8030140340303021500b00c024000c0d910b90000c1c1402d400d8034000c001a01c07071440d04050140281c068 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 208606987 1250 208605737 208605781
    0xf0f06090106120e0f0601030302010c02061003030c020f031006090606030c1803020f0d050607200a0c052b0807030e01090806161101020d0504120905060904050604140c07020414 78
    0x9800c150740e0295000d10808641e0100042611191f40e100d08003c0e0180c42c412680c880140714000015280ca1220320700c90054940c107580d080c0c050f510301e07000c100d444000b130010950305000d841201c03040340c040380c46a00020f203000d40c000700d982ca24089000c0c0c200d804e00c0b20a0390500c9207107840700c000074142802403c156641113401c81c1c0c02506807004541e04a4000398002e180340300303a005100120307401031792003510f49005001e9161440c05410f0000c2d111f1100010042800e00101c1007445280b800740020284a0100c400380d01d03600c501080306500d40d0155403410340798190005214000d261780702c240d40a20304005e00702100d9841c644000e05a0314040140303068150074410f0061300e8028407481e000c0328000c100500a5446200b8100c1800062405503400c941045d84400c099035003038000d401d030b8800c54200500305410950a04103010180500904042e8415659540b0000c0e146102000c607008888030b08529485420601c140030813109a0700c0649031605a400130010803e8031803002184044c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 208608237 1250 208606987 208606991
    0x207020d150603050d0503010306110f030708090c040903030e0c090f04030e0114070302010b0f01020f07092a09210c050618040528060f1208120f0f0609010612 70
    0x981d501c8558014031141c0c000820300c0c0600c202d2040c1560f8080040c505032030013810308100743d0303c5110a095451203401700e03854010b8010300c0090081406441d146912443c00d80940d6550218640001c00312680e000044001c0399851800a4a54000f0055081d0b42c00e015583c40c0307200d00b041d640d00d00c0d1400d03005000604211000004400c80e900c02c60110710300b0289041200d071a40303650715020340a4040e0110309400703400c008a031202158800074410800c60714180103001d425082c0308100010702809440800071102c0c0880c0c2240012080900f41d10203211651007004450400c0404049082c0d030540d545481c4034400003450221b5aa4030f4a20101d810444000750340b500b1030182280d2613408481100c1d4040d10b440e0070001e000c01d45a00c068840d81d4140c5007520180543c0701c60b44110360180c010f54041c64200c0c1c1d410720201000c20007424100e8041c4032400d0030500303038040e00b41001004681707108044034801c040c40409000d0514880d0000000c648046041d030501000a250149002200a85036 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 208609487 1250 208608237 208608263
    0x120703080c01090606030605011805070909090302070503030f0325050306012f06090c0901080a0b060a08011b14070209070318170703171b07140f0d030e010207020d 72
    0x207002d42c841d02a155200d1030600c46150b490401c000104001d11420b849154040d00d007074109010b5104080c0f1880103a2641c04006041c00c0c080d50080039012000c42c15071160032404111958104042c0029a00d050005540c0b89003455500d400040c42942c0b816820384c0c081756641505401c070b8140c5c1c2d8803482c04e190950200590380104901b5640e032407483d0040703a1030005110300010001c55454418103804080340e1007034400600340188800244203d1041e6040040e00c000018404100143c12401c02801c0402071900c540805084034007410199802940d5101450700050700202c0038a80c41d00e840182a080c13500e5500440c0c40f0350401480001016034074000c88003421600407070089039541261590507100703a0f100742034501d680140400c0d80801c8038800c4418941b002c2ea503540388100d104e4031080308542410158807030160002c5800b101c0602480810082104040110250180e0880014003034010074100c050111810b01030060440d9004001d0f100c090f13220941c84035051136020050706d4500c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 208610737 1250 208609487 208609507
    0x101509020c0d020607090302030c0f040b1206010f091e05040c080307030203090406050406030f120207090e1f0506011b05010207301b02190b030a06031112070308 71
    0x10545540194050a00c08150940400c500007045075074a11181c003207840b103860b480c0041d5601c601a101c020352560016501a0380c0c0c3c10094099a041240580b0209000c03100f680021400710b15400d02c40025403000004010507010058220014401c40c90200f0210414800a8401c01c881c0451440580d45480114040020a554a40c01080744a00307136a01c0303011130318000707440ba131041c2a1a8801c0d41003030780100c1c01d4038003449070100f280c2c0c1c0300031103030051021075a601542c462003080c440258040e44500151503684c2c2d000d9010900000d40103049903001042c4007400000144041c120703103901d050104103050340c11030950701c440c03403503080c0c5000c0c072030058035006029104100c401080300c003040c1d6001070354400c030608500400c0307500106058540011001140c5030350343e40c9070000503044103d0622000d800e24044408400413003002c03c0c094030f0344400711204164025954010182e51355030b0100240424011001c403010b10480d03601c0103480c103034080203950300c03060b00014000c0040002c062140c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 208611987 1250 208610737 208610771
    0x90f0b07020f03040801062303030406180f060f12091e060e030c0606180f0c1c05090c1002150c0c1c030f0b0402120a0b0312190f0804030210 62
    0x30002e004021a80d81d20f0321003840714042d25092040c4d840d09031810080007130300c1e04c5003103410900707190240003542400e10780101150801446035011410f007982c0d010108007130103282110401313411962070b442140111007000030020400a4805580c55143c120074500041c0410305681c00030360b032450461000c0d189410401e004100c000d603040800c0c070001403440c800d150701141c444c2c0b1490048072841c200d11031b4440500c0020008856410141910000142c0f025034807d024050190b1103001c055038401e44482c0035012641c00744e0700d160866029200d1200a4034000c035840d0b01c404011710103400105a105408024480064042c0603042d801052039040c2c1d54003000805144100d4402c105000c603440e2102a006006c51501d0103d0700d0b0801d4440d0019050a000b02c900b8403031104203280300341e074030810b14400070700203800c0702542350048001042245107890301800244031303468144040741d070708054080c02000403a0028020300920004010120b900030803625103c480c01400400c0410b06039451a47c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 208613237 1250 208611987 208612003
    0x20312030702150f04110a0e0c0f0c0604110a05060a09030b0702010e0a0c080106140f010f1103120a0b030105040305030408090a030c0b1b06190e0102070b0408120703090f0b0702 78
    0xa2400426400c016613140251942801180a80440100d100049052042c100b0b0503024000c1340395409008200c80720718480040081e40c101540060420000d00d200b075041c10001d50b0103039040b5107100d0f00d601d65450504800401001c00b101c110745000124640540020400d11014100e08885000102c81c0c83c000e403c0b0f901c030009940f09584c0707118540d1904043d40c9080f80109030040d80380007408510420110313034540c0c00d51401071480c8880c00e0781d1401101c5610765200004100318170301041402036402000600900b00000c1e2a01020746095a403e070120750110b150188a40c0c10002440040382d04581100d800640101c5202d980300d041c0808500d940d40c007644010300d18560b910300002e00035450b4000e0202480b801c0801c4400204c0c0078041a40c4250554031510120b100000c1e9494800c103541c00b0100b1030704220009401c11804d9140e1391049a0115415075445d00006254070003404002c40340d070b50014542c1802c20944d01c458541210455903948014a4a1000004612107038000c00c1a26 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 208614487 1250 208613237 208613263
    0x1d0d092304050112201f18080d110a020a03081806030f0603010510050f0103020a030b0d0305040503070e01030305030402150d0c0914010c17090613030507050f010c020312030702 78
    0x4042c55a443c20500004440308006850b21800400c140800c40104400c0c400c0c5c05e40700412100f15841da04459082404440c0c2a900038000e040351680384102808000c9001800d8100c083e10b00d01603401409020b1800300d80e02101c41d41c101650050050384d40b917400c042581d8000010507129582e06111211141080c8184c6034010340120411480c4911941001c0c0b284006600a01c042c4c1c0780c54151210f640d0301409129403100384007040040d0355129a002e0319014645140216040e81e60750007103000303017080c0c060940000d00001800d004034141000000001d2a200c0c82004035507241d910018013901002e00003e2051800d0030f800000344241070141d41caa00f00d0712404101d45040755a004d4000d806038412541541625458855658040c5400320318103034119011a2200c4510880c81045600c41c0c103206500604c14410b9018040b540365100303010310310410041102c182420200601d01704100600ca0400030050484401031314085401c2c072510052440c0d035902ca8070307480b80c140e0810b4600c2e1404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 208615737 1250 208614487 208614491
    0x510090207050f1c110c0d0201120902150301060807210b0a0801050a0516050a05090913050d08041104180201080a110c03040f080c060a0c05030906030106031d0d092304 74
    0x50041c8051300300d80790381c00c488991181d01c8000c0030401e034242c03142c0e0b01c0b241403588002d40c3c82110b40594050b03803210718020b100d01c0700040e0555050b070000b103860620034826500c5182c00f00050141640001c8810f0300b040d214248011210a83c007071700c20303e035914000003015094a400c2e0102164849044200282c0420b400070303c05803820174503030f01c0100001c484001c2420003401d101c20b8141d01803030488001c0e00d600e94403185011441e80900200e00c1026116082e0301d9010755003000840d800748400a9598850b95a002d00e40c20320341030600340780003c403c000d4412841d00c2c00314110410210344c03c05200d075081c00c1488072542c889012030f00a015040c28520f4800c000600540900c0010000700151030201c01da440480344c80d2080e07965254030004c5541d0708000c04000e00040f0502440b082515184500100c2c0c2c42e10a201001c0740c8503402c00c0c0e10050100741c45441d00142101d000e085a6001c0401100524100c82e0402e0300a050b09124400c2040c56520101102002c0956000d810b8190a0141007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 208616987 1250 208615737 208615753
    0x120908030705030412051e1e0a0c0c0501030b0108010302011808030f04030c0f0302010806120703050307030302121312120603050111030603071a03220c090c02100510090207050f 78
    0x8042c02ca41d0040741c0480b0609100d10b88100d1282c094000c2c1e5121840c1d50117552039040316600c0611312a40b004591040e150801c1c004403228840c020001d0440e080d03940e607800400c0019150203010200e25030480d07410705090160000b501e90307005503c0741c11640c0920300121501c40320034a00200d600245c00202050000190303100c00b441d8038000410440e8401c488039040e06544800d401c140303105600000740010113140100c2d060340350814107240405410000d03140032036583e41d01d03075103107920440c01200400c0d00802e103d40318155943c6003e502030311b4401a620080820b40c1ca40c04c400c2d406d00000802c1c80a0a0701007440e401442d40488050340c3c1c0704000304000d0004446486160f001107511900c40c2c400c0d0308010801403a0b0680700001e580d00654001c1c20750310362110aa0314640c80801c41c01980c070803001113902090f0070405010062912070000510b11159036002820700d402c00e1109000e40b2300381300134814900141c070200c2c0100c038400d03440140c03215a54a0124141080c039050b4070254802d5200c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 208618237 1250 208616987 208617001
    0x30f0703140702030a050d0f020303090a12090b040f0e090109212115050303131206110706050603060a0207030917030f0a030509010f18020415050d0602042d0612090803 74
    0x1405403441c141038407060b441400352340049a0340d21017101d600300e0300d4114100ca4000111114440644246207040c0032400c5602d0700401c1c11143c1142e4000d05c130004184404000701001814125040b0070130200a021102254881481c0c10754005141015041028400e00d2a94441d154003200242e4500704507145030720041c00c62000e04010f8103043c2140895034000110351030000210741074108100050030500e850450000b20248103520300742c03100303a1121400340252130030200400b1018419a00014182040000c1c140341c070b0741c01030074441d64600c1040407202103038002c00c50384119038130100d80c0b000c04d8003688072482c25801204190080d201c2c0c00f02d1205042da8054104c02e2080d95014002c025500000151740256940c00700c0c0c0c20b5100c501840040d0250800b5080b0900401052007142860313980c49000c80d4686840d400305682d181c2d40840c6c04e014401081c180d294081c1642c80b0310400c4848910b0710710004406030720a840c140300c1200f100410103482038006210b0150000d00094492400318 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 208619487 1250 208618237 208618243
    0xc1f1b05090a081c03022104120201051b0f07081605060a0e21090a08030c070e15061204050a0503031302030613050c0418050607051308030f0703140702030a05 70
    0x4400d2902c140340306400072902e00f40c0040c0902094030200030030340c2e0b0a10000c10039002980705851031740c1d1030064a00d070701585080000f03510380624880d4101c0d4003584e0321564000d003101c20260098560500c20786002c1a40e0315001c0943e0941300540100307030364545203854202c0c45031240b02c129601e00342003070005030b052010100d290341c403405031880d050104407603000308142c0361001c174140b821080050000710b4400700d03103100142c80c1061001e0551030040745c841142c585941c124444640003648213503000d005a481038480148c110b00d5846407401001065000280305005100034104501260030009040c81070070005100384640106c20303295642440d00842d044003201d083c05078004d10607607011411055a4541e5085429040006058000d0515040201400820341855034900400c110400428020303c000c40c050b111a464007179440920311907000c024500da40c041c50b402e4000b40100c5003080b6200b01100c0503aa41442e00c1039900509016801c668010404003030342621a829503d03080100c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 208620737 1250 208619487 208619497
    0x20c0a1e021305070219020315010b0c07080a05030711061b061e1905060109080102040e0a11071a10080f0d02010f0c1e0212031510050c1f1b05 63
    0x81c0c6640c500c0682c1c882d000c1094460a6600c1001070340500900715008091032204801e0520007425540c0341c80c000c0501504c071100c02c6c0c01c980c0e056a80068010740700241008194020400c5001800c06400700703455a684a00507101c0241401540290392005541c440044840001c1c1d0660001c1c1111241c070074003561b900044401951603007021420106503203403005581d120b541c01e4921070f4100c8494080740005444054240d0f4144406110302180b02442030000e00080c103555075000d405031800b00011030a803038102e0305030841a542003080401194800ba944102030810b40e260f011315403281d0786414800c01460b0b109404174050707001100d16540000c141d40c00d0f102960750092010500e441c070807900b103074030062624001c29000ca5260340f844401c080f50035078a040038010f98a040794108888145544201c503d01c0a45070b4084440b10b481c075040c1c03402c00b241c50103440d02d581000d04040800c3ea445042c400b42e80c1d6080c07460307020740c0d0b03900c01079406c0384aa05545482c651000100340703501030800c2d000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 208621987 1250 208620737 208620739
    0x1e0603010b04060909140a0b150c0105060906061603180f0902030405070f1d1b0c07031403030f07051605070b0403061b1407050102040306060b040303020f070806060103020c0a1e02 79
    0x100b40006800742e040e001b4a4224114510b00310542d03204c49145400401451038000e80240c0101b0101d44a90105000303059040005400824540380074020014008001000d0600c541c0c0c040c400d10602a540c01c4981003013907414104501c814030506082081000e0985c0038009402e41c4040100f5002c000d500554040c52041d02100c1540752079010150741652180600c1c6080c00101d00a800e403011840c504680045184509210901e801050030070140e00c0b10003000d0096104a404000b084200720f03420a04003d0713003010754214100341410a01c40e000c060064420488045000152500b010040310070581e401002c41d410380f90b4405403440079801a1105a403642c1c54451340c80c102071031034070150030328007170070742c0d4402c40e605180205078015006001c0070343c1c1e00e6600b404080000780c00c0313100b0740c400782c0704180801d5142d6285d40b40091502c1080d44032100640c0084c8030403c010361000a1460300000c09090150b240c040e010392207807400a1441024203030700e214581d00b140c03502c00c0c940e00c00d00442c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 208623237 1250 208621987 208621997
    0x601120302010524040c2a0c06050307090e0411090906010f120809091305070f030212030a08070e03100f0c0311030f01030201030f0b130c0e010e06030103021e0603010b0406 76
    0x914218100c801d01560100f1a500c44003103001030550746000ea0201007810b03020309111560300f056001007a4260f481008022189003141034547c144100040b0b090010072151600784d281d0b10f451080248440b54500c1001e801e02c00c0c01011a04020038810303c6001c1120141a8004a00e003600e103140e906d500a224205a400300518045040010034040010700394000d400301d448c0608100502c801020003c20407036910800004800004409014402c002c011200c2d00402c030600394010800b404640408a988640c42008006c01c0c04d03411020565100030f203810032103c5012020b0100f410f010302c520300c3c114441e26001c00d0a1031102c8a42c03004e02e039150304e0358007045400303d11100d00c58a84800d682c0c0b1003410200000400056102e0f40052030000b004e0f540119200c064000032440c801124030782040215151500102e446501040848420100f440c00c10300c9141401d001c00c4440c841800082e0140041e1010441ca09120814807580301002610140d600e41c0e42d905140040c1c2c10038000c0c080059 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 208624487 1250 208623237 208623241
    0x306060c0109030f090b0f040b0307020307020d0c061b0f020d0510151701060602060a0e2109011205060f04020c0f12040905150108061309050d1808010507021e01090506011203020105 80
    0x311108081c0c9024a4910003088d16207030824000214640004101808600c001c02051005898082c80040081d2080c00c2d01e0303525a040c8403002e040da42c8200305100d41160b21048103008115410408021550140c40d03160700c1c403403541840da0501e2100c000c0c842d680e6040840b45080c4025560001e000c41d04109140c10580d074a150226081e2051480340320700580c03104000c00c0800410f640131520081001d004ca403054071048030800300c108500794030000060408600076495580140c1000a03016651204012614210001031307030a2100001d10360286034003150700a00004100001c01c0c4d0244480301f107440c42102406000740c00c0d0303c1070140e0090b6905150210702c0c4c2c0034446070002d98254058460104640d186018048040c0d01c03129144010798481d0007500c0814000e22100140e1000e5603a0740401003043c220a044000e45944103c1c99a0700d000c08000c2d845501143c2c030690141d550300e00c110400320140d10603014107503201c8003400f240507140000801f1408040c000301c020b8801e4000344070503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 208625737 1250 208624487 208624499
    0xe0f0c041109011107030b0103061d070f0b160b01080a050d030207020f010c0f0b01170d091d09120f030601090806060108040201050a022b020118080706020306060c0109030f09 77
    0xe00c0d103981c40403a141d4801e000c031a0382580100000f8035800032040440b0219903a0307454400001d0000c0c4c2c0140c4500d69907514500e8442e840015003004074626030001e0410b185401e0246890041d24815580780b09004070300304071072036015054000711540200c0c0c152000e5840e83c0c00c00e134940c602071004903013500c5a01c584422140c0240291075001d90001c04488124104200554030a8080d130b40840c0c051824100c24400501c100d4640c1c0c1c0607045140d9440c1414010f804941e1034003204900341c00c140324030050100000b100301c0c00c3c20140b2002d00740036407070b0340e03290300b800302d072911200d010b441c800c0c50f80103d103842a410f4400081d600c244026650b45101d5561380070015101e08066170001c2c0003814400029001d075020b00028041c0d100d05104035503e16041052210a801c4180011604003d1030300c0b00d640c00716030901500000d20b03c210704030001e401040d5503905081c410a00000c0a107900400080c890340d94050540e0082030f8164002d00801201c0e2400620201d10007a010010605680340031403a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 208626987 1250 208625737 208625741
    0xe150f0106080f04020d15020a020a020f0a14040f1b0507020a0b0304080904050c130b03100e0108062208070602090918030703030209040605060c0a0c0608070e220e0f0c04 75
    0x2d182081407503c02a2143d03001e000d41c0008983d02a00c070404004035409641c02c1a00c0103100d01c00c07195000e0074034803001e4030412442c0602c9003c100c0c42030b60001d500b40f15040d003182c12620740c0c50040314002400d0040701d04c2d0701d01030464003521040402e05904801d85854204c0700604080f0300c204c0e09005101d0f00c03a00180c0c1c05000c1138802401510003400b4050590400d0341c01140c2050f1569001d03401e00a01006c0460b0079505500009280c1074084184800505444401c90181c5801d2444080f030398104801c0d0b40e92600001e0101e004001070f0404a00b14030210a00840c0940c1c100002ea559106617080c00d40c0a54800c45009000c1c83d68a4009060202c6c0c0b0762030644240082805140f804140351022030294000302d44055002d943c40c0000144c90396000000d1211140380300182c030b4038041d68108cc40212881e90b00c10814400c1006c01c00c178035980d1100e070032001c54504462081400c880c0720000088010065050f00503907181407039140350b8084c00119074041410113001c4602420810040c081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 208628237 1250 208626987 208626991
    0x411030f070e130b07030b0d0602040f090f06060807050f040806010f05120105071407020307050a080604031d060a050319060b091e0a05040504020612251814040e150f010608 76
    0x841c5031180f001c6905107100707801071384008100412362880740c45107880c2c081c2280c2c4168000c10b6100e010b030108000042d040e0040300d5019094031420010a440d005025001280040c02c120401100003907450007200680c00360740181041e50202c0d00c413581c4907407901c1c103040124018684030340c4503c180c050040005006451060403281c0d2144e046400c400c0c0d001e100d07500403c1c4220703418040e1100111b07a60700c5080c5010000d0252100406103400d0030305024002070400c29040c984003000d008100899203510080710240c0d201303860310503903035640c1c0f11400b5045c00845a00180300343c1030010000b041c0e0414009001c2154040741c6e00c4500500c2c107000191282051920705800c407008507c100171a00d0070341d010a80c4280080d202c00e2074030380801c0140c64103003c11070f080f811100250b100822500090118000c2100007820000101100d10f05128080e8001c2e108441250a8910060403176454a4101c400221014422952071628441045940010486490034240284030000501c2886000d03828 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 208629487 1250 208628237 208628243
    0x50717060d120f03020403080304150b18040b070903060c09030c0b0c060411060c0d1110020a020604021201060b0a030f1116060e071d04050601060807090e0411030f070e13 75
    0xa40c0c030b040c040060795610182c03c03c000506500f0b0000001003140040150b100318451410780c982c103980700c00c2090807110081c2d03006010f11a0300303901203440c45a049445410940000a182d1180d861a808640c400003940000b0001f5040c4482a0740f042e40044000c02960b1007521146180d40c0c07200620202c0340909858042168406030100340800c1d14140c00302d11041014240500e03012004c4000c526243c2d0544c0c0b02000a00d5001c1c0400c0030702c005200020003420002c1d000e525102002c1402036880300003410182c072404c080c440c0e440e1400300941c4044000c1080920154480b000510050300800c00c16890103c6142440b00c02c10010000c24121501c902e0000d0b44000c54006a0b19500020100e03150140006c0c8941032002c500ca001a008180c004e00ca000003410035840e00b03280c500c0c01d00006030b1021b82405140c40500403c2c0d90460540010740f8408038030551140d03118140f08400c0c2595811954050041140300c01e960400819010240c0f01c158500007296104d0040031100c1051a00d005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 208630737 1250 208629487 208629503
    0xe0c0402090d0f051006183206130614040b0405010305190611070c080c0102060606031909140304031a0613020f0714030306010905061e0715050717060d 67
    0x80081c90f030702c0b041018240a002220300038024040d40c03000702da169402c142c0d80400e1a4812030034094240c020211154141900c4240140d04107036819840076031520842c2000003107600180c4251913070452042078920a080070b0200c0c075503c03500c0d410500803004c4024012424030300c0e60041c0f428140038050480b07502c14010800c02c500d003000a0241242110101e83c10b945540e6005041c0b4560009444070030b014010180301c3e00d182440741850125440005410754020004000c2c1640d0381000740d03036201c21620700e40c0c444c000c599240c0c44000c0004180080205a44e0840b043c5c01001c000090410349104108030244280c1c0c80202644ad404211070582c3d0200c0413600c40b40b020402e90f000303400b001031039011040c10150640d68881ea1b0311081103100b1032542c40841007101c40c0d83e202000310010501690072529011451110030401002c01c6400303003081000090103010400928184034649074800740070011410513090007061040c50350701007548804a040407441e035180c0000c0e1024466489008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 208631987 1250 208630737 208630759
    0x90f03061003030503190c0206060a080c011d011407110f01020a050c100e0315040b070c02060d11070f0f0605180c10050d06060302130603110d02030402060409020403060e0c040209 79
    0x444131588000c0c4240707075034010703074a000e0b83c00302460044072001480c9401400d403e03d482c0c81801041d40107030344101101e40c0f182d5880001640c202409600c03808400e5030314505118404016510500c0a40c0b180ca09024006001d10034000000c0d209114000b044801c45510b8442000480c0c2c2e4020740c900140298212403d07000c6c0d185401003141609524604210080654000001342041807003203040440613000300070041044109290107610003514100702060a45507000b042d241d000342074810310202d540e94151341400032404152424213130700020381146900d0903d004105140544000c98225041c04c0c0800e0740c00451403122042d10703180c40c005110001078a000c0001413003010b100a000d020b402c110140000da03090240c88081d04241d01d000d6900c1c0c818010344003680c1200d910010416150105402c00300c3c10400481d1211300301c88070050303165203d600020f0080d2080c0da01030340c505480094000b040207030582200004000d410113846c070740000203040c08142c0c861590100e50120400d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 208633093 1106 208631987 208631993
    0x10602030a0806010f02070501031e11071b1202060304030e100323070906050a27030201081b0409020c0c06040303030506091602070504020a020f060408090f03061003 73
    0x10304150104041c0e217000307440360494041d00703041649884643c1c4070700076100c900355034481081d101048044465052910150b00c060000c072410181801501004800314000e501214a58141c1c100704542c40d80c200200c40e03000800450a012096034022020f4440c09840f0075050181e80300004c0210f4894000142c00103640308010640c1c820904000d0002d60000e60132084030500e042c03450f1030301e0700c5c50000d403050b01c03603040703810000c03071481d0049c0c2e0a131100807000e00201e9000fa26003454a445424031003040e500080004030703c0b48410002000b410003181d0007015003400c00c4040e0341d16500d1540c0000d01c48e034090b900560000b6100c00c01d020140c541080e8a0341c10680030415000041c80d0000065100c9140740306140c0303d203a0110f081003640e030092004c078032811515402d4031028903040c03034100000c0c0c0200c035403507000d48020442c9241d68200012020f00811003915620f004500d156 = true := by decide +kernel

theorem cover : BRFrame.Cov 208453237 208633093 := by
  have h0 := BRFrame.cov_init 208453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 208453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 208453237 ≤ n) (h2 : n < 208633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
