-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4338
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:17:46.023072+00:00
-- url     : https://prove2.me/submissions/3de6c90f-b6f4-4aff-8b4f-68a9ed0d70fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 780035971 ≤ n < 780215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 780037221 1250 780035971 780035989
    0x9031504140d140c0a080307121b0f11121606141603150302040e030a1e0c0f03020a0f030e0f0406051c060b040608071d010608070c02180f0105 63
    0x54240064008121002c070024024940c0000c03da4a9880001c0c1e444045a010018491000d0f0701100c0c0381e48901c0c0c100d0f00034084445075143c840010341440309040c2e0804c0310800b007092103c0e450305ca1034200c0c00c2415040300ca03500000304400540c4601c005044644000304040c000010f6544544a01000189032102c10fa80082c0c10000c1c0018055007400f08203004000141e400d0455440c0000e007611030807100044158480e131020790050314060708010443c0c0044000c040b401029151403040345114010402203d011a030814005103407601c005001030340e510780041056000744121100050180c950000e0303485105000c0f0089883c040c22145c1900b8404085000300c0c000b00d500700021450b000c0400c200705003451281104140c446000c00400c44030768004042403001500400c4141e454000d80ca43d181c12500030242030140201505240306070400c0a5416103110395185066500d0b170314419181590710100c00c90f1300001034105100c01d0000100d0262049050b600c7c0344056502d40024009281 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 780038471 1250 780037221 780037253
    0x409060b1e060702011202120403021b01171602070b030901051e1e0c0403051603051501120b130f12090b0a0815030a02030a03020303061e1f0509031504 67
    0x600001041c400b42d542c6010b807603d8980a0030220004941c1032581d400902c02c94504c240000740e402d09100c14580d0004e034059007008400e603000741d1944a81d00542d03a031154250085040d80703500000540300c0f00c1e8a41c48031780d0012140101d5801c251a030450b03524540040312209044c0c2e640c2c40c100402c01321010211a400f11420340c4000e054101142c0164000d1444c00300080c003858101e021490411425003100c008580240507103441032021402044070650512003982d1520a0704030187c0a6412000980c1c1207170824144030303000d40d5299552000756203000b03004d43c00101d00d0035080e10200d01c000e030b0a0000b4520581000045140f2008080c000c4031700c50b005096258020710803111100e810035202134014052001c0e40c841d5440100c0002e107400d52aa500039054060301404000301600003016501901088030b034ac4040c2c14409402c4500a11600450741d481049440480005070714580000603c0c5011701e04107142881440c003092426900406800582420381d040206001074010343e00318030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 780039721 1250 780038471 780038509
    0x904030e040615050a03091407090501030c0b0306030d0f140f0d0c02060603030a03050907120b07141213030c1e0302060a140c03091606111c0f030b0a050409060b 71
    0x440c415903c01000c500888003560285542c64135100140100501c50042ea9000e20048400c0952942d4902010b04400c2c03108a411100407507011401240c0390302501d2055801170700522020341018000c507035240046c42c0c0c020a0000000a4091000b000c40040c0305407814600d4865550600310200e41c00c6607103a40e071903821500300d0010b10129075004021103014507524a40130901d0f03140d8140c0c990074243c0650112801ca40c6001143c01040801040c15101d5031040c0c44107000010003810322484c03442105c41290303040b0300c0440011043c0001011000c0e403a402843c0c10070842c5801e541d0b80344ae0880c401c3c2c48140110058075000c04043d170409c0550b038000000300b014089180002d50151081a02030016820110040005000c2c8a0200481c8000004003400c0b501480c2c0d03038013005010f401d20200344806c10f000f210324901230710300d000e81500c1040c40141d403503070845a4442c204600074500b03860a560b200c0382e14800002e80e65213034021070240600901c13000880403130a03010042c0c411400c40c01d1401c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 780040971 1250 780039721 780039749
    0x70c0b15060d09031b030c0203072733091808030402091906030f0b09010903021b060d02210f010e04021905090f160e03060a09020d020904030e0406 65
    0x80d91600c005403a618181400302150461440c03600b511100448a8418030f850704960b100e406140d400134000000600940c01c1da00c100c0d454801b550b000382d89000c1402c1035002d080a02c0890345505a00440d03c41d5910384000711414050f00480131107501001e1044401003008505103c25001485842d440c4058080d12040d0141c0d41d50358000070303010050019204205030310003d40540e611010304804030030204d00070002c0c5030304e0b840c001d00c0308400d00800361945595900000e038880300c14454102401c3d0150014200c41480201002259140c10034207904440240000c2c0d054064034000340038520903103400d600c901c801c4d881d1050400d00c00108420200c8080340c00401400c011201c00e1a04030b501503a56004030100d0143e156040d1100c1d601441d0420310310804c014100301c110320341d140211003045048030550071100c812140f0703102150300d00f0b84c0f5421800204911030441c0d030200c4426440038041d00b02c00125a000640030040440e0144c1c0450b03200103100000340b4241c481d090183c4503000c0c0f4450 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 780042221 1250 780040971 780041011
    0xd020612012402070b07051f14150d260a1d0a1505090607080705030c100501230a030605070c1b0b04060810050a0602010c030f0507050702061c0203070c0b 68
    0xb566102605c900c1c004400d0000c0c1000511500384140740812a41001000e141c80c691480c110040444666008030f421110000c103030510404440c0310103c070340c02406a40920a07580300c41c900c95801104500413082c0d40c4800180c80500c03407020342b41140540d1030752200c4440008c0c0c520700c600c0041c10b5161003112044070510406100c0c01031020559001c0c076115884c0c161b0140461030910400001a010450115005080003800802004001003000a5510365410416043e09a0741d0078040e5194200071014081105003c290680c900340303e008040111003581c0340c640c0c208640040e19000b002400c0c8201e0001407000412880c2822203514050100c5a032038990796071450300440c020030081008100105008602c150b001401a050003445040c890303a172180041e0081502c440c00501080c101400c81018908510981d4801c00c60713921079915203000b6070b081005943c4206407440c03555000c4122942042e813648055441030784503468140c4641083e08020f02c80310742c024141a001ca5000000301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 780043471 1250 780042221 780042223
    0x901080c06040e1302041806150803030c07031808010b01020f0f120307020114010b0d0e07050609091e0106050304140c030703020103020f090d061a03060c03040b060d020612012402 79
    0x10103c5110b40c0c681d004684448404401201c034001c0065442070a2040305400c2c2c2e070052040c000002c3c403406042103c0180090740d003207194000d2280100e00d410a20006001c0015036004100041c400c0c504040340b100b4480400020f19200d03000324034280c1d035443c076403811560100040d18440c0d42500c02821600300211000b0340d14a01d40610b802c0f00c40c030120102d04542d000350400041c2140741200c2031119038440c1382d00100c0e600316180069110741498284d1400e6913010541d00140d41c170160100e442c204400040c400c07080c001a0103495120300f685050078480c0c40e12513066010700701c1560707101d03038070704040c1000700b2040486401c400644d00f0461141c24251340004a8100700c0e0303420b080168075405d40c83c20707030085401a0408550030140e61516901013050310b500c14000085100e08110b00103111809056031007404480c60003028000f00040f6000c25401c62a00b90701040c014215100040300b46d000c18250b800a655009200c40504d00502003000c078512103c5040c02900940090100c01003030003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 780044721 1250 780043471 780043477
    0x3030709171c170a0c02010c0309020303030a05040f0803070905012c090403051306050408070806010819150612020f030105090a240507110705030d1e0908010c030b0901080c06 77
    0x9048801c50511641c2542030141246405000403d0140f4041c1c0c03900c80490000307420f0507001000154071340b081d001c0e549400391064a0800d07401400039400d47d907840325400010034003d0002c0c6c1c1d030341b1075050303044000a86040046116120a03552a82200c1c85c01001404249886075403c90200712041d48aa031460418410024070303208403801c035101c0d01c031803c00750b0711803159821030035605070001c002007081c9400600420455009200300c680d141e0b907513070003991500400e010700f4031142c01000901100364a681d90344440030b0301410100d004481c0c610758010488405900030050000320130041010741c50f1001c0ca141e040b0030290020b01552405d101003035150107070440014090803088108128008003d00b05002500e01d582e0104081d04040f40c01404030001007107881c0d414410380801241034100401e2000c071080450310350101582d0314104a07100070940d40c0d0b010041010006001a070307107509014402c2c010180e518006100c09064050111a84058000260319030000c003840741c03681c58032811 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 780045971 1250 780044721 780044743
    0x30b040b06010c1e1407140d0302032206030b090903091c0c0b190e06070201030b0612240102060105031b010c08030f012607030b06040b09090303070917 67
    0x4040c0c216510800162032045003008090725140603840d450000d90304051554220314020b5072480c071042c42854031142d80da40341e401400e04041c01034014104605190250881e040e119005603401c10481c0b41c803c1090340f1544201c003003203080c2e40a0410205416101c0d41c1621001610001d145180594600d03907a4410043c805009040542c0c0603208404460401041243d000f10b0404ac01c554800c000ca11030740050f0300039040b003800d0018000c0b50a028000308001100041c000c030f800c104454005500600c0e42a00705600250104801c1e04041e112540c2c4610819010440340f1030445184140c0087d50b240d4161241907520000062006640c0083c104d1080c074004881c0c14040004100104c8040d00303201d100400488011050250911000207401d06070f030041030a0720b00321f0f40c200c42d040c4140c10100c01c090305c0c0c41e000f026050022a011040c1a0340c048405040468807084a40c046601c84108076000c5c2d400380c00220500c00b502d1b9010a0220080140707920b0015172800c0201101d44800c6c003451 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 780047221 1250 780045971 780045983
    0xf081902100c020303070c06020105180601050d06060321090503300f1b100507080417041203050d0c08040804290a05030406050108160e0901090519030e0a030b04 71
    0x640c22020700d100d240000b4410f81d02400340c1c0e40350651440d20050070b8803c4e02610025500700000503020305100c0000020703c4c00e203940240191f03441d10b4244003810541280584840e6101c05001c40460042d154a0007402100d111072050300c805410010018040c45d000395119400c84d502c400542500800003520a041c4416841000b012034044404103200e01251848142c401107036101540c181030b50b00f0b070103502a9109070382c1c8001d9034440c4039089400440340c0c000468402000f084c041021400300c2001074040c0039150340380544502000902d464801c60450005200161041c0000441d00506400955500f0407010b1414140e848002c01d00072400754012507443d00320504100c00c0300d03001c0b0301d840e0981c7d02c100566400070035200030b055600484064440c0c5003000000142c14100050b2800d40c011101a120501400c0c080210700e040f4002d00501540d640b1a200280803440a00c2100740040c0d60603030b02300b080c0c0500c0c5405860048080c403484d1081006450803c04191100c080644c0503901c29 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 780048471 1250 780047221 780047239
    0x213020f0a032c150a1103150d2301110901080c0d0219030504051905300a02150a0e0d0f03021204061d0c03030a0f050d11040f081902 59
    0x804120005000c101180c551111205a4071215804500e0202000200400e40030945c0c640258100b558044042524107500c10400078040d590a81c00702d0039400d0700201403e8000c601c1d51110a20200d105640445d04100c1e0000700340761890900c6500d40c00240381d40020704100c40500060031088009004103030a410028014000c050316504944005e000c0001c10020101c06220060090204580c215550312400b1000d2145114418a000f84558804010f00c1c2c0e0b05801a81ca8000381000e1803520b01d00c506a00b80c40c0014003841c3c002c1d0155003007070303030060000e401d00d41d5032030390799034009040c405c407540c039200810650b0038010a1102d41d2074410b0810070400e00e403402c4200c0007403080001c03101c6034100380c2d0184001c100c0c903908800010070458051050250303034034a8081e2144007c8502035415801005080342c1c1324001c503a0b5401d0a000d9080403030801004050540a0303851403020b0340c0303240f04005418805403c00141c0000a0944000240705041c0c202070b1103014803d004c0d4010303200e41050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 780049721 1250 780048471 780048491
    0x30c010e13050c04030309051e190306090803040605180309040c051204060902030f01060b04050d060204030212030304031d0315190212010f090e0715020a0206030f040213020f0a03 79
    0x1c1080c0e80c0800812040210f0718000b0306400254109000c104d002030742941000890346040d1500310101c10f80026502d000480b0709003041110000382d032002e01c141805c2180040803844520851171101e0048101960724a024900340044900050891880d114a07010b8064040c1d4000141e91590b6010303900054002c403441c0050b030b4680500315803e00c80030700c00e034100801c000e000d03007240c14514400e4040301c40c8135040003181070a0318114040d401490030305200810161600c202d00648240c000d00c00189041e0f120780226200920035038074442d02c0c4e80000306220800d5480761441500ba007014158071320b00c03210b0b10f0000713464414421f1780c1d0054602e1a4089102a05905901219110780d00011982c900014481e442840801d11a1540d144900766000541031028022000768490500240031842c0c00c000c8041074005148051404602c19600603100503118580118000c295101c121002440e2030b204001103c0c007031401c0070300803500600840300a00981800d031100b149080c10085550090 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 780050971 1250 780049721 780049729
    0x1b01060b160318061106250e120a030903120203030402060703030b150409090302010e010c050720090109060e0a09080a03181203020c070605091c080d1127030c010e 72
    0x42691106010b800d880700065401c0d0801440c5090f00c1c00d0000b0b80e42145d441f2880ca2040704101a200c621001304070103000074180c8540004402c843c0300400803544480100455403a10303801a500b1808100116402d109001705411070203d070181c0d51008624500d80b540c0807440c0c1d0b010b9400000c0900d0703291500480710781e68aa94170a0b0f09079500300d03040d231141d40c0c0e0b058900c058826284217801551820040d0030842106018884103001c1603140e891900c00e01d1b03618644840750445030015000c2c60a01d0b03049007560381080381c0307008080588010401e1381c10182c81c482d0f64403010342503083d010300c0d01d41c04400050250081da84064550305000542c005100302c0da02001d00415802040e0343c035401c02220f6469010340c00740140d0681401114003181e101c03003054035184901001d0715800600120540c0c3c5001821401c4607101d0700c0b513402c260815003110200800c1e1400e00004400c0c0c1000441c0f56003003802503554138140c20302c45d44940641001d130003010980b100128640da0f41001007121603e070054032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 780052221 1250 780050971 780050987
    0x11070303050d091e03030f0c0905090c070510050c04150305100e0622020705070803121b0d0c0306080c01050711041802030f0703120f080f18010207081b01060b1603 72
    0x1114007040c003542404c40c80c00030010300203404003106d1245071406d0400c145100341028070070740342d0190030300f8401d8490000c5500c3c207800c600c1c3c3c2150703a442191840c2c0d45441c03050284038000d00c04240c1c656110341c00d00100d420801d43c101032a0007010b20b01805c00100c1e070b0607082c44204464a1741070400c801c1d25500e000c01c0c41c9000999003141d152611001d9140e00203115402060307030320301800c1501c80c11030301d07071062980300d01c54846a500c080c0d00820120346030800c052511480035081840143c07400580e1030480080d2a280c602d5500070175550740d0104144002841518082402440c01c0740c90401c1c41e030f440c45060084c009040d4040c03a51000b500c2d544100701c401120310203800808450708258101b4207942e59001c00d010441b0440c0340284100c02540c0142e18020fa44519502c03602c4807540d4200c5a51031120005200012a0074040643d526a81003840202078040c01003601c80e503a034140745c0440c80654403900c201c440c2c581c50800d04020881603001620b040f92280002558480d030a81421540a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 780053471 1250 780052221 780052253
    0x140a27080706090312090315021612030906050f13030e030102070206070503250f060902212a09010b0d06090c0c020f19060f031104060f11070303050d09 67
    0x11141d400041101a0885025401c582c861200201c1c50107079000100c45c60300e401e2100030841e00c03000324901c00c0111241c024200b0102c0101500141801e0b94440c400d54090722140c09000c80d5803501c1034420b00c1081d018441d40190a02480050741c2020303507080310030f20003285003c1c4c2040341616100040d0faa080d0121140d464000340f43c1910741b0001d08049071680c2c0700e41b007207a4203100480140900c1c102c580f10154607840d0498001125005140c5455000d0301403007400b00d90000c01e0186014428403182e034405258a9600000c10100000403000d03142002c3c0c2003540800c0262020202141d0b90301d5041f43ca040d148055041510380805c41c000101a1001e80c008101c400d0520955601c1140d200350b40714202e038002c95410030400044000d0080401016107210001c81d2050010700100e4058610300700c01049502c0c0000348014030048040150300705420410021740200503400c9842c0c1d0185031143c400002e44060034266196070f8000e040c1d40718194001c0c1c4910788444004d4203018200944811207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 780054721 1250 780053471 780053473
    0x7050d08160c1109011508070c0803010506070503071203150b040326070609030f08060603040b01260f0d0e1f1b0503030906040204061703070206070f21140a2708 71
    0x141d61030b80c08081001c5444511b20001a070000001841c040c400c50000300001c1e00030740702c0f40c6035909200a000c0c41d50300c50320302642c0d148010440400001c0f2450804c0071001c886660002e83c010104000c9000c00c030403a0700400800c2070501091000c5412800c10020803048034182d10b2440c4041d0f000705009004155000c0c0015151407118418560041d06428520f4010340d181c000d26a100000c0200350f0005880c081c0083c0d440030010702010724010001c50b112042003012a58a0340c9900420345080615662107481e07402c443d41501050350483d4200080c180201c0e6a0449840101d0b40710020404219980040111a141c9103c5594100158214440d04074007500c1d075902e06400426995102a03d0890049240c1900001c030784000064004041c0080000b0354500380b00b6808220668202141c00d403800840041c07000000b40306142400410040901c000104215440010389001034442c0344440ca120100080026554404021a080e84450206011401c020405080f45102c560462865 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 780055971 1250 780054721 780054739
    0x30e0c0603090a0b01060f18060c14100f020904050604050435072411070b190c08041209050a0329090318060403050c15090a03030507050d08160c11 65
    0x4400ea0082e00c10301d900c00923807641420034401555041540c01c140c0b10f1000010600d1083c4800540000c49084100c5110740445031410180d12603d0202c488203030320710744866400250038070903090600959500c0b00381160108807914164445000b6215200c0001403c80c10396031104498004d9040e00b00030151301495900d40303498662502a54204c2d0482e900c9440e03140980030003074416424004d00081c03070112100c041c240312066a55008201020b0b103100d40528841c1c40b80240c641c4c3e0f40c07080000500d0955280304090820742401d25aa01c000100c032001c000c14a41c0600c500c0e212002ca01080342d034000c04141500c8920310701e14102a81810b03610005003407407400c1c0060741400002038203140108040d011007034103a110401c5120301c00e501c0010001c6e00b108005040074940314040c809074007000710711a072502d18168002405103849810440203d1000304080342805020885484440309904040b80d0900f04940880c0101166809140070484880415020010000702d2825a24009080c4000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 780057221 1250 780055971 780055979
    0xc1e032a1009150f11070812090a15021c1e0f021c020c121615091d040303050c1e0f160503030403082406160210120c030e0c0603090a0b01 61
    0xd00c03801d0a1300302c400500745107412600c540010440c1011110300d00020080083e442c200340d00d03d900080141a03200305c0c00d0100044a41c543c0c101c41509103242d5014025400c0c401003041c4400c89000100b1040121f105403900c803400e01d5040086103c900d5041c03900142003140b008900e000304022800e010080950b84a1068030740000c1d035629100d6084648840511078200250b41d210301c201200c041d005410f6500304114688261500b40c031384072a261024130952941c008450103000c0c100c0c002e0201303507500200000d0503407500c00d107a0800d031030304110b07882c20200100349180300c0600c035501025404002075591002101808507441030610001d190001055810019101d4200329020750200300c511000a01d0603018101d864120941e8480c403820f800190014464603411a00c400c40d1401800c14500b00503035a01182c56595408a507141540c240140c0c0100c2c080d20b4020300c14070107060030b195010700700c42d06c00700303a40800713031401d41d1210707269030b1108201854600028800381003280300a00100e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 780058471 1250 780057221 780057227
    0xf180207021c020901061403040605040317010f060806120c040f0605030f070e070903050601030b130816050705030c0f090a02131d010e0c0304080703020c1e032a100915 74
    0x181a0f000700c540c0d10441e070781c40b281034030604042012a03131980c50400024000501a62040390403502a19000c84002d50205140c543c401c400c1c0c03c400d07400741019034100041075200c0c0400358005000d840340c0c071000da80c0c5410140d8880c10940301501c9103403600068030b0326900c0c1c0e502140c0101402811111162402020f180c0ca640481c0142032601c06440c0003d00e080d40250802002c483d402002072a09030301e561103100340304501404080c4d48402ca80e420802094a0002400c0300414015601c00319030b84511340780d4a480b0603507002078041d0300720a070000c400e42d43d00340032041d00f42003e840959940d5940401e6100901c22a9500051000c517441c0118060a00010300510f1440d540042010759072900304080704c1e07805c100c454000e2044200009400a000c4034090040e0364030a004484800c001c50001070004041c4c0e410001c0d40301810010b445103840e00700302146030f2070348104900447d02c2149009401003030000c20141d00400381c240d08100c080744035011440080101c030038482e002031100c2e0402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 780059721 1250 780058471 780058519
    0xa06110403051612080c03130f0e18030f0702010504030b01060804021302030f0a09080c0f0f1b0901050607020a0914160e0d200307240203040f18020702 67
    0x540b1a480303003040d030307500d00e1060341d000d5015941c003082a0b89801c100c0e0b5503044000d0707105980b0700403107000602001c0c640c01e4072040703800090315020025101031424040040000000104004030700501b0308a141040000441150103c140030120b02d50355106034001611a0300c5251309c0200030341c0e8028000a0034035800b00e80daa020352300c220340d0103014000c4e09880b5030583c0000e403100d2442c048054082003007000c203684000d190510074181039040c45140d41d111820701070003400640c03a40d000b45510341034045041c016000d4000d604c4120880100c184000b20780400c50501a440c01072a0005140d400d41d51946e50a00003828594414040f1800d40000044071190a4ce601c1d140c400020400f5401140070314120844010043c00c09d100c2e240080d10b9030500c0d01c1c003c0214268101e60320324214031548083c0410006040e500e500d0030015940c51824961610149411360210340081c03005002c03621700d060700a011581d488080f11480d42c2d000410138024420407e0084d0b0080d140c3c0707010807402c400e803010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 780060971 1250 780059721 780059723
    0x1103040306140106140307080a18150e0d0e0609121002090a120506060f060c01020c060603061e0c130f2301081909050307121215050105070605090a06110403 69
    0x560301c06036039409045d11402c6290160100c07000d07080c00011405440b80b4103556012000e807802189600c040280c54000d216414015641c1000010f4890030b0794615010f505075240110703004160000716254010b00e003a041c42c90300341c400e80c0005444045035071b42c1c150072525488501c06440d9940329a0380342c0c00c001e501c410406c038015100b0300d0000400040b1604481241c2c0d41040180185981d000c0c2085140300d600d00032181d012405000700502481c091010f070650307007000c000602250a0a0b0101072414400030302e05d10000c141407201071001c03503031072034400e8000440c03143c49900da240e81481e00602481e00d80001b13540512402c0005444801038401d8010403400d421213500401e10900111510307503003210000039500c04503001200c440c0465002031500d50080c81a681401001d03582c000c03500c006115114002185c410a032010b40d1460310412016a405c1241d004002d0b2030100003802e20302844402512542e51b90780001d070801c10511001000d15800081040a410030310345040c0c981d001800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 780062221 1250 780060971 780061001
    0x310052224050301051909062009010e040603170a02070317030105090a06051c240219050307020a0b061807120608071206050907031b151b121103040306 67
    0x140020b0142418400c0c507008100301c2000c2c1001050b00900f80c0040c00d080042122070980c0c40e070901e814842c20b03026070107214079642e401c10b40c0e82042c880010010407900302d01c1d034403440c544402000040c40c2c2003070304108603101c83c941e25200d4a50400c140e0414070f041c0d0004d01035607007450364010403882000096050f0f440032284070240d42ca0b80010007044680c58021a6080300b16080600c0661080741c10751003c10388201c40010080710003038000b8520700305400d000a8000c1d0007040700700a000300142d104010211910b407841c00c515262400070342c0c1d49881c7c00c1c05865010703200c004c1107098849205410325041c94008855642c01d148400415240c034111038801c1c0c251a1110128500c0d07000b01d00b1104030760b20216850145c40c00358589a0091902410801140c85449800800914500c2200d454110f00ca100000c12524200303010070500b030103003042030402c6000c0c001c0c0c154602c0c200000b11800360b040758808050000c56403050301c4030355142c84100d889110209001042001503004080700d0b0310303446 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 780063471 1250 780062221 780062291
    0x8210c06040f1202030a080105011b15020702041b050403150204120506060102060a0b09061504050d05010902040f06050913230105220b28021909050603100522 70
    0x19804c076100d004152402001403411001000a5885600d200200b544034001c40c00100c40195240004048410030b151503107600403404000b0f52400b07200d855800c4019840060141d05401001010b0b8071076808020201e004201c01102d1424095041d0740181038103281011b4070004600300190f0341d140448020340184141000600c03260610f00804880c1800a0403042403074907080200007a80c50324030001d125400090cc00080c29a035030000b44501c03a400388000041d1040640180400e9034212203e6008260914004202c40d4540041140d4425104601e00094190342d00d000100d010400c109183d9094603004442751001042d4070243c041d2502881810031010b041c1d032a081c0d0228a0300c0c02a007002640f60008080c0c2901c210110360051150040034850410540f030502240c20201c421440840c00700c0b00554120381041c01400608821110941540b801c0491000081024010940100101680500290307403010110710819090401444803d055421580540320102c2901103044910 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 780064721 1250 780063471 780063503
    0x190c090e0133020d0509040902030a0f06200301180e0601061710080327150d05101a0c010f0609020a080f040f060902030c1518060408210c06040f 64
    0x189400064002c0d40180c10034020300e00c030540700c982015004541054564181702d005940602c80b1703070246441220200402581404e00c1e00440c0d180d400b281c80c5400075a0f48030740340391070b60034140c81c11072301c0c0350a10310800612111440701421440c20904150312482e4004110907400c81003040340c801407840300b0a03280e5901540140130134040d01c9420b1aa41040011104003440b940103941d02a480c600710a0204600801050707040e02507481003850700038049100002001c403801056000a689a1805882c60816015030810341e00d0f13040d04041c0040000b140c81c050034080d0403540c40703040452000c0081ca580c0f049004043d510007520300300003c1c041c800040c0c0e0003403a4182079002e113811455000300300b20285d41d8100105899a01668140b0920460b021559141007405110078160000c03903884400f00442084980354510125206000c288424041c000d070000e41186240ea00c1c0d00b1002104451f0805040988600519440c90780108007c100c01d2103020b148108010340306030f111010074649 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 780065971 1250 780064721 780064799
    0x1e0f300313020409080403170304060b01030b0906193302120f090a05031009060c1103191103040f060f09030f0b09030906070b040c0608190c090e01 65
    0x85448040c0e07420307032480010160034a0790228901d640303e062a1454182c49031100c04c450050001001d02e8500300004100420400380500302d1020703003c1c00c1c00e008000c000c40000e207507200b001780303118041e0b603116180070305540404200c030f0010702480400400035020910340c81036010700301919104203070051000342141d034800038508540f01071400b205401c200400404002a50148080c2d5a00032625030002c10a0f9a05220200b00210703890800500b090880c0741810039144030501e4041840051140c15044141c04800c40e02c01c50018140040030700300b01c520540b41c1c26072014902c0748031701c03000c14041908400170000c441500c000b0b0322042c121a0301060b040314141c1081c00024038901d5030b80c90740400503c800d0792090b001200782044d6810700f0403c071301003000c2e5082540180c0d000400c03001444103100700704c0c010740080d20440c17515090302c0c030b0007103001c2c0290034403910301400550b0365004c5800101d102e12040005000703917811600c09035959061003903514148614060081d01429500400001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 780067221 1250 780065971 780065977
    0xd0c0339080907090902030703060617010b040614040504020a0e01081b030c010509090a14130201120c08070810080601060e1f091211040906140f0403021e0f30 70
    0x3910310001c0c401582000440e402601c174081e001c83c0c041c4144503001c000900035020f05005048a0380e00c01e50800c020318541401c1d55401d000352405585802400c0c00200c00503089009007900c26034010070307103840b0742c03001c41c032440043e0340071883c4550610008214101c1c0441c1b506015108400d507040451951802c254072944140c00346408036004014401d5107080070750f241c650144280b580090000e0905060041903002101e0350103600b48019940070443d0b8020a90403280a42c40070b04218003015030308013800c80a4003609250a01c40411b0001d25921350468080000d40b90034025901656036800340904110310607524248102e0b104001d82c2400c1c0f514140c00000186103070340d80d840c958a400e2001d4007503100c0985c00d89074581e0311202510117440e0b500505026511030700001507020400004213040200113001c40f20b00c00c7e400c01c24000402d500007181c1401c00440c40101410040c8052094a0800101c0c141c0105000c0e0622600040f6a032890301c50f0306202408803900600011a6214005d02c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 780068471 1250 780067221 780067231
    0x20d09050607020904060e060115091e090207021507051005011202010212030a020d02130623041a0c101a060a09141903060b01140f0d0c033908 63
    0x207141030051201614149001c550001c0c010900090319801c04c980c035a0504034241c00c03902d07920480740c214800282d444544031004045014514800c03501c2c804da01002c041702441181c2c006070300843c01c0400c0d946c03500840148001e035892002c2d9100c0c03580c0b50030303078444441c8103d4041140c6040d0001509000c049204108540d05038040c00a00000800e400000c0d04060403080207e81e017484008554002840108001d10241c0310b08240305103094401804581d02d01d8014621400d000000c01142c40104181e80a64a500817003038400000000900180e01541081d0b180c0d511440c014960a11425482031020000d002c0f0501588044442402000c0c800c1c45d0540b000206249001c11450b003044054100011005007a400360380303c2400c410542d0201134101341e07411980d5800011140d038015400c0c00c0011900150207041c42c840c0e8180f030b00c5900441251540e041d4660715a001054440c1d4080200c0e00c5c01c0c86001204400640359684100709412004800f000202d04d11185041c040c0c0c086500ca1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 780069721 1250 780068471 780068479
    0x30b210604151b02060a0501080102040b0f0a0e060409051503010506060406110a06020c0f0c03120702010e0a0e1003060e1c11030d021c0f0b010e0f0a0e0a0b01020d0905 74
    0xc0c0d1520350b18001088541450340c0102903644243c00350424020807420602c803041c2d4010300c12818100071b14802c481c0107034841c00b01a8030400040007458101c20540c4c1e0060b40314000e042d1103180d1020242ca900c0b080803941540800000340c0416401030940c001c0b400344222034010466102c0785420706088400660b01660322010503c001c0102a205120001d0706444503403ea4500c480517507150000d9030444082c120790f68000b0043e292803000b08010001e11504120000c0014955102c03c04030700348100040039040004080140d90b4607241c02c10a5001454549a805805d14103d000300c2544441030000700c40381410a0f461070302940c00010701010601041103100320443c8842c00640f0542c501e1264088140418451078503104440d20140c0020100d0b9611031741d07100c84900340d80f001c480305041d44078602464084050001c4c1d0b40302e0a80c80c0d0043c4107588000d11410f1040014602064940c01a07094042d00c80801004a24681200e0704803142a02261041390b110300c81960f04201c280521900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 780070971 1250 780069721 780069733
    0x18090201051621030c08090d2f0a060501060f0e03100203041a07030921080114210309090108060c07020418020306090f1e06010b070201031b030b21 65
    0x118420b8102d001485445412184403da0000c0710700840d41861251075008255652018414160020310007644190342001803e10180c00001c060a2401e144c0c2d142021941740003c140c41e80c500700058a04001d00e82c40842d8000e00846c540307a0060a001d0140c0c00010301d120841c03e24060180004c400c03c2c00009000d000440040c08152009410003402510010f0403507610280d020801c603843d80c01225550340100b00c10341350b400e00c8481d030100d4915160840d0307440e580c0390810310707403120400d070550b04100b11040710200c1c074000090384020b5601e65400000742459104000302c10000c01403085100c02d580f4070200381c0e0307251a1292500b500722121511170108115000061403c6c2c4e105007070f101c601e500483d4052030a5008603161100c12220030b80705512464052040500402c00484005100d100b0048071585803082d440c2c079102d040c85501042071002c01c00383c046a000b50080282c80222240300c001141006000601a2240038007050041c0107181d801d406040c940101c00c1c80394035a42d401001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 780072221 1250 780070971 780070987
    0x803041d06031e240420030f100609051f03110616030201051b2505150f0103110d0309030344220206030403180b041809020105 56
    0x100600c00400107541401403640385021448402e1034282c2440091004214445496001040c850044445014251442420000007501c0a0707009580741d02048000b101000c034000100707142914510140c00ca600644003201180100c59101e1800c80d11354040c18055516081e22020203030306200310030489410403000c00d00105071a601140c4c05104054541450074080c83c00214021004102c200c00503515901071000307042c0c0560881198014090300705151515851340b4030451042d90f004505c0c5a0066109038040c06001d204c461040301503650111420302c0c110041c0c1104000901088411946800d02c03264541004035002e00780650545603400c01a00b50b84040e20f040d030960420b5105e080d42c0c400394501886040d0700d101c082c0240500030300b1b001c1320f105894100c2800d0082c0201000700d1040501c400018085802a400a405590442c0d594035207040031501d1010716a02a901c00d240c0c40400901078080740010b00c00c444440136515007150400c5405030a8500324030010780040c100344030400d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 780073471 1250 780072221 780072269
    0x70b040f03080f0f0f12070e0a150e030102340803010905060f10021e06160c05190305030a0e010509060a0b01020a0f08030105041b02120702010311031906080304 71
    0x3140780d0f0243e1210f03074107049402c0954615948441010a44081d0101360a107989400d16691500710900d410000005850711010400038502c500c00c024202050803e01c107011800f8070b82000b8002d80c0a00250340c3c8440c01008484048013000e0000b2181040045a8a40c020111500c0000e03030360010409146074605054240584000b07081c490307220b5101c18288201c2d07910700000100004054016040c0c0d170038404910b582c4144485507584580e0015810000c4108203908441c06104407400d05405c800b0450900c2072a203005840d040640048003c5040b040c90703006000b0350322405000c00300b03104290890000c3c9080e68401e031180c103090381c80f91b0042a620040c031741048040a4041c4100d8140b518140c450b880c480038035071000e4a81920000040c44076081034000c0032034072000079100386a111070704d0000954a07000020190491007000c40c0e03480440e0300c607820260812200c00c440c2502d9050107140e40c03007482410700c0c0708014986000c900280544010056408450f440084240f102e541c0d2384900c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 780074721 1250 780073471 780073477
    0x140d0b0a23030616142106030c0415030b0c04230405070c03020a02150c0106141302090a030f0f02060304060506040605010306050a0905180102040b0a172809140a0203070b040f0308 79
    0x90f035149101130141c8031481100c084086854903c1b6400883d060500d00c041c14100482c105180740610305101d6001d00b0750729180d0a82c01200d51001480c02c80c2d81c1e0700e011070105070056811000755621211804507a0018510700320100d204110340411240d1034613030003550203103280e010040241c0c0054804d2070161601245009400302c03031a0256142c0b41b4903d1200b0708580306a04504034100008082c603150341462560075814500441c0b046144c03002c1000002d00114107480300030a0426458408010403110100341c0c00700c6507024160507264280341c50000007914040344c03424055860b05600040b2913109008000854102034061035001303042c039134260701401001346030040c035418014a017034800000b44014401130031900344094441c099020028548608805403058a50003c0140b03d6a42082003903500742090307030003c85103070034100038110c805400300d03140180600c2c401c8520b60a0340c0170086903a2040d507108405a50304603886043c62101070240f4025a118020310800500c0000d01c0303d002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 780075971 1250 780074721 780074747
    0x90c09010c080a030603110301060b030121050615190e070302090a081204050a08010b1309020d0f1b2106200325030c140d0b0a23030616 60
    0xc1d28464490b01c03620190ba00500d071103400030f81d5500c0c0400074407004002191540408034001c1c40250300d00201404c450006001d6100320440340c81c1c40c8503640308005016100f080c0d200302030360403510300030350541070110180010900400d0b030300321285002050000588160f8072800070305044c580720001c0440081d00100641600000c0e9020041a020000c024403800c0c1c24840e081c035650349040600b8491a1545a40000f803e170303050212401c220783c0ea4080304103e8450b110b00c0040c010b4040d0001480b00b51403008040c3c01c0b200191a41c009100890380c1c00b0219602c41c85408840a50790741160444180d1184018a03007541a5540e07400105160001c010451214290510026103020050250b90055511004079140103540c000300c1103e007100a928000581010413214641d441c010304071041c001800e028003d40065464001c0035980e110950001010b0001c400098a40c64000301d4426050710112150115003220703115440c000a00e6072181141c15826940c006c01001c007a2002000003c07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 780077221 1250 780075971 780075977
    0x2070e06041e1a092505070c03020d030504090203191a06030402090406090c090207030905040608031210090903021b060a050d020307090e07120e060c0720221a090c0901 74
    0x48900081d9240c84d065401921443c41c01d0380400321142d500081d1084441c215010b010301444081e000c00e441d1403818088980584001c1c2c410160b500d0200c07058412a04030749030003403020080c00200442d06826140c280f401c0c05c0200f04d00340c0c01507083c2501e0420b96090903845001000020b006080c011503081e0414816103010074030a2195598001141c0c9540150122550102d182e400380760780040402d00030b10007900c0802055043c002170a49a05c5564603100c044180707440031684400e0040d400c180140b0030004100040c000c540b070000c1d00c4103824000c0d21011152407140c01264130f4a4002c988081d07a55403111868504140000c1000c1d40005000c0002c3c849883c1c800610b882d0b48400c1903104000302c0d0f0f100203a924000369103000300c80c0d07800c0b592015941b080041005003841c0300221260746400c410810f007601c41904414601c0c14110700641d420003c1c04410b156056190a40144040324100701032041941c001d40c003000280c854005140d21041010116500403082e100908064074189 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 780078471 1250 780077221 780077261
    0x1b0f03030f07260a090e0403020a12170a02040509190b0d0b0a0c02120d1a030715020d020c1003051e0114030c04091208090304030f0302070e06041e 65
    0x1a0104070280c0100d8810b5070060b41c1229011030020620800d07403421091440c04900748514100001d1079180a40200c03034050300990081001e05000300160612a030344007800d00d4515030403c0c4000c01c03040c03e03842e541003950384e0740010600310040ea0080d030b400e8410140c1041a10b58840c40301c0e10b1025010404a08000d46da07140d1007034030340c070b07005034210105006c1c5810f89010f0600480080c201c40b00900f800e002c40d0448260495001615401c03101c1e4000c031503078082015402c10401c2c20581003030404003035044c40764407000074440c111100320135001a590340030b50340e04003001401a0b8407080200714865000f403e800e008120240070340d00181d000000140000340d188890846c204c1e10f014280c010f1160046280c0c451001407604004441003408161400d10503102955200b0804e041002041800e00c000c1c2000199a280704005a074011500800030304010002c41c10081d460f0400d42c000c00e90709406440c009052820140616072515500c4001d2a0042010421040c01000f000b81d45103e014580 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 780079721 1250 780078471 780078487
    0x10f1107030c1805061c0312060e060a05040e06240301050a0c030507020d0915030b040c0201090b01081501090b01030b032b0f02030d0e010216110a05041e0f090605150306091b0f0303 80
    0x40d00c1404042c02c515030928550341402f40402083e4010791f0b0010744038904022115003804004281c2c140c00004d85074001602010406542094a5140e40004d81640c0b03010208224000c40750010201107005803410000e5883c1c0503012a25481e0058103a404943c901004200030f0301640c4d0321071014041c40c6400241c900402001400791803105103003100507034650321440d00b03000c0c4240f0910b00400b851070003081c5030700c03c15000001618051091282c06541d80d44e802201d0f034002c2d0000e41d8032502c01010780d80040314a141c181c0f03020718444450b100411240e403c0f5100790f800343e098140210b030f464000b1810520190f0300c00d4064070401c0000c01d050f54082c0705401301742d0705d80950720102ca8802d648801c0c1d448a04024424a440a46e0082d0320660038903640c146199105640e4800326911280041114041410382c840540b00c1c3c40c20041015142c40c01b0000900850f02600d20f40b600110165401a141d240400e0750380c175110302c0341d58600612a0f00305401c078074044004445040014003500d081c0009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 780080971 1250 780079721 780079757
    0xb030901180317160c030e0a050402160c061b02060d1d07061407020a03020904030306120f020108060f010801090b131a03101a010f1107030c1805061c03 67
    0x30010044012481d5038007404110f01400944562241d0014411034101c903520800616550303e600d000f40038481407101001450710f94920080140101a10656a800b1445000d4244c1240850291030b544003440b40400c40610410311442d0000344050540d96440c4c95030200021070b031020f020300c490103a8510104201c1502c400c04806e2a01450000c0c02000e4074202c0d014103110b0940c429040c44400400088006035202443d03501034039016188180e5554481c9015401080203402c80c010096090541d8010841c1c404101d20f102c40c801e80e07039104540c40c0d08092000c2c1c503158554841c08244c2203801070004040d075500c4140c0401005025003680c01c40207040404640c83c5840d80014081d00000890203800d08001700c1207404ad4600003049002248841c5184070036445600a0400c00f011011078503407031003003044c1143c0c00700d250b0a99101560303d240042c084c2c1a42d12940c0d0440d02c4805520070300c11254403400d0b10a1070003800307104c410360144504d00882c252654048051290b04076490100b166 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 780082221 1250 780080971 780081011
    0x1509051519051b0714060405030d061422090209090c12060c03040602091f0306030b100815042f0f040606020c010e0303040512010f150602070b030901 66
    0x150100351050541001c1d410702408040d0200200c001e142080b050001141c098003000c0d8084088030300d041c0d1204081d1410802090001c800821144290310a001c203020b408001031070724480008040203080e65034100291280d48807052035902c1340303a0300c1080144225000034441c103002502000a41100c0c10307400a0500e0600f0303210440550700814610009040c8500d402d20f44140480041000d4a480a11405c007840000c1008080c2900800c030f004281e02c407500c92501c00c191003400b450800506200080060540303100c05e844102142e40440e00341101d182003d41590341490103030108044809114041c0398000d0000c940308404031408850064154110030310040c1a4410480c601c8030035030400a00000202c100c61043e86000c0d000c110705500003e4000c115002802c00c0d03180700759007500080c25030040b0340c405504141e40e100381510b0105c0c1980300030012142060708010071313681c803141c0080c4e910141c000c0344003607805075a040c1310803600c0901450780030171120004503213150980c500000301e103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 780083471 1250 780082221 780082243
    0x14060901030e0705060714060705090607030302160c0806070825050f280f020c0a0608040c051e24030103230102070f030809060f01060c0f14070f080105090307150905 73
    0x14001d20010840d00303805000c42500710380d403468001d040be10404001380309442515801002d150780050f6150326201c1140c03a80c1c400e01e4000b1340c1000d00d141d8540542e5144d10f4101e50700e43c0000c840800103500c194203001c07424029a100c61103000c00340d5030004203854580c45003c8200b065130041c041281440041c0c609000143d88800091440042d51880607108205074505107007990001800101c0c5500d42d030240d441201d00620349928207846905204207019001d8200580110801210503d40c4292240c420711050301620800b2402d0b14002410b5800c9808540100000c00200010400300e00400d05400c0030010340301420f1100b0120101490880e4014030084a080c400314603613405141e0410030907544450b01a0180c070b0186003105400440d49030500074041403001214001082c0208034600c1e17031109500000d02c0005203141d82441d55209001e1042e0440c1d800b9000d4042820141030241d6402303080a0401513041c010789503500045124040040411035550750b25100c04030b034041203803401c08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 780084721 1250 780083471 780083483
    0x3050913020f03390702210a14240a050912071b090e06040b15030106081c3e1c0908010207020102100b0d050d120614060901030e07050607 61
    0xc0760310134114160380b06800c00404840058501e8205a01618101c8451541c1141c01c248400e03070651402c01c00c2c2d040d5001c1c1081d1407241c0c02120080002d01c2001714003041c040000c64a11540c0f1090107075940030881c0c00600c4505210001c035620144c030782c00039a044a040400e490090320440b03101801e60308050340a83d00600090ba903040c0700b422002076403010307042070b03201030100500c03414110b581d031913010300000c2c032036000b0000145060201005650f6481c0340100240400380e85c600e10581c0c2d40a60f2100010300381071840c0002c282d140100c0c00804a0361006804400b5900c00081440c4489081e03143e120900b008031904040c2c583c400e000c040e104800444100055640346030004106174000d800010b020781c1704011802c05070b03800080620f042c040341c14000c5109800800410104860309100800602c43c0416081409802c080a0300c3d180d40400c008200c0b1a55135030300c60120200803906075401c11000c001c40d550651294002d64a843d0824044a200e03907628408034080341e01c400e0060f125 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 780085971 1250 780084721 780084751
    0x615050904030c1a0606071115300601020d0f050409020c0303180708071a0d0203091005060a0302010903021c050d09030201110109050303060603090c0411030711060403050913020f03 80
    0x40001183c60130390000c0401003e140541341c50310209090344a40000a45190700c2c4012924107a911020040c0d4580341e039001654441410ba100e001905050814050700c5a0341c60f15070000001c403400500384907400503130060205c010102001d484a0004100e03034010080300b00004200010940000e194003000c0c03500842c0d481c5404607001d0040c40c80410000481c3d040303035200f00844d020002d400c00a44400001c0b002d80803140c0c40191207076201d010840e09000e400482001007003040484c1100c1040315002c4207012942d144410492202d5990000a0214028560a0001d4103142072100c2e1030b2035000e001c8080000454072820714103110044040000780f10340c2820301c21540d1110102000700e481800038001c000c3c40c0d550b21501c0c0d0200070105405150017100090504c5401c0044606000c809002000fa00140c3d03248074100d64012520200841c034001c0700f8403800c010014480e03201c0d43d0507a5507507041c002c0780d201b003228050312140d1040e81d0640134050801d80d442450b009600600d200601d10360 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 780087221 1250 780085971 780085973
    0x801020a080109180b071d042a051e09063108061515070804090510121a090a06050c22080703030309020402070524060307120615050904030c 62
    0x20580744000e24510b440030084c41601c0000344101c0501c1e0700020386040c0016400c881303601ca46043c003921170b00c0350750040c1044d8850704100c500190500507482012a40c5c0321030485000f042d43c20744100010044c064400460544240b24110054100c1a00041c00c0e0303407400382d80d242840101c544201c4201c0d00b00ba000121a000a4441890b41c00141504000703854545400419000b5001c01c40801e40d001c2d91280c203880c001444d1403c1210940b50b40039080c0d5840b42d4940050314000c0004683d40b454240070310001051418001c01c007001580c4d40101000fa0030000155803540080c000350400c1c009201d42e040c00300010b40d0a00405204100e0a00b445841d8103250801440c01c4030b10f00000301c80c0c00c0a054062102c0440460400f050329058240440c00070401d02c0464000e100d02100a41b40f409214014180c00c2c07008074000181800c469950b1502c1c2e1507a604054a40304103206804008012a020320009126504800e030003514045642d141682c0c2c41020410341c52048400314009120024008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 780088471 1250 780087221 780087239
    0x2d0712211a150304020f06041a0a0813020303071511040b0c10270f3005340b0412080a0b090c07050717010e0c0402070305040e100801020a0801 63
    0x22003086022140346a1071520000d00007400d01c009000680141c0c0c510074821b605071100c404940041000c00d0741503003501c01c0b1940135060b942260944a0020b2000b9000c500000c9070110140070080d0020051032a1085a98540d40f06010110340c50101c1a22440022400070394203015100800c0f0018036a42d45001c40000c0b0740c02c00b1901c0000034207003880d014019900d5112540c1d041c9454042c0000c40c00081c0035824103002822610350000e186040c07103044541d050a84280c410601440700007800500d086402c01503515001e844021007002c80100490646072480c01220701d80b0041c0d5580c0c09450760101e8880003241207048a0955801c0c2085100b030815580c000c0300705501040b90780c01002800103540c000388061302c0190150002c100007207a010144582400f4150042403420308076800ca0a030707004100c2c080c04280d0b200141a0140e0100c1000c603040c0350003203480d080d034142d46140c5001d0030032054131403080000d00703684180c3c0820780c00468050b0092006040c0b44810b5110000c2a614064105c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 780089721 1250 780088471 780088511
    0x5030f100b04180b04030201140109140f04080a0f09030507120b01080309030703030f02010e0a030f02010c05130b0a02160e040605090c010f0e03010902060d022d071221 74
    0x2180900c3c60300604190382e5a44800c0e0b1420183e00c10b880e48141d49403410224003404c01c00074400c04e002c241500020340f51a0031340c0101c081024010714a8010355904030711240c1ca4800301c602a210050410501408611818024048600b07d0601c005881c0e01c0362202c504d00342d801d420401e0b0f480b8042000c1001c0c080e088082c0303401012b0400003107182200034804251552590301c0020240002c0205240400d4001c0d00200c4207604240103c0c0d00e03061160400902000c8080111009540f034542a1a00c0c50310481c126840e004207003084402551415041d0b10b0b4517408181d1440850081200c0d207201c00c2044014900100000f884144032804c060528030308654029128072a294442800811280d0b0820010b405422142c10810b9401c0f49070b60100e4054402444000c0d8000800a0416031103500c2c0d5001d00450051200d581c03851710210b85e4403004040e1546aa414611030070b016201c001a0b50045004102c0149c1ca0641c0800b6010916118121281620307582081d40750792100c5141040784000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 780090971 1250 780089721 780089741
    0x60b03070b040605090d0807020d0b060111010c0e0d05030708130302030d0c02010f0305040203010609020c030d05011208030a090305090a1508070305060a03170405220c02120a050d0605030f10 84
    0x1c441c0b60610708440904a03114002c5c0c13042c050041804410103018141054a02a5801400e0072003c4240b9140889504c4801c48640b80405d80c05450000e10100c14800d440c911989900c5020300c4490210811800e210706420803105448204042c0c8005140c0401411034400002c0c40703084110304510415042c1240d0108070010005201500b0f40981e9024900c49201d0407982000616a01c1d54004a17014200540120310494000a200844030000000406907000d07028810401c0340d0b03d07020038986400181101a0280d44c0510104071150382a070701911200b40310b82003e52502d64510007044038204a070b4482804140c00120208031070342c10100e00b80e44500986010041490403000148400341c26000150106c0d141c5620a00541c01000850703010b050700030712100f0078a0450400c03040717804851484454081c10007010f001114000202ea01005003881e51141c1440c11a100031a1250800442c0c20480d0b40c90320800643c5480501000d914400d038407019060a030a074202c036030700b81c0d01c0d5101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 780092221 1250 780090971 780090989
    0x40f0806060907080609071e09090f05090c060309010f0507050301090c02010608030f160c030c0513050114040f0b0d03020304090b010c020a0918140304090f0b010f1b050703060b0307 80
    0xc001c0100d0340000b441c1d41c441c3c0111000007047c0c58042c03003156038114140900f80048583d900b4107603150b8010102d94121402c03c1402c0c08a0041d001c080001e03600156019039082d40165500c0c2c000c2c0c44d01c580039660110001c400085c07600c0b030042c14032081d14819200c1c07001003840000107000070320360f0f401aa0100726190000f403100ba46004041a601c0c41100032141c0a96400f0980504130380f08030b480e03a00d141d6001303140c80d100036440b810801442c100303a1040318070800400454001c2d40003035006142c1218492a0200c0c2e07054204014000500400c400110119039600040080350b550010b050004500980c000c68030f070346c100f1201c10100e440000c2d01c00e0500800c0021079005a941e03003050305c240c43c980703000410402072001c080c0e4540928284001c0c5200e40c00b545031094001c1c0000948115428280203110410003800801e0460350340620280c006110500941e5131385014500b0068401c041d03640e485481d0030745880d01820541307641c000326151a151804607120385800c01030800580140c42d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 780093471 1250 780092221 780092239
    0xc0e030a05071401090b030c0c07050111031206220504350c460f0f0c120803100608010806070806010e1806011202090f1201020d02040f080606 63
    0x107103a095441d0458810750b40e22038444484542c90b039100da00141c005024a54042d0380700c0c2480450208039404c626581c480038031810380700007441d6200c3c0c802420740040b0000a9450400c0c04c110280000500130155034001e0210703410250003038248080034140880c034810000700c60402c0e2600015414500c01e2401c80d01c04d10f0031f1228402d00103c0b0445d409030122901d0b00b96507152510b0828106000548000092100e46d1032159152100c0d403620340e0b04240710381c0c0201c60241c45a0242e01250303d03051000e0043d1088100c0c0c840041c205078010031030140502c1c40354007400e5890494280700305030b1b41030440e9000800b0040c09181d007840b8135840060807150038000400d40c18a4002607652030014007030402c0040c5100070451907402007070360060024024003401401000b10384008800d88003501d04078000390415074648211041d510a9905a81d40104a9102840340c807041050544101d4810041c0d954200100c1012644a100800045c002100c0c2e112509285c5412641041402012680908860 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 780094721 1250 780093471 780093473
    0xc01090b09010e06031509070818070e04060207060b0306070905190302100f23070308090d0f050a170a0b1809030a0c240501180e0d08190f0c0e030a 65
    0x1290f18050107070004d9480c10341720342d101412515103a1134110703001e8000c4800020701c16840e40c09034145100d086800842000030004464180c1d46982520401d00b030f951502c1301040020b03200d50003d02a40d8001c0d40e02041540340c07500064140b180540d10440400e540d18400c00c201d0800341108803954403c40c642600191558000c644482081000301040040d1046100c407803030301a141460700508500c0d0191014580082c160107650700000c015408200f400380000c0703020b2800190b80c2e40c04041c03542d402c41100407003102652103402000a07101031114402d650281180e0b1007090b184150020304d40810700e8403810702030104500146690303124040b2401c04001c3c5e0a000081124108100380c9020036203003441c1d0400798400d110010841084045c205030101003d00c035604014140c45a08215103401c1f0f44103403451084550300299010f06800a2022510391809411a1984041d04481c1400c007507201c03110540807070f000441d02d0101d0355500d1101c44e10341507000c440c038104181c0543c000c1242c02c040d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 780095971 1250 780094721 780094727
    0x2071a09010e1f15090606030507300e0f010e0705091317070804120b0103021c0201021b1207090e0706090509040204051f03060e0d03020a0f0c0f0b01080c01090b0901 73
    0x180505203d01a82c850740d041c0b400740b03401001c0c28000c00e05404108031041d241c0200901504003a2b40c4c0900040d80e900d001021082d00d8007501c240800707260601005440d2101401024000b040300d40d030020300407008230081200c400c0c01151200e0101401500d80d0504210410055240103000c550009205210b49000900c094200c081003a072420310107604c0749040d1600280720300c51500000e07a038641c40c02240c010000e17840c0d2014107aa00c21581301c1e000541400303088110244000019005a11a51100099480414098a0a5002629050071054200c50700b41c80c0a115600000c03a0075511a14010508018003a9802a0141d850240511752034200060030303464000c0c0029110340e94030004202c1c418001012241e42c2d009040c885d10b880c0f50340c0d0508200030502c10010503e24001d06036280f88040c401e100b1078140d40f203140c541011703280c80c1030070840d40660840400c07504104600303844004505807521440c020070040008006240ca15000100510320030303442440d503000c1c140404c0c41240c1e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 780097221 1250 780095971 780096013
    0x40f06170c0c1b0a180504060b041e1a0306040c0f05060f1b0705090a0903031d0d0c1416060f0c020307050628020f15100e07020102071a09010e 63
    0x31a200741c000d250f0f095800021055015a8441146000300032007480d480340ea40d8106a1240d400742d8802c2002c98580310900042c0d4408003084240c6035007181c0600040507269000f070b08280e4000345000e4840b04084003180c070348041603e003580d0b0008400c004201040c03184207103101802003580c441e81400641240d104c00d03030107540380011002c080c10160200583c0200324241c01801c4c020909011360a142000c50002c1041c0740c0c0507400603051054030f80311000c0e105074445007091248000d0945a0140707500b1900f0036030061045903181504540c0203094202007042414018055403045040c52504002030079001981700c03100c1c240f0803000c1010000d42c3d404102ea104680c01a55099603503551101028a4405c0c08180b00204160b09490030002640c00038101400c09070100c1111300703003004030f8120380c81c0c5501200c803c82c2001184500f03001089401402c160420b16a000140c2803081d02d0b40c40350241216107901360000c10458080003002d1400f40a1510008401c80181c6002c40c3c0048000c0101d41e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 780098471 1250 780097221 780097243
    0x1404050405150d060c1101050c031612021917060901150c0c0b0403050d05130b1e0a1d010908191707081c0e0d0c08040f06170c0c 57
    0x599107000042201400d441d072001c804900030a81041018035161803001400fa200f000f00004503500603802d040541445454001d94065804a06654400e210304e03100b2443d413518031003040240c1110400c1400c003800a0001c280c028159803021401d8010003c0c580e440603104540d444055406010b501e445a85130319041d50341009140c3c114980c60342003550402c81c6900024650684043d00294000310000944292071048040c1c0310341c200c030803000326058051701b4211410030f80401c80812210110030010003107101d0f402a40b40d40305113a98203d44054100903d8000030405c0401d020003c1c401ca000c4d0308812031004d08080c1c01490500c05031070764801841d000205546295001c0805018003c4210b08042181c0c583c039954550291500d0040c0341c00240d0120303000c1034511408042900c850051003c01071110000b084500b01b0700300b048529100101081e17503010400c10000c10b04001e034050030b0016002e0354417070388000a5580424014154020b1100e10080f030b00b80320708a617814010503004500c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 780099721 1250 780098471 780098479
    0x30a053016021e1b06030c04120203011e02070203012007020915030628090f15060b040801020a020f032d0c15061c03050318010905060108010b0a06140405 68
    0x40d2101d008207038548450410307444100020091202074110300052038043e8403102c0f113100d0214480b2907060082078081038500da40703550300038001444003400010701511024001000400d408241e8400d800082c50380799022412190009480402e600f1709004038420005020300c84000c005058051069a00680200034800c90512000c02d0380c01c03040441480c1d800200a0640c2c01d1810310000080c20103002d00c040c2c01d0701018941c103d950304070042c400c2885d07040d0021015094903a0560302e904480442408140328140c1c2d980307000c01c1e03d1180c10080d00c081d002d124001680c8410014001e4a80702903403186101540c003c11030640540460303071042071106030765a4403a1400b05404220a868040d80c4207900c2d00d4410b01580c450030701c1802d4040e50240710700b03a43c002c0c200f481c50030001140d10303c0a80c020b4086a401c20208bc10400c011070007400c400080000050288900c2d6941d0781030103801c1c1d0000350b09030b4485c01e18600070b06c2c00c1e8400ea0020000d03810195600041c9030344418103400356101e810302c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 780100971 1250 780099721 780099751
    0x108011404020d1d07080607020606030a03030f09150e0c0a1503021c021908010b0c1e0312010338010509060432070e01091511030a0530 60
    0x642d000713402401c01804c0d42c0328101015040840b900383d60b480d043c07091480c10b1050ba00440c04c69400400ca003401840007a016080004903a24290b01030942c00c515009903550791a00200421054030743c0c10204100e505021403d10414060b480c0341440103074115101d5600b8000402c04400c5032075001420000c1400c0268a81d041c4c0f81c548040044000709044500740001007000440114103550b051165954030f41003080d923207031070319125a806480003d045940c410012101a0080f0011400701c5642d1101120324115980f280c1c2c07042002c0a0b40220b0f070900640c829220040050141038038000407618045015502507000c145041300103108603400b9241c03910200d40d107500c4175000041524504a51602107481407450038480c3c101c0c0300c10f032008041d00c28000c03440d2148107515502c0c40e000140d68440e00c0c130342014101c2204840700c1500c407082c0640d0500c0001c4400c03090010740901d040c0c030748038070303403284261980308061213800c0f0004083d0240c4016400b01020701c5501454200808501c0078103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 780102221 1250 780100971 780100987
    0x81e13030b091f0b15031005040f0b0609010305040503090d0c0f0911032d011442070c08060103060e010204062c04050c090f040504020d082b06030b06010801140402 72
    0x1503806400d11700000b202c40000100001c0820000c040c800301c0c1c07003d850800c05484210603e800312046600301641c0600100b0418216611a400c4550410f004500b50380c603054900300081c03034034000041c0469849801c0075040015501c08080e840c01007a02400900c1100912000c21080e840000c04544004c800201d05450b61954452a04081450a0107440141d6100c50781152224500885240700e4510500d0801c00e2441014068041501d6040084c9403800e90442d050704140e00741440108008080c0300340c00104003c1e0034100024203005000c0e10540d4114100340080e81d1031240d6040050380104003c0011702e9100059000c3d510036445100703e4188800c08d400d0340900c4a1240300e600604042c10310080e81018802000d801e00b00301d0391012502a19000d0006488040700c02940c41000c2588030300114031a01c00070400b034010280c2c4d071000220b06400061102c0800410000c0156440307170705108001c00c0d40d400350f03002042400c011036a5031520141c1c0c0c00101030840503500850700491040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 780103471 1250 780102221 780102229
    0xb0a080d022a0612042f0f0f0307090504052a04090203010f0f0203012105070603020f0d051e070302030f0703152606010f030b04081e13030b091f0b 65
    0x42c0a0400c01426a59204064410301581c07034010b44054030000b0b4288403200d541100b4490f00244c0112458181c54140700340002c01000c80d40c0c24a01981100d101c1c41010116503040c04414060700125a00003440d082a0801d10700c3c2c691048070002d40700d101107040b015400c152148001d43c440c42150040740e00b440c42c0c804280500156020700c0f43e4981410b103074000304840f54003d54141c801c202461500300201c440c8044418014030780c090540c0d0070060003401554400d800400680200e420480c0c60300d00d40ca5003d0007100c004a072003159012068514001e030400a00360385030860070900d410750840c1048000b5480112014164070280341ea18100c0d103e464104518950040070724900f030240c0c0032002403c012642448002c0e010b854065000042808501020000c1c140c0e0f40211112680d0b60716642c403c43c450b48110f01c036414014866040310041c0e2011001020300d41200112148503d2a51408100c0f81c1d4028100030350942242d446000050a14840d08040c10481c0300d02140b41c200c004003007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 780104721 1250 780103471 780103543
    0x604150c0e03010509010b010f050405130c03060b0c0a170301030b15011101020a05131d0408030a02040906080f0105010503010e0a0605040c050603040c0e0601032007050f060a0b0a080d02 82
    0x1d030303015401c110401c0311686066010700311154083e01d684050300c00030502140e00d0311803070040960058130028601c644c10030b42e500408845000d070a00190b2292541041580d0780c110807030140d03007940b1100c40501040398100408061400b004141da0035941507aa601959060040058030600646141001c5582c454650071140c040e00308021903070385810b00700062075980644103a0000504100000460303a03080d50003d0092503c066a0b2081c0d51201da903003290070391020f84000440d64082c08046041d40c594851000103095120040c84041d00c0714007140c0c00d5960590120340f1903494000701007051400810b83c1400e035584070300b0000700d40e034480c070384140358003d15006190404004020003041002c0990801c05680c2941101d4002e6590400110140c07036014034500d0840e49012048410705200c103001d48915481081030703074424030700c3c0000a468508200c03101d02d6101c0d01c1b408042d10700c5c282a401840503041c00c002515414100106c081d6031040d40315480c84104907200c501d40c049036011011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 780105971 1250 780104721 780104747
    0x60302031314070e0105180718051806040b0a21060906090506010617070504120204090203010c0e1c050c1c150f11071a0702070b1210080604150c 64
    0x1441c40003440b010100380e59a40240180f1607003c8407040086079915003407002c00080b00c10010800b103d5a103948003243c0181c00d05d046d042c01c468004201094955800094042803400605900d03014a029004c00c416130700709000d50b5008503007200003409100440645000e4960048904041c500030384d02d44840100380a00000c0c225902d01400e40f4204000810094100c4019940d01411048400112020b0a00030380301d86000c0340040108120380c95034540d080c003003180014000200032201e5004a400d4449050486c0006440c02c50144101c2c60103c0d10b14056111240d002020a5041c3d55080c0d03681d03501c0900310b80b1a00b900400280740e4071210741c850906580c400070300f010845041c51903001509030002c45101460408a845a0000c041d00684140b950085410700c0c00c2c019024801c0d89071076000d02014118082c500002c1602e140300300c002c20921210f1050500c140c07600003582c0e002654a5040f504e080d401900a01011518078810003411620035580040c40e034a240d60151030707088210003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 780107221 1250 780105971 780105983
    0x70f050a0e1903150509120301120b180303090a02030d090f091116110901090c082a041d1003030804110d060c0302120c160b0603160b1c02130603020313 67
    0x4104d0303002c2d4950002801400e00c6070071540040c82604a50301140424005c500c4a151040c5e40d03040403c001c141c0460f0400c103504110400e02c129003180ea0b0a6510031030f02042640e1000d8107031030860804000070800c40d640c034500341080504000c2e18101010161107021500b075111141e82c00c0c8000030380101c521180040b44186210906441c2c4018201d91583c6054450f40880000060103500e500490a10007010341c0c8042855030781e002c41c8018100342030100f1070700d00b0361394081c5e81d4281c410600410191811294001c2c40c054000d09402103044014544400e841c1070100c104002a00075003500e4120f50322201d002c48001a040c0070846800280d00060702c0907060119903014280c0590040c03002c099000b810690740d0380e4144005c865480380c4d5049140c0d000d070810116000c01c08107980300744c0082c00201030310204c40746003071040720600c010b40251061241c0000c89032481220301502c249400105c040c150f06050001c841400c681d0740c2407050006042d0000700007414161160462460164015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 780108471 1250 780107221 780107243
    0x10804050c060c0d090e012409030501110d0f021e0c01020d1401090b0a050f040b180a05090609071d13060501030c17010209090a0b030f030301080105070f050a0e1903 73
    0x42c5003c0c0c0d0313a03000501090200316040e0f03000c00d10144031084c250580b0100c003148601565403850400d40300c1100b0300c0c110100042c040020001400a00600341c00004001e109615154200311241c215030142800c0c500451042000c040c00b100d0050804080800c4001c0c5903456a01e55100c56001e4442c0300651104146000301d40b40004405000d164103892150700b00300b080146040c10300110f0041e078001c0640c00014001c1d0b0b94014a01038204804141e0041d00340315a80403000c800e00350052059900e0180c49031140200461858100550b40e80800e11344020700c440e620b0401c00e0090044100c1081400300d10083c00901501402e6011b845030a40c00b40080006607500e0038901c800000d68060541141600c4d05440402c42050007940e04a0f1001051f00c4a182c0301c1c07080d0003004004121a1a0700750058078141c40c0c0742007003800994000d142c0310b0000300705440c0c90b20006011450164007003061140c18400703841225448010f4002d941390607290403086d01d00440790844114441da00041841d0000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 780109721 1250 780108471 780108487
    0x7022b1203060609050d051e21071406040305041a040e04140601050105070c090b010c050303070e030d170403200304061107050105210402040f140411150405010804050c06 75
    0x150700c60822a159076135081c4045450b0800c004000c090b1000c0a0215407010a40c0300301c025007548108660b08020040301d00d0941c0a000e81d441d050b00d035078400b4a6060003c604c407414003003100c11000081074030b40d001c1e07d0646001d0b078028040c1d00607070040784103082d40307082411040300c0803904076005054440c892a0132450680303003d401d1070a01e11107a140c24000d66000107910f500030825110101d0340040b00340310050074010000000d0614103101410424400d1045000c14000e000441c080e10240e66051201d003042c6080c0341c43c041003080c5920070480802c5801c40f050701140c0d442c2d50803d62520704995000c2c00c4080b03200076000104114016400005400100140c01480440f840340c0244c080e01c0b4a259110010340d81d9000310505403446d0710f0a00700346011000102c507070a5000c5e01c010000941507104240840846007913a0050b030301c01e4800d000b400180824001040720400f42102c0804208280c44002281d50055110319814040c240c40441c0c1008030034001c2c49590080a0f040303544071a06 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 780110971 1250 780109721 780109727
    0x18060917070b0313030509120c10050c030f0903010f05010b220315020c0c030f01020a021608070b07080f072907320a081914010b07031106040c05130207022b12 70
    0x1064548900c1078580c10f980202b26800343c426528480d00c081d0256040a6205014000680c0300100142e49075580344010b0813188000e10559010b40a91040283c030f5020504203190340303c5030034400301e18030305015000b000028811041690702d281c8000000d82c45a1010708000d28048032055030700c0e4036004d13182040503804415805004c0845003582110b41ca0740c0441054010910700340551051030700800014805094200000d0019620584900c2e14001c0e25444080c803c0e084540e048134500f120388903800a4400c0b0601100100030024210001400c1207403010382805140400c0c02500200c8120703000200a001c5030381c2d10712a480a01c580d690f00c140b15002070100104541820a100120303058181d20006442110740d00e00e24010400006d908000800e4000e8024020032810041001c3c11711004031000d0068601032882036003020030705401d0000700216030010035440842c0d10700c10b00601c00540c0c0c400c07200d148400c014600d1402505402c0c00704103442e840304000035180c0001800d840e002154 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 780112221 1250 780110971 780110983
    0xf01030222050108060901060f03050705101202041509080d120506030307050a060204151b032d02070609120804121e1b0506120f0718060917070b031303050912 70
    0x410705c4003c0000b50344275980b404c2001c00c0b0340070190407035000d07200c24022418000d65600c007402890a041c0240f00c0c0000c4d402007a41e010f41c0123210584200502242080d40000c016006012020301070b25040300300900c010200c4201e10b50483d101e5403181d011940b65213060003110b00e4190027009440542c403460030400c001e07500502c1020390301c3c0508c145081c1e4031446050700017015031f00b00c4151101c03410603071400c0342c0400e42d40704a035002100810b4014900f0b41c00c0226200b04007083c1c3c001c7c040c141e2038044d0280c2003240c0d40d8080c240000780300e40c4d0140011000c208882c1a034207400c90042c0256060300340f41105074404203101a060a801c4444000e001011040154003501c0d001e10401d4651100180003183c028060759002289004020600a401d40da8200e0790220b118940303070b82410800391000c0d0f0072202650040003c50021f420a00c2070407400c1020910b0a0348090042088514056816510b071000400008003c00d2200b090410140702d20100ca80200c0010501551076122203903041d03c881b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 780113471 1250 780112221 780112231
    0x106020a0f0819081f0b03040b0604060f03031809060609051c060e0f0f0c0603040f02281a160b1e0c0306030f1b0d02040e0d180e0f0103022205010806 66
    0x701001c2c3e0400c1e10401c414120745e041d581c4002085003140c59a1350385010b500700242c61030703134410386450300403c06107030703908010008500aa8070003210905900701c0110040954111103a00750900e40c0c14410150480502c10885038281c9852424a000740e401c00950007845c88010725180c10306420700040c580000d6440f0340420700300c2c02d0312404070031603020710760b5005043c1541c0d400020920005003c1001601d540c450140050031a60581d00c02c000c204586c410100a0031340c0341e11120505000c9228440200c0000320422006176140202400300c100c00c113005120300400ba035071000009400c0094201c041068203120074184085810007900304001604102e81b6127009102d00803011502980000307a400404051828100b0800100c1060005d0b0880e21201646c01c1a07d888507500612010000e10401c0c110a6468108070040500348000d003100640c082035a51a0190074441c005a42c192803e0450750304540c0d5074034800d105c01300e00164001683c40c6800d42481c04000041d5200041a241e200b5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 780114721 1250 780113471 780113491
    0x809030601080a120f0c152a0e010509060d0b060408070303051806090d020907021501030c050a05030742020604022404030809040b03160905010e0106020a0f081908 72
    0x8045030400448161002410280004d00e00c511b80b9804148a0f005509a900b8040004900c255440d0501d800d00c00c1c60301d44190140081c030074180005980101c0036902c4072000d2802c546800301e0800011041c0c0a948142220035071303250420641f6541d92011100140100c0c019503036069901d00300a00725801807059181c3e618041000034202d46401c0c41150303107600c002090410996803503000c0c06494a0014001001d40c402d00e2040400a60800c19150003907128940d080a1603081c0424070018000035030041e4000c1d441044103210032400c4002803041c0b02404400c49650720288100d05084449814000e00001c40041d10902080e03070202c0c07100d01c901d00a503002c240306084074098076032111507140c25032009074080c081400092061401800c0e00003004201003101121140040c0c107005c8000181410181d0080c001c01843d4254001d141c018032814140b0205503162210107034a0301041280105008038014050081190100643c0c24900d071100b09010081a8900003034101c80b1305032058041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 780115971 1250 780114721 780114743
    0xf03120f09010b0a0b1936050a0e010503071d01060f050708040e06010e0a060219060f06120b06060a140a120c021006080303150d0807020d0b0703050717010506070809030601080a 78
    0x3410380901e094490b010001d0300e089000072075210500445000c400c2008203404854031f070008030741c1d84e0192050040c24001004203a01d51400041500c2c0c41d0917a13100c009000e00c4043d80801881b11034100c181111210b04282c04481d20600007120b0609c5503120040c03e0383d00102d00451640b200e00c409a100d24002c2e00c4075581169641d0030840d001040c3c0c4a040300580c49003c4801452a42508600c0ea0742d00c122004100d1101d07030403410702900c5140d0002c1c2c0e00b00c000100c1d00c80078000d450f810740390010015107680b803804040070801001042800550806c591000403440143c80c41003d0160720418407a41c05c000700002c03500c0082d190b00845c031284211600701030011502c0a00030080b00e0080c1000560741c43c01590040c01d000c494550144142c0348648248140d03c00350302d9001c0004081480303400300181c00d20b0440c4002e421141701030410b90410110315011129520202c040038156082126000d45400c51071511000074454141c43c0c3d070f014011007000040f894000a51948403a10940510030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 780117221 1250 780115971 780116017
    0x705101a1c080a030e0f011d25050906030a02100f0212120a051905090a021e090a02131a040801140c0906070305160309080f03120f09010b0a0b 63
    0x39a1080744009040c01c08100301181603c1e01a511241191a0a205641d401e00204004d40d00b1100c2c48212902d0180a40000e00f4980340d084c8148440c464050304401036243d0704040d800c040300c295010300d500412a6501045440d64200280d03000581e004010b540c1c14096024010140c59004218501601c514600c0c4285e1840c2c42d010395440740052800c405051380d42014420213003502801504040c3c401c80c40c4d405c0611110f01400d80b152420320005d1000d08894814401e00980340f8182c040340c4e01d00c40c3c42c40c06003030f40c0300403090b0b8000511550150706c52816003070516440803254042c451403d070840800c80d00e1003003000a8401c80711860000c201410301407440048d504404c4514203c030400401444000e480c2c008058813009000317142203800c1207011682580c48041c0310f50140c000c01c00030107003000780400400c030481c0c18044240186042c070b0f00d400d18404c00380700302800c607103050020782d000940e10600c2507208408410000b4070a25034190344000c0f039816580000752048141402c411020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 780118471 1250 780117221 780117259
    0x2060c010c0f030207260714010218041b1229040e0a020108041218140a05011b02090612031903230c07151508061303050306060705101a 60
    0x1e11041d07040100f9001b5116402d060040c902103021103124559030600403440890285032000e008500140300050350350a40a1600e8040061103610510503820301c4086883c003240246000c0c0c0d280001c0c00d00c1079440403010001c10103800c00f80758500107202c0309450202508050055002c00724401e030b60411455082c2c0944503283c0e04d1107007010380403030b51800101d0001904030b000400a84110b144c2803c4907110020f084c031141c0d9040e0b0001d0201d000030032401e001803904010540c0100000d0800034800150200301194a205c0003001030301c1880407400180e103644543c01440010340c1c428041e00d61304e0001600c19010b83c000c00f011940001e1400b103003414009c1c1c03041c01e41042c8400800718250740740d545582e10641980484001c0f540590300060b5103202c0b1200f4080c00e0324a140740c110111410b418100c2c4c60b1300d0030301c004025002002d02c6400c2000800d4200c800c480d00402d054403240d87c2d551036030405600d0300789101100c0c40003d190480b09034004800e440c0030309074018115144006140404204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 780119721 1250 780118471 780118477
    0x2d0203040209042009011d090604050616030216080a17090c1e0a0803040602150c030606070512040f1502030c0616090f0b0304030813030e010309080702060c010c0f0302 74
    0xb50050301107800f0602040e5440e415030745811201c5407600302007540300c0203c3c0e01c9407020b82c8401c101c041080c0c403032a0580c094451190b4070881350750007803e203807400384c42d0140d40d02800340801c07034051a285004441c00e44242c04035002c010b80c0c0b58400405000a142c09c05159000d001403c0014152288a0301c0c111079414131180a10155001032480503c01d50402600d821500a0705440800c080d058403460380310208184000c0544401460303c607864100e0103400d001504101c0b20b842a4070000704204988140152034100000b03132102a240d42c486d241c03117868940703003030000000c00c1400b00d07000582c2c0015041007002c0d41c404683d00b00d410720161206a0b900d00401d400e08441e40c101000045110300c008a010240e11060b140200d0344a03541d0001e803410945135089240d20303450000802041c5030b004441150001036a0010310045c0015440080c00c00b03003003580c0303c0e04040d01c40350404180403001064070006600141140c3e80c80000c0b5000078000c150761414100441c03140740b4200e0b0118028070907 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 780120971 1250 780119721 780119723
    0x303192618010e07060f0509060705150901051012140313122f0111100906050a05060d0f080d0f0c0507050c01080112020409080d0c08092503060b030c042d020304 71
    0x294804007202400a0303030076401226070a274000b0f5052040b0008074004000302e101d4403409006400c120304140b80036038251400204103d80d80504e81000b000b4201c0800045600503030011110070a0340340d00300710750381140300310300084080c006801c030b0216820300314201941000d44940c1c0c01c8001c403078407074500c8508440500e4607940444045800c10340154022071442420020100c16500c00b2400702c50701c141168680c11081e01c085a90b18100406140341c2d2041c0d981140040780e4a0355501c0081d600d4078000d40c1034a50050104902260f410b01003600c2e5003180040c0300203000140300003140d02200030004d030070180d800c0d1010b1049406a00b9554010403599050307074a0030116400031026902800040c00e524002242d0f5110304004c1d542d514078040c8030320702403102607030360360038a07410110b214910f001019040c119001084d09000c4204000b614415001c0b260301540c04190070505000207414600c1044129402a00b0214800e0107a0708824a4a4110500002c03848540b100c0000a804070b000c2150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 780122221 1250 780120971 780120977
    0x40231080115060c050a120c021c120c060b10120c080606160206090306070c1a0c0d050402030c090406020a0201152105072706050303192618010e0706 66
    0xb0040c00b1451089169602e0640110700300c0307000e10b9140d0b1754901408244026000001d00c009109011440c1c542030b0201c04940080004101c3c0e02c80340c0701c5101e40501c003a0244280120340644004100c881d811015401100400c2c0504c1c251003072001408400c0360b0101b0b40d41c014900003e4004d1030b401010668020b4801820150034101806100340b418400700e0001c6e44c1c091004c2c0561289a5020031855104490342d544100c6564a0f40c41d151101940003050b445c8807034840340c2044240703401007080d14400321400c0f0010500e601e5a0011030700707154401c0e1109800141c1c901c10402480880c1c0c0040035290444d5000300f04003c0001e01124004400b8020324001800c0a101d28004000004998040300d006005442210360344a81742c0c01040c1d503032403440c03014509038204070110040fa40f2698004050990145291000302c08035000d500e82030520280c1400342c0020f400803068240e90030f00207609542c20100d21281003074105078502040c030350703455110741d802c000e9100310311800030942c402100d041c0d807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 780123471 1250 780122221 780122261
    0x71703040507050f06030f0619181b0516030503040f0609030e0909070b09060706060f180c030204051315120305030901060f321c11010e0f0f0402310801 67
    0x20741042106003420507202003000040703001107070311340498504480961a074000060a180c0c0be450050308066100212418454140484104440000902c01d000c80d4549041690b907652442c080004011006000c1d0007c6d2625010500f05a00041080950801150080741365501d8221240c1d0b1180c907400f80c001c440d0014061a0060300780310001c0c081c490f00c1048080f540c030740c0700c1d880217090341c0d002e52200740100342513080007108400174482c80340b81c1100342c5410b610b0704d818280403c0c041412100c0b200d079100d613914030320303018041450440d0018100b4014480c00f91800e50900420302d40003900c640100c0d5203041000600741c400d204102007100d041c40c40040302040e03040070314181d0782d1003500035140101c0e104524003042ea40e00520b00c14515540c402080c4004001d00b080082c1a1380240300505112179881d400019a540c0302c201204100300310303603030602d068070b4101041c080c0c020016030540306154510f52a02c0c2c0a002c4071022901c00790010500c00b800c1d9500d1045098a5201201c401c0c801180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 780124721 1250 780123471 780123481
    0x501050a3014030d0f020301052b15090b010e0708070f090f0e01080609060103020a0b090a1a0a0813150b0612040813090b0a0b071703040507050f06030f 67
    0x6080c0701940030a059410901100a48614480c2e0009a401900c5604000f6021035400382c184200b03c08039000c0201141158180000f083d030a003102484042c10f804c0005004c000e85d480703205020b0460303078070901d8954000140102c1e4000b90802000899032944881e00104603a6081c082c082c0c41200d03d6940c40310151200f0000f46c4844281220300c0d000c101c0003070000300300702003000c03c994020804061594004d43c0750034041c2d82030520180240b0101e13005040108050b0b81da450000c0309907030030400722540d103a0320784001868601c80765020040c040c04820480c1c0d001d0489902608903034007070343c9580c4a2950780d00788202c0c00c410102001800c4040100a02140e1180c03640314a0740c0b10406401c16103015030070991000e039030700f04803000c40e4903c0f00000c0448a1076600d103440c00c014049203005010ad5508040065003114807030203030980301350012400c80140075a020682001c05610801030387c2e241081c0c00e0032922940c1500a0783d004031610001103002c3e050030811648591240c0119040903214 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 780125971 1250 780124721 780124769
    0xf01030816140a0c080c0904060f0b120c010207060828021b070302030f15043008042609040c02160f03020907080103080406030c051b010207060501050a 67
    0x14001200084860900004452520b00b02c10588004010228950f10303142c80000048150403004030b5802074413409000ea26a10082034000e580100c01241030030560204000501000703100c190301030350241e04481a07690202d11109021820703801d48545544a000a0703454001c256001440301c184062141c203a00304804204401195618001d494000b4404182c1c1d0380d0743d655941814642c104210820442c070701041b170828080c4102c80640660801c0b00400c401401c0300400c06018414051f040720200d0100c9a50003105c0003001c001000c0107074031380500401154040301e00300d03140e4800c0301600d290508090340324152018408005c518212110341444003500b0601800c205600c54120039002d101d002c5641c03030029028180003000c98901d940100180780300c0c050002c80038080c0c1c40c8010310114030a44111401d03210903080101d2140801c6d0400c94803480b500c2c9000c10b0000c00e8001100c95050190001c0000760b0040c0021b000d54bd0300c800c2000844078040c441c9884c3c92458689000c40c1c508 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 780127221 1250 780125971 780125977
    0xc1706070e040b270f01050102100905070e0405030a030513020f010e0414160905060a050702150405090408220b0306042a050403150c080609061311090114030f010308 73
    0x100684040340908003100490070f07828031010131245641c2040c031205040034101e0b0b126544054820603a02855240c400085d44603050400010050340c0c9844601e4248042003114500400f80d0141e01c40f02c43c5440c0c10f00c00e07104d400101c0110002800c0c0310101c1d800440614007100e0080d002030254030412000c00040d80c103c07079041000d40e0019281d03030145500002c80f090613071180301144e42d55101888444401820119640c00c42c510901083c4200c0d10020390010a580b1003981c103a9509114180b85840300081c0c0c003a40e444a5807150b8100c0410040043e01005006588000000d204582151b0344210307145c0c184902075008802818400100c0629182c1c00181030300c59030151100c08201c007429001442c45a180e0810040b420000c0c04004100100e4041c00d0002c5c00800d0403c00a60705110040401ca4013908240c403501c0100e010600503580c0ca9401d030040c615012041000a034181c1c406a4203400000c0201d01207400091034400e801e00c40011240f113514060610305541e801c540d14010590 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 780128471 1250 780127221 780127247
    0x5010513050426221206020c120705070603051333060801051e090607050f1c0603170c03031305030403020d0f020f0f01082701060f030c170607 63
    0x14200150007802c0340c40071031210410b078551040e9039544c0c080100c6205503500c0c000380f400c00388041400040103c000720032415001250710035005a510380c071105070289401d2011080e81010b400005446042000004e0000206c036a6074a007071020780e841c003401c12201c4d002e41a019200c100c0000c00c180000c0c0c64110044184a20742d12a007140301c3c120445038081301c8140c1c001048581d0740f00144040c0c4850202c00003640307905441d0020306403230035a20041d107d01000d04030b2001d10501065071040c04030b55405a441c004030180c1c508840842c000c10f86c80103403105105c2039030002544000081d003944407004640384104408001d515580b20f40c2d40d400071800200800b981c680c0403d020100c016901d0030003810303c0c140950507214003000640104418404c1042071140b080400980e03071503159800480d171503400000c442c2c10000c0c0d00c41d00300410301031040e81d241000855280440104100750b10801c204140d90280c54400c0e0001e845103584030800540c00101c2c0c01079400704000503140d506c80c00e444a114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 780129721 1250 780128471 780128483
    0xa060b03011d040611042607060f0e0102150a05070f0305090d0c0f06021314040b100e0a030210030f0515010212030406020403050616020f0c09010626070e13050105130504 75
    0x2004448078414150b000f642003400804440b107044903d01f900700441171009100b0f00d004d03240d80341c6890170241000040801c20014003a8590405089038000e00880100714a0b940c40441c0501d0203084800060078101e032000d000c6043c3c03c2c0014046c0d80319201d050b100c0e0038080010329580c0f619000565400304400412500030040d071a0b00c4002450b28000340c0b070900707254200c81c4c40260800284145056031070000902a52074001c400d540c5a0f11010022510016418482c002c1e19078040884c0c030304243d581003e900501e81c0c00d58100c0c1180c3c180d0250071000120b05080046884015266100044290a080c016031003941803640c590300c51401140c020344500b00061505660b076070b8160405004036002e2001a002102001c249074060151074104050080a00310b1041294002201241c040c002e40003000007000121070b42021041d1020151080300200c150303246090320b40103151020205215020300b40d00d500c0300000307405030300500c1d0507141e0052010515007040350044008080042059a42c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 780130971 1250 780129721 780129731
    0x30102040810020403210206070807050702120c03070509010e040b0601020f300705070b090a08030c032107020304090c05090409050d031109060d090302030f0f030a060b03011d0406 79
    0x60800c02c00228070003691200540c4852a60070301000c0c54400c1159500c4e807048540f5000042d66001c5070460303000b075031824016429107506904445900801c9402074218030303102c140e80701d6547e001030541000340d42201203480360740d110024000340440030f20860111510302001701d000140e82c83e42c201d501c013806104554078412035548d010301d440c20007040e640320343d030038125500282d007441c01c1d900080b00c0e4142902840e000c16030b5280f60f990903a921850318400307008a000505c81c1e13642d42c8104001d180f1728007100c0d1122603000b12203880390b219150614a5509419046803218100c10401f0300c079200340d4005d9800e01e4500300d08a40902100401c58040240802c000c0009a070b4610880c0a990301440081c80c8009003540701408550004c4071409008105000c0107456035100011145400c00c55580031500c9511032800340c1c0f440c040c0c8040c01240200c00308184e5280d034000781c0075620070360311100b0030b10005a0359100101103200a00603c5c7d40d400140180020611f49549950342043c49403a000038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 780132221 1250 780130971 780130979
    0x2180901110313050c06070305070605061518270a0f111206120102250206040324060b041a07020f12011415030607180e010303030603051c080c0903010204 68
    0x1090388229000c000400900c1d03c68024070004014201c1440e006a03129442d04c3d9041c5c030060428028041c00500640d1604001450390310b418400315140b0114202c8240c0720320f040c2c0c00c0c102c145a0190440c44c0101010304a2002000b12040c2003040410442c24201c1d280d00c402c041c940260100006032030525072103072030b00401c000c100c2c07004008000d400640c1c04402e0605030100104ac5101d541d105241d07178018011200d5188111640c540300042828000c0c111000500c0410954007e40d84041c00140d44d50302c0a19178400300c0814100550811780c010440c9940b90b02c030400c09800341e8011a150300303c100401c184062031210003271109500040c00000503c409400095840641c0400f0b42500e035150b5851102c2542c1c01e588840e0881c803c0390000e04020500e4001c030b545c80d00000c103600108500d0003148011640755411007000b0b0017680c1410308440d030b16818003402074440d42c4402c03030346403007110040300300035030740240000c1c0882d42590b80d441c82d501c4080c200c00702c1d40c215501a640c155402c210000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 780133471 1250 780132221 780132251
    0x412120b1009080105240d020d0203160e0901060f090c020f06090d141837030c0b09031f060806010314010b010203041508040c05130f0f0902180901 65
    0x2000c1c0d04155880791992400c24a9081c29180064124000c085a491807100a404640c0210502e08801c1d185401042c0c0c00e4000581059050440a5090f0041c00146180e405a40c0756100a441c2440740e00c0c0c10680303a840c03105080750301c0d0f80b050a5654104520620480c00350b0f40004d01c8851161040710f04062a103081c0d0790808205903880b80559003d082e13030b20580380c3c12101414000035016452070030050f101e2105203010a186031085e02c6218084d06042c0440104400a03480348101c22036121074400c8404000055070140c0010f07905100000c50010750100760208403007003a035010b4040e1203c45807500342d4502242110180c02c0c0c03010348a07100810786030001c0140c0da0003540500c11080e029040000c11900b1925102170690440d0070070002405880e4010b00c3d400100d007182c0c03422420a669500b00140510041d401441d404181401d403074069189541041c50141070148081044203000200d450844080b03102c002d4000060140c00c2d18000c00904086034014440000861a120400100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 780134721 1250 780133471 780133489
    0x613020f041a09090a03050301090209060403080d0504150b010c0f0203070b0c010207060b06030105010f0806040902060a1e1d010c0c050909030a08131a0a09140102210412120b 77
    0x42102d0207000c0c160000518180c50065003007407512000d08050052524000c1c00c921050240005140d000688280c0c5510380004450045801c55020764803889116500c002406003501c0c2036802505c030f03000d08600c1980a11509880d000f05071105c0179001002d0343d80001800500c035041e42d160260b072100250320601c0d08000d081c480d8580c0001a80c541a900d13000045450101c0b446025000a00050215980211494030385001c54184101d15039220000034016140380c03d002500f048000c6071305941507801041c02018206002d00c054002e01c90701c0b40c100d0b04100b001d10311035911810701d0040701095002e07584d19040d1a010b20030140b1841c0c1c89101080107501d003a9103403a0b96520005040e03c9131940410310980200707030328108c502c0d09003054079040c040040d40042c035031740080c1e114041100715003140e2210881d01c2d484029500e0030180003142500139041100e028002d400f01c038482c2c807160b042c4603800b103110710703404248421034413684102112103c166610f003c4000c0c4e07651346810110795502042e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 780135971 1250 780134721 780134741
    0x40f0f12020c0102070b13180608160905060d17070201050405041104030b1012060c0509031605040b0f06030718170a060608030c15090c12100516020613020f04 70
    0x814410701000c0c00217181802d15440020400c1d402d12026200c011030010650896040410f92440401000d2201c4010080790f8002d40da6480f651501e0710707143e01d14510302000c5035030070b40081146545100610202d1005054010242d800c050144c100c800c00c4140541140c600600d80541000e4503800490101ca80c00c072007a02c210039011504100300141c07407141030343c0120010011107080e864040c02e0204030102d450002e01541d2546032410b1464424400da0b20007010080c11200300300391000341e04516000c12300440d4000e0382030820f001d0701800c00c134030307860039000006d4070451869461031421103504044110a01c60400c260307400240e41a2400180824424080050100d20302689004401c8400d42d030b11000490708107010b00840e1020110365005015042050b59413141d964620785800c12494801c0981e020560032101c00c61060002a5401c0074184000204101e1701c1e1040703008100ca03905250071006034003000000b914020558141121207101070800300c80c02c00740c0300c005010307200c0c01f2907 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 780137221 1250 780135971 780135973
    0x7020a0e010911130e0a02073203040501020c0d050f07081606080106050702010c06060801180c0515070609020d080304050c0a0e011805090f03040635040f0f1202 71
    0x6116070349941c07181c890602d02c94603106103003001c1d8500714042c10307403070303108a451086032174001500e5100e464044400b01640500c0b800001880344244641d01d0782401d2034681300a40554842640d0440002113030150340e8160002c1030803060180c10400f40a14481044030b07680a0070001b5041c1d240108103401c05800d145e0060100240c0c98030f000501d10803d0703030003013040000c400c004002d05600030341114009502807901c142003070b07000d0404801a10300c1c0c0d0b0041e86250318211000101c042c140e82c1703088089200c2c2d08060707a01030381c901c10010202c0036507510641c0c035a000c0040500084e65640f168000501c068001901c0216985030f0340c00f01c2d0021202a00c56400c01c40910340c0358036203104002e025182d0b5a05000880d4101040900010044891a400315545001042e06c601e401c2112000100030384003200d0b034031904ca1a0060820b00c81d001115041000c0134000584a0308150201c4e140d90800d075000a050b903280d448040c080d1107141070903a90003045482c0c000208000f0500d0307003044040e5030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 780138471 1250 780137221 780137249
    0x804080a0b011403030306011704061401060c05160b09011b0512070b0f090c011215090603120e10030203072309100c0209060f150711090c07240207020a 67
    0xc02c4030308000d0043d051282d0400c004100c01e0b0707a002400d00720181e002040700401c51b525894104014030310042040c021210240001400503442206611122b1080054880c648008040c1c1c200c3d20306240105e2a0010b0140400c18003944150040302d07082840080785105240c00d9100c060400851328000140301c078001a03083e0902030619542e0b03400c003445410640c2580740100a5644403c1c0040c04541005009000c002d006010790b00501c1020803808091952603540b800700000811051204a07800e102030165407645901440d4041132164000d0021084030141c110202c00070340c0014105c40c1802003440c1c3e009031680400354040c0a5829110311944c0d120042020000c92100762608a4200f2198550382001030311f0b407202250704a0700684807404d841054100044003c0c80083d500901008041103800911014010034001c1d0351064481c01c5d81601c1d6800084046d2142c003602502d10b4100043e0155098841640040c000480711001420219564002000303247c0c80c2c1e00840000c6884 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 780139721 1250 780138471 780138479
    0xc090203070e2e0806060c07090b120604080306010309140105070c0c1202150702040b060a0e01031121070203090d0507090f1e020a03020d06031209052b0804080a0b01 73
    0x4041094942142a800240142c0c0d4500d2500b000703d912510350810008401c02144044d181d100c282c80a03c0b4142e003d550902d6100c0040d03900404902400511444110080e00c2620074085002402583c00807101840c0d55140001903000d010300c0d880496284264049041400c0c81c28440c00b070080e951540c030043c450b10b8038104030b00c4494164100800d01c81104070f8850059940c0340b940c5140282207a602c94550105000041c0203020000003a038010800191600290ba44204041e40200090301c0800a07048e04100c1c400045c0030b9140d80c010754107078280340c0c80d106280030750145070711240d24412030f442c3c420398002103103040100c0d0034126010703030040c0c3c4103210507081401181807180c4035000c03c010072807004c03000c0504000c0704003003054030940c0060174801040c40380d0112031123090000d5050003420395901d842c5110104a504000001e1403910b0041560b1828951840d612080021101840401c40c00492080340e0400001c0360032103001c000000f9805000d104801e80540100240d800e590300d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 780140971 1250 780139721 780139729
    0x609150e09042111030423180109060e071209050a140a0317070e130f1404111f1107150504080d02120304060f0e100203061002010504110d0c090203070e 67
    0x11441c0c02d00038800413012901207510004159402c075031003241c0b810103508008902007a06008012450b820402c1110b200d13841600c0e03219207a040340c0040c4800c00c0a26a41c400348020128191440c05c006041c0c0d05003401195560b40242c7c01c0c0074043e1040d2443c40100c0c0d80c03000c6a503150030400c00e80c1900a0f0b1002e005154007d14116007a13032002036284030360302c2c203660008c018511a01e81d06101d050b03062607040e001402c0ba405099425034444041000150f407880340f10110304201c60031245070a40c0048400c03503042501000303c008000d1491880410703c0842c05880300c07104125040303541d2195420000f11003405128455485410340c80300d56a80341403040d82400c2c100c1800485040d03500c141c80481014003800101c81d8003035041000001d07140412100c030b9014001080217001c1910445410384131507031840d40103501503601140e040610003104441a0b0aa034002c0b075000d407104801c9054480a030505000c0c8050b0030780b144000050f80c0d500c1c2c543e20001c9800603200b41c0300082690700d001400f414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 780142221 1250 780140971 780141023
    0x1092703030f0c0206090c011103120c07021021020d180f1b0305030703120204030614070e041a060c0c060310031208010806180304051e040609060609150e0904 70
    0x8020b1014005031b00c5c010079820380d54a004e025060400403d0380700c240100c103007803003524400b038190a006104d0f4100b071754002002d900550400d922601c0400c028200060081d090860381d1002e81c0ad180450f681c42c4c144040081d008416030a580c1d9460309103c90285401520008503a0b1241c900380c100d081890a120075030a18002004c0c8540703100486c00d1001c41d400109950629034545800c403100050a84260080e014690005100c1400e01420342c00050b850f0f051030b0320900a130303500d5410a12001c401c02003990000212200b03903566105400519003020070080041d5020201100e0140804402181c51640112040040d00340b544005004005a10241340001c81e014503084a00b0750500000a0312002c02030007110f004080b02d1804054110280255002000010803403000510600d584a030a4070741401428802c900d0310101017403500c0c40d4850101522010380e1148051030902864406035040c184000301440350f0162030304070a070b85034441d8520403841070318082201e03101008541c2c5a11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 780143471 1250 780142221 780142241
    0x4050105061519030b0d052b05040605030c0405220501060203070210110a080d0e01051317071103070603020a0806030c010813140d08010812040e01092703030f 70
    0x114681d90403159118800b080e6400104000e00010000000c2c1c101034008101000c045a00f01c41480c103154148840824424054600080c14250440c0d100a284800382000b500b0040400e1061009100107846031024560150f11003034500d15243e00c40700003800c1054450300c10020f81da000344004801c03841a019440c018403003800218280012640020314540403000d0311010080782584e04600000c08004003008150081c0001755643c1003040c1e400050007200500042960070980402d282468413200451f03525040180c41c40100201c850002c5203500001c0241c0d14090b0421407102103070b40a01c040301c01001642c07001a0b0310400070340b0140940d00021b0829100342c01050402c1540d90300410792541c401804459500040781e1454001855010054002480c2c8102283c5130141e41e00184024140d40e5000c085030511b030b541200151142c450703805080c0c50050301c0d0b0010401c027580c41e04020071103180c111103407482c500d4010700b200507002c049900ba000640c4841001c040c6d10841e2041074218 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 780144721 1250 780143471 780143479
    0x190f02030306060313060902042903060c1218030a050403020a140907080c0d0e060403020f06070212030709050d1a1305250312080714120a0903260405010506 69
    0x50300e0b12a0008440d030100521212100010108000030002a5031000b241b055004004100c5218100408080c10b10058140606007071030300c4511843d464002040d902c114030542d545450b1100400500c21742a00c013500b0036250010100d18080000d02c18406040c0300035040d07484a840b280365004000034020b603540035091110580d020800b03552503481e2072603882013041c1070603c2da0f501c2e2002e01c0030f150310501902d11a8146130803060001c9640c003240081c0281d000758201c4040c3c0343c4a910140e1a420300b62640005680301070794901201c500e5602455100702281000d01c140c03550340010844c480d015090850b102016080b1a05007140445005a00440c0c2d94040d44150402030b034407155504240d01c10100d048000c0c01d00b00321030701c044d0746401015550040e01190040d080083c0030704158070030f0360440d001c10114144428141601801d94031104852f4900300d4442e161031500030010302924005030b00300f003140300c410355100d00e5000c0410344088510b0280c0300c2a02d072904000b030071120043c16007446 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 780145971 1250 780144721 780144727
    0x8010236010309170f0301180e030a0806010e0405010b0a1101110906070809040606120b03011b201b0307140d150f05040b0f060906010807050f0d02190f0203 69
    0x404009940380c4500100c01c0c200001ca9090070b0516100a91122400252418000a4840c2d6600c8048060b50417500d43c2a0b540c005003410000070030595444254a0202d03500a121000801f8403808642d604120706041820581c540100400c054900c03d030890b0411035000140005800e50042000007410b14483c020040d0b49184107100c0210300c10090307024421400440c00101740034a070780c211141032800420070011309507200d1000c2c022556944030302c512146840c0d0f0f001020308041c0034034180410078a08200c4903a5410b001030b100303800702c0701c84540c00e01d803040c080c840b401004200c58030f042d204d401e50811074042c0072020185000310030b8010000411084d000261030381c0b50381021407501ea521500c484100500310b440040202034804010701441c0c241001d0109120311401c0071801041030078944d40c03907690b81c1c0080c044241c100742c6899001503c1c2500140a0b50700c10405815002da02081c0145016125400a8281d0b004044208202c00045294110841d08040c04944403081400030f982 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 780147221 1250 780145971 780146047
    0x90f0c03030d0b010306151e0e090a05181e0f150a0207031806081905070e090603010e010614010807020d12020702060c06100311010c053004080102 65
    0x5281c2c010041140d00040d11042c1c41d030f566038040c0c0c2012018005500c900d41100b0601d2078000c2000da0b1071202d10f0a00d282d403440d40e01000d480f54410700d80303451010b80350080e00e0321104d07440c0004100040c8040381d1742044403150243c80e84180410700d0800c1d46520400542a408407000b41880e0104084c807255a200840300702d40d1203c12600e4a030b010354401401621500d26080560f48540ea8917107505261212030b102040b10b80e00030720003e008418924000700701014101a17182222015500c000104d014580018028540941030a03070110010f0008540001e07483c10142c292005074000d0350280e407142441a40c196405000c2542c0668a44005c02c20740c3e41d00d450140141c541c5242c0c1000c1d07117400040d0141552907442c111200b4400480490342c00345890001c030000c400e80c41c04102c0d0302d01071001801480d0340c440c490b0140065000805000044115124142070802401460310301e00425440c002201105502801c002c12042c40090780e56165655a6024403548d150801505500308071503032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 780148471 1250 780147221 780147223
    0x70504050414100b0a1b05191401060b040e0619150e041104050d081e1b01360f0204051810050103120f0e0603010803090f0315160908030d0203090f0c03 67
    0x3e003c0d0700e030340c940094070700d819400d02c2c030b040142315032854100c2601071004800304855000c0e10035403111140000c00100782c4842410480d40300d14415000101800070120f4098030b03000f003030003b000c6086400c80b4030741c0c3e035190320501090100000e0300c0302080a1011450322410240106640740700c2120140f40340c22b041500042c2c01079504d400140000c1d80200d212002d1520040c2c4011000b20080b98164450184818501c0d003521100c0341040c49500b404070003802c60050340c00d10591400300580c0034403180f8051203100c80c410303d091415618415081c8840780940c4980c45518042c8400d24040701420907521880f40c98056a05500c1802c2480e210042020900d0002020b00121581c50b1000d03110407074200403641041800300060740b107640080009800b25001004094cc4413081d203842104c08401c1c000c06413541c0301580030910301c80100000540c1a00c06c02440840700046003484c1315160780300c2d60041d14503049030325030700c110541c0000ad000c5540420010502c0100c0c0910080000400c0b2001007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 780149721 1250 780148471 780148487
    0x130606080c03061f0e03030d05042105030c180a030302071d040302060609070c05010626010e0d030222060c060e010c0e06090301140903070c1a12070504050414100b0a 73
    0x2400040243c106040813980f190f019070301211401000c0303a8a640701d42c40d2a03401084141e500f10790b490303800c144507610308990504040d8000c50320b40325941076651704114001584d01c01041b9071030340c00c9810122651a51a04d04d02d10146010754020200030b8203003200080d0000020300c040b0301040c13200c0304201c0000c2d070004505501440c00d03182c0c8082c58a07540000d860080500d0780003442c80d420705c41c001c9a00200704088001500c40141200d181c004282401422900300b54107c2a40713030042041c28024070b02030f800603c403401828000ca6a542e108525030280499660401c2e80003921001140060000b140968180d0480341c000030444484442005024000303054820340c007948001c41d045009a42c20740c404003640380c3e040100061481d203404001c2c0c480d8440c420484240710710b0070700464071481030306151044c2c400f261007803854a1118a50500c1440f0001c24141c10030000b0000032800e91030703a00070300580d440c0443c21a21641000d03200300c40e0788045c1e82c110340c80e030030320038400381c100d2035484002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 780150971 1250 780149721 780149749
    0x507030525031a0603161409210f060a020a02070e010e0f1b0a02011409010b06120406180f02180c0d0b1315150504260705130606080c0306 61
    0x20000003040b04503d011045038052640f00d03801208000c03104200e240202c1030000103542d02d4a50051403482d03694075008460361107400c00d000d981400d00461280c0380280728034014000b20b401400605030b100b4540442161401c011315000f08100c0900c540402c641c034050421260345d8034140d81490301010032802c0051410001c1d02c008030201d03c09030804d103050181f401304c400d1040d60341c0d00707001c8010b80a052071050802070400f00c68001202c0d1107040c42507850b0550010001d17450103042070140e06803e0000380080d00c039a0b0f901e010140d15080e4001500000c180f02c0c141c280f2010806004004482460144000d903041c40b550800410000000855510006881001901640941c0800c90440c0c0d0b000320b44072150b16000b19640b070520400d00d01400c0303881c055580850726072104401c440c00c0c0114840c0b6003080c40c0310b18503400c140c0360507604691038100d40310441d104c031652880001c0301c00c884c4040c80e0890316a0744505114855201503d070358003801c1e08044905e182840d0001c21070101855074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 780152221 1250 780150971 780150977
    0xb01261e160e18160c080c0a110904031b060e010c0e01020d0305070917070b040303030506030607021216030c0c030b010911040f050103270503030a0b1008071404030204020d0507030525 81
    0x41d864210b0080c1c09172081e80350030000340341c1c40e401c4400c2201d580300f05166050b030301c04412075020000c5182c1240b40900c600ea043e40d400301e100c13400072030300e11403241c11030f2085500680365440340501e10300900c00c0c0d0f224110360340e40d142204500b110003e400c0c146844086410103007488200b04120f600003e03240700300d40c1400c55200d00503650024160070009242c2007074151980010b000018151f00d81c200034000c200c102c0584034191a660303000c1e40c0d21032402c0790410728490180000901c540d581d8069040300c40c060b0400ea620f002c0b5661f44c0045480341600202d4901801c00c005000340c8916101e0301303148d20013020003c2e18040c02c0002c01a01c42d0303090b10946040544a89000e04c3d2a49001a841611400709030a0900642e036850466100d420441d558000035281401c0e0204600c0c190b00700842c0428143c03602c02068440300c0d8212031b60039030341c0602540a00c08000000050302c813403004003945088000009494100114000d06030384001c0e101020241e045407e500f44908504521920740c08141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 780153471 1250 780152221 780152251
    0x10305060f2808030a1b050d0521070810080c0a0333060302100813020d140a030305090607080105010f120b0d05100b01261e160e18 58
    0x2c1c0a01e034000c0700c0c4200042001d6800d040005048000102414404100d922000d040380300b4003180c180701400c0b0803005800b5038000b95071184018003500090141044c24172a86190090b090740500e40300b0b10646941000440030b00401c120003040071603144c040c3c450080600341045440c40081c0e42e819040c00060146039190028034200d410703202d0b1140084070351100307011400c10f8800401c0c0080075940f10507400fa480c1202210440c034400c008080c4500e01ca044907081c0c1c606181c00f48290050140e81c01c503554100c3c072501010320b58041006207607140c42950049418a416288917082010282003070091054400c01404a44c0e0002c0c1d180396403000501d400310b524009841420007400c0c2c4a04200d0b0000900c413211300038000040703174051055031445003e10400444000448981c10415013500e07840a141002e5029401c01d9034225411209a01d82d10150309210840c09a40020a484408110032800a038400c516006410110310502c111001500c46000b526640f2114030000d10b01c0c1c2281c000e11b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 780154721 1250 780153471 780153499
    0xb0a0e07140f040204031e0c0e0f0412030e060c220501080708090a0b0703020a031503150b0607060510060f080702030304140312010314210909040c030501050c09040b010305060f 78
    0xa0380c1640e00071500013070040c0150078a000c1da03007c24403220405694862100401007002c4030403100345405941032040c4003040b6603035038884003243c18610056804168842c10b98038000d0b00200a058040c10301e0124142d928140401c0c8240f0300212102c1205140c2001b8a042000d03a07040150280e000c0348905004100b03545503800c0904241720102d00074101c490700801c4c402d14540c10340c060400c1d0784503030f1000c118a448420740c03074420603950f05c80209007040601c000a003440c3d10f9080301c100244090900c50518006650380400d07280b04480c28209106911410401d82d90311002e40c080b50385080c10852180d091030350000b03450707200040024145103a5080d40c0d0401060400441d8010709003240c04042650f1280780000501110087d100c815206000d0200215086c60300c008092100c1c000050b440d0881301000d000f00318400600954820b0480714002001c24007c0c000e45103d01c1c441c0344016941d0104900304011180a4a42c250406103080d041142ca51500c0110140501003129110180110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 780155971 1250 780154721 780154729
    0x4180c050910230f03010905060601050a090801020d15120305030412090b0d15151d0f0a0b030f0a090b2410030b1f02060109020c0703020a030b0a0e07140f 68
    0x715400001c92500c030720004a40e2001500390011010001c0360303180d113061070f54070802d400d840c1d03044405052a04607001041040d80a0710090a107400e5a00741105a59660b410a0742241c0140b41d03485a00760f1103050051310f41954854600c0039102c1481070891065a07614001e1540c003000b40024a444440d1462407070f43c5e8002c40c2c1280c01040e082c49040da945c0000c0c214003014001042c6000196003201c50003040354441031250081484099036003820007030003403200d41030003120142e2140d00308440b00c191501e9070320b0b00e20602010f0f0070f902402903900e007066818014800e400620b00c0901514102c491000201c0d00c50340036030009001c03240780180d00c4c0b203441c98480d445400841c140d4446142205800c40540640111140318804c864000a50300002111401d034008050603e0050b00040700500080210f40d001d00704860100c0c0c125014a901ca90204d98880c80c5900241d4081e83c80c0800c0142c02e40b0140034611182032000007610003c1d10b4109189810440b942050380304a0040c4118155611 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 780157221 1250 780155971 780156001
    0x6051e0f0904051e0c0f070b0a0608060103050a17040302010c06020711060408150906040305040501140405030a0b06030d02071a070f02090f090d0306060e0d15050f0604180c0509 78
    0x200200200319905195603554000411200b440f642c404c0a100001c0d610110081a1420303103400c0001c41d403070418590b80d01003100d24000c1c55501159503841003c1030340c2c0b1040055601843c0310f10300514401503a400e1040c0c011405540d04441480704000610050b6844004091040d50150015880c0c84142c039000e105040200020780d086100130a001800c418000303001000c42000050f06020b1b51104220f40d51901d01c2128080d0214000700001c014a5218050a824207404039103003505250710740f40000d0a00c083c0c503c0942d54035296001388006440d0503c140c0c03403c1c0203140000d0840e01e207044240304003410388407400c01108401113550000d210714800388201c200e41c020b2000c1d030b252034000110f081068003528900d02d144076071442d140b07040d802880750005880c400d0721144400050b0394100601c80e003244100711000320032040c40140011950048a005a9850b064000d280c40c00105100469000700c0694120420f1000360501094002580b1415200140c0303150185980c0c0c40711180c1d07482 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 780158471 1250 780157221 780157237
    0x40c0506071103010e071403060c1e0417011a01080601090911310509150d031704031d010309230c130c0e040621030201150602060103020a06051e0f 65
    0x5420982d440044100104030041560f10b5152403460f1801c7d4842859a40c003001c03500c0c001d9083c1c2c1008003a0350519640340b20215000d9180c405c0b441e040d1542d04881d91050703800e50300c14031691110302c0b10030740d440c46d1900c5480074102840c0400e064680240000d04251030b038899010459a07400e608011707560400100c0d02c1e810b00e542c0818014400341d40d101c6619034070055082c1c041098034131000c00e0301d19004c03907094042d10701020a00a40f00e0394004101c5107081140c070440601c00400c80040c5c482d4146500144a54000d442e10360154842d40c00214010360411a140d04040c640001c000000303541b025030005410810071001c5161301705059442ca03200d140340c0c8050b0b100400350422140d400071a041501ea48030140d4407003160500034000c1c40141e42c1503020350075841000c0c41c0004002e040365000d02299501034400400c1c21403542c62003001007500c41c1c0140c401030300b00c41c005105604081643c140104800e161540c6400301c20458000c0d0090f000c10072a074441000a204202d4030240d0047d14501 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 780159721 1250 780158471 780158473
    0xf240b09042621060402090303040303030c17040b04050f0c030a0f14030c0601150e01090509060f040501090e011407020a0b1e0a0506030115050a0b090a080d0305070215040c0506071103 81
    0x9521a411041c1d00f0100078504036074001050400900103003014000e44034001c40282c01142801d04654080e4040e0000040700c1c010400da050900c03c0f405601502035009038012600c0805909003414a00c0c10b10070700d01e40501903648640d01d402c0080d100019449541a004a02121301c50000e151144451040d000310000900c00881d95178100603020032141d040b00e021014094064292090989884000750541400f040c2c404200300403a0030b040007840d0344090003c0001040441540c005000c0764001c1e001160b00075a0390032140c4000710244944c01e942b03030302d01c0c00020301c51030407080c000c6da5600c840f10b009040201200c00f064095000080764901e5582c1f0034520a12880c02d64940f8000b0321046030f45a21941c01d0001c010045040300b0008400d480c8044d100c20b8103303040c081c00040c6c80d48411615504428081c0c400500d045091100241450302e1340d401180d10300b40042d00074900390320315003c0d404a0401c40b003071100040d0700c05000801c4450541e0569118401400c00d0400400c90310002c82d01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 780160971 1250 780159721 780159727
    0xf090f091008060f04030507030509240d0b090103200316140127150e0409061a06120f040204240e16020601210f240b090426 55
    0x40305400340d9090703030ba41c00100d482d25540c443c080100b0040581d005400b04408000714400f180c0f041004001a8001805850602d4401c7c15081e1148074041d00c10f210503000407a640c0081c2c41940107a080c03d8900301e03100c111550441e10703800c454820b90603014624a08444802e4840e40307081c0140100014101e10340c00f805030780d4010883c045416004098006066044038844070348031020103003850740318103000d000510b0605001e01280c52800d85818103015000074000c1e40399546012383c04039984140b0021070707148036481204c0304640003022128440c05040c020b0305506d0a06032a000c0d8002c0c41aa003404950311070b400070030010100c801d641221100e030000be0030841851019002d0842e000301e800d60341e1701d98039003110030300d030849940c00c02c0f006802000040081400c00220603009410b0008104c00000b0203944202000701c650504880f000030f1001c8400e04c620a00d01507411610082c41c0c14000c1c50000800100341d003100500040c07400341c08401c900020050300d040403044001944080303903 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 780162221 1250 780160971 780160981
    0x70b24031f0624020706050f0a080417180901061103161a04080712020c0a050d06060b033903040219090509030705010b04060323120703030b180601050f090f09 70
    0x1c00030001e03c071210140c4036803100000c450303103e501121890f0030718903203072402e2020305101140c0401c0064800e07a421055061451001c4017280020080d191072010030a03505903102e000c0c061a400140d10601c14010b080000c9a40110007008840b00c244840142801d1201e443c0382c843e0b00b49008140c00400155290704000400210500400c0164003980081003089032880e0120395656000a645801c1000034008108074144060392081e43c41c82584049896902d030100e0a1181c3c1045801004a041c3d026000c0035568088002568070001c0100301e2003110300e01d40c0403a4162002900023405032005243c4880c00c074000d0012400681044a414480b07800c0040d24956617030007461050f20b0b19403074007001088514061140d102260380c04104140c0000d120748914210040c80101102c40d40140741c1c2800c1e0039850440200440ea00c42d03203000840301044004d000070058800000322003855528180202a80c00500740c03210f0380c0f00f13031082a81e03900800c2c0118400384612803400f0340000e4031781c0c10f000f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 780163471 1250 780162221 780162269
    0x6010e071e091805161103090d0302071505070804210c06020607110601150809100905031215130f18140d0801120b1506070b24031f06 59
    0x4120b4001204482d4144000c00b8910b045503000e55402d43c00086070402400d8181c006c00c120310803101c15805807420074280c030010503100fa141c440110016000b2590612401c50802200c00c0301032054035080742003900b00c0d41c030040e582c4200c1c028501000c500364550068001080c8648900d00e90141c00d10010590701d2801030360790042640d4200200f000162214401ca00015006040b615070721400d600e101c00303040c0c09856964016256000e180a01c94003150b50700300501402d61101c0c802c100075661100300b250800880000944240c010300d44e0501224100e40c0d844546003951081014001102481d200e800e1000300300000c00301c401e44e110445070105104801100060590f401801e65135600001e1394211402d020900407601c1164012000d1008901c40d01007a0764428414102102424134100c0041e60680019800301d03520762a00e13007049805440b180c119103007c000814200005c10401e03000944918500c20307072540807141c134103500c1000040ea400c15001014044404805524144414 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 780164721 1250 780163471 780163487
    0x711070e10090e3d0228020a051b030604030e01091d01030c0608190f020d090b0603070f0501090b0c030f0f040801050108030703080a020d09080f040905160206010e071e 74
    0x8a801114011440915910300121460400180d0b0028130344505001d110100290084c1140b07100c0c032421200001004a041e604082051060350000c1c5130041da54680070b8600b00307400c0520440340780c1d1a0460880c03a2000210716403c02c1e0300d8200fa41188400c0c2004894102490b80130340e140c0f01e071502d45481d41401ca20ba200741070300d0140a446881503207504081e5030800069070000c101d61b1703007400d200c020000540d2042d154403904101c05440c03c08a03921030000e0b0340440700d0540301021003001748012840c04102000041c034413001c99000c11441c103400071b40944d07014442c2d440c5040d03000903418070b198010300031100c43c07506c07070f4a5080d29150342c4000000c00d50064000d1801540c43c0c44004125103100000742c0781650b80c50b942d161400d40d100541d143c06500561032001c0040d0b00c500c1124001031685000d0b2000b0032100642d240c40c0ea00d00412001681c0d409809013108852100c0d500307641c9580802c04505603a9010348091054031020070841d01080c800c403041040048040d034000c00d8070350016034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 780165971 1250 780164721 780164743
    0x50d020409021c1401050c190c0f03080106120b030303010620060903030f22030507060b041a0a09020c0604030c020a08030a080406060503010c02070e0606041e0801050711070e10090e 80
    0x110301004c1580d00890303802c0324010795a5541d006170920622200b51006a01040d48214074546030002982d90381d91103404004002046011031004801840165032108200400a010a005002d0070a100c00480c1e1030784018010350003045092a8049110504107001c0750a48203a041201c105142020b00389890b500f06454809080c01035101148000011000e8000202c100000410300b0f9450303a941903034aa40310036030442c1c203140c5a400d0005941e44034810350400d541c4603200503040010701010044c00400d90740003244814414401c41a880d00300140b01948140e00d800c00e035440900d0b0f40000398580180e90700120b561304c800507640001030341c040701ca03500551080b6824010191a10300b00340c265101c1a010fa00180e1010f8010007042c013201410903000400a4002c0e40742581341c0000a0803d03101c2c8001d09141450703044104202d8030241318a50303000d280761900110724209500c03c103881c1c03003407481418948400da46c0481c154400c015020b41c005c21880310f04010620b910b140490321090302d109 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 780167221 1250 780165971 780165983
    0xe061803060c12131a0703050703181a100e161b080a030c0306120602090f1504030f0305040504020d0b0a0b0a02122203030908060a0603020a050d020409021c 69
    0x1001c80c411041ca030301036483c1258850b44035001a62501c410040b0740042c0501038403018164806003c107520712642c0640600d0b1590380104152921030300c0982035801071034003c26190b000c8912540450000505150f50390702c0900580d039185c4541d02c8508484130706401c8040280803850601c038882850004c002c00f80d11468841000018a08042e030361101000034014241c607004005001101d803280c1c1c403201e403811050400056558443e0401d0482455021088400d10307400030b440c0010780351030240003500940440d003440c00700d06201c1844200340140c1c03100401e01c0242c01020410180190292030180c40e001c1c0c0119100c01d10b40d41108080d20950101d10300070944002c012485040750400c1344c180e0b842c250000d2400b044082002c0e8410350282c0c481c2e659411509034010340c0030400141c4000190701980d105008542003814150424002401070020b8602d42030007000161501c0c09088210345044950080180c0c0742d0000c9405881c80d1000254895405401901e1001a01c4048141640500303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 780168471 1250 780167221 780167233
    0x1b0c03011107151506080907080609070303080a05060a030f060e030a080f0906072c150a1106010303090501050f090901170d11151f0902090411120a0c0e061803 70
    0x43e01081212054003510080c41d5616800340b09850007402030503009840c140880b20380c0e6135a69020740c24494207440e0501e050b004940e04001f4107902c07415041d00900701c1c01040109040c41d03000141140c1c4c00c0d11004069519485c107141c1401141d5004c0c180340103006003070b03d5030b600035900020301d10103044450006150400000c00e540a40000b001d621030b18084c0c640f5070302c245046100c5450b00150000143c88141d070702200640c2d548950f0703e042400891540758a844c2c624014001d08a0100048018190307032101004002003544603501100702d03a001c7c00c006543c0c100280340c84404d442405c103599000003505000103403407400c5d0303c1e20400856510b01620140d41d0304070f00445c1c0c51442074100c1451540b0003c107804c0000006180d594001c10100e1840349002c0a012203013180b00040d5100c50f00c0154041060442400e141c050f85008010b4182d01620706104054940161031003c1d000302d01c8540d40309461070801e4010101420b030150300401c0a0341712444101c6203101c0b001da05029901a000f03034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 780169721 1250 780168471 780168503
    0xc0804081f0905060414010e0f0d02010c0c11042a021e1615030b090f0105030712021f0509120705040c0c05060a18080c01051005010f051b0c03011107 66
    0x3a100b01c00c40c02d98400c018007041d440d161282e03207035411020503120440d540e62251403991041040200002d120b01c0d0b000c0c101c8086080e0340a03084880042401081c04040e800e418000707003e900c800d01c012074045a0009098045500044660170403102c0c0d01074281d0809011503071241c0000754000b01903510150b0000410304000d100e601c0d580c50144c4c100040410700780c04d001a50300306042594a0b0524070b0300103070031114000015055a030954680048144000040c0502d08050048001402c404884030034003000550119001e1200e08100c8040d175901800322034105031040c1e044804005000f00308a518482f42140305464021621409201d01d02d0301d030b40340d50070700d020701400030180382c004029107403654520050b140905004074850307040e5080c2c4600d1000042030341000d46145d0121000008040c50300b84070302c1d0880000c03500a18144840e541e07030750b8440c81d845412604a5014640307400300402c2685103184c980358101a0f1191b00d9400e040400429504900240240718002d4900c002101c2e00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 780170971 1250 780169721 780169783
    0x3080a1b050c1e010906031806090b090f0307080a180510030c02060906010b16050129010f021b041d0304030317340509030105010801052d06010f0c080408 68
    0x244030300f150100d0780041c4100003a40c000c0e071240425a098101242001c0200d554000071640a140c1c100c4d01d1303403514010300902ea0010000c40100401802c01945082c1154403842c801d801881c3e8010100540008dc480b403070000300e08030400400001e010420740743c100080140180044004003401485403000081d9916000600300c0c2c12030346a0540ca40c0381030001d80e007001c20004641425501c544d201c0142d40b010400b4910006550510403440c2620300e110b01700014100d42c03031000c0e110119840100311782d801c1e00000c2042141500c003241c0c0040c1442c60304442004d079441c1641d415030381d404045000414581c01140704105400c0003141c050300baa0792902d01d008640100b450f56100c0b105640310707400382e0b8142001140005c01c060700f0050305001045000900307582b003d0b000b400c02c6945520902490402d171280c0601120b08040e01a1071444a0403103032034403100024050f81c101320514420320001800f41d20a200d2040d004075040782d1369511000b005a0b103d503844814001d03c2000103080441d045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 780172221 1250 780170971 780171019
    0x10090209011407050c1807023a140f04090509030304230f1204050f01050a020d050a03021c0911010e030307260a03060501080a0524031006060314180703080a1b050c 72
    0x9c1d220300c03503460644242601c2d0030b0164000500010b102c50030045d10386541d44200a0710351448242e1120355214107000082e001c0c0c1da4050030401e0643c1c0241305000c006002503054002e45041100a2842e00940d65202450000e0710b03010100c0e24000c3d640c1440030032034460001c0c000c2c0c81064480f400e040204500464152007510740c640010382008095201051249004101d4403420b40360141c02c144900a100b20802c01c10308090010559810800c002c200c48001e0b041144482401c2131508142107001183d20791203003e000a0007105070076000303002c048803049441110500f0452158583e02c2c2c2a0000d0002d0100307010b201c0c00300d9040000685058032600401d032064418002601000c84041c0c105680300103994036450b858041d0a0085880c0042d030f204450080c03429a4010400f43c02280040b000c001e806400454011041c6c1401e10315040005221004c89a10104131aa41c401010045440c480c0d00640788030710a0041991344140700f00018905403400080b661000d8091658008501040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 780173471 1250 780172221 780172273
    0xc0f030d080403022b021e0a030c06060306050117070902030c0909250f1b02090112080906131424070611030a0510090209011407050c180702 62
    0x540000e000040306449031007010380052090044641c2401103100040c1d041960601c500004081e00c10b0303c0300300d650304120b4a030004250750003000031000d50089140c0c0791000390320082d0034480b189030700d0020814541e00c03940045800036020005540c50360000d05d11605080b06244d290f116020011441005510031a800f0f20000010b2624041c0400207001c052a07004085000e058003842e125452035074001c0606000a50a03a40e0454401c0701001c0034094500c8240340030390a484855248005031200c807059415038014903030003c41007103689026021403080010b22500705030040f9290b541903030210003c6040d030341c0c4600495180d90303a685c14802c103d51207207040c1c105c03480c01441808140b20680010303c19079001c3d00003c901c1e0741c4002c0340401d05520030790f0b414003500c3d550000c21040d03076210400030020307000d508019460300702c200000800403190300c5000740001c0000034080d01040410407041012400141c0032118084400d034203103200c1c0078111075160142c0150312031720b038000c51000200c003598 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 780174721 1250 780173471 780173473
    0x30f0a020708070e01050f0d240e060105060a030509030409060b0405010807230c0a050a0f03020d0c0308070e0f1903140c0a0902030a14040b011e1503110f0a030e0c0f03 74
    0x750303107088108030319107800d9407c4076000303c404111800441e00c00010480c0d01081c403070b031004800191416031401c4032a40c1082c1c4030302e50440310041c01165100320440d01401c0e02440c0c0441d41e80c031426221402c40c41036610403421240307007280c0021512140e40260044403c03d0329103510380d540d1001d007903480359494041d5507000702c0c2d04c1000c00c01440d2140054501d0b0fa203594100c07101892030b6950766107001007880083d42d42c01d41e003a050b00c042540c10082640c1c01030080c0340c0071248040554000c1c0c60640c0290842052007903a150b415099255403480c0d800d00d00004004610341d0180d501d414100c5485d0b0300081c0e40841c00700d58446d00e40301e8002208401c08501501a1003046d00c1c00c00403500a40015010450003030b00c5aa034003515040d0b114a0f180a54010080b84c1040e52400702c01403000d419140d1410703190140001d0422141050b614407141070b08a45c100800d60340e0000f040d0b450075204402030b8108410000c80ca46802e168164018132035640443c1c12181d50780c50138410840c40c0010268030540c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 780175971 1250 780174721 780174749
    0x30510050705030601021e07171506010c0c12030e150a031109060706090809090103050706172514031311121f06030c0b0903061003032708030f0a02070807 68
    0x21f1800408500600b1821a080d91504c41d07c1d5150465407104036406500389070700c03141e034069450b01405841c580214003405d02c103030b0795044c0740d40310000d8268074403070b0f240780b403051312400404d140c050b032030034901c61100070f00130608800349500c0380c1c3c09a0042481c82d40028a490740f00c080810b918021500400e0008007014104150380d44e546000c1e010564044804520038428041c01d5290f41d94107d018500c214098a46a824070301c1c0103107120b400d000b41902901d001000c0c050650000084031103484030014115144040108050b500141c0411024800150010800034424a0f6500c402002031140b00001203052551042000c10b4008850b04681030b0400c0c1212500c03280101c00030341c0e4140740c010300032407815580e80798540154660f9110b000d01107000a0003c0745071600744500307544501080f04071006181941c07030084c8180702941c2e40020b000e0a29140401c429440030682e0014030282c82207076034603020106142015002100c1c3c40340540700b401170100d54088003003030350802d41d042e290040310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 780177221 1250 780175971 780175993
    0x20f0d050318030d060305150c043b01090e0f0105090d08090a0c0801050a06080a0b0a1d12090a0803030c03071214180606010507051507090f03051005070503060102 72
    0x1a9842c0c801000c2400c1d48800c004040c1401c100340283c000640c040d50242c815040c0f1090401c0980000410909248400300400c0c01900c2c0c502000303c01500c0190030704600e0786450b8050020000c0192035907840e0701508400000c100c9815040300c0c0c1c4c48081030041d01c081003d500300c0c840c00c1e81e4007a0b80604003a04000d40c84007200740300303040341503000c01ca12085801010140e00c3d9191503502c1c070740003031110381d440f1000c10800030281e014100c004c0c240d0300010700700c101440c4c0b1441101070001d00008601b030b4a501c5244810b100b0000000c02c001c840320b09440b842c070301e00c07840208a80d0100c10010300985d00311000241074200030065907c5011180b200318915a00c80743c007210f070084c3d00320328060026078901400740c1d410960325440b441003885101c181030490513103c51900d4424020300e1903040000810000300001d402041003940e03101050742e0300103191254802a07540c844260429a8510302c400000410700000081e82d1500782240703170007003140392101d0104650500c8210307161400340e403113040b13060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 780178471 1250 780177221 780177241
    0x90f06011e09031709100f0e06040533040b04030501050c09100f0525030e030120030907050904050d0315030b042901090605120c010e091009021306020f0d0503 70
    0x40380308500e085816150170171140000b18100700031038401d0300003441c0c0ca41d8549919002292400760841c102d40c4075007001d00c4d120000c1c81c030340f2070700000d20b00000880074451511082c40d0040b80e91740003070706421500c95440f509041115002480290341541c20315001c650400240001c43d5135034840038001e1a030403c50030200f45c2c2c0410210b211030301002000c01000070181c4180c0e100361104c1c1e10f1644015503948890400802c1d070456611054403e9140c0074006181c03010035120500f40c1c0b00722a606980342d90343e442d512428800300d980301c650403034160001c010810101145604244641343c50810891218188010004250340002402c00c0c0d05500840c010884020114a0840c44104a21070031402d10100110000c4203034428840c40d0b8039100c1c1440540381003840b451a001a0384010300020a03003400007800f900c0c00300200782c010460303003000c951100401c06000e000391664031410366480d00c2951900340c0020151003414010301071560800c03a881c9010684505071105551b656041d80c464520390 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 780179721 1250 780178471 780178493
    0x160f0e0402101101051017060108061302030f100c09080a050c0111010219050301060906020c060304030309020a0b040b090901080613060b04061805070905010c050d030911090f06011e0903 82
    0x1003d0000b5841e501100074824000e40703100e01200c8104608507403070404a1468a01100011400e603040000103005840b80010350a0340204011284800342004c0e001184c2800e201c11001e107950300074071030300e00803c03503d036040b0040c2c00129565020b8120341c1e441440d529100d500f20014803030b80101d800350f02c99600c03604076441021008000140350030445c8070b459021880070010040880c2011004211050b0030402c0c9038000c06d41c43c005040781c2d2522500042044c4401003008043c1643c6003244000d6441c0c8a80385400f0303003015419181c0e5640c44040300c080301d4000d00780302d910030780c0e94100101c2c4200b070100368640900c9041c6100400f082032581ea00000d0090003240582081d5550f40000301e564000048030748240c402100003800703082c1a50004c1c07400ea42500014188940003100034001903002030240000c0d072807881e001a0040891401e41c2020300d03044c0c4030f0703a800a141d000303012540900a040c180911402d80721002d911728041000040400190048004114030190800124198003a8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 780180971 1250 780179721 780179749
    0x3070b18210607020601050f0a0f051c080301180c0c24020c1b1f0f0c21030b190501120902130e03030109060509100b0a1e02160f0e0402 60
    0x80006503210403803100b0700d07010089601d00016804a8010400b82c100038544006821042c5d82d07000845082c400d403018880000d1040300d004041107502e24000103203c01c1d116050350790100c080c99903941d4a0a20b0310340c28040e0721140601d80e241000703221130b40e40100c511409480e0300102d1441002214032590904a0203468581113664003003000c1042144140042c51001044015070a40e46400c1e41c10b2284103002c1c1c42e40c0c504c1d04071000c01280c1071582c00c007080900f00d0070146498015007049180140c807002d030382d90440001400b44074451540ba80c142c1c0184012160a40300f06001c00c542010440303504113240315050110b5151581078000381c007103810100c8400d00151044400040c0800d81d04215800910001060340001c0010300c640c00f40c078007810740200f20444a01205080195405070004880d120b699107003680011003403400c9001c0c0c024402d140300e2140000d201c11006646c00b03503c404041c203d48003800010500031842d260360500f19000d855664501c03503101d07500d0b9824070420004030701d9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 780182221 1250 780180971 780181009
    0x2150105030a1109040515010b0a09080c0a030f05031314041b080106050f0708040b1c02040315091b0603020307030605010816080702100f06090f050f07081e100503070b18 75
    0x540f41001f107011280c4034020070725020555550900801e0083c5039030140e40200029420044114009940e10072440050301d03085140005c58002070314107039142d0710590060103645110440001001405403007950004a0142c46c24040b0b941c00c501030305d010005042e90000804d81d0324005101c45071090b405811b008980c0d48465241122030745400440f5041940010204c2d030b40010b1443d1541c599044510010040c0d0506504090840e41c54a211050309110a10303041d0b45d640e10704041c0a40c0c114883c1d540d00342920000b12803034403044000c010754000c952902c0440d0030070400041c9544580c151a20902c00c20807013441e882030b0b40c50120381522000c0c00d5042144142c0500d551340b40d003c0d10803070040b9071003072000041c0035242c182c800d0240c420009035a02040d207800200309803034450008140d801142c6191060701582c5001d4010711503003a41e0400c00003000c1440c01c011083c03030410b8411003038803000c5003121004c958030000c01c019485544064a0242d0742e480c007011841c14010301e10600700907080c0e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 780183471 1250 780182221 780182233
    0xd0c030b01023f03040501060506030106020a06150905040b04030306080c0a09020d02040807060c1e02062d12010509011a0a2f0c0906010905150d090b040302150105030a11090405 78
    0x1a00301007107003403c0900e0646900000b05210801100340f02c2d40c4010703c3e0688016003075603d014000fa444010051026001c20348a0040d03140c02d802841e240005044454800c11960400d030a05002032482202c0850210f40303091000710f5440e00001e0050140d032002410450380314180b100b07100182d08034000a4500b150203101c082600c403003e2000001038102c0d50350380c0002c0d600700e040c600c103807401d185c0d500e8010305409025003002d07172a003030111070803601c00c981e11804c0c0701180383e16120000018940040c0c20140450702101e4100921403a60494108030b40b080e1302e80c2d80703940214034003d44441000094a80410200c03002d18020a061801c1d406007441121903541e41440640e1541203811100e8160b4000200000c0680380c19a225a0400004c0c68034100c094102400314a43c1020500c2c07445075000b01103440f820b8429180c0044400302c0c2c0c050300c806101e08103860081e540300c04c200c1301c0c11320100d500800402c460400003100100346800008807104001c0c510107015241a000c0c1054400340141c6c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 780184721 1250 780183471 780183553
    0x1080a1811060910050304120f0507020f010c1509200303071202150703020309101a040e16080f0601120809100e0a0303020c0f0f03151801050a020d0c030b0102 70
    0xb0300e1a4139141c500d9a12029528500b919004000d48401c01c980418003242040010381c00c2d9116003924011035054401c5520b2910722401030b00d078107080b00b60040c59201425942031660086409c40a00c1c41d104650200c40c12000b40c641c0366a001c1ea10601640561080c401c0901107040a019552039002c1030050b01d90800a015841001004c00c683c200d000c01d800105001d0842c0c810085c8103100c8030310300c2017002040720204d030310012181c884481600c25a203440203018911000c0c0107030309285003682c1c0519400c1e95038501c0c140c1c58001c18940b00321179000b480000500c2200701500045010751000e80207251000c10010042d041c402c8801401c10031810750000d070807684904540102850203600101101c401007002c0100b03500950700601d015028007038180b01541c82c0000c0e0010702c1c072a09170303102c0083e030365010754170042000c10760f120403c960070907080c000d03802d2865004102d03121084038203201118016100741c083d1202515100c1c0144d00098800910411000b50510726044260110540101d6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 780185971 1250 780184721 780184729
    0x903151b0a0206061206040525051e0102070503193207080f0c150d02090d0303020904140f0f061906020106080f0a03140913140601080a18110609 64
    0x18214070030142e40608280500c0b441c10404042d12440d00c1d00061400d881c1960b1070300d442c0c482d801032600e0030100c000e040d105241c0600101d8030103040302400000403e007080c001458500f902d9408030f8058082c4003400303c2c145c103004c1403d001e00c0080b1a450003007001a640d0b51442d1074081904041c5000130090543d0442c01c144000001c00f1040030010300e40c250038410840d0800d2448080140755600c0709005649a44403409220780300d40044440585a6850760412400b034825562629032101178240309504050b01503000d808d02140a5070304014140c02c1600200d070145050755449603144800300005c90454801100b56402000941491a80b4081c917480c00140303500c1c3c0c0c0140380540d443d800c0c00d120303006c0200100400c200d0110000c210410300380e03c010301100c46081011164000020355070311951514007200300c00d81003040d0108200e206000a84402d0201600d0345800a41030a0200c0c401d054130340924601c88014445006804606688100103100e45051040c2c00240502c5400e5482e91 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 780187221 1250 780185971 780185977
    0x1030609050c07110102010209010f0813080c1501080705060d020c12040906180902011b1b06080712060303050405010e010c0210020604051002120408030a150f0602120903151b 77
    0x10b01a01698403201d45203007288416500c0d0b5051411684140108040c981c0d1240f604509010f50742030802c8642c0740e02084800500a1600107024008001000b002c1c2c07210010320407501e00010f030750f00c034107590301c5151241d22200984581179100b030043c8240300c110a0b4aa004021038942d080c2211052202000070780300720381007603000703600c500e0f620001040f4009030342000040400383c0036410440c901c56640040d04241805040b82e845100038040d04040140c3c44000ca9004c00d08000700312101e40e84c5802c02440300c0c8044913071100103005d076120041c08841d40d00505050301c0c0d0549490742003c5c1080011140300e00a03403501810003071040c00d848003580b00d4001d226007501041d80501010310349801e000e4035003203082170040e483e42e1041200078003d143e414006900140d001003640c0c1d0302e440d80c1c8804000390111251024060040080010781c58440c0745581007110259003e071707881d5841c1d0660140090180010164058110010810043c400703042290f0307200c42000c0c2c000195011254600c05660 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 780188471 1250 780187221 780187231
    0xc0a0302010608013b1509010504020f060a0804080904060902070b0601090e10050d030509060c0f1207051002070203031c1521200d080d0608010e06150103060905 71
    0x7075564482400022001c1c0030700b81003400b000400c0751814500c0a030f1003200b082c4020f0a40e0b9904044083c8060709001401524400d10308012900810b0500d081594000c0c082950101c1c8118080c01d60411541031034003d494a4445a0712207804507034441e19941110390240030b0040e4002c0e540c40c400b042c00c50480c4060300d1220b014084081040c503080001400050a982000000a151038100b01082d4020103034882902c01c01c0d03c5400c0909c180345025660b40c0603200300030b5400b66011408050794900003500c41400725114045035003c01501d0701d0030841e480788880c0503000f604214040d0156945640040810a2010302200c0c134110725680c80c440341d0800c50011962468803101e0040b003900201e04c010014080544c64480d0501c3e111469144044944c00002c0550044014001e68a402c2d1005500131940c09071403020b20091034540064107501100940b0302d05481c002d03004c602920144603140d040c08164008020f2078882007050740a800070011054101929040003155003021401064019 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 780189721 1250 780188471 780188473
    0xc0a0303050c070b160f03020a081903050a0b031e10020a1205010b1801200f010605120c030c01050c0a0804060806010e04050610180b04031209170618030c0a0302 71
    0x1c80308210243c0c10301601c2e0b8040c0103001428484d01071051060050792407040c0e071055107000b000f4001d1500b83d0504601d414080d00a500102c0c503101d40e00140700403d0a4042180d5080007280d031028858030031117010070079058069104240011a1003412082e40303411180c5c400450fa841200d00358103605036404140f0000009000030402d406841d0346018603805020942c0d140c80c104402c02005044059a0700303641410006c0f50401800703800087d03500f010354004008240d0b008504c2c0c0384241030107000309201d071070301400e0070202c980c0010301d010602441c524802006040f5021803800112001e811668551a0742c5c050300702ca2200180006005000030401a19082c10034549880003501d654044403203075006a0511080040340d50b10360300041c000745032505102005c0b2034003c100000000b203c1c0c112184059000501005105450342100251980750355041e00c0ca40d143c0102c0050240d40707405038000c66200034089000303401c85880011403501c2400403242410b60001c0701c0e51400d0401c600030b6004d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 780190971 1250 780189721 780189727
    0xc0d0e01052211040c0215130203030d02090103020702120102032211040e03130e180102120c030c071b030209060607080405040908070b160f030209010e040f0207080d0b040501050109080d08090c0a030305 89
    0x10040890a1f080d622585610404800c074085401081c1c491203600c1480c1003030340d4000b030102150303030007035060358001900908103501710340300964068000d51050340d82c0d0380100c500c4a2559155200c282603640183d03071207035020301507540d03100030711000c6e00d07400c03144d00b040f07000c1804090b618002e050b0744c102c000c10308601c0d1000d003030070127040528641104010700f54182e40108002c5400a07841d10705a50403a03170044240e642ca80e1420244c900d90702035540000e00f403440240b4081840900380c00c14a0a0380d00071642403459844100c1000141d20030004000d1254030140b108100515240d44a1003409029011940c6094026560710398801c10456690707204c280c80aa000044a81c07041110520720041d0400b145400d00a000281140704a90f5240e803045413030b040300c00d80001298055668541d0b002e00c80a40b991860607204024281d5268a10b0240e8505070002074150b00c074410200031912100050b08051a401908495032100200041c105101e04481c010540d2101503060700214007039507440d61 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 780192221 1250 780190971 780190993
    0x30a0b15030708070507320a0308010e100f0b090d150516020c211c090312020a0c0b03060d050d0309020f04090c2601050c0d0e01052211040c02 63
    0x8082503020780184d0810109000410000324545071241c0009641502e030105025030501d000380c50340c0d2400f940b20f081e00402454508042e0048a124140c1c4c40030800380d40713a40d840e8010401c0d2800b240c46007440d040c0e21400308010064001d0001d1041c084042c150140e00000b649450308020100040101c690750b85400b0001c00b0400a0801c2030300498074070103460160340b281d002600303040301c0003404626092506100142e8030130801982e40f410540c0b00305039001c4040e00314054102682480203070389001d0601d00c0c046601d032020030901034503a07001440682d0541002c111310460b400042406412004a0404d2008170782d04011410090820740d4001ca41581548144125807200200031401241014030110010f4030700650704003600c2d0404001800e0411f510010a00302d403020040200f15403a02c03091118004503440101140189820180502c1c502c1d46281307401c0750b0b012072b40c1c07142614810b44080480c201200d0411011401900e0030703245004e80307900060440c0c1e240e142080140e03000e642060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 780193471 1250 780192221 780192227
    0x1021201080c01140d0c05130f0e0108011104150c140c0f0301050411040c0c1e02040c0e0f12070b030c070c0b0c060f06040e0d0210150f0308030a0b150307 68
    0xd030901000e01e8114208003500d1340000042c0941c05800403500c1d122003111105610950035916540301c00c58185100942d5011190001e072028051a50b00b062540008500da900c1401801d034404404141546420f14049c01140402d40307413039014081092940c04100822036010507a1002c6e11948080c200e614414030402a800900041c9180682d04120030040800e0041449884000081d40e000c03500210040040352580040310004090208400254282c00080100560002e01c02c1d5000c11605041101c142d9001080b01c0707006500a041c1180d42c000c40c10b29a0b801004002c02000321081140c59a5540080e500101c031618420340e004a60304040c00090003a00009040e819095481c000c092003855450705e41c0103008052820390030010600c20346896201c1c10304845c00100f900e182c03400400c402512040d0940a8482c10340c01c1249a0a6900b21342240c1001c40740810003003a0b0349450b55403142e2150304014120001550b84000c44031054450351a102c9c7c0444043d40c0c807658a1030414405 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 780194721 1250 780193471 780193483
    0x603060603090804052806020303150108040b0610090807061805120304120809040501030807020102060906070c0f14160303091e050d061b0507050105090a0b0103170c0102120108 78
    0x8030201410310700c603480031440180803182a00c00c01d6402044610103005002d11500040560403144080302400046907540440654000c0502c9050420001c0f083c000445001100380c601402166680003c1101d41c6007900d010055074685013450328110307076140303421401d001c1c0c030b903100002280f000780c400f00c00003071051041e1002d05022110304179644031401c4560340d01d000741d0081c1100c0401034800d60091040c80d009807200c0c50401802070040c2c9da140c0c80c2026860b0840b0004901511400c40401c06058000c24610320030282981c902c50300700ea140d102c481070048825016107090203c040c0c0501c04803000d110019440c0d2500d01903211a5246280c01028940036074400411507501d01621011007800b49841012200211001d01c01c2400e80c2c20002c0c01041c6001c00032119440700040702503030503000703006494000d003d000200140d0b6902c4440e65211018a80c0040070885181c0040c00001c0c1003160015252004142860a16021501590890340110144480c0c200c0240040101d17000c10441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 780195971 1250 780194721 780194729
    0x26010c0e09010f03030813080c0703060b090a1e0c050412030c0209100e010902071e061a040b03060403050a090e0f0f09010c09030809040213030804030c0e10051c080310060306 77
    0x94a800c1c10300e07540b4010140600900364030800b9480d107511f442403020030070659000c00c41c0c1c10161010b15a0320b03d0204c00038014400c019018a0074036002030107031481da208404003210344005c186100c0d0b8040f01d8031001060380703150300814003c0502000c03071902c4070441201d80c000d00c02d4a886045034100d004200c3c10340f8005040c90303000f07501140706102030003503807140a045a50000c000760b26a003203490450079449d2488404050117556038000828002c00d5040000f000f81c240300c1d60000b5911040503c800d403046d84d42c07040c1d090f50103c4c0104000038416401081640c0311480c10115258a0b10701200c010401903402c2180c0110100501c03440c0006240043c1d013003020100208106a245035010b40000094440680f01c6040414124101e441e10703012503000d0000207801340f81140c4c60b880c3c104403540040c0401e845a200c41100400c02000b41034407103026665210300c1c1318149140004201102c048242d0303040300515010140d43c001040d110295016100302480b1000346418044001c08680050f40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 780197221 1250 780195971 780195989
    0x90302060603190b27011a040207020607110402090d301b1407030f0b16050f09031009140d090b0f0309011d0307030212070c26010c0e0901 61
    0x390010954182014084080b03901c1180c006107941e4644040c2442c1e00900e034400c0c152500340e1307445040405d0640c02500000c01404040c80c0302800d58051200700d01070707000020341002d4100714035800304010000c190405000144050301c2c00300c8076008600102c1c0d072414121100d0f5406110100d00095200581a0100041071b442007851061100140151840a03801c80c000d001c0014070400c3c0503440c07200010754100c000450718965500e15100040e00414402901d60000c0e00c0040b440d42c0d0214040400c104405646d0707941400074800c2c1405803507000614a84d454855100541c00040050140003041030281060841804141002c1c80c2000d01d0364602e0300401854660500c9041c22200603541c054405030f1500703840e541d51341e03071407030060101141c00d580030520b2240b13400c55041c0000081c00014800c6c2e0a80b00300e40001c4003010f911380a140e40c01010340310b03583c0e000e01c660a4210100c1c8840d401ca104950000343c4111081421101050722500020340c1d0064000e0840c2410340d11180103024020b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 780198471 1250 780197221 780197233
    0x303080411060f1c090204051e010f05060921011d010b01030c02031602040915091505010602120a1701030507050f0111100504080d060b0406120c020604080904060b0409090302060603 80
    0xe103c0c1d803a20701c54590000e050002d180d4a68884840c0e42d0702100106502a008000b00c2c03d11401d10f409036540040008035640c4030320004503124858400c0794048980c06400c0a0520707000c42c0401043e070a20118484c800740082c0d4800c007219109006034010301c50300100c0352400b601000603040c01e40c0c1a03030b13030030a040c1070501318144a116400001c40ea8000e4140d9000613141400d0b20004020342000c2d240500807103000725002210385003e6200c00c0d43c0c0ea104900080c000b2150641e1101614024400c900c00741c0c00101e00550088041c0c801001c100c1046e2a00d0075910510008105a4100a80081c0c8156010280034015814144d04e007015214090071700803260701e0342000050f0b44400f80306040e20002d40b01d90100f01085036580032358004250740601030110340c0c1c5806c20403130b85800a108072000900b082c00c2c20101c484240c820030901004ca0b038040c1140d581d0b0390700c40380790b5a800220741755007260341e5080004007403076028003130405414107583c081500ba0f52414003d24110700030341400e200750466 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 780199721 1250 780198471 780198487
    0x120a17040209010b160f060b040b0a06050f0a0e1f0909021c110408120a0e0f0904110a0f270e0307030e04020f0301170f0708070905060d050106030308041106 69
    0x144002d1411684108201031313032810740051488114807203440041c00b10012070544003c002c8245c0020040c210156000c00440c8128030800811130350b103124280c04690208030100c81c13501ca00004041e24815070808203000d00c0c846c0042600700c00b15401080c441c030344601559200a0340302031400c0003070071449030a508055107254051110120f40c00242c859607521100f00003007184460560b402000058140c4214400e1542c90304145d42c00003550100140c600611410300b403a06e112150924107001d07002459650320765a80154000040e0181d0b039200c4d8955000181c906940404d03d0701600c0044c0d032a9100340903500080c0c0300d15100301c046a426504110b040c3c147c2c100000291400c2c9e60701881c24220312103e840100340240300380140c00180c8040000081441c000b12700c944540c00a051046410b0825492200c503200e001c14018a10107802c40c403010410304446400840d00804000c2c90340c070004070300382d0701c41e400c560881d4000c4011070342c941d0411051282400c41240c2c121401d0ba0b14502c7d043c80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 780200971 1250 780199721 780199729
    0x3040209180c04020c070302060a1707032d1b090306060b04050f0d0606050a14240d0903020c030f011e0b0306040b070c060c0504080d0e0307031211120a170402 70
    0xb8401d102e001d40d40c042186107030028104113240c004e50700502003903980c4d95000d00c002c01d8511580c42e580502078250011600944c42840382903040082a80103103c804000d4901d401410303030183d044480d4a449078017000308101b1407294408020b160751149074011b8510b1030801706030382e03080d84191000f00301480100104d850b03400c90845004001c40b80c20700081510706d803441c02040c2517002103030002c1c118840420710f20010f9a14a20046088462114402252400f49540704890000350300c1c0c41014001c05022004a0b00070082c0248a03005131040903c140001c80d00d002c080010505c042d030344480c03041e034281d0443c1e00c11100d5060560420721440d10f070000030030350322540a00010b05001c2d522002803001da210720f4a43c0f082a82c001004c1c000300304a04001032240d0000e014020080c000d0144618000e40980300d42011060081c0c060402030b46942c550040361901983d00350300b8029954122410454180700b5100d41006040349070781c4035459100014042c8600c0840c25180342204020310000d40c1d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 780202221 1250 780200971 780200983
    0xa080c13021312030302070213020a0c110103020706050a1d0609121b030706050a15080a0609020111070905041505151e0a0810050603010204060c0807020604030b0c0304020918 77
    0x10500581d540000d2400c8580c440900c1d03014443c01c0308a80428010964550003c040302402201d81340b102101e1407400354221b20030031166a02160807842c03540002582c168a0554413441410018100519a1103031002c2e207004440c088001592107521162044041d80303480c60b0400d210b0001c2200d0f19150520030343d680001505915040c60100c1c401c41441c5c0508054030f510088501601e840e00d59510f05100901030a0b01d1046029041803003a481802d40110100c0807140c4150003011145017a03185c07940108002c50702030781000103121440961850401c01080104109180020741d842c0034103110407084044030912090741d04000c24080c401e4008070010500074012070302500c0c40d20181c8100016052491586034022441100010303d1174404510442c41180001d002d00c26541c8110030075080344598040c01002c03030a607000c00c1b400704c6c0741030018020b003601c090807051500741c0304e807034042da808422038255180550010800c4111b05000e805a9089950301c2c8040550f001c10362540c5440d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 780203471 1250 780202221 780202249
    0xc10030203061c030804061a010c110f12060106170403090e060d061d01062922090b031e061305010603120305041407030c031e06050f060a080c 63
    0x160084080344503607581c0f01da01e6100b600607180b03159001981c2c0c40c02811840c1c04403030640f40180380441c1c801c1c2080e21406000d00d07000e016552800341c0e64003541c03203005401c01041455000f28030390303162810301c0e10340d510410b108200c110010440c0c1d41c9095002042d20001c10f0400c034848181e5018040001e401010420907901d00c1c94920303409550b45008540c4118407074001402c110300300001540000403400340342c4040700b0150f0007844001e803950510380542c0c080100c812104426095054103e240c6d40c8080c1c01d54241700c440425403000c0004560b222801c080d00001c01c0e09507581d640350070340c0c6004c00c1071aa041d9502a00640c02d060501c00c03e44d245d0000400020540400e0a04107041010a60100003d5640040000e03840a0200030040c02041d04540440b042d034406c07400240c03107003000a501c0003120f5100070844441815991190010860100c0b80146070303501d041003600003021070241038843c148410403004540740500421072041c40e5581704c4e00994005205882540d103420b01820842 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 780204721 1250 780203471 780203477
    0x70b0906030c221403030708220f06030501062601150309050102031e0c1e130b0c0c01140903031204020d020307170105010b0307080406090303060f06030504050d020c10 74
    0xd5a41c00d040000700d20649000070b00001c03001c4081000e84400c6580a000c0c4d880c1082144002a580c00a1550768496090088c010250038800d0300d145468640c8070404001d414400b0240c66a07851940d110011039a412910100391a6401401801d80c085035040a008061541144442c0d000d200f0030800c100c107004030321270311401d01d0034012005d00035040340700c0d016881720007190740c0e141454a000c0c00e65513401b40e9020441e9002d000c80c510f200d100b8151400e5240425161021840b10124019160701c0031507650300d0803000d0840000d80320001005060300641403006000b1103a403000004105002c654900b141160041c084800345031000401e8071445100500103044070b441c7c42c00007403001d142c5410004c1d0b25114101c2c0205000c40c420724000c0c10329005000034007059807519401c440c40d0008446a00c0001d09680001b000300740c0340e407c50001c41e40641800101c0d90740f1f400740c0003914402500003002090710f580034401040000c120074621420030384040c04050701001700240030700d070365505d0003410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 780205971 1250 780204721 780204727
    0x610031104051b040e0411031c08070c02090414010c14182e110601050f0f0a1a0717130308031e01030f02030f01060513020a02100213030b0702070b0906 67
    0x80c2494207060788145840320b45843c2d4580350b8511a08030000c508030350880e51a0f50940644000d0300700050761500040e440d030304501c1c29950020048078103803001041a0704005420540704090307280c50003c0360055009001c01e40e903450003a84401d09440c0704c4040001044000c0c2d02d01602d00a101c4192080686103030101e0b0100d10200300000c03620510400b03a00030310710002029000c01c04080044504c280398a4607000c0e1a00500c1c0051a25080248216904a07040c10103e400030b2400010204404900800719056642c0b12110078400080911903462520000942c100601200300107075025082c241d08480e2609045403c0050306900300e00c4020301000000c0042030841d03940e00c465004001010103c1d40456a582c14544407202d40040181c0c00381c09600c182d02c12030541130117400c042e00c4014045020161000c440c1c0402580900e110310b085028646500c3c1c1280c1090000f000000401c20300c140c0c220342513080c8040b80000283c03906080d0b5015100401c0040c04010550740007034421200c070350b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 780207221 1250 780205971 780205981
    0x50f0a020a090209060c1203100618060f1106010303030c140c0c010e030a050609010519150b0a0c1e050d0519140706050406050f0c04050108040b130807080c061003110405 75
    0x659030081b005485198044c0340700c1d00220ba402000030314461401c079264003002c9542c805069030140354080d0350070f411898540c420b00499001c0c0ca4100481d00d410b190207444819404429420010281c00450029441d8941c009030aa80000c846824147c0c0028151420180e0700049030b803400b01d0100b0728148083ca0510a145950500c6040040d503004803c5d59880d2034583c60351341c02404100c401c0d0481551583e102038013080d0500c148004064a4031240000c2820015280e81e603420103140780c4c04210340d450243c000218a00e40c19031412840c01d04003a449080c130301c0c00f50304004041d00b440d002c10405000030960f15144076000399240916040616000218003554240c2d8410b80034043d25641c242404c0c4010004203900c8548644c0841d4071000d11522110100c0341e092155104141c0019503c101290224640048540e040725525404c01403480481e96140c80b29001090150307412040802c00d4000d1080920616900c40760203282c0d0b841c00c41c19079944105500d00c1d803440360700490391800011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 780208471 1250 780207221 780207229
    0x1a1806040c05070f0c06180b091e06120a0515010219030c2103060512071e090903050a032d020717030109020a030b0f011b1a040f050f0a020a090209 65
    0x1c0300c1607001484080181c466051050142c4207078806d8400080800f10b90114000242c840c500a444003107104600d4500728504120a10f05030090820007502139005480c00355680e6001000340c880703602d005090616008030392104488008000108818481c01503003456070307003c50141011b18a4100010f10708110f810704450f1007a2105004001985000a01c898044010f0b0760807400391050780c062000d2903c03042801881d814850140120f80c1c0031200a014607041c0021038865506043c1480307043c5c41e03a8942440c141d5030000070507808900d0021300722007510b0b40350151100c0c412026011040b1440124402d443d10710141c804407013255804141e001c1041100c120900c0300c0210203500759120350312a41c940c8004c1d07110f640120003091134240c090f0401e08080d003007900c035000140c45040c0c4040c1010007424909020301021581031204050040311210340ca0f0b10507005d030b40510b0001d0790400311841c0013441d06179450901009076003c0d5040e070340141d07502d00038001900c800c82c1c0b0142c1c80380351a8000c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 780209721 1250 780208471 780208477
    0x40f060902090f04110d0c060e04020c030f031e19020c031207020601050406170c0f03190b100801020306030c010e01030e03070501090b0705030c160804030212011a1806040c05 77
    0xd42c031003054000d00c5014080c15480c0b60040b8020484a044100f14208001d101e000c184002040455460f0080101e42e0103400c1649070244043c02c0989851003c400090031a1310040311401c20b40c4010050045405110601d04442148640f05240c24200030480c4080c07810b50200d001182c540005002440d08000d00545a1802d25032001c051030b410030903400781d01d96800340a4076004514000000400883e80c0750b00302112078194002c1c0c90303400c030000103000c00444405071403034240c400c0108800c80203494910080e0542d0003165005042d04121100f49200e01c00c030382c00681ca6070300501c28085655400b0501501104003402d10b0354a114130180160702030112a401d0440d180004900b1405104041d004003180c01d1046070801516a0b4044e0240d03800c1c081951140c416040922401250500c0c595000c041d0900520070a0f00b45031792039000540c80009442012200d945175400f4501d424001c0d03420034004e18046071003200002c1c105464180a000042626106540354180c480e5258010411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 780210971 1250 780209721 780209723
    0x3040f0804150305012309010e091f0b15070510090606080f01020d240b0c1c030209030f03040b18042408070614030403030b010e191a040806040f0609 66
    0x41d40c034111450350b0103401004248540f040c103851890210110500054402e15070440041402c031040c2d0a004a20102d00c070000d00d00140c80c070540d40703203001c103415103030103024500940000415545140c0050002010740000048809c81c0180302c4180018800718407070400c7e807041500064060745504002d0058171313851f800f100c2c0b02c0c043e807411001035110640040828020880042c0140e40303180000d009244d01c14070110300070070070484086c0300403001f480003003001a0003c001c86025a1035100c080c400c50803040305510102e81c2c00264100c01d801c040c801e000340300c070000c000365041c04d1404c0d41070b580a200310032081c125076a0801100c444e6076603e07880a61903556140350801c1040e0035200403e40022180074941c5148621040010550300c01ea100880e220a503980f00b50454580c1d0303034103402400d030880d0002e040c0040580e0044560315444030a881800784024103c02c500d1906c135104540344091603a160054404000a002c203440c0001c60541040d03020300c00d50300076030140c140f080003003000c080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 780212221 1250 780210971 780210989
    0x1902030a0b060c07030201030b09070e010c030c050717011b050d0e12040e0612010c2f0d2006091b130203040b07080108030711100203130803280503040f0804 69
    0x10f9982501440002c800c0140e034400e80701007010120803410400c3c803880868802000950241000c0a00d52050080c11945482424242c0c0000d40c0f6942e52401c11140750003541c2d180d4140048254000300c03d00494044986080c0401800d90444a00500302e05c520744003005041d48401800c0d141c103000300060f0041a075209051929240c03205111040a0800d5821500c2540c142c84054282881032181c81c40740000ca445142d800c0c4060340d0129409010740c0220030b14000b1041500f03a032100c051010081b101030603940c4844004d05207003260300140c9001200001e56000408100140a001424020074240103401010303103444000042c441c80004510301c1da16074004002c1c4802c01461144071402040c0070340380d28665a80f9041c0e000c2e943d02401070080c10206001c1c4800140c0d09101c14081c1403581a8030640303140c940c4e012481086581c103640880040d034000134100e0980d4060003800003011303400501c0030070030030300b03100004295000c06400a821440b0000b4500c00308410541110018407803d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 780213471 1250 780212221 780212227
    0xc0304090f060303031b050a030f090b0a2403050303040206031008070603091a071211041203020f1203060907050315040e030c01052211040b04060323061902030a0b06 73
    0x88030740014208610007200401c0c1810308403070000e441006080403c0300705943d214180950000d007100034000780424402e80550781d204941c00702d0084107038180b1554608c0d0021542500f0401d80f00117034100d20368002c003620080e0405100040c0080708403500140c04642242e00d0361100c1c060a040c40300f41380c0c400c1c521442001e0380090b920340c01d41c00c0922401c1c0100e00e8072480f1252914401e20340041100e0210001d03a08048c80c034400340c242d9101c00c05508100c40384a0500b40c540c4681c5070a0000a0f40c02d40c09a402843d281c000c0c2882002822000c0c66000c004c1d40c154140000801c507844409000002801004400142e1a9002c00740088403010014020b0000c0303810300d42d01e0303602d0b030b40f0414503c840e070350030140014020038042c42000d618280c0004104010f00c11501c501e4129180d52011a520548401e80d920b0180d980d401a00e015500403c203001c01800b80d49400c440b10b0104140c3c81c1c02c182c001001700140e002140d4901d00c82003800c3c1e032025076a0340c0e032207600350000d04c582c00141d54000c03404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 780214721 1250 780213471 780213491
    0xa020d05010f030b1f06120b0a120b01052403041a040f0318030c06050904150305240402030d0c020105090a03081c06030c121707080a171303050c030409 67
    0x7222042c2102d0107025121035644803241520451080420310320b10a400c0750404000c000c1c41031206d203940e40347c442c40c00a480d00900000070032940e016400300c002c3e8200c190a680030300c100c1e14840760042400301d485001100f800344840340c094081c0c1c2ca03482402136001c00018140104000c8100351800c1b42c031020701c180d28061400240c01d4149074410350015140c3d441140308101104507000c00e40e41c00c458844541490482c084600b60b102c4066950030984581022024583c81d145090185114002401d182c641000b4406070a400012080f401d1144020070700c030140e00d01140b68400f9040a140c100709001150005940b1072040c09011900005014000828000d4007c0074118400070f004200c124441d000f0383d402d080c4c400340d000282c62000604000c10216004401c1544040e118012140c046200400701580c290441c08007a0344001c8001204545176070303c821000906c1c0500c1e40540d000d81400c103900501000d06000050601400051988640e0410801c2d01d00503c8440740610420000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 780215827 1106 780214721 780214739
    0x602030a02040f0b0a02162909180402041506020303150a05421e1902010603050c0607030f1803150507140c0d05030a020d0501 56
    0x10070030002440c0f42800c40404004c04c100048561a00c0400c403001e8140820414520144c0719411403e0141e455009400c1855411001010b180c107818200c0201c80e038400c40c507402d40e1200c1d21540e2040c5008060b03070070780d1003a0b100744d600b0301026021040180c1c810145000d820090303081032001440e038182da200c4a12105074010304841945070398102140344440352000310b1010042503a01c101c440105c441d06d00c0030302da4400c06040c000046405190000307026900f40440e0f0189090180c40d445001002500c3c0118071540c120440701c1e250140180c001c3c502440115101c0c081d041d0241d410340761800a6401054158445c0c45444c006a0320071141e50320314001040203021038500c0840418046032120303401b00c105540024003070815040181c00c031600c007024044200d004000c484280000803c801075100d006d428866181d4403414802c0d4080d0098a03890000f05140100008032003103 = true := by decide +kernel

theorem cover : BRFrame.Cov 780035971 780215827 := by
  have h0 := BRFrame.cov_init 780035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 780035971 ≤ n) (h2 : n < 780215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
