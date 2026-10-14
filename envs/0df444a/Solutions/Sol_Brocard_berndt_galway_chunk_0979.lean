-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0979
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:37:33.197865+00:00
-- url     : https://prove2.me/submissions/a76c992b-83cd-49fd-a191-ecd1216d95f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 175899280 ≤ n < 176079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 175900530 1250 175899280 175899287
    0xc0412020402070b04050c0118050307050607051c02030a0201111204020405040f14160f0825031506150809030313020103020f0304050a0b01060309050d0809010b0301060602010b12010b030706 84
    0x440080303030050b60070020030000c0340c1c00e5580340b84901c0c86440144007106030600014071281010306040f201f803480e800140055030b00810b45a003500ca06a03a400d48450240c01c009141c0754018203481e801403805000304a480b640031004003040181c1d0f030020700c41814140344051241c410707010740030b12810510001c100149843c0c2c01c0260070501450130110b03811501e49803218807000802145a4581c8002c411241c01c00001d00c1d8100107003860141031049134540300c40b5584803401340c0c000f0300c800200d00d02019100c041418205006d1500b0181c030403110154111250300801490103003007030f1883c82400a4174598031410501c0c0c07185103014080c41c01c41c0c0751007560300e40ca4000140704905254080c40344110001c3c629010358031890140d030041034404687d0a210300e0161068020400f010308119844011613030009904070700410f285081d41c0d82d9510440140d00400a0034012503041d420300400141035503054028012000040310790350034002503202d241d030807664904071043d010f4000c21010000b9500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 175901780 1250 175900530 175900559
    0x30507021f09090b030c03060a090c03080703090e0c07050717070308160b0612060105010e0a03120e0907030b091b040503030304060e10051e09011d03091005030c04 72
    0x1014084100703440c41c0c0c03000d981c44080e02110441c0003501000080110f000380b80500d00342e02c9000d82c00b0341a03600a02010944804004004401803520707070490b101003042d5860b640d4000c40d00b20041c152900c040d072800410b900010b1188100445441d404250040034490485240a5004000382142e9141000098043c9010449880e990050701c0c0c001010030000c5c0f0041610100c22a03000004071183d20b082960580060141400b450112607440381c1404d002554a041d2502405e04034a528000c0c030010300c00c5049034000402a0f900c0984074100030750442d05001110700d00b21100c514036940c1234401c408580001c0074840e4040c2204d004961301c91030800d400c1602d520381c160311615103074070340c0c0210789190310550381110070707613624200d203000031405000c1002c3c4e40e80540001c0c8410304100717000b940d03824a15006403180c81581000300f01500801d600520003103202c80d0a04440300040c0c0c4403107441e50000010745011b01e130030420800502c0d00c01c0303081303a00c02d0070b2040c06d41e8185814100e15081510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 175903030 1250 175901780 175901783
    0x80105090f04030504080d020307020a090204050105040e060d02132a210612080c1b0f040c111b010e1f0507050a020301090627081626040503071a07030507 68
    0x20080461010030034892000207c4842d0015603585100e841400007203c2151b102e01d04107403050005101e0782c0e03446001c64084440306850654103842e182c00003958a000b03c40002d500048141590b0410030f11908890100e0445070302c21a075071004000c520b5002d0310700b907041100142030140082c4100e1001003042c0070b020414800050351a4543c0304199001038900c9050350300e0040400ca4010b10f0104021021203403a904001c4c40c02140ca61003c24401005070300d035107119a80360406080c1541c801d084117503c000a1a00b210381401c06030845c46c0c0028014a82d1500041d8224038070900c5003814400410041000344841102e0200d03203000702e996130003001c0c08450364000c03910410003590742400b510907044d008410000d01c080c51021031040b41d91002c108801c9003805420000049038103a420f0700c81101903900c0107404551286000240812003203000680d1040c1d0200078100b811010b000307001500c1040d41114003858882558450172101030504210a480030030400000910030b4000e000c805 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 175904280 1250 175903030 175903037
    0x607060519050c0306120c03030403032307050a0b040204020904060f050f010c0b0609101703030109050105010c0b061e03060a051605070c031509080d051b040f1e0305120304060c080105090f0403 85
    0x16440200060304544c2b00368415800141e020f9200d081c10943c820000191456007514649440c405a0302d41d03460f654400000b62001c244d940000c0c05540340c940449403000d000030b00401c1156180c4020054214907030040a0245003001107108440d409503003c02074480d00184800b0740c664500d070402150520040030b86c1010003103088009101e45c5032020b00c0d2195245440655140d605106207003040300c005a000504106011501c800450320b41c282a40c0c0024040c0d580da20306030401400b0200200d8680c807060b0f0140b061100300065041d07a0350003a80207000c0f900000e141031600040c121441e00594038050042c540c852020000030390609804418802401c6012407900b00544a480b650b400c40c0e8408035480d51604104009064048460300301a0b05208189040c1414001042c40f07000e028000e41c00c1292050391842031700340d00051132600440c2e00c0000c9601084c400c02800b40c482e0015142100e0711800c01a9111140b806901064141c07030018002e042d1927603508807000c1303d1039006041030317003030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 175905530 1250 175904280 175904293
    0x618020708040506030c07120206010e0c0406080f090c120a11121e0c040c031d0115060509042012090601060503040609060917090a090b03030313110607060519050c030612 75
    0x74445c48c10981600b009401500e421b6151809003445064014807040249808000134022580c009030307070542011308841010384039595004098941440d400586500040900c500e6041d12800280320030240d01c19a042400e01c409038041c890b0044983c1180e11894000c1000c4410001080040428861391401103420084000b40880d003200c48200d01c88000030f07100c3c014010300d42950300a0750042c012000003082a40d42001c0a003040d07401a02824040100000390001c90382d4550b00004007000b490841d00e451040440703140c0710a51303c000300b000300141e0f01d00300044200c0408505141259495200e440c42c40e91035540d00f01c014055040202c60180c1d4411103080030600c3c080c0c0a04800e1040741045680c3c1c1c401600300b0010220300c0d0700c9003950504042c9001d820784c50200a4a4002c4500640c0d50200720443c6050064010781c0090260804e002007045c00c14098103401c900d004400310300b060b58058500054820654030100c40015400108002042040c00e00c0080341098910b6902510310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 175906780 1250 175905530 175905533
    0x111100207080702030c01080f180304030b0c04050108010801060501211b03050114061303030f090b12010f05010e01091e0909080702090105090103050709020a051207030618020708040506030c07 85
    0xc0707070490101070315074075000b241210450404001780700b1030138000d0a00040ca0b151943c440701e07800d5402440b4182603000080d140b80d00351010806d82e000780d0f0780803c10707012a2801c01001d510580192080900141000000050040062040300195035041e9500c14081000c0b01d040c0c8043d6503d42d0810081950f9038154080d4076039151040c0340005c0542d50041242e5140540d0031401200c00c000340c6214034410040c1026003542c1006c1001140e905042c0910100c006c00300c01d845000b1181d1119010031000510480705540c1441c11a050302c2c807502c000d424031510b860045504940140700c00b80031510400040c01a090070511000401580300320050b2169100c6600c0c0003136440c03000e421690840c003c41c8460441c648200f00501500065400c81e42c1580b442d11056510030840c4911030946500184140d501846a000c8440c00d041010685580f8240910014000c24a6116a80c21a6001c003820401800240211001c0a0704041e08900303050070b00040019035030010f001c00001d0201086141c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 175908030 1250 175906780 175906813
    0x123040c08071d0f1003150e160302040e1302060d02070b1b0c120a03020409090f060c09081e010b0406031a070e0d030c03030b03070906031403180111 66
    0x54040195a407a9482d007002c0601a080c104040000e03140c00058000594660311941c00740c1440a40c00c0360b108158001e81c1c0c905500400104040d000c0040201401003016010034022501880c03521150301d80031800810102d00300d01480c091a4407a11043c0040b80c1c80124003031103030300c44a00041c4840d01d80b4503000b1286e400c03030303011807000c407540050314080004803011040d04e92415051420103600c0c15018000907038a861000c00c0c000030b044c4000c07854038081d9100381d040d6000341ca0544000c00c103806083c10855038070703103038440d00701d801c84d04050044401501c80c50a103012640c60100070444a6040e504204441c801459403078020365070f44240e4406aa15030188600650013140200b504081e00540d21150000041050f4148074246603007100d10703141c4100c1e0b845503e1f0540303042d0030080400d01d0700310040c103003054615078180b082800110b420403050b03118200310303841000c20340c03801c01f80c80300800d44901445130002003010582c03140d0340095004051814005d04c5c5a015103200c2c89200c0d8486 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 175909280 1250 175908030 175908041
    0x5090907030e0c031b03010509070303080112081c02031501021c0e01170709080f0604170304080702090106030e0706020a21051608070b07030b0901090e030f0c0c0306010b070803012304 81
    0x44080895040c002c80701b42402e104540d040380016002d0000c81e800c2d600c000d0603c500620031070400da0410030788507041c00405802d4646038034044584c05a80d00410050300f000e07410986000c81908040c0004920540c0000f801502d20310500410302150810b000b0151401041010624188144c6030104460f608842012500c10341c040e0320785908441c240f13070b015850001d83d2000c460269120780300b8040030503c0c0030199054002c4902d60076540744c0d690300e0b159109015805e030003034018003042d0011803483d405401100045183d00b04942015a44071012681c0e0001100f0103801000402c0260002c042240c0340007080e400142420ba15240540c8618600321964413000d0354002d6000c1004810000e41d92000341c0c00200b0b615040c49400f50000028550b0324040c0304111910390340c0c140d04ca400d90010700544021510a808107500e5030325080440b9101d040c1e2071601c41c800c2c02144008101c0381ca240040d81c100a0b00117040b9802c5a0030010003000c441030141209400b20f4455900810580e160b000c0c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 175910530 1250 175909280 175909303
    0xc12030f12040512120a09022106060f0315060d08090d14010c0302040503100e0708030d0902030f0d0c080c1f0c0f0509010f03091a040b07080705090907030e0c03 71
    0x340c40c03526043c141a42004079000f6202034800042003600f03002900c0d0340201d90040600200020b943da280c2c800212030078440010200c000d40010b15400d040c0d20003061042c030500096641031030030a14001007648034507001181501a224082c0071820383e0806070200e19599200e00300d41e0b40381403150000220300d80f034004c2c0f040360700b400408441602c000080c061600c0080c203d04056040c282400d0000e901c8409800031107904659031b52030220036110400040006129410a03266280e817001c2c7d4401c007030702403181c2c142c0c001d209074907270300d0500c6200041242c9a030440350b590181807900d5a036a16056030106617003c140703100f103001800340e95410a284001c2203000702c10029841c2c2001c000070f4841002c0002240074010148003843c0307140d030002d06680005645e858005070703400007403030030700305040c01810010171340000f1b20200010010840c040502501181d02d980000780e5802c0000c541610034690596007020005000c41c100c0c500a8100c1903c0c407040500307580501c052000030900d0124800103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 175911780 1250 175910530 175910557
    0x103080403120f0c0b090a0b09070504060806060105040501051605010c0c02040b090105061903140103030201290a0504091505040c0501030b06030108060c1b030c0705010f0309050c12030f 82
    0x8080040007101081c01c00b880c1d01e2400e240304000340c0250b0203807a54114900140038018100001250780f00180700b00002240d2091000d203003810548101583d88038103000e401d0085180c1840401c409400091192061005035601803801c0c0c00d10300115400d03082290b86200e040e0100c140b0078009502802a00441c034104d54400303500507400c2c01080291160750b0b004500500ca0040180059243e00c400c0320143e8501d02d8030380448070720101044000340103240c000184912140300100c201941900011210420161015898008285c0317491121011a5210364450050001048941042d0704507488940c000d42d215042100130a8011040d41c8086134104c59119010384148a20b613014412030701c90040541d83c090442d030411011983e50007000d010100445004100d4021142a6007070712a10f100840b4207981d1900c85001300203596140f14090903020a41585481240e907110f0700c26070f0002e43e0000020107030400d002e02030080c0c0d02130400710104540803c020183d8005081402450740201c45078 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 175913030 1250 175911780 175911787
    0x180315040b0411090709030b06120a0b0907080601060804020d080c01020714070f0806060f031f0606030c08150111160b07020f0d0b041209090609050609220602030a02070803010308 79
    0x1d054050f2403102003030345104066803000c0c0810a0b03840560b00047e40d0340010100800c1d15030500080c012510750340c0103021403182030013100400900741c6046000e8510042101d40145c0c50343c060a40f1a9000d0250b00b00040048000038003529201240d00f56039400361108600c7c10a0100f841801c0e42d00c210740540b4990f041104001c820502040424000c040155a50b0142403c00302181e07158000540010301c2220b01140d5814555001c1c00401041c5403481039100140400d007503407101030304a51080402292801007000d01a0b401b81c040248100d05410700820104000300045d00c0b90290021201c45510030141070091400340d100c60000605a61076140d600c0701d200344104031180d88101e10b400e0080b4446c240300d20000b003451040075003150b0303c02100d250420002204440d41070841d4015070b0460700b0704000280d68003007a070126004450984600d18150b07640c0c0c4182c941000c050b021004d44d55010300301a400304105501441d0454451140940b03840200e80f903460309070300281c00640744000c000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 175914280 1250 175913030 175913033
    0x71404180816151a0108070e01030908091c030f0f20150702070f091406150f07081917070e0d080d0522020303090405090a050a0c08120f180315040b04 66
    0x44e0502d8410202441c00408a1030421401024101480220340c1410348a0600707000b00301001059514010700500a813031103100080b542d203400300b4260820740225910102c0d1110f03a5100d01c8280c5015200d03a2603108003104280a4011094002c2002c14480e007c0c0b9001c000c6d0307060074846150301074038140e0300070700406042c00034107900c50980b5444100c0b09841c10540317824646907001500d60050084890700d6004020440c02042c3d4801d481f200c0c48001c800003214000c000d48440a0548580c610480d48030b18144041e003542c040c1800446c1039030710b9411360001a2468894401c8124901c400381c410310001500d55076484e0103401404100c03520356144d8042000710015207183c51482c0048403100140d52401350042a181d210f6012424000d030745850004006103400c000e54070000d507000e0100c804034501810150b41c070006074000d070091030180203081030695440d0b2042d100b0002c14800910310f004a106410f4020340001410541c050090100252100280b0040c4910a601401a001052070507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 175915530 1250 175914280 175914311
    0x3080306130b0d02190e07030f0b0103051905071b08030a1103160c0204110d0903120b0303091905060c030c070518070305101707140418081615 63
    0x50726118040300e240c4645500160340b00c1c402d41d114160151510140008503c2d8030b800b01140c140c1007030f04c0b0541d0440078080307101d505a00c48803410045580410003002c40c14011030568a00b42c40450f54454002c00801078002c43ea4009600100c0310b0401e0201041031892a40040712005029540804003100f0041400105c1c0240c02c5903641040c401881c40c50300c0310242517640d00480101c0100542c903203941c030440d2500d40c401a0b40380110302140da04d416004a0b94030140c05008002c8000076280d821a4042544501030b0b940c44c058020003031350400020700b042c049242d0200c120f240d042c110140d800a85515600002c212014048001e5076680348501c11180c5003802503480240606c074010305400c2d003106802d0143e40c024001c0d103004aaa501ca0b080303124007001507901b11001814902088007582000018014103d1710400303541c80803e0400c0d401c00c01280c19134034100400001024841c000940c40c00001c1c154560b40940020101c40c00c0d40b55444d40340c803445540751240d680c1e22180d0495149 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 175916780 1250 175915530 175915549
    0xc0314010e0705040b0708091302070c080601180f021204030801031406040305192a030e04110405011b1208040209060405070203090d02030304030218190c0915020a05060103080306 79
    0x441690454442c20501d00c000e00ca880b941c840c4520120011510004000803041150301c540d20041070717003007400d1101c001a0001d60001804039a010641e4030006204107000c200c0c6d6040b07034055041515064248121040a440510703040b0064a0342046024074140350064041e000d5402540c841440b0340c118580111320b07070b40c2403900c244154060401c00c80041d40c42001c4880014200c4e20705000c254130600700351011403038000b118444854000042452410414021107001d01a60300d80c0e40344c0c1103840900c02112405400140d50301000c01050041354041c000b180404045106801a0f01c05542c9448442d0414504a034001032412805c0c0825480c110b800c540d00000211400c20080c00d00e240041e41d2441030203009405a0024800c4906543c1c052042d07400035900075016080e42c81c0b0102444041160440e107684100c40704581c5140c1c4c03502d040c46084402d02090b00c4000d80d0304c0c00e101503610300142007287c1008500c102814a0002501888030038000e611031f0008544038100402004010030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 175918030 1250 175916780 175916789
    0xa031709030304120c1b080615040207050c010c020a0b030a1401080c101b0822061103030408090607050a0501060305011a0108151906110c151c0b040c031401 69
    0x5100b4010b010100300d0b85030441e000c01c07005041c5441954410300e03100e010700c2c41030710342101c00ea034000320b0000741c1c081d0100f0114413443ea20101c20200c5060301c003c0000303c1c0141c420180040d80800790066265000d84030104a00d0700042803800755a41c2c44401d1280c070ba00841c0da030b5120a496030101c05100d04804410360162240d81c0107800340512100100e111032011140350f6040151404642202c55121f22020340e1640d0091001d0b03030380710512400460580207203c00d00c7c016107a07040d07001409074400c4500c4511144071101451031500c0da500d41c0c0c00d00350000d913412130344200308120800000e0000c0200265003880349001040c03407495400c100b4210b804662641a511402e800e54162a07a4403035402c03a4000805542c12000707007407110105d4102e105c94400719074030b03500310440414203d8202e8544d42c9144d00440403186408090000e11001110105890f98142d0081c0a0f0b15000144040c0000080c86c4400001940d0b01c4143c0014058030a800c044c000482d580d680418400500d00c05400d0140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 175919280 1250 175918030 175918033
    0x5030c0409110f060c010c020601080d081003030f0315080f0c09060a0e090109050f150a0917031b16060e01020306010903020d03051e030a1401210606080a031709 71
    0x1c102580318481410480a00b4911480c0e0b46204840e032651840b058031a0300e0221002001201100ba0010f56140800e004540d03043c428018007600651007066000e00c00d111085100860914503907090782d000c200031f661031050603180c01144034680070f60503a4800504003003008040d801d070035030000c50a050021308014007645800c02003000c0c90320355101c000e04440580186c2d10381991480d501d01e0042c440d13400000c0150158410203504014005012810b0500d0303159000c0d0652a0444603000f1100aa80010031020000c0c1c841c4248408400185521540210703004052101c1c2a02d5505c0d160f02c0071558240100c1c608540005100740e80c0b2401143c4100307480214038504042001a01506041c80000e11070b10b80d03400ba1004051240050300c40c040c00b00c1300b130800b00030409034409030150001c07180d149078586042c0603c5444044400306504030340300c2850f0748503031452640038001a1000c00205555060b242e0344005000c2c4000c002c5024414069038914400c03a1059180313030824440900071034003a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 175920530 1250 175919280 175919291
    0x30313060c02011505010c080d02120402010807020d020d08040816120e0f1e131a04320603070b040b0405030d08090c0603061201050702060a0b030f10050a060b0403030905030c04 78
    0x18440794013008065480900302205c48042d1480c04051078454450780800c101e00120386151031030207804819000b58030036225881c1a944100b07049035101808154880103920444898034281d01440b140360300540200c60180c9031010700801400460421001200c00c208401d030035002c10f81d4416800310051004882c8616680e981400240c034415900000311581003800360080c0711a5590300010117910b20500c030600a031500710b10014030b11154401c8084c0114200103805101c08503d03005020b030300c0174141aa000d50b00a420003a014094014840307030709031294210208031408810058401040c01c60300250740ca6040c94203260405003e28015014008142c00340901c40c00045800401c3c1c1409485042e201d40e0f03140000780d59500c2040f01c40d03d6952900c0c06100500358007040c100d02c64006450180103000103407040c1a40c91044c4940d648042d00450000401c034280d58110315006041e000d00800ea1036261082e0500a900940c002c901007025104104264101071103d40c0f00c98000f00d408100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 175921780 1250 175920530 175920551
    0xe0a08040b0a0216030506010609060314040f022701050a06030c080a0f0f02040806180d0504090b04201e031009230a0e0c0906011b050a05030313060c0201 68
    0x8180164060300d0205480882c14404040c801c000d80400c611800b451215529078a003000e0703464201c04c3c060000020654030003c00c0d418000c0c02240745404403516250020ba54540343c04604806e1001c049034454021401090700c803d0355180421540104000d00309203525060801c8a14a1325074030480906003809040321030150805526a0f00a4845001040d04e81c00b4404450007010b81e04c01ca08002440400c1c0801d11110001e1024401d0603030305000e004020f006a0700c1a80d91204d110323143d001a0b01040148020f040310342016041c03500c081d02c00302c0d5414108010740c1555100c40f07450842c1075408100390080c1508045ea0700d03d00140c116141d032950030040c1510704102c1c89405088604c58440d11051407880c21020800c00d0440c0c40b0b0910700302c07030804012401c003801c0141c550b41441d01c11000000c0307851a20315806801114141c64541803a415004448454aa07600040c2c510b806508524000f18000788011071051109c1520100440300341d00c0c1c01422241c54032485011a03140100c41031b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 175923030 1250 175921780 175921793
    0xb0a0e1006170c04030308040c0906170f150109020918040303022101030b1308070c0e0a0617150c0d0c03050f0906060d150e120705240103080a0519020a060e0a 70
    0x101034a4151900000550722414032781d403065100c0e03100e81400ea1501400150400358002507000c401010003e0b1540603243c800441c1e0b90b09044241740d2091994400100211141c0e580240414040a08011007001c4500d0580c040130a04039004d8010a800040c030425004c01c03001c8071140d425004855081d594150389545500507002088c10600307120ba80012418010064280e0303101e81c2c1c1c40a06a130000e03440e20140300c0c04160944070068214200030010542c0006140c00b0422800908020325005095009480001101031301014112000700010100402c15016201c120720884d1004942420500c1194145500003404e00c0b959801171300c14415142d0300c1d0400103600c00d401140c1c03050102120420030008040e00303110300d40320384680041e550304181414040c0c48818000e40c00d8444400304450311240d181041d92151000e1001a401480020342d0500a0b003e5020249411403c206c0d1058031154001001e11041001d03901054040c0108a468010075446040103c0900300103c482c3d6200d9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 175924280 1250 175923030 175923037
    0x50f100603020d0e030a030614120606060f120c04050f090411041a0a0e010503011d0a080a030f182105070b0a0902100f180b040501030b0a0e1006170c 66
    0x4030100758000502c907102d001d00e90810f101215501060700da903800010000380003007a4070b204a5500c480d140c7c2d0302c0d078000c4c80c0010008800a00000281c0215a11501084225480a0042c0a428030b007401317020b40b030100034036815220b4001801c00da40d4450916040007086014846028422200300080000040f55403a0181200005440100e810fa0002e55080c101c031452442132900511101400034600020000e0541229000c0c4c000300000c80e03098201081c4004da9450700700782031b40044030310000920a0f0300204042240c07460005047c030f0600220000380c030a0120324060380d042025600003842541000c0c80f055450f049084100806a40000f8085019144010700800d8205c1700040345443d07160054548154001d00c0b021000d43c509001421300b00741c40303044000080b0f80c28032000d030f0241d01e08a19015a248590414186031034480118041c0840d003c8031900b00c891040c00044145500b21868065041803502d41d0502d818204010404000c00e16401100104a82403001082015084 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 175925530 1250 175924280 175924289
    0x6090c0509090a0e0303131509020f10050c071202030d0c24060504050103050303040c0e010e0402060a02011e23041104050c0c03031911070b0f090c03030f0904050f10 73
    0x450080da10f0251103402031401402c20241d602001041044500441d07030b0b03041607103100b8840c004030340074a03244034411a0050340b002908071840035a043e0302490010389594604c1c250b03140080c54185c46220003803d00c03109078024900c0d68000d014000031450300340310042c5800303c40d142800811490b03482d0405000348104405100340d10080d040310102d442c41d000000035100290051015503907901d0090359a520884003550800000e07600030403034242d41e035051030490760548007804094549400304409503020000c168155942d80c802c2400203800042140c86580d548080010300445130a11231820b00c0841d103100c902018050100700010307146c034012500702d48082d100000c469584a0302080e09128140c804140e80c40007004201e030354881c904080300c841c0a0031a040c0181e03a40ca060649050082203001004450780c24009601500000b042d90707400b22044048816204031040170a0070340d4090590540c070000d0020f442c031503905190103115006540440310f40c032189450403400c5410101c0c1e008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 175926780 1250 175925530 175925539
    0x32812080f01051c02030609060402090c0a2709090302060103060e0106050102030d0b010302040b1b0c0f130b012303010905060105090d0f0201090e0f0a060902090d0f300306090c0509 80
    0x30112400c1c04003144c007074155405400c4803840d0034403406003662040e044030120310075006000001c42039404401518035500650704c0381020031015081c03800d0605811440741c0032006104500003050006405241031041c040c0c1c024152950450038940160707603201d505004641c3c1419170402069900104032001c1c052040c03400201102c204004902030b01c81c07540090701486000c42c40c13038000a680c800801800001c0800c946082c03007440e0501c0a6504c0284840d64000703c06080901440b03401d0708800700400051400000c0540009020000c8503240c16860401c010088018081691a8400e45030000b009003001c40c2040881c03400569602d80c071002c0240320000d450440000c5901411400340948010030314a840792a00e003d060100700002c23910082180d04000340011047c0d41c030700c201d07000c1070406000308140e017510b610b43e4100713000c001804540701944100c2108104043c0d40b2001c100840850b21203040a1542d40000c0544100b50009884540740c0407011060b0754001381101c048980654 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 175928030 1250 175926780 175926799
    0x301140607140706050a03060602070e0a0b0f0a0603091104090b040f0c050411091008010308220801020a0c02010206090f0a060f1d0f0114060a0e0402032812080f0105 73
    0x98450b0850b00c80da11101207503c605600412600d4004004d440b411a0b59a81000001d0380c0e40001c0f0317030341d00c124450800198440000f1840607810360700302c041c01b00c0d409800d00c0141c501c044003052182c54540d000e0307000695910807080c204001003640364802502110144503e403602c2d1103541880d4800707400142041044100c0e60304101d900c0e000d071001442c000740b04100d4130b0105c002d0100e142c3d07c0b4105240c80f907602e2841e0519035a004401c0719040c0c0c1d800200460500c0151500c94100001c50100d0101c0304880c40400202d090090000b090f1803800795880d0403c044852002900e4043d001e0020403d17174029800710701030760000240034a50baa400000110741d41c0090358080000703100d000844050140455400c14032400c0c001803140340801400000c01149003581001c1c2e80541d0142c0c0c0c0c0d550700a452700d00c100b02c00c00c0c2048955800500048c03c0d035240046040d1429610243c0d40341c21702e401c1604200071418011100c600014116032801c06903032074604030207420301d607600502807540f0503031743c40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 175929280 1250 175928030 175928033
    0x71b020a060e0d0c1e3807020a090f1107110d06091b140a0503100b06040e04110901090513301d0f0604060305041e030806030c03030301140607 63
    0x4080c2c1d816503604400050803c0303844080c03003414031904001c43d1000724484000024184003204020360030402d80c00c000c0e560200c6481d014031840f488046c03d003801800501030381c409a5100b0840c000207001c003400005000d0b40c101581c2c41a00c04a02c8541d401d10002e20800006c02e031000040030036680111482580c160300c5280c2800106441034014082e901c400035440032489030308030900d05680c0c040107026511340d010070800c860700440b4042e4541503040050a0406112950811040310500410140c03c26889011600b00604100c03810b4401e0b46450141d03100c181802204940501030a0b801070000d0f1600324201d0480c442c00180082240d08400f11070160112044040c50390b0030400000900c03000340451001f00065100c0c40011080c0360400c18045586c0340189800701078100c054895400e00b0b1034520240c00610000308141e070a48203541108a19100031088600300c2c5200741c64500103030800c142030620b02140314004900950041006228000d00000b0616054034101c41c055520703500ea = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 175930530 1250 175929280 175929289
    0x302090f0c1e0c010501050301150e090c120d110304050901050d0f0204020307030f060807080d11030f0f03070225170102120405071811030a02030406090b070503071b020a060e 77
    0x102c41c4100000701c49107540b51140d035498001401040d15a00c0240542d90300c54007018220f4148004502d2060000c4000304040c0402c1c0f96005d03403284400b000d5030f81c2d400c205000305074051448040e001c4076400868a15a0703c42d00301e005002c0c0c0341c0d084802182042c0c00d1034040352821806004c2c06100f4005001c080040012501d07220b000030354080e1042d903c900342840b0180240c1281521407618a0030402e0200e88031100150071011a0040c10041042c80f0b0800b0054034980b1030061240c9480c0410480c00380c8520b210b00042410201c4003405507641d10701030000904203503000300380310100780b00c2507055000305140c8480e040642d0003101d503500e500060009024024441d1b0031680460b11030020410042c0b00010038103c040711080308842010481c04489001101c40d96034140711910014004103100b0501a406103a006105520004580351240c5502564500480700c20300001c000000308440507a001c0f44810304801d445190307203d030310030303940c001080c0c1e410700e005403410084110102901c40d5203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 175931780 1250 175930530 175930537
    0x1060e0d0f060908031005120606010e0a0807060519030203090a110303071b05100503041208060111150709080705010e060d0b06040308040305121207121b08011d010302090f0c 77
    0x14441d4042003c082c0a00c2c000070385030422a45003803041020403001038141824406690001c42c074502030b00456541d00c0c015034141d0100034015400035503080f03012030f0b180340c20000d00000c0c140a45035503440b90070300580d980d402200c4107075200400d80140188a0540740000e0b44120300350340328105088110388100400c0c518040c10b24050544c08a814485401001d080d4107070050307907419126151350854698003a203540c4010740d0000c000c10071540908049074450490940c100c1c905150626842100c0b45419140403d46403154a03061501d00502100c65040417000d0024200342c2d0141c105c0130714000010b01580c9654817640d0103038200280007200811150303c00d00ca041b00041c1510348a640f641080e80c0550064003007182d86124140e8003585a05000095a641c102c05450440031740d91104001c8a84c82034075003c13118440e45610300801184c1d040c2030032604401c40c0390f460011642c9002c4001914074095418401c40b81910030060016881303205686610401c00d4080345125210501000064071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 175933030 1250 175931780 175931783
    0x1d030a0c14010c0e10020a0b0112030219110111060601091a0c010903090906050901050609100c082704050411060f0408160e06090123060903010e0601060801060801060e0d0f 76
    0x140b902114181040d0040c035000790584c025105da00d24505002000c3e80e4a1a81700c034040c12040003100100039080b100380c041910300740701b48182c8a04d44030801202181c0c20050104032480d48101c0404205544d00155525191700c1d150300504e55800c003000040c18a50703035401440403480900f010320510102c400d00315042003050744001c00042c0700a042c0109158114010711503c1410848000346a1800142250513204003c14841c580785240d001c000d0310355210854a812b2100024084021401030005802802141c142462026a00c55038481d4040084100b0605c2145400240301c04113011440320080c0e29421b440c1c8e140c2d5468101e000784210b00035a030081c1014402c11789070200041c01c0104410481d40343c010710100d5922464100048008240104510308001d04950b2680700c031402e504042400b030142c01d131031401e2544c402081c01e540180e0164400c0d0340c040380040103c41d50214400740117120710702e001d1801e541081402023501410800d80e5100350358080000d0140202c2c911701d4003486 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 175934280 1250 175933030 175933033
    0x13020a0e030a0503031008011b050a12060314070605070b010608041a0109020a120903020a06021c02120603061602060606090604080f1608070e010506031005150d1d030a0c14 76
    0xa0a20724015540741d04c1143e030f01c46c100601d0003001610b10414050352032040803c030051121482400310480f20764202810550401c08038074031100d000001031007a64041c1d8080e00c01c1d4164480d001c0c0310a485c210240d44843d0421108001001c0850340828070641558250300e0205416182c5003031948000f08046054550303c1e10700070000445000c40e500805164000d41c40c0d03120001c244a034404111003583c00043c001d43c12003081c2b0800203200f5801000c0c0c5050307010403d509806000043d80813070308402c152400c811803060038045130345420000103510103607000401c102e0011071400251100b1014024074050180031550341c40954a02c01914003601d22081100c15810b000884141d44000326900b410011040380320103c0d90304d00205076842507070b502c00c61107107590b442c000c11f11603268002403040101d410605401301d4140d80d00706400844081c10080241c55110000c00c01d8111802c128003840a40c11520016580074000b00c103890244400b414003000b521381d00e0414510688894650700041d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 175935530 1250 175934280 175934293
    0xf0102070e310807060b011110050405010f02040f060c1a0403021b031212090c030a0302060a060806060d02010c0c03050d09090f020a05070212011407050301050f01020c13020a0e03 79
    0x251000303040e1802120b00744041004020b42c0c801c19020700c2650300588a07000c1040600082122504084c209501c18909002810300d550340c0c090400000313800e20b050151703c800501c01481001d0140d2800c00a10380c1046280c6807405142d580800315510800c028024001404024040540103a14030b0f889009104039143c075241c903000b91548035110301e9a09225040040c2001070a00080c0c01c01c1d44a214042c2502d030803501900381606100090044859208181103009562400e001400f0920710070380080c0120300308600401e05481807500400d00d207a0241041000e80e80c0c071003504941e1160282400c082c0d00e0a0741c01c2031002c881e9540c0020b0101d00c50070449400311584080070340c5c1101d03480c100030013240401c02140300c00da10810b084800080c0d03081c85100050300d4040d0441409218100001034840c1003052001d042004c200c071a4804100007100400417802d2104680c1c140e00070901c0a400800c202c1c00c00541116110490f40016a90100e0243c4150340600c0f1000b600c050010101c0f43d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 175936780 1250 175935530 175935541
    0x40303080c041a03040b0a090c29040306060819020105040509070e03010501290711061612020109141f020f0918070f080103030806010309150e0c0f010f0c020f0102070e 74
    0x400e604c143c0d012a2060450400958648042c0c4100310350160300c1046da000c0c80c0c2c5842c01c4d5014819252001c07100781c80d00b0841440d150401280107000441c070a1802041c030f249090105805c0610607940c8042c0b8904582e1209c0060b80e01c03030201d50070343e202200c07409c3c2952100d146c01c40d00c0c82008151150076602e00300022421400c164038000701d9403003405038100040700043c00400c490094210050490304601c42403200b80c03428a02a0805248252240c0941e6186441b4022481d40080314680540d55901c0c0c01d0040c0580511049800184040284401541c0464515244500401007840203501040e10614050703900c08503110302000810000d84088180045400804103482031350114020305210502c0034040d60b0510b04813601600d4004140e914800107601074a80040c040765001545440c40303401031224891101c552007148004c00c00c0784c0300c22051058001800fa890341c1880208110b05240503802041c801e0610380c140c502c80c08804480340142d02e01851a041000c012400b03134204003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 175938030 1250 175936780 175936829
    0x703020c15010305061317031503060f0f0109020307050306011d03030705070f050306040f1b0f08030901110c0d031d21100c050a180305100903090f0b040303080c04 72
    0x10705a0b070090050310243e03100c4840325584100709a0000b01447d00601e400545540404069907000031142c1c07107401e8003c21640060700307100040302c807070411041e1001071280303e5494880c42070141c412280c04600e0b500b8000400741c2039010040402e8104540159501d085603041c0c540303001001406421641c5502191410a4903540140284110340707501020014071403400190762805035400c43c1c15901d84e89150b07114286080c615040d12018114010390010312076031411a10001054500d0285444005050005002c10302d0b20725003001341e074001411160150f5400c00015107061f45800d100340c3d0030400e8640c10382004200d080c426030104880000d40c6114117088001c2c00d0801e11030041d104082c45408010007218040001c100028405001c490760150003000784201074141d0b45990005181da964645181440c038a20078000380e0384980b51360040542024040000e4111034040b0201c0038180078610000340190311000e020042c042e0013140d104a03200c01210080e084a05550a224100f0845c20 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 175939280 1250 175938030 175938073
    0xc0402040f0e06030a02011407080c0709050a1401030320150906040c06030204080307060f090506041209050a0b19090e010305160b03060a03150b130e06010b07050a0602030703020c 79
    0x10b20140d410319000442500d400710710aa40280e05841c2c040208103510302c00d810030307000600211032400041107100403031801001110010403000002144529041c8016000e07514101e8a407088508207000510000342c00a40c15407034020b085203981e404801c070700c0c1d505151840b00c00c801c0c01494032240900c40303c10404908544124011900c9600707059694004804a20a902c204001604144848000202c6503003111140603998480401c0c032403029180c542c1031100070707a000c485e08000500e907078260a4019664a000340400c58400070114a0100c07420301e01c0c458030000000c68003403130900b040c20a005124000180504183c24001d9603120310b070190740c0f032900d01042c002c171808141c00013071000b1001c0102c81c8200340140042c44147e156588114500140d00c6801c22625284c92034071000d500e03900a080701c2c50310075660100703082c00310340000e60501c601078002d6014007008200c40408100002039014a80ea440030f00182e4950b6810801c034001d01581d522030610380204021070107000b03000340c0702 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 175940530 1250 175939280 175939289
    0xd050103062304110103090f050d0309060501050f01020c0d08120f0603010501210f140d1e1b0b101a0a1413050d05030409140405070602030a120c020c0402040f 70
    0x4080b4003241810000c00320841110700500d0425207502d541c140394440e07082420958401e80c200783c039101c0a9902c142c2881c52840310080000e54030490781003441701c0c90189a0041c242078500c1350b110a0b04400017034a601c0c81124982c0504400f1007040c0400c50b2050403074091210204090009040441c801001982d00b914480c0c03003503090100104840c0142111050f0320100c00302c11500c145803c0c0c2d00c0070604201904141c40244110709500750029050000605142c00d9a1700e001b80040c840c5000e0034010700e885116400c0001d58008a4207040d09031380750304502030700820144841d039540b84c41c0c0f100964440c2c00080928000d40d0145000500c103102038054440151200381c0703901c1240d145640c4502406041000c03510000c0000c00c000d00342012480140c46c00742c81601c1c13405845009440030b80d02d0048131903641c20440c0c410001403103401d03c00f400151140e0710155213842e0300400001c21501c080f0a540c074800d9034401d40c2d010340324000c110241ca00e1034060015529980e0340c502d80340c01e02c1d61030300c1b5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 175941780 1250 175940530 175940561
    0x190c0c05060a0b011b020111010c1101060b03151c0203011a0405090607080a110c030f0a11010c1202090102031b0303090d23031308070c0302010e06120601050f0d05010306 75
    0x31a240700741034003c04600143c184e440c0d1074145003142002c000090034801c10f03814424140b503540f001c100207004160f214030341c3d42c8134001441c400340b070110308542d103591103484044070034030034401c06482c00010300308030392802c892203001c0603c1b00031070121100b0003440003503141d0f01c5d201100c1c1c01c48251222038a4003944c219410016580c03100c01c1144ca48078101d404100207100303140001c00410342d6500c54959580042c201504103807800c03e00310b2456212000000e06c0c2c0c1c03400304040240b40d42c001c880003401c3e01c003400284113402080c1c2014040c88401c00d200d0800355000706a4003201d034800c00c10b550402685c00c4a030200000381101c4607499510581d10ba44080c06010719800302c20703001e148aa0a0320300070b0744212100c103200007241d0030b213038201400e5072031600418003501c408220008040c00c0464052854185954514400540283e00c01c4a80e035004603801d0111018400b2100301c60740d404102820710135038403984489038203190321640d8a11051580745c08008000c0c003603194049030900480c1174 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 175943030 1250 175941780 175941793
    0x1270b070c0b040807090608190201030507090905190c0212040504020d0b0612010f05010504050d0209040203070308030412020115030f0f020f04060308090a06032c1524060f04030b190c0c05 83
    0x123001c5510350024a01003010841c2032505400154072a90107564041c40c079180802c00a41c4407205042590030554100d001848c190104e80c10075800c0b4400d0100c15216400201000780ca48505482940950300c15944140d5020a015102c5e000d260002c41c1080d6006101a030744000c0030129000300e41c1c00703001d028a091801100800e580d401541254180e5200400f10080c2007120307130070490340000091040340c06025054000000401c001c0183d0f000714030032044444c0040c0441802400c41d4010b0388541c400b41400c1d10304001190b02d052a242071650802480741d2034a90314004100d40804018000b03802501c0d00c000002444000d1001d0040440c0c229120711040303669810440541d00b91490606071158540c0c0300384030180d04a00140051420700e4299041d0507840034001c2d604840c215100b21030307001070341030080c0301002c1846a0040180c0440b003080c10080c00f981d2003c4140158007000302100310703081c0480c1e80006200442d02103d02c10380c10501c50341c800100d000380580c8101d50100c51b28800d40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 175944280 1250 175943030 175943039
    0x1b0905030706020a080f042610050c0f221206050f0f1807030b0a020408010e0706051912230c0301080a02100507050f010b01270b070c0b0408070906 65
    0x2040c01c5044500e181c3c0184040300040c2c80e488102c0d84494000006405c041000007440d00b002800041c400132003124989620a00280240c1405100c6017195902890542082584040603080e9080c80744001c6600d612515101c03a0005200d0a111300b80001c0d920600c000120391000071042c00341a0721408090201d600c5200c07454209a0081da6100002006400020b0041904152170700711024100d0032501b0003582c0b80c50701a03243d042602d8540c901d9800240500c0540b20900400141c140c595000701099490224014101c1c020b0801c12103100170b22000e4084114482d4000c0900e960344100c00b04081c0325240c0c94100c050039642014890101c25400207807000700c0200035079048481113406080b42c0b200a500300509031401184800a11500b0301c503420100c2c030104510b44c03904c50131030000a5000c511800241c6101c04818804442070307400d10f030304a40c020400c4000b50817a600320120988403100d0345454202003043d0b4110107034408010400140e00344000451804a5850341e10401150b070f103e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 175945530 1250 175944280 175944283
    0x2b020f030c03030105040209190b0d110c0c010302030a150b0703020105090a11040b010c0b041511090f0913050d020c01080c0a080708060604090911041a0108281b090503 74
    0x541201c01c1841e00144010081da041c80d800501c1e0074000140302c80500ca02111585003441c2d41900602111040401e0142016010b4852401c5041401c02424205580e03420701d555204e0210411740d04054000c0080386052003140c20400d9491514085c0c00d22072912070f074000030990003100e42540150300f840081000d00754041080300c1c0c02d94000c4034515074810254180000350803540031040c10440004014000314107200d031900d014512904020b00c1c600c1d00c01c035001080d241d11105800e0303159000c02040c4516914100c04050303108081c1c5100415581f0800e94882020240d403014040b0301581a02a103603d5001c1034560410000341c907041405c1e11941001c11460080c130002e1000f01e8035210200b45130500480e0140d500120042c06146401c1d141e0280c1030559503850002c4031880002d440d0920580340c503000b500900d1041403141f41510a203100001c045042c0038140b141e000040703946003040401c811090680c031048220051220110b465103803101d88002c0d00c101d40026a410b100401c01e03250 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 175946780 1250 175945530 175945537
    0x3070b04020310060506161e050a0c050a2114030c07030b012702180a1d061e1e03150105030f010509060c0c0f07060309020111030a080103080901022b020f03 69
    0x1c00b0702100d003440040041d007500e1003940d8000791000d65500d00c03942a004043e110700f0812301d104a010300218255494000202041d9030061845801c0da007105110344507c0010164100d02410a4032100082c58180f02e18940740c0030038646454000042d10410b401c1001411000712880760f41504816a0b030345480500781401000032080b45101030200d03480c01240c94001e00f030f0701e41c0d0013170b0004030310a54540040c91079429640811403492031032082c40c002c540c00c00b51142e8000d1040e50307035921030740b540d04903104044401041140304070f88a503d040c5030030b04007030303025641d40102404642c0d07160420702d92006102400d108a0344607200381d5424068a10042c000c083c003c20008000f0111925500b0101a5035000810000c4140c4039003c2803400060041000000509040c0c60000740c90440340001815150700000c0183c40e0780c420002100382a0b0303c1485035044035044020a0f80300d00c5800e0040b42000038ec601e03201404612205c1d00381c4030000d401e0a424418082e82c0840320080c41c0e1030300c0705490b0f02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 175948030 1250 175946780 175946789
    0x902120c0301030b040f110a170d0c080a210e0a140a2013020301030606240207030b070903060f1e0b031207020301140f040c0f030b060f1203070b0402031006 69
    0x15007201180000e40c0303580d4146c07100751040c1c141d500221415400701d030760305610b41e10515140c00301003851030b440b200501500e01075010501d010200c1c0e800c0b41c0c85110769889148100300402a0000b01c00c2484200d00c0f0101e42c46480072039081c091010703103900565880005000645980050b41c01007814100f0010310850350320380c0400507044200d0080b104d11802c00d8441045038000c0d40710f85803c40c082c0900c0c8015406544540700001d2000d007010300005a044241489041c0f3f192841c1031402c6083d00000d2080c200c0e6403201510740e41d030303407103100c00c441c018540e61004026a05000c61187c00c0069a0400c1001c030070900304884414000910103011707034403903180240c1c2541051a000501c3e00340e07400240714141c0003500101e48070b60b41d03152202070b8401c1143c44900703080c601014001040810b1a81000404c68424950781980c2907460b40420550b001e0175880c450641050034481c41c0d00c40040000c3e5274980402900e8030f8100d241801e81302c3d5031044508034884d0040411190f00d40755244507280548 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 175949280 1250 175948030 175948043
    0x1403010501080a0b04020c150907120203070b030a021e0702030105061c0201080a020c0a211707080402030f070605070201081e0402010c060902100e040c020f1c09030c0902120c030103 80
    0x29107884003480002c028000000d500170760200b000244c0c40c0300401882c145500061001402490304911030350900d03665410828003070303041d40c9410016913000200c40d0169058400100d82d80e84841d03a096000b03100b01d1007400d99458a00700c960709412481d0014242c600d0080d4000e200a41e40c208c10003280c0016400400c40d40001c040c2c0010255100c1c09505900c05000500103203400c0220300958034120086400b1905020462407012407102c0c441d09042c1d2a244900f0110011020300007004441c1c00010225820402c0b000001029503a0400c514114041d0540c10b03038502c1911054001c0203a401000300f80d000c0f0340260701103803581d101e100161046860124480130a41c48642c01150061803064017a02c81c0f81c0c0707400c502000341c0e9400707201001c1400303680c0b9480701c0950424140015038030415989804e6410445a000780341c24046404442441001d940c2a050000b000081d546010aa080500500994000810200307071541c000c140035100b0281500d6603070385100c42124113120902004004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 175950530 1250 175949280 175949297
    0xf090e0703090b060909100c050d020c06250207050d030c0f0302030c01060f12060207080c030d020a2d0e030a17181c030e0a0902030406050708090a020a05091506030108010204061403010501 83
    0x20501f0315400020340d115245021481c0a1500b0f001c0410f980181d054a41d40f90044010300c08003200b0281036201c440d035000403036010a03000c080c020b5121030844c07144a0096500b1009441014801d907009403c05500024010140e001410000d6403508810450003441d031910b080403400c00718080c40b150841d903466404010f02059079480d01c001c0c0d0004641110005014000b4041d941010f00140c5200c6042410040c1c442413006002007060019005504010044408070034122680d880c01c0b404414260801c43c04000000780400d1800300129805006a4000300b010340094002c040141a074600c141c000060300c0140900300041e0744070540542000c2d09030302c250000080e01802003800d03001d0f001024103115a5403140040140d030700c121411140366940340308000116802240c1c0f02c1d009819007000300000300c856070108160514500032140f003401c0b202d000480c2c040c031114140102e00d801030706064483d41c0d178074846170103034102c2d01804e0049000201c1c10300c0105c151000740d0f4120340050b52030800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 175951780 1250 175950530 175950553
    0x1305030708090a21060c091202012304080f21120702120408010c120501050f04021303020a030308100b091c05070506181e010e010f090e0703090b060909 67
    0x51540c40309030b10302c2d00600c040720002940000307079040444446410103c1c00020001c4c2c40c01e002210000b102c800248028240f00780030403090254503061255080c2000c6c80a0110360038500000c03030f00ca4a440a20900004012030f046001040300d4100c01b029200325600307428008440401c809900c00c0070300700d4280c02c0c4540c40e919108440081d40103074080c016140e6400189100c0c403901d41c8140c00201c0d05079182d031013488846500c94106401c032101d00c0400c110650516000401030b412908000c0c1c40b0302d03000b1424101e11403004004d00300a540c0100b2001c2c14a03542e1501900070842145c07140303c1300c03514050020711003038503070110703107034200010035078000424508418400342c1e48445098559100d50b100218450300c40d00001d150000e4203d010b50b0f05002c80400304000350300345450380d0110b191642120340059801024a281000e02403c006c04050381d501022542200241d20006ca241120340910841c00e416a00807061240128080483c90351002c0511889031000d0710f00b1000d40e404103141d0103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 175953030 1250 175951780 175951793
    0x201180b0f040c050a140f040606050f07061803020715030218010809031201140f01021204030f020310020703030b040e0d0c03120b0d0503040512060c181f0c050613050307 75
    0x294014458400107010740e484d440851a10045504000090700c40c1038009003280c9050703003411903004c804503424440207040000c024140d001e07022419420a07004a4028108102e50300030000e82c0c281104106000c1c24a030900075990080c0388150700d1a041003094040b81140309008480007510010b003c01d98520b01c810044a0450300140342048600041c010b015020242c400000c0c001c203204004600309030310150800109518109039681990b200e90f0350468210340342c600b83c5040b43d0b007000480000307a00d00d001181c200314402e60411442c0d4400501d41e400c05406a00042c982d110503501000480c241c049e44543e61030b82200c8000c0407070455108100040d20682001d01c0030302c4031030300104603030080e0030105070f0800c2424002c540d130b03400104040c0214103107800700000640207038009040d00c2c1861400603500b84680040794024958020b1460040d03220411404014203c0b91401325081c2204a00144103201e400003c80e03281c010200490150040d001c0c0c050000d40d0804082c520f0503000e55101c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 175954280 1250 175953030 175953061
    0x1703040b030a09210212070b0f0c0c03030c0706060b03011809030504090606020609060a0209152b090b1503032205060c03030f010b0421060b060f0702010201180b 71
    0x10400b50b4a9503241000241e28448800c80f84070482d0300140041480c010103030801e010010045002401400007a01080b210415290030030110346c4000140d843c0c4541412261050140c43c0340b0030300c400001d006151460300c00410704c82d401140204441c0da12401004194802803260110038030000b25400300d074070340c0c035800381d80400d21070b040141c03610380e80e00038000644580d60300460250700130303c0401080500c00e21940740d104415100861400c81524000380c10030600301c0c82a1007940000c03c01c5100708102540c0c141102d81c1c20404070b00c45d0369620421401500c006002121043c101001190051a144000c0360075010300501079400e002c03541001100c400080c200b02071810703c2c0d4010001d02c685494009054000c92100a1a030747e00d032504a00040c0b50041c0d000481c01c03c8d0802003000444801120184003d0071000403803545030417410700700054a90071080d0750f4852070020f1100701c080b00460040440710320070303002131000380e900038591f151810034214044d207015010000604aa6540c4981 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 175955530 1250 175954280 175954291
    0x901080a060906090603020f0604030c0b03090a06050a0c020d1812050313030f0318082e29011b0b190903020105010f12020d0b06060724061703040b03 66
    0x88859492802c0e406440b841c0e4000094103503518410310541c144049158404481681d10a01c0c0c44e00d190761b403610029140c03050251403030001c000b0401041e070070301075048419048141440301d42400740000b030003006892011005849064401fa03452030080c0001001d0203111580c019180c0d06d0306024071100ca4604c10125014081003250741003001d00660309101840c081c40d0700300b00e40411407802405a14180e60905101e882c4550f00300501c0e00001084000940c0c2d02e1100204044c42c0290104821000517101c06107604041c0044903000d008610444455140d00178000941d080340e0043d15020158440c005c440780340e0850b07440104001004594000c101c038071400d00c10b0403001c1040c41c2116030391102140103075101d2004100480c610030b101030113000c0b015034a0304016580e07030001d40702e0010002c0091010655030f00090450f07075801d0a45408542150b08803c07041c19240c200b0342d40c07041084004180a00e403d02c046004c10072141c10145e07900c51b0000842c901400d1082030700b00c6400040c207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 175956780 1250 175955530 175955551
    0xd0c17060102240c09180615070b04030c0c030b1305120901081803190e040b040c08160201060f0902030103060c11031e0913090b15010f0c02280602120708090108 71
    0x91241d444481c038130714070101005500e44103410420304001000311001040c0713562305802c0c0f00210103d1813144580790040e50508100c124070800745001d003400d10141c4e101031700c00301c4000c0400510400d2058019061840b40c0203a030340c0b03a1130310080c05030340d40102000903000034890030000708444040303c0d081008203140030441c0c3c2050401c0700d8007114bc00141c0a00800282030000116450905024482d40180c00300c406100c0350070954002408101300801d002d8040c105021040c0c03e0500070f45c803007805402d910041c401b0494035401540c029500a2104032041450480120b00c1d2131301c503040c05503503003e00c040030b0362130500c5c0c0003c41c4400308680700b82a00c2d4804100614a8242d4860944000102c0d0f92000801c00e80141e0410807009880204540d40d00d80d000d0580e14850381c1d0003480c06508800c0c50500700d021000790f00221301140c0c00d10340c2a1080d50840e490f88001030b0035a0b41500100c074460381c200c0352040f0110461004500503903400400c416414003000c01c180d802070b04010b501011110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 175958030 1250 175956780 175956787
    0xc0909120406050406030609093302190806030c0105040b0a0504080703030c050f0d09090f0605040203040b01170706021b030102090a09051012021005070203030d0c17060102240c 78
    0x401200441c1d100781e100c2c0e0082a40018100b081c41d8050180100428002c0c10801c00c661103615001404040f0a4544090b054911301d007510f180b03004c81d844400c0d5100910111748510545140c00e0780400d558100c0400308589100084061a0000c0d603000c5480341a0344190501d03143c00d598023410740200d0300100c1070010030300000c540b507030f81001aa0011402a030f10100c0c46d961906140341040080d05807400b55400c10711070bc10b10f984e00103010400705c617a9198000b41142e0b841030464010540c0b80c004590150001041c0000c3c040008045410780e032814601010910000350745035943c95052168002503040f1550300464550b0140c40d4000c02c40c4050b0000d072500031001c001911008803900b040c43d03903e035a2824440710649401e0000040c000d2588001440d0b05142c0004102d00c8008070098100100000c2c04401c540342842500c00d4503050200500005034840805408101c02ea110054003072010000142d031980300054003410092201b982100b250900b020381060210003c0c0455101003080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 175959280 1250 175958030 175958053
    0x1050c0a06090c0303030f021204031b0501150e010e13030c020f100c14010b0307030b041109040804030b07030b060a080723030612010b010203030c0a090510020606041103090c0909 79
    0x18000e00708814420076071551044d00f1440c0207412111042e034815180381c410b004140c8440c000443c0180c101e070b01410308000854290311203454264241000501039420700c03003403070f514400900703054090f00c20404e4035100e141e032654549451100100e4112580c024048100404a4082d00c0c0810142e4005000401d4801134480454143c1c0c01c5421440c000480f03100c4030300c050104c0d500b9040c0005219030024091800f0a10003c0e9035217900c2d000c040d1002031010b0200302085500a0700e4940e105010785441c11a00d01824a40a190828402541c20707402c080000365100e4840e116800c90401d000380b400b03040103040070003103c0c4080700601d840b00b8480280607a80d065081045132187ca03a910500265681c07400000340040c4051210048442d40e040ca03010500907a004000d0300da0001c1ea0410041d151340700044100c0c3d902c0344550000781c000b1035184244102503030204c0d0140c4a084151400c4c0200c1c847d00302c0c646154881201c01c1545904600c04008452401c0c0c5562030f080012a421281c0f90184c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 175960530 1250 175959280 175959293
    0x170601050a0501020d0c110315190b12070e09030d0509070303080a060b030a0216021f020c0303030f0414010b1e041802030c010c03050f03070807080a061a0d021c1d1b01050c0a 77
    0x1a580100170040907100c204450602f4001e1409440080d45c0340018840100707040350b610340d07440c0129581c3c0342e903107000140c291008006885850a905205000600304120480d0300c41c411030006800040305400001c503500300901480d01117448403c0000c5c507540d62004220001c2d0090104200700c100d9602007a80503941e4030003181100e00310300003106c40000c075a19010740741c0140c80a4440c00b982042c010042c03481c20342814503130303c03603000030074405482018007005004210b003000c0c4a6119504507010301c81802154034a15404e042030301e042004903444014014608403000c0b00940c1a8001c603010503503544144800303078000c0d2103404c1981c00e042240800c10701c0c64208490080c0024501c03000c0014035540044141d0308103950000400c41035003000802030715087c10b40001c2d000a0070008011880401036811070b078080c14544590102194250b84120103401c2031074041c5c403001c08070060a80701303000c0406c0034000e8a24003c1410003030005580150344e1078002c10f8006d08240101188100801d25 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 175961780 1250 175960530 175960573
    0x90d050901050705072705040b04061d12120708100501050a090b030c03040303060b0a0503040f020616150e0c01090909080403050703080901080708060108040201080a06170601050a0501020d0c1103 86
    0x201b03400d1030090554100803035001c01c011210252a03003402c000911020550b0a038441340c00c15040040825040c80028081100c50180b91202c8000e00c00c030800e54029010310400303400a1300203225251603a40b80d100085540402c00c5e59801c1e40c540780018100303c0356019400400301054182003400783c0668500b50070380e50740c00031100261403803400000c0108169240c0b1500d800342035668007071030811414440c000c2c402d020080c002805240910248001d540e940016610002c0002504080869030380c43c20a0080c111100303520412820460b1810030b07204042050003408006944252902c0d2400c00b200c405803211001c15141c5500410021020641c184031a50207180107001c3d040d078a1391044001801050b00803c00000c00003c603081c0450340e0f0b4801260780d0421b409182502903625440d030b42c0c0c40142501d62020041d0746424003640c001484c08248181281c004440c1076090300d0340d42c4010798039a043c0000701000145010290340028080900d11901840003400f21541c2c0c982d8411410400f01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 175963030 1250 175961780 175961789
    0x231b01150909050106060504030c0909020103090209130203010e031e0d0e12030106080705070c1412010e0f0606040207110915040204180b030c03101e06060806010215090d05090105070507 82
    0x58071400c52000f482424000c800051640740380c0540f400f480c42e156a09280d4080c0143c0c61100d45409410013560300c00d811140c1d03025001400301041e42010303440c600101c1a9040102d009509044108080b110084190b540845100001418025400b035000c074142d405694214911981c8100d407420b0500c0400803410031580103078800e40d0301d50610b07102034010300d0010400d0003000b50800031407000a030900c0c0480d0840b2120041e0a54003504440014041e08909520010715840d200d44a400c02c01c00082419240c85940107859080c1c4405040c081a40300745100a440c1003005958001e81c0d061602c3d44540c0701d1144c040c1485410070140001d810399129621116207401501c0e610a81e410591045c165842c00490090402e0000c0c01c01103516051a007003400100707603850403a01034800d2546581e8620000d0364008000d0307561a1000030300820bc094a2480c011310451000903c480c903c0072103036001d1242c0348000d010b0b40107904400c0b00c20b03910021625040040500003040011001c105000190 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 175964280 1250 175963030 175963049
    0x1e12030d05011a0a050403120c1a01150305060f100207031b0512010b0907030c03020904090f050c01051e1605030d0f0c020d1d040603050715231b0115 66
    0x15498006000080380f540c1d4031407528030004100c0350782c1254100044a00b169807081110300d0903843c41006640071001078001130300184840030741c1c80300141d880311f5090580d00b000058421190000400314104c90701290300d66000326015151441f140340010200500c08010f10445070b1494580d41c074143c160001c0a050f03510003011070700a00051600c5814045c0d074030b02120080140d0304403500012180b0f01d01030003101c285903440c10491441803194045400e5400c5c040c00500103046a46000344840414803420740700c038040d1a091908a61242c0115040510b010000700d501184080d0b560307003941c0c4051040309610301c10030f01060000d0307024005013040c4071f00c0710300c00a401049405884107841f440c00c03216045400080c1e040031550b800000c0b032085102040e00b041c0102e511100801e00510082e00007500c184a49580010a1201540c200c400100969902d1110b03c080c0100100c4085003107040b080c0e60b0409110400c0b10805505100c3c0e11090038800205000611050742c00301c616564015400c0c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 175965530 1250 175964280 175964291
    0x7080f1e04060e010c050d03051503030a02030903070b0c0a0602031302040501030b0609100b0406081e01080313050406050604120309051504050a080601060f0c0c151d0a051e12030d 79
    0x1600d810a0f003040b0740c54404e080c000c961520310b60300d89843d06001140c041c10705640e80701051046451960703001c0b0180d809001c4999134848000060b40e25048070344040e2007845031000100d8101a0102600c0c4544040e03001408424200da48400103034100401030303041d0043c01520800569101d020b1a0300842c007a004041d2141010303404d000724200300a0205d0340e003074407154007042841d071144c5c02c43d0b08460540c83c1c8005283c45140155070764408140d00300301c1454949001141148010008090410350800384802e0140c0c1d0f0307800c1c0415140c4a00c81da07540042d0034070003005041c02c1600c02010030341c428074100c114651160b0000f58000304095148658102c0440c4c1808941130903244e21000d00b2070100140095031411000130f0400c1800340260081000700e0340e000040205540444000e450381d49280d0a0f006c1e210200140082c20070070300019001503014481080d07040140401054a001400c3c5840d090303040d400e64004580403c0495401a0500c000380010602c1480503012544803074802258 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 175966780 1250 175965530 175965539
    0x501090606110606010f0309051c030213171c11010e030901120204050d080715020f0a120c020c0609030c0d08120702070b121e0403020d021006030807080f1e04 70
    0x1003288244a40302142c3d1100041c000c503603030488055a1701059500e00455010074034580103082144e183c00c1c84012001c00030355580745c00d4040d0054113811034450310411071641e54402d0980340c0c610b046000740c441e0b000342d40303000354851040e00c180040d0101c604080041e207103d209850308540496070582560340012035400c1d40b030340c0d2101410010180078041941018201702c0045c0640c00000c40040070341d10000740ba00200035900110842100051b04119212241d0340c0350086182d0110500c1000070b0384907050041c2c00c3c90540308462042000340d009210340d038449402e20200d0f40c828811194980b0608040d5003c580d01c50141040725071145880985641000c007010a4401010b0509004d540040d102840303454141004d0f5141c0800b400501c00044c2c071014481c00c0525a501300740c1780880b62000030003041c5500000c6078036481000750300b21400d0012840c1060308659160000038500706040200034041303202000500072480720198078031314006449244503000c1c00c01407500d6003a45c00100d401c01c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 175968030 1250 175966780 175966787
    0x1605040b0a02060603160302030c060a030b131b03060b031602160f0314010203040b0403080408040e0f18070803072006070309150801060f0305090c10020a050601140d03120b040501090606 82
    0x1d0f092280b0310540711b003880c2594000307603e030040d445c3d489005950208120303041611a07013160303500c3e600c090603610b050640c2c1300c0301d00e01503c11040951140800c049061405174800d00c190300071503d1781d8404a04640b5000c0344a03819502031026101184103c010b138111101e9016100e2000309a4220409240c501e1898039440d03001d90b41d00f001e50580d1060041002080c0c0000b0440c0e40540c1c107140403121075a880c075000119008541000c0842c03280d035000c00c5031342c80b401004a07004041e40c40111003102c0c2080f040a03540d0358507001c0c20006800a21401c0000360035200c01d6003003004001a4207041c0038601c03010070829040b04a040d0009400078800b0414805103616245d00701d0ac00b4505102d0f20740c14000040d0980e103100c680082050380d00c1000032000c007000d1021070a980c00081400c14081c0c1d85180083d6591514501070b15103014000c000038412440c0342d122504800090456030500d81e054a00351442050543d81846036611452140da0a6940d882410f0103000303400000102d4070308082004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 175969280 1250 175968030 175968043
    0x825020d03050a02040f051302120109290109050d0201021c08061f0504060c080d06080d09060c17031008010501120303061509270905010f0c0c0b1605040b0a02060603 73
    0x900f0b0040c810442409000c098403107205c19680240d07611909500b001d0000c80003441303074030807a00704d20303000300000b00380705501da0084071400c1c9070a142e515040510004100001211022150100d910003e00300464101040b00c0d02c94540140181e0310070700015409a54200d0390f100c24400090315080800c185442c005010841c10120700840c0d2418900140d400b80c003030f120702c0c0a05002d000b5044040300400c4100342c00c88103d0541541b00b488110380d80c0c1c40007070750740c00c000e2480c0300811094030022481c6031107096000e52030764004603000028020301e00110010f500181c004480904c4d10500458034400034041c141c0208020072402030a2001410000c0441e50550465640e01c89180060040301c1c2c6d001080500b0f8074014861011144604031520540700d0318094003518081c1443d1407901444010350001040112140b01400100e2841200700d60203404a00c008110200c6000840d1000f030035040110540b2119003419480c05489800041d140c0d0059040680181d012004101550500b840304 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 175970530 1250 175969280 175969291
    0x90503030a09020907110705040b1309030e01090503010c05090d022709010507050306010c23121b2a0d0c03050609120406051e22061b0c0302010825020d0305 69
    0x10090480c140c1c0c8803591207c000703106181c4038985803030340b40c5040d9965191480038406028020070601c40c0c01d1074003400c1c0140204045002c10b400c1c0100042c3d07414180039031005030056a80700c03854000703103c0c10031100030815071041c0c0c0c200c10301407070000d0301d585111090303215080361107446034181c500700d006c05007554001000c103800c00c401031090102990300035208c15910340c1e214040c0c440304180344901c04020058120350880e0fa100d08508400e900740741030000c2c021068a101d40880c481c210682050b5610b071802c1c1c401c80c01d40e41c60261010700a1340d801d0311822800c8001c0089442c0d80d070948034078085070b41d5a0000d8440b500701c08103100c03000c4803c00c0710401c403810305451141410318012000c3c1c4140034004d200c81240000f41409018002c5e5101141c0850210b030160751800442c03031002c011028010b000d054007142d4083c802029040ca02003403070200c1680140d00314081c605550045441941c0030382401c488100d0548031071900700603800d02c071021010960003000903020281d8000c0a03034401400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 175971780 1250 175970530 175970537
    0x80c03010903080c0d1401060f090b04080c131107080315030606220b06130326090d151d07050105030c0706020f0d020d020406030c1b1203090503030a09020907 70
    0x4501000079040402144c0c0402000d00541e240d000000c00301c0c014041e03000c601c10140c0146000800d60680024071040c84403c11781c0c4035107074103460708006c00b083d1207107020b18034103540071211501252030112089441162000c0340821003400051194415070003400c01242c0700040881008038400380c0c00c40007500c86004030004c00060825101152880030070500d2240022501200c180f20514560061624960050441c565480007070030460740e0100c0c940401c0700c800b001c80300f1003451440708502d000b503500c8006100610345030030300b010000c404040140c1145c0e90749540c0c0e481d0307049400522071840809100001280e50b40c3c0c0e10010751707003043d00d6500000d040c0042030061150007400d0900b5221182d622103401030f83c0729a0008001e03660b0050180050134503000280a101800b400d4018004880f40b5803001e010000082200b80c0f0425924a07200700001c4d04150003101155400e120201e049089090008005c1200d407106805e42c0d00442d01401501d440704480011800c0000c5426808001480c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 175973030 1250 175971780 175971791
    0x20105210118090b0f090c0904051e070b04050103200d0603050c010c0b1302041103090312060909030d0b040209130b090c120f070e0a080115080f1002030a09050115080c0301 76
    0x1e541c1340e280040504024000300c00b0300002110070000300550015031000404005540c9446e2900c1390303945400750046100880d002c10b14240d03140e000181e0406a17140d00803000d0505003400c00450041001c540f001400c6810f401c00c85503045070420040402114125001c2441e90071414075502d82211319007030b50304021999030400080703185950850340080151413140c184130003500000d0b0241c1800d4004003180f44000040c009001e400000410f9014512010942c141e80c410301000825601207c0780403071904104841d895400c869400f40e0018030300280b0050605035040c0104020044426034030b55496941e100950003450145030060303002070340700409440c1002c4010b1951041d2406403441080040610102d0421750240703801c0e1742c4ea000040c008204150b55091454040d040c00c44084424015545002c20b0900b0040356103003038011040004c4c004040c0c550035441c025032006204808469842c403c200020300280918080d400b500400000403605000381b6506010280401038400d03890708 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 175974280 1250 175973030 175973033
    0x302030f1c1a15030606040b04081f090f0b04050709020a03020913060b1207020309040203160e0d0b070f120e0a030929091f02070f08030309070e0402010521011809 72
    0x800280ba0f0b10721481492620390301c401c40415124010340d0820080c4550114002c2960000080c502e0f00f001509507000d102008030380c0d4028100e4032104c00103004040c0c44131004020030801c04519030403600c0380c401c50703900c2991056940100c3c2c01c44480c6c0710000750000303000e000c2807a00b981200080101030300704200c5580b9020450955108003070a125100d07880c0800a8003540c001d0056070781018000c0c100b03540c3c82c80c0c48082d0396884940281d04001003240c41c03040c5001820714200c020383c0380340d0152004040351507442058a6030411200c0800800100e62020801c01e13000c2c0c043c109400c00301c1d0006012000c803903e0080c1040d1001c0d0090700a603402804010b00000062184004540d805140b0680d140b18000200e00c003600030800401c0001800c8032081d600a0380002d1810498880b035800a02d01a215070314243c8921041d912900103a0040c0c1c1c0901404510f406680d4000d07105040003031a0281d100e442e04440f864580781d08040b050380c130004000d1403ca403070b650084503903030034410031000784113 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 175975530 1250 175974280 175974289
    0x20d021e040f0e03090d020d05030d231e090a08120a050c0c10020d141009110a020601051203070c15030c050c0d0f110102070803040204180515040302030f1c1a 70
    0x71380c5c902c06e101c0d41c2c03200c5a00d015511014020f10700a40c0000035203070b85280301c005000c0500900d041000341c0301002808515402c070303010758080c0030701100108030000e403483c0c2d03600910b00000030388600040d0194850780000103141000a01e282003640110b1b0101c0d1403d0000c0100700c0e0001041a01500010000030140280124140092007070300e4500507126188442c41d1b000404c407801640400c1002a0244082c004800c203001044440c0d00a080c0300110031705946000c0c41c0201c1100314003613402440188110f14043d000f484414607036408903030801aa94851102500c025405003450000424003d02e40c41ea00d0300913503150702c0850810b01d160411001801e69100744518000f0b0810115440311100c0d05e11404c8d507101120388001c020354880c802c1d810400e50551003528100c0c4200d01c0c104e0280905000141c410303003c250000701070203d80c040e0070300003043c0c440c00510807400c50101300120310075500b05801414070020101803015000b00d550704404120f5030700e480c40c0d200000c10185180c90700da84 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 175976780 1250 175975530 175975537
    0x903091c0b10060c030503190524060421111c030206060d021f1110021c05060f0d030212040f05090601090b04150306050a0905190b01020a02010804020d021e040f0e03 73
    0x9040ca801031f0389981380c83c508a06083c0d4101d103103552509200500c5a09051441c0500f113245000742408180070f056010043c8900c260701c82c40d40c0c194114030803201a0001c2051034510b19004034a000850701101c0c1c00034003000e01000c140440c003088040454141541000100e510110903105001e004415070000b40c1c4030b4080c410b0b40582c62040e803291480c600d2040800d0054403282a00321807410010046880294010004588051854458110f10f12140d800391500548010b00181c91003208803040c03106095100300c05409501c1040c840354130903000b14008000610b005040f1441060408041000c2410007130070141c10021695424010b0b041d141040b94111840a021b081e480012640103801034803456000c1903200e00c081000046446454003c0342c0b04110003403170340680b003e9a08501086621000d40c2d00e005a10842c50340c1c0040d4000c10000d60000d00042c86042d010106600049081440e0840102c10081542426401c0e08140c0660890000c40d000240a81082c03001d01e039540c4d02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 175978030 1250 175976780 175976783
    0x9060e060a0e060613090f0606090f0b06070303020306010504030b0f060411120a0e0c0310020415020f030f031801020c07060201110408120a140f03010305070b041404050903091c0b10060c 82
    0x156540b210405d60103640d80103040143d4421101d08114010307041080c0108490311500d0803007400c000d00b801c5507007041d10504500c0d8200410050406042e81c45c01c5000350401802d00c0c1c1402802c010100104406030026489440326205160f0b0600e001070522095912542c0381500a040a100000000003210001540070250303c13000501e0b0380154205503c2c00601c001e00d941c00d4041d00041d0380c0104c943ea002407050b100c600000007400b0b280b5480403030703a03070242c0c030035850007500184a03038072001d01c0100080d82c1101d111b40f505d603040ea4481142d9801c80c3d200050003445d0f5800003500f04000c82e0280250045a02901c10799030426181c070350001d855145130404515092000540f800080f4026154100985020900d90f81c2300c0c02020f20310042c07030341b00380810786aa02c500b450000d014492a8120b600761800d2400c901103000342ca4060101038400501401d030b6902061288800070b840e070400050011011140960098566040081c184403001d084162070007010b04051007066000350955440c107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 175979280 1250 175978030 175978039
    0x30207020607021003060909030c020405060f010203040e190606030213050111030a03020c0f1e150c0a05070201021e0304030b010b030103050303010302061b120408010c0806011218050109060e060a0e0606 89
    0x4c1d141d60012070042c01d90381c01040038a0310b40361800f020316501c120388100440c420384040015440384230802010745941c014050069104000501c5200c0f004002d00d40c0180c42c80b42002d1449031207014100545256400090010b540400c540039207110111001d0700074a400e092034500752032000c09860301d0b8403c0c2c403000803d0540009101d030151504008250f1343c800c540c03059800c103811903a10f003c513504982581804510a00354105004180f201a060003034000000e500d10f42618480242d504d80c000c0001a0b042d030054002c100648449110f6402040c1741ca0000385503035070b0451401c00d14403130301038101c001550018001070000a000008490660350100c681e152503440d5051107065044228003043c442d0301032402080968013210011f070041c2c070320100080c403036564100012585c09a04a88443c0012060403c20a1085240d400030b02c2c03200c0301a0550720218104e4541c03e094800c28101240d082d40e451301e02015111013404629040190034005202c1184100589685c8040103400180715 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 175980530 1250 175979280 175979299
    0x8151005091504030212010e0f0f0c151308030415031109010302030423010c0f0e0a060806011101020c0606120a030e01030f060e04050c03100603031413080601080c030d03020702060702 81
    0x48500042c2910020f50740100031a40318240e9041e81400b81170340c000101c2961003119400700c5400408502031030031082d41402046440120030802654000c03480031446040703030030032140d4140b075000f03443d15000c0c1034504001c1d540c031490200383c4078001d101851014201441c025039280000003140031640f5000c824a00540c4944940c10040c10070712268110110444000c3c541e01c51105064001161401d420b403291003030241a11802c2c2c41594550b00c20b940e2042d03c0c001c050000501030302c19103400c800103240404084580030005422680640300b0790704507a120a0030400c403881c2c6100d20104c42d02030741000e003240059558000e0b20f0003455108903070516485205817a05c00c1943d0b4480301c02444442e40f511141e04040c20b200e900c1c0d03291421058002e00030b40d0408881ca0000340115412241d040e076480c4440580c241e8005019000032441e40304000703500e60000340c0c450701006414040c000400107803820710040f100701440c11130211a15000c2c14014000400540d90b9101600c800f00d4058500450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 175981780 1250 175980530 175980559
    0x180612051005030a030804030806090103020607031d1003090c170304120f0f0b040308010e06010905040203040f0501061e0602010b10050c010f0c0c0b09030702100c060b060a0815100509 81
    0x40d8050282c00c030941620030344640700c0a050b07110a441c3c1c041e90090f00d44000540300d400501001f42000d00019402131820444400041e03c50b51217100c00c0141c80c11580c07810b14429001961600406001400085d00d42c3e070700703500307010160040d8801013041c2800810b03103020b202150341d12402584160440300074000c4d586424443c400c5240d0a41d140d02912031000d103901460100c0c9503010540303050340051204000802c141c801310301d205000c1c1308161034000107d86800c081201950008004407440c9103108403140003c3d03030034000d407805881b501a216548100040f851403281080780d019808582c10460003080d5926501c4460b05210b10b40d15042d95102d80104000c0d01412103107a00c0c0703009038a42100c1c4042c59a11440d104010b9120b08a607007699141d0042e020355a000c4c00340c001e03511501e04100034035541d0259911204051083d1000b042500000740015440d810031071040c030200c0c00710340810103c24000700c0d005402c82c00840f01c103c48101c035810010414003c08003900c0c084c0c0e050610816 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 175983030 1250 175981780 175981801
    0x30c0503070c09020406030507110309190b030702061b0901080c03070c150515010c080a030207050f0613020405093004170c0a0602030a0e0d030e090a060618061205 72
    0x411441d044909641c400f6a507014000082d807141c86032000080c6420081b0340c0b41c51040b00e0540703010420100440c24103107040100100c1c030315081c00407030100e00707010070000f00541e070301015602c10306040d009000c081c640641626a02450003007c0c0c0080841000a01301aa80140c60b083c0c11032042441e50b51242d44100b82a40c5124483d58042d20860b10000080044411508048c0c8201d0380344601c10380d8031445000549164050580c01000c40c0c42c144901e0748098441d88c058141c49001d802195003000c000307078042e403c1c41004d80707410320042c1c0f0103a108d60541c1040e015507034001c807110006181031002c6000038020061401c045a84841d005041c041c0040c80072416a8083d100851076401144415560699940303002512540540311890000800c3d40c008400e0303400501542d210b00c50642c60900c1000442c003030070308084080c07060300c1507102c8541e2607100c51540300d0030039000e000a80301d040c0302c00944004d507a02c4c441500d07540d903024240305103988040f12015030316108034041a1615088680b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 175984280 1250 175983030 175983037
    0x1b1d010312030e06040506070908011401120f08070528050a060c230301050415050102030307030b030709050403030b0307080102040b07111c03170f01050604050108060406030c090b090a140103030c0503 88
    0x1c0f09548502ca081c017003408008204103000e8925a1100d0007121f603141601e50a890080088001100d00c401c010052040c2c44280c4008580c4038030120380d50001c0d15510410076410405041d02c2e02d5000400720a00500c500c2142901c0380c46140032200b07802106c0da02d82d0b80c0e031013219000034101501c2d6400e03082c4060241180b80d2140080c4c0380c4040d6030007131804452000360400d100d03040c0b00343d0074801110400d0802d00411303c2640c2d8180d025600d103641c0c1c80e1043d806000383c00c582035014401d240000401c0c01c0c0900c80c907401288030b81e6010406207010020103181584170740004c41640d204000420214407414201d4100c0c940c040c00d83c000c00000c0c440094131300408030b59544140040548040109603125282c030706065801c1c0900c030015202c5610100c1803175802d008454001e1802c2000b408598003500d0072950050008002140303150312503840c10b00100b507603403107600c1c0d55449a000c0c22041c64070620140d449148050208441030841651604428041c40044d00b400001802082806400e0007203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 175985530 1250 175984280 175984301
    0x309020111060115031b08040209040c031e051515010c050a0c0305030a080709082a1e040f02120f040201090812040510020d0c080c0102161b1d01031203 67
    0xb900c030150b07518404284010784581100d0300281c5000d058130004070900040004644071556000c880340d45540c02c0c004103110160040d104008070741d07400400a10f004022104034006401d4104800c292440c281e890308031840c4e5985002c04100007040340f01c1c0204015504405424a0550451107150078583e050049014015090703540041011041c01800402083c1850712569010b00c26070f0380c1c040407215555180900c400641110a00c0e0400010780d15480346000c0095001c4482020810000307000c00d60b8039200480a644034040c6c01c03200740340c0341c868418840704200017035160801d42c2c68200319100f00100f5502c142ea100fa00440c045d079100c0c0c10040b02030b0030390400321560364141e424104c440d0707002440b41e148100380035076108118610200d80711140c4401e50b1a8242c140c2c4866856032260f03007104883c0c010541d801e00041d158404d0008000041e13601982e040310004581c1d4040810740c5549403c281d5a187d00c01100c1c05842102d440d040341120b030805c400381017950340347d04120050541c0e43d18 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 175986780 1250 175985530 175985533
    0x20301030809150a0203070b0601030b031e06010603060e041217010605030f010f06020a061a2805040506030706110c0402040e07020d021218060409090b07090918030309020111 77
    0x200801c140c020040003405001c68110300c249803241e6052010340700b10713804038005810500103900000c010038202600481d0505001c1407501d52407011a10382500741100001240d000a0002c02a40092120a024040901e070a102c40c504190064074045070103040101860142a0440c166500c54060214101e00b504030b01c40c2d80c1e50391090014142c6d0000d490070551404030400001c2c80b03003860302100c001c0707038500d40103840c00d0800c42c0c6441000349502411310308015400c040348002c542d10b800b4903102035000d00c0800340e6411036030b41040c0f88807a01a00328a010364601018070800e40d40c00968a07044a000345440361100c5486401241002e00c42c101081d0090b002141c0482c103c0107030284e00f846041964202c9914403103445049a80d0b2105284501500400700047c0c84034042e2035141154015000c0d051525040d61024540d048691894080e10782d040007009003c80107038000075810003000c8824040c4005040d800244018002d0181300400307042e44d0310020411640100841107190300c0707180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 175988030 1250 175986780 175986787
    0x5030c030a0503090c0d151d0607051305040c08060607050723090a0501030c050f0619020a12020a02030304060e1c050106090c0314060609010210061e08060712110d02 73
    0x20780150407904142e488040c40d000750b090009041c14000f00e48560150003201a644400303041d400180140030340001d02421901502c0c1d500d800c0c4030200b00c0b20b0f004d520199559aaa12000455000c14400350b412852145041c120020350f010350080000d50031507001c40701582d46d4001c614041341b07003451550051040032403400100416142c50300101e890141d0030ba441c00403640d103008003142120001d010080c20054422018011810300841050f85020098280e44c9000c050b0017612000840501550f00144d1010344004208403025690400005035400180800c034410750010f0346034000c90103141d0810820704804442d035a00c0c1084e4000e04402040d5500345c5000c01d09000d406400d00740a0210b0440c1041110740c2400d110b07100c0d501c0c00c200f01e401e1340c0d8059101d403810880c141d407100029030704500c10400c105a910100e8829013004001c140c1002401403910748000c03200c079129602c002c0300d6420210400c17452540110b015a40c0204069001500480100d110f80d81d5001303c5410240103807010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 175989280 1250 175988030 175988047
    0x12050d0e030406170f0c22090504140d080a051e09160803040f090b06130b0901090603020f070605040816030909110c150c070b0c1206030601050d0b0405030c03 70
    0x1c8020415140295926503030200e01c4860114110710a44084118910400c00582c0012500002d41403140035000d142e02c0c1e21041e800c08001035074103500900012a80c55052008100c0c2160f0040400c1e1104000380c40c1e501d958034000b80440380001c21003214113032108006144c410007c2540441340c40c83c200c3d10320242c105a10510f07074858503d41006841c1030200004201c120000041e05e080f20740c0a943c4826841c100803844000e40300c0021034a4200805108003005480c1c2005000c024201d50003902c1e03141c1e010ba000040c00114103070f0040342410710400402c0550b58002040b80e51182e044100410350741c44902c0c00030554403d42c40b0300101d180400c01031108043d4090030f000101c81a082e000d20501d0800000e1102910440c03074481c000354416440c500420103103407031960b07100e41009840760404840e5100d940c0c541500300c40880780e00c0400a181c101181010000c507800c2041a402010558108004991504117420010381005451000141000420421100c41c2c920000c107403a2180d101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 175990530 1250 175989280 175989283
    0xa020a0209070e030d030207140a14120f07020402090a1503061e0806180109050307060b010f03090b01092d0509071a040603020705010b03151e1312050d0e 68
    0x604408a11070340000d00400c190700c0c800d0307098a10700000140508900c1862402c01d500a500c5420219032400380138010001d10391061148941040c028501004500302c0300302d80e45c1c14914040d441e0f807404078091041c0703a540c1d50740030180d961550f41607400580d1b8180e00c2d4002011a01e8a502044c0321108031800c2c100b44650503080035040b190340c0d040080c000441c00100e100050141e000f608060b030702840000c1c4a030001080b402c8562058540000b9031069a078441c40e08581c4030b00030a41e015612000c0c03160a035603112100e034050110a01e001c12044206580742001541d041c42414021619201030405600480f4072480f98105484c1c4034036a06c0100301050303c09040304031002c181e240540080015281001c1e036413002a09100541640740c1030a00d2030a0380250041c860542d500d40d620254a0f2064034100003280c80c500b01e00c8001c0149203050b6508441c03c0e88132000e40e80203c0841da060000d10702d6002e200034040c80e40301c140c041280c103240c24111001d024414144906c2c070704100904055010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 175991780 1250 175990530 175990543
    0x201050d02070221151308071703010303200607020a030503150a080a0b010b0a0903020103050709030807260c0a080a050c0d08040515151909020f0301080d02070b07110409080a02 78
    0xe188240e4005651090700035840c2d0170308030fa81c151000294102070000030041001010070f41d1041c0d0003910100c0c0075a16074401e54009070030850200740c0040c0048070b1204400d86d07240096681c00010489444d048000940750180c51500600b80304010020500382007080d8100c0030500d80240034006819915a4865650700000c0030035522a084480003140c0c0070702450488015030100e0b02d424210703524503030044004010042600c0b0070001e048601000041500b801420410300911025400e190030100300f41015406090501c40001d0820200d50f00b0480890003000d09a0024203150312007030310b154241e64030702c1a40b8245029010390720381e1110864102400901440c020011640700b0800c0040c1004150019500d100740381180104a106a00e0710202d94008030b08044000c0420541c0c891410b402d030b8001000c045481900400180010202040a4500590b03140f000b440036520781006421948581c68000e0319152303008100d503001d82c54a030414182c041d84000d2003035440741441c0e4000d44440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 175993030 1250 175991780 175991839
    0x809010c11121c0201230406060e0c0a032a0e0303041706070f0504121509021002010e0c1516050f1902190506040611160f0f060201050c04030201050d020702 69
    0x1c52003a410f070941403051056091005c0040c1c0606920b4a01c0320756111034800040c81100c4158450b40040703403070a0b1031359038a0b021307019920b4220b40b240756104000e0700343e032500414001090b18101000d649102d080e01402166281428411041d090040120b811803089421814441500c40845c2c00840400034a5074811001c6584001c1c005081174011501449513200e65488400300c070448101044248011100050461800207a005400d601040c40500d070a0669000350b55a6102001e0806040c050340540d000c00301c89071152107000d00c62910380381c081c501e608440181003ca600c000c00804100035004e0030311210407501c04080c5c04003c1c40a00f800c82000300e0041081822030030542d8940c01d8844144c2e400145640e0801e420002c2c101d07011452607000c806188034020300046a010281031030000340c11503c0c1c032041d040d8140b454220111801c0ea00c04421a850b000400800058800135141569070919015990b00c9103954104080e0080748000380d80a0300c44124510300012211600c080720 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 175994280 1250 175993030 175993063
    0x304060212040503070504180c03081c050907030b0c0d060905060a1203090b09010903080d0506090f1506070c0801020307020a02010e0f0108190e03040803090a120809010c1112 77
    0x1400403800014080c2e84522038055021a50070722407490a82c00c51402031030400004070b0035040b680c45a00a080c9681d01c140c6441c000041d44c030015611128108c804010303100028009820030740c00c050b60f103503080d00c4050f00050742c20700862010b01030300c0308803480b074409a4014400c42d80c1341d00b800310061005440b6240714a0402000007a02d0180200002015405803200c0c1155807515054208581c0704075000307810416800d401000140f0510060310b14010040000582844c0210a00c009903101501d05001c00c4005000c0016a22100c00c00d1485a402a10314540b102207500e40340d0060450740c0c0100c80c0c154004020002400d50004001413014001d0361403100c41100701d03050100b444901c004060025000000180d030304000801041d1000c031355120700282c1e0303012402c041420b54025412070071140d000041c000e5420720740f031904031000d816543d60003042c50040c0d5036502464860040a40e05001d0030707103c0c00f010300454081807030002c4400703031100a044032200038441e02c440301400001080c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 175995530 1250 175994280 175994293
    0x2120c0f0108130b1f09020c0c0a03050a0311010f0c030c0f1d04050612010608031206030c01080a1503050118050f0303010803040303050c2509050717150a0f0803040602 74
    0xd580314040c042d025404481000109a500381c8400a00300307401440c0a00c0965000700c100c40c1121482d0b0408002d1100900058032206110320040c00c04115000b6284680348015040c0b0104402103230342c2107903a907d03060219034890400e40d00c0b4003504148080328000e078a8501c2c0c1c0003145030944c10401baa90a0780d40e070340c400e450051005680400c01c0e1500a0002c0c200c00c0c41034010f608042d403140707030442c4000307080d003609005014034503081d02d2158004040707507000800d00e044444000403a140d0088001c80192128400a5000803c03503000244100074880e01c1310150b6000c0c984000341040a90b81200003170003803006405a43d422002450710403540c5c3e1080b14400d4258a601209490580d0000400b55181901e0754600700c8054006007500341c22405030040e210413031340070411107440d048030b40200c0246440c98030560380112000100040d0600c5075102150300241c6040c0c49407980700d4042e65207a43e61008202c0402c40f8088260003181c0c41c80640d45022131240d5001018208859155085442 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 175996780 1250 175995530 175995559
    0x16061a01020c012d0c020d0309060908030a121a09151201060e010620070816050402030403080711120c010b030f0a0c231e030d030c05030f04060902120c 67
    0x4854012900b0200c1800c042441e415441045201d0301003404c55624000300100070540004661210354803003100031401034032080001c550416028001411030070003841c109000c0320001380817501001c000c43d8103141d030b0f140000d00d40100c085011010017000b42c80780d540d078604a401408522801040d580c4254103103d2000900340050260000f517070040840c0d41d0031b07a443e01e0001e550002c03c00003805066280414031802e0002708000e40d00040c0000702c010a61511440482c0e0715070105038000314000d9004001f0840400d4204a80c2d07a00440a840c0c144607110700791250344e0500380403040c0800350420000b200d4205610540104060500850aa41c071080b4a007200039a525901c941c002d116406c1c2000400026041401079110902201d08480c0c0711000440081d1100181e114010751580c0400741040690404000e1a502905036050404c80310104440c0070b0f2580c00020038088900030280e0014042080d03a4101a40702c660185c6070708003c800722401d07961103a0300c80038006d00541508902c0031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 175998030 1250 175996780 175996787
    0x50106180204050a0b0d140406090c12030206070f0504080a030c0c05030601080a060c1b0503070506010b03060607060218030102071a0702120a0e0406050919110a0203090616061a01020c01 82
    0x30b0807030760001c00c82002140751226205650308007103294940660b852144911321072428044a108a00c60320002640d9a440d1800c150725081340d4109103268141c01c0030000009030001a129008219030502000c1e450303402c11304588622864000701c2c45401211640010560400340c030b64000d622803002405069110b00c14960f60301d509125605040d40129000c50100d000c0e0340c01021040d84520740400340340e45400c8104000c0c64001c10444440e80001000f03028000c06000141c00b600b05940990301e941400780000341f841c0608130016140729030000720f064510300019003d0280201c0a0f000350b480702d04a04214000015104030402c0d8000c66000107401c103071000c100307006100702c080c95550800d5a086022240e1090402c07100d5086940d99a02040d03035512500540e00c600d550342003601410ba2585040c10945451f4503442c0101441440040320710b94001c02920a552001e0b0f40168582e0081d4400046526610001502c0c10345410803440d400c8080540c0204108401e0702282c524111800045 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 175999280 1250 175998030 175998037
    0xc0405060303091f03020f0403030c030e0d050c10030f180516050d0609020301020912011a1f030203091009050d170423030c010e070518070203041e09090501061802 72
    0x1d60000490350004c9918010041020100c00c20b07207001410484d0a1010242d1540039400c02d41c0800d0618466804066100c0f0b4041102001610900010a06552060f0340c031442d65000e64401c100c01c03502040514440d07403003200000c0e00060300b4440034407450410610b00b14590380c01c0c1c815000d625482008103541d000c02c4821181c0c042d122480040700e58544400814001e04d00b264195001c110340916940c032607100e841180c00d0b01c4000100c03c1381098010401e2861807005030301583c010306030804405c0f40305040600840e450305000d0ba4941d1390014003407c0c001c1c40c105000340c2900d00b1051b0410721500044001d8180380130b842d4032820b080100d548110741c001c01c942c020b00629840c0802d002c0121940600340004150100716400c2180300d4090328250344500031001c00ca6480b600f020403c07460b05030720f50025210000a00f950b1f6040c151380c000d44130701c01c0380104505408003a01d03003011204104c030034a00a1651080c00c0000042910b411806410607108401c002e01d4480d151506a006a03c01c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 176000530 1250 175999280 175999297
    0x30c0601051504090507030f1a0a0905040f020a060c02101407030c05070819060501050406150c020a0e09031c06120303090c050409080309010c05480c0405060303 71
    0x2014940c0c60681000a103542c00c4074a01242c035018400042d02116078003880d401625503440220f04112407807a080129400086850f141d1130303449415003410b0300e482510400b45e8064410205c3d00307950f242010342005040100080d000160802c002428036400b04250600d28401c60b41500c00003401c140466080060381d441800041042201c42c0000380031754001d8012502c074000303940c0000e548810792030400030344080305d00d0851112541c140030081d2600c101c50250000700c508220307040c203014501070040c0002c605c18082c00740d484001e80640d41c4003c2217070001c0540c58402c0205252580040f0f490760014134038054000e0280c2003005004096002e5074095a51210f0144c80d91421901c01f10087c2240402c1541d0008100c5004101c90300c441c0074200e00309004003480d6950b1304101104a0840b64075016040400009000300e00c42d00302070701035004160b071000f82c1c08441084071064840145907130000d03111503400c1140f48024a01c3c004203401d5100b60084604014554032101890703160304c148500d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 176001780 1250 176000530 176000533
    0xc08040b0c0a09080708010b1903120c060204090207060209010210110a120f02040303050c10091a1e180106120215160f0302060a060b12041103120301032102030c 71
    0x41d9400141d60150070a034015240c400c12030341da182a024100503264100d0741e2603035140d0b600722850303003805c480424070b43d801220107004403072841e1906418615080824070421141080000c00c0c404075405a074003501ca800c00c110758074410f0340b41480095006084590141c040d001000f0140b1200f84281c0515080404409203010030320f09040704c00780d400c0309607420300f00c1d03403110502c4c0184028405880954400d85980d40c0d80c000e2480103501c0c064010f290380000d5414600002d00040c02c0d0020301d01d44510540c4541516101d510707030604030781c410003040445007100f48100b000004610350400d5254440320001c001454503031264000043c1404800780d08500007409080e80030f40002c0013804010684801d404d020051030383d800c402520361070810382c0168080810b200c1c4460440c8140402801c42080b0b036450210a0011244203100050014081810b404d02c00d0180d80c13800c1c084a580030010342505950f13581c4915089400c0400f00e0203907038400344440450f000407800003045403c000300b80340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 176003030 1250 176001780 176001803
    0x1706091002030705040f0815010b0408030a0f052b0605100804020618030d1d0a0303020a02041509021308010509030304020d0b07020c0406080d11010b0f01080606091807030c0804 78
    0x240d000296102a01d60000c1040420002502e0100c1c03840c0e01020344680009040603810071410003503541410b810021124504110800c8007540c000100d480c904503d00b000858201009001d03145030203003020014204030000d003601d0b4401401c184400d003058091008104068440041c00002c00c00180204003052240000c9800f40c80e00d00c1c090030080d1800321289181c0038003400803a0420041f01000000700f059400c107071100114081c4104041e6500760383c151034241c0745803002541c515141c80b000e4010b81da40c8892540c49101c200800c0c02500b652a410740d80c50017410f144280c800c001d4401c031920340d440c2a003c2a2205404801c0f00d0090303400030940c0a02c588152078070074456401070300400540c03040c200710032815100c900400c00241048406001206050003019003150030b05d01c0f0f038901a0345130809401035555011009030703600c0001e1030a5003441ea07481000c034403c1d104030b0f600c842e4848180b14207002d80b4210260311a10401c4103540074130482d0155030003500d040c00142e500400241505 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 176004280 1250 176003030 176003053
    0x10180b040f0215030f0a0507080412140301080a060f050c040e0705120f0f090c060316051b03090a09050c1c0f0c02010e070803040312180b0a0801170609 67
    0x1000010380190140340320010300c004660004071000803950000014280100c10014141840345195512410303409040c061460300900081503a0001040200b4101e03405890100151182070303d00701c10521440e400356207584942445a440c6c8580c0d100700c0c0c0c03285c01d110710644000d849010b458001c541c1c5003481c81c1030604140b0455900c910041521080140a002644610800c0103c00f03004601d0601022000c0c2040880f00c00c025000500d000e80542c060900c8000315110301049a91200301d00e070390300d00d0030310003004100e60300d02c152103914000207014050080003100200040c181601c003202c0310316000c1c0e076070003070003003662801c407005011500d080c05484203100701803031034110151421000040d43d4407144d403540c046624a10106006030354900340c10040c5441040040058094500114105840d69a610a41603c4902c03540c0801c041c0903050200302c03100c880d40310060b0400f6098591180c200d9000100040d00074030496540d0840d00d641a0100c00006c108940106001800b0f009402d950 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 176005530 1250 176004280 176004293
    0xa022808071401050912010f0b0f010309030c1101110a060c031b0e0f041404050601030501051b180a030507030302011b03090206071b0909030903050c01030b0d0b0c0f040801020c1018 80
    0x300f407440b9080340849040d03030304003075003807007441182525010001a5149e40b24140710341c4500c101c100c0d07412305141500c0d000100c2c1c2c01000009446902901d0b12054602c08401240c102194000c454528032813a419841007103d150440940e90101da80c040014a0f150b01071603c80c13a80790b00302d00000c204282140e130458140390401144c3c0d24009000416181d814260865013004200e50603109908a400140100710003030040e1504602c6112200d0904011001e0f41040c0d40300714444002c040103a000c810300c894070b44084001c001d640000c02e840c0c3c1145d0b6410068042c101c426040c1440a0560150900040c000d115040c44540c014100908100003680d40c00c030ba82c500082c0d19400c0320f0f01c42d031002803240e50324064022102e00c6035651032281850351400600e8038800d00b040905060804c0410310803074481c040004805038004500e0011500c40025444241c03041c2881c00f51341000c0010080781205054006145403088182100d0910300741502e49002c68243e41840400d0700602000040801c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 176006780 1250 176005530 176005537
    0x50f0604080318030f03070f0e0406050f04051b0a0518101706010306170721050c090a0207050a0303060513052202010314070e19030c06110a02280807140105 69
    0x4040f04980c075003807a0403c220000d420456020001411003003100011070b500c050300b12085071060f6000e00906040a000034180c1ba01080b0030340c001d070ba540c0c00040380300e1603030b00c3e4644001f1103111620780c2e6040c14441c000c240340c0c03040070840000f08007910350311040d0400316910710341e5803a44c0c0e840d0f03a140c0c0e000d03195008056901614107410940c6070400452000e0300700001d040c0d80c0589100070a14145007011761042429002030b148850080da0180b140032440118200744142c0048500e0f407201c1d40c5082070030703000740034806000c2d00c28403038150035900b0950150b00c00001e03110308030b504c000071680a00040c2c090790400c5070032800c80c568902040203100051501008020300c1410040703500c100d8120040c100c0e80c02214044005010a1b0102d5482d060007a0311280886580a04400050458075140c1100d0302e036210b000100405507100c0040c146090018401c1d0070390042c403200740c203260019100d840500c028490480329080907030020300d8660010f0314504841001402c40c031940d5160005450507007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 176008030 1250 176006780 176006821
    0x305060601080406230106020d090f060509010c06020c0a060501170a20040218040e0a0c05010f050d1802030f010603110907021f0c030c0302040303020303060d0204020d06090207050f06040803 84
    0x20340f40c0c5c41c2c42c2052880d6810b00100d25900100021056142241c02441d02908140040602078019800e000c010810203c0340240c900f24100b46075513241311401261186aa20703405003002e403001c0380200d00c0040100740d40d141d0381d001300001d0010b0390f00d484603406410404503e485c03181d031000014900003444007007440e54804110701900b1445541d6070109069900c080410030000308138508051103481d15100f4421550711040c0144660680c5a8800b101950305000310741c10320040f1940d4080d2144500115161005242c400784241a4014038111182c07a00990403842401843d030b880b0f4087d50148100e0040325081502c045a00440308144180c90344090500303400c5003c0e00180207411102e5081104141e04420000140c0b00300340d04004044500e400c07101020140100b00410100b503000060f02e0300034404550903684801e1610015000744180d2100381411070420000140ca0740e2281d01800d00c1c0d0307009205807900d110915020b030b03840c0d03001164014844402030000c1100741440810440040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 176009280 1250 176008030 176008043
    0x30d090204111c05280b0315040c0b03130602040e040201030f020f0a0c020d060501061e03020f030604050901060504060b09010e030d05040303050d0e072c0702061303050d0f150b0403050606010804 86
    0x25032085c0424800805400640c14500e504c1da0f81070766050a042240c551518284603a2180c0c9003400c0d43c1d402c071503216901c1003000c0d030400440454080c40041e0255245294424021503641f650b07400d000c00b00782030499040c0d010919041030300c04000400e000b21642e0b10f040038400c500d080d1f0840c00540d030b1910401030690300400e000e02c00c500011418480c0e6030182003d80c170744021070914071440030030307001c1d0000c40501018018006080c2c0c0e03a050001341d0f5003000d000c8a000c20581d850360100350041010307920030b66000382404000192100050010030182e5000c2e0b07260054411143c041c50f40c2c50304000d0b4894000b40081004001003840752002e1711204031040c902280c0fa441310298245040103640140000f40d922001202002c0c0d403101c440b603c041c0d40c000202ca036500c0c0043c006911410020694040718041c8440c000c101440754089030000840600104482001891158000c0c80000044104131000785d402281c241410b10548040303130b80c418020040d0741d484a00445101c1006482211070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 176010530 1250 176009280 176009311
    0x1050912010603140708060a0b06030a0504080705011a0a0b04030b04020d0f05010207080406031a030a03050a05120a0b01020705060c0703062a030504031803080405040207050c03030d090204111c05 86
    0x1501003408904c035042c00001013502600388450281001c00c09480403420304e00d8401d40b000340c1d44900c001e580d4485c40c4080001030700c0e916410300c0200b5202d00344006286528020310300300140c00c0703400c8080310721304250f8441400365140c580e2040c0910071408042c1c8598609000100145021700c01d181481c1d00c228140410451701e49e49103400da811203e0200e039154030124061000c103a051280740103481d04200d643c2802444803012a4403500c0c0400050100000098102c002c00d000314111207418200840d071112074500390165100801c0d046e9403803030050140010000d0986044019111250946009401d4051a50399004000c00d400b4140c0400d5030280301c410704035020780170706185040015850110f00e610b001c0c5002090303880c201040c550380358192801440480c080c7c5085c0c07030035940182c400590350003680c00c0c80d62400340c1480a859161200042d40c9404050303a03005110014803d0340c05200594469412440900450441030508119130703071841200c03552900110b41003441c04d41c20404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 176011780 1250 176010530 176010533
    0x5060304060b06040b0c01060305060f01031104050702160e010e0c0309190c03020915130203090a110402070609050f10020301060e1306050405180c03030315010f11030d0501060e03010b01050912010603 88
    0x607a0006c8030f800159075907a030420814800d0038004154070800c50615640c2075810355440c5000c07c48108201d0740601d96a40000b0324140c020400300181d1403400c0e54502c0841d42d5803074541e240d60401d004420030b4000b094042030024541c03000341c90240320303c10083c103628001c01d40072004480d140340b400e550b941c1b2103130800409138581c01d903502c0c01140e0600a0b2150074020005000c202000360254591040c410010880700c580081025100e0700d1b800304150700a0f0f800c03d4000b8010303004400c0040c0042c1d1074900d004040000000d44818031800007400c0e98246102810703200228002481030360b001c40d140c6c800c00a042d02d01058a13104d02da50303841000403425140e030f001c0340c203c900845500e001d440840c035000481c03d0302000121000c0600720021469841e010813150115001c007480b15040c428582000300500b402108140c2a0181140489403110039888845028080a115410105038043c0d81e840c8982418090790b0884030060b103840d442d110035003040c444207181c0e048601a495584100200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 176013030 1250 176011780 176011799
    0x8010b0604382503080105100c021c050f06040b06060c01020c07090204050111120706230412110c01090302122104030b01080d090902130e0405061f05060304060b0604 73
    0x188807203814400c0544510103080707100103c040110030b021030203c0c0300050000003544041564152036090b26800f03ca40c3c3c00aa0036208440e140310b000b544081c40e46c80303e07581200d840ca520301e070090207036080710701c2c0741c10520742592941000d03200901800c4c4000000344250070110010007e030b038003910005251030203241a25007001125000030302c41d01c1c1c00140410503513030312500c4043d070000d41c000036040f42112100d803600c00d8828108020040341c0c5a80d4100403100c00d4400b11480c2c48055240c0c014a40340c54940706841c003803200341c035201140348092041742008000492203002201a12a014621b00319001c00c800c00d051101e01d85220f2144843c45c41d0030103c00c045090b01c2c2c1040c4011241c54900310303c0c04014009050b0400a45036100190851400c1c4c4e10101c5041142c41d442001a81d50541c1415034a00b01d5060b048603242c4541c0704103110030080c000800920902080f0442407003002d1301c1007600b02075403491042035440340c020300104000c260035502401c0c44031b80007400c09140503560705008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 176014280 1250 176013030 176013119
    0xd030b060f070c0608280b040b13060911070b0403030509010b030d080105040c08061f020a0b040317010509010b0f1305180103060b01020606010c1e080414010908010b0604 75
    0x2120f805545003410005203400002007900031217068241c1c40c0603030b0360305500c00c602c4454015060b000c5c0e0303c60702945040d40f241d610101501c44040e0041400b4001c80b4480c034050a054410888001e180c092038007030303d850711020748094a50060703900710f442c0c565840441c0030b00005850109195a11a20321003c0d6400304011140010300da200d2811540c03404c020482140c142d8a01c00040c42400e8080241c0ca079548101070400001140c2d000b00600c203942c50881c81c202d00608003e21103000c82042c00700b81a003280c2e1090052802050600c07960ba2100103201c40c807103003841140c0d1040c1c01404481800f21900010300700310000303640c5081800c1e41d260006001403141c0c040000b540c5a1520040c024051140240290001d082c0020902c5007402c0b4002000c031418042c1c040d20460700c0720b64000d0a20b2450046400c41504042c505841d20346440b44006481082d658640c0460000d8500040100301801504a0501d00401081c1031503d00100072185c181500502d0411000c0713020600c90440c9800b01d031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 176015530 1250 176014280 176014283
    0x18010e0610050d0209041e0b030c030a050706050f0d1e0c090305030f0d0b0a0e0601020607030c05070206220306020c0d08060a031b030605090102070210181503062601050609090d030b060f07 83
    0x21402d804030741c050602b40701c590304003140650003489001c00031510000d1b411080380c106241503503440f602061558058041c04084103a0b0070309001252001060318243c1c04840080410308004180f4030940a0b034480030540320042c940e401c20301c908081560080080c1c00c41c1c64003128080341c0ba4001c01c0003e280d60341e00317030803943d0100080c4040c010b084d60b0410010764442082c2c14100403014002e50050301c0741c01a084002e100d180c00140070790b00901c46000c48004903400c1400080e085441b841c04401942150300000ca09200f182004102103124060042c02103002070050f01c403560441d142e1110758441483e001881c20320302940040059070500c1100e00c07800e0700400043c2c49a1051040103407030f40460302800100042c514904080e4400c040000c411260b040c800fa1a1840b440002034000d4051075102c0640d10001e10b0070407001c080000c3c03112802c000403000030010b44c2e450f00d0400030704100a50392502c1c140c1c020064443c105000b81d0103da0040300080500c0d040001845241c0c410790f10040c0b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 176016780 1250 176015530 176015591
    0x70302130b070b0f01030809042c0a0203060c13090b04021314030606150d0c031e0615111c05040e0903190e1014070218010e0610050d020904 62
    0x1019400d028030b100f20a50080380000c6000f0344d039491030b11600054010588482d01c5182d650280c4882091f100c03030b0907102c44202c02900d5400306080c2e060952034010400060340280102000110b500c03510388101c0e107075004c003039034031100c080d0500d002000200320f80302d921a009903003002800c4038299441c003613074018100160414510030700e9200f07140c2004000b0304080e02400b181324501746510702c1c0100b950030700f810f00d0301e000800d07400300c3e041200a0103458044a1052880700116100403450b41c0000e029140007500a029100301c03603c00711a100d038030106600d055003003e484401c62030b4a126800e24000d0651a000b400c00b6294110803991100076101d40380c5540c400600d0360a035100040c80d6004500590a01c244030ba1703e084041402d00c0c040c003589004028120300030003100d1403a00b040e10b95658001e84100c021000142030040201c100303004a0005900510002d03e4925005123004240803140d641e00d4200a000f49c0510043e40018400380d61050725454131000004a16030300301c401245241 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 176018030 1250 176016780 176016787
    0x170c0f0f03070e0904030806010c02030a0b0109020a030b0d23030d1b030b03010504020619110d020304080f03091e040e0f1f0b0901140102030f0c150105060a080f070302130b 76
    0x3030003410303c0e600070384614060000c0c1c01c1080042504188800d501400a003440314041d040f03403000a050803d042c000030080701800d400480d00340280da003c0c0108241546040003480e0301841003001c00c0343c90700002006502406002d5503082540105042c1100540089900380720316505100b068803070003410600c0c0040340764900004d05505000700842c855054000304880c1c2482c2e000304030070384144c0c0314641d210b0f4141080130303001901c03130001c3d04201d50300c803c1604c8520020410003500c90740640310720303542d81c412080705510000021040b159032004c01442c60364400020341c214140a10800b4855500c207907684804d2030055410f005203180b5460301d80141040602c8000304040580c3d9011448200a1034141d620301952503e200d6141900c54078600f0b820100303181170040340b070351082024038111008080341050344034000040641c444101e500c0c00c481d003a0780710014040a40030f5203a0150010708007202195840c0107a5002c00e410544a00e005443c184800340c2581505440707a02c098503181c00003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 176019280 1250 176018030 176018041
    0x1512090c0a061b02060c0a0c0e25080f0709030f06050f150d020603060a03082206030c0509010807110d020606040b120a08090d14060603010b0301050106170c0f0f03 72
    0xc01800c06845a03003007a000c0303a40100c40007060000c90281c024010700001941b94a107006c10465548140d9000381d81140e82500c0303105980c1015026134111070b1b10300d25801220b41107250120224444040c568a140c00c5d692188191120201d002c0c0003002402070100b07010000c1910141c503d035115004210200f600d0a0040d9065000200101099124607030003081c01c01503920868039840c5940c04441c03007903d94460000040564000f80d1000307048207800501a403070090000420105803101070b528003125075440c1c0058060301c003c22040c000246080108160541c054070080e034204000349040b074031498a80038410310f4051f085104c400960300020400070b852500d0700a582d205401501d6940c0343c0e168a85400d079803410303e8800100002c202192039400f584800b40c110202c540c000820f030020396001a00340761940c0c03041e10b031039001e9402c10b6900340d450b08050041c00c1c12944150344008a1201c40d1071030221810001d40300b100f0301c00080010205400760400601a1100d0301580f0581e217040c00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 176020530 1250 176019280 176019289
    0xf070804060305041a060a091509050117010e03070f0b0414010c030f3207021c0c03020615100c03031b02070602060a110f0705030706050103060b01120e030301051512090c 75
    0x2140400f40c5d2030692000f049041d0711100300c110121215494080b5681341181c040224411742a00b20381c0050740703850000995103210710b0711710103600ca4400003088030400015031aa12440b454801500702c90700b421103800081d524545d80c542c010b00480f9460001d4414910480c2510b010280407030000e52115010104040c0d0f80c03150000b0511000e01100c51041c80121900000c1c06079089a01e9001e8080001803460b4001e20101000d140008004004482000f601030905000800250018451100020700d80c0c0006e0a074140c8405000b00300d030103d1490391204031050b588201c000c804140c1c5400c8010040c1d503006005200608494024282003400c1034402443c11038001d01400809040106d40c041c010149021501ca08040d080e00e62360390007a6080403891807080303040c010b140c43d241c80000403e100c481d41c8030400007042641c0c0c40c081e0031940e40541c130030340340e4950304907103c0d80080004001170700e82400d040300d03d503e0201905003040307880124442d8450041301c3e00c80c3d2130741121401c0b1205160 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 176021780 1250 176020530 176020553
    0x70501020106030203100203090f0313171b040b01020106050603040f060b19060f050906030a051b07020306060405070c05030d020c0d0924030213060c120918020f07080406030504 78
    0x2803000b08403480c5540c0000341d032000c11407511130b00154004046044c424081c0440429401510101e035a194498141000c0b4103115100c2c43c0803100c103e1503d1105424007090306903841c801041d2002c07020300180c013048000c201e08080c25065660352040080c031600c4c2c803000755200e64020308a16001803080e0034444140c6405500a41c403c9040440c000c0b400b8114a2004064403060710b010f540000040074182e0745c1d44500c050440d031080c404000c0200c4802d140c1c0041e1f1140c80c05450080000444044480c018010000c00a516401280014810741041d03406070380c2c03242d5035150503080c944080e11640d046512450055240b0741e00000ca889140400b044901d01c110040d1030080c80a1749002c64215154242c0c0144280c2103841d800b58100062180d016202c02003030b0091400c4241341d44a401a000b0940d00408a41040c0401e016106560140302c685049843d11034640896030802d07207444000b503105902440d0500f0040c4450b00114080402400181c410758800088506082c10241306001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 176023030 1250 176021780 176021789
    0x30e1e010e010e0303040c0b031314060720030703031806060f0807060e06070605040201020f0f0109020f041b11160e01050103140121050106150e1314010308091c060e07 74
    0x14805c03c14800020305001c0180203c03040e4080c1c190b140d840e1644c001180340c4407981c0c0500340c8803901034410061080801c11a00509068507000e84200b010103018401000720170f02c080711504284404800f190180d0017003334154103000c000300340e40b507203668440c403c032541a00801d000a0320300c00144000383c0c0401001c4040c011505100c0401da0600b070000d5428030404100928083c0c0712000304017164020062112105141401c2d60307048200311681900804003600140d10134404e00c40d225a06041611906d05289141600350111003003440082da12600c411903c084075101d200904449140801d80640c043c01c176400d4262015403502000505956a001895202c1c0304803000401c560350740c1c0091644a04840e00203139114140c00d0030180e00615055107c441a04280101d510101d548850540c002c80e03030459114854010144548080300c20004418220045020041c00851212006000301c104001c00c440b0000d443c52421600c040c620305400c5502a0700c9080007440c600007800040e0141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 176024280 1250 176023030 176023033
    0x609050607030b0a06121805060709051516080f07060212060f0f011202040e0901020309011d0613081908040606050409033c0c0203100504050a03030e1e010e010e 71
    0x2c00030300b03000420921103845141d040c40000045107050006d26080101003280305850100c0014807803c3c000d031030300000c498084c00039002407800308040c5800c000154040e15603441c02d0381070004007030010031a0640d404040d81c8220341404003150b0042d0603001450001d00c515400b680350840c85910320010540a046507200c0c1c89660b400030785d1038480060546071b054003480d05240b64490303403080200034825030700a82d49400006040002001b01500218000c00070b4000822643c81e05031142008501030070701180113a000840822010400c0408610a2074050b03190540b501c401d81c2c40800070211558501c00100e500c40041100340200303440350b24000c000030745060100e03490781d07500140400000e400c0c01510040c030504029110181502d102c00302c00b19943d02c2c2c0803c480850001e0410325642138100d21038864828140344440150050501403075015005020607081590290041c12050010f0b14103449981007020b1480d07a45001c00030942c103040000981070445401ea203094406103599041c29 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 176025530 1250 176024280 176024291
    0x1406060906030a0615050604080307051b03030f0703140703180b030c160c030206040b030103140a0206030c09120613061103070504230409141e0c0402090a0b07060905060703 76
    0x203510b02107050301440d680704a00040c05024520751181081e51078101c80c0d0000f102280100340b0300000002031264034041c07000c484035520340400342c0c607101e4416820260550001d00206134407004031806000e65500c242419400e210304070720800000d4209a509400041003c0c00019100708004201c2016050000f0010303e1440e1074a81c0e070200d403043e030410040001440040c0c205000108000c1740196070300070300c0b0310760b00e541d5240212010780003804151a0650002450004c41030005400e59186034042c0c001c074150380e034500140c03c1039040b040213980c0007042100034285a14041c0000d038480c9840c840280811851405d000b011162003d00085408078104213024407960000c00361012102104940349507050b0300c05440f901c83c19028800d0b500a414a042c0c0010414070503255038070614201c0484110074501802480d50641c291180d1070a50003985c1d0840450030581c000b00082c0c0409061007480e240c0d1009201c0140c0d11246058500d00c0c1e07102240400c0100a1041640010003450140503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 176026780 1250 176025530 176025541
    0x10050d0c09050609090601050d0222020927040b06210106140d05060127052401031e0b2116060f0e010507030905090a0c091a030c0c150414060609 64
    0x3941d1b0410700a541c45807490381c2c1070108540c0c480542d01c0e0411081944803141c04490f0031b4050180d080045071a110b00240c1001404100749626840c103480c50344841454252104d0316001c01038100901019080981c501c131005030700b4004103580040c80030704000040c21030f18082d004010b2400b49204944120780380c50940c008114000784650541e00040d11403030300c0b054021048000f0742a00030012012a00344410031000719558030f21a01c031851011440000c00d9180310044080f18640705030740a0707000301c1c806070440c5030741190f01c00c5880f03c40241c005841800305070b084100710a42c0c0c0f40a444c0035405200804540102c0505070b10041069081140c40c640b26880013500c00400c035900141040b0010138402c0a152082414800500d409009101e050502d0508000907040f862511004195080000940900c90b001c0079148400410394207425a00c0303012002415501078041b94043d8403c03081c2d003403043c3c2e1050800314042c03031084840980c3da21070003044605000005080e50b04c5251024100103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 176028030 1250 176026780 176026783
    0x180f0109030b04080307020a0f0606031101170f0a290f030a020102030703082a0d0608030f0414040e01050708090c03060610032003010603060e0f06150310050d0c0905060909 76
    0x141c000d580180d04d16141c2d0b40f0241d0481c505846400d016241c181c52520074024090315a011005480c051030700c25810b505440015610085079908212803480c40c00000750101d1801c0d01e116401246e45400407807000c9002d050103d01180700c005000900710210031035940c2d40b03084d4803550108107099000d03242d000c0107500041c0d1030703010701080603041c40f840c1c200007892011842e10241e01031454400711801d80d844504041034a0301725201d00c400070b070702e00040416401400010366841c141303140c03412898036091500250501e00c50b40400e6030420388407007401074000400c3c020b45205141c503a4403d40030b441d0540e1078a2518018884060103034100005100880c0c641d401035101c8417041d0f00f0f02241da045980011410b51455070341c114001240400081803042c6c0c150407140403245040da0001c45500c6480c01850207c1080d81c0b05540128800540c10070201e09802565003c040c2c4000c00743d40c503540344089042000030100c01c480b60900c2d204240085c0469204a5030404000e40b05505240b03040706c04507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 176029280 1250 176028030 176028053
    0x9050114030303010e070e09010603020307110105010509150a0e010b1309090201050d0e15090f070e010509160207120620090f040b03070503120c011b02101a06180f010903 75
    0x7041c005858100086e8510302447e580c460002001e0700ca44881e41e074603400140203400650360000044e900303541818018505000f02c038180e03480101594100e840d804030310308145101c07407a031a400003141c3c0000584580307510403450080000f201c449607188025180004020090341007152600d00d09420440540d80c00015909500502d40c1c0016172000c40821180c5459202c403440e0460761520350402c81620408200d10040320808001c450007641c0301c106021604409000303483c5c109c148400011860030801c60704858000c441e00542d85820f071903803800b0344a5600f605080d41c42a49806d20039200e0070942038030075805040c103041e06d420303c0b01c5c18001400766600c41322034910550703c0e43c1440c07842e654207104010043c00c004049400300a1000444c10b840d4000011840995182c102081c0e5405c80c082419448401303140d000d0300c07200e2400940074005024920240c00ca0788180f619070a85070315464000c0010859000c054401c0f44c014408202080d044400240c2c10071050050070400a2940c8201 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 176030530 1250 176029280 176029289
    0x91b06020c0613180b03010c02070509060d050c0904030512070203030105130203060306040609081c0b120c13020d060f061d030d050a0309020f04050103080d050a0203220302120307090905011403030301 88
    0x281ca04203811030944c4000e0203560609aa0652800c3c0040d10302d20380014244003103880945095400703640e41e00c20040310040c0500e0180079500700d0280320070075223403a05080303921901c24200242048928154600410011a1010007590002005014a140c0103001002070440f038102940f83d4a00400820b031a2a8003a00041415031200c00200412403407074162088004401e12400444d925540364101405000c0d400f24000c510100c0b50600504020455052410024085402c86000310001100a5000c2c580c8904d000f9a00d100201d040c14000c3c41400c0104400e641340c90901e815007268002400c2d0b1000c41d580b10381e01400f80c02c00d101d0b0300002031342c0c01030301a400c00140074a00e5001040100145810301540289880004002c11a180010b00b000c45001742c4200300c0396403107480d02412031006540d5402c4000f01202d0f9080141260342524000a220b88103940300080703211180341309074000f42c6407440070400c400410f1103940424840c1c140103040b00329403090b190705941c000c01c1d2a480180207 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 176031780 1250 176030530 176030549
    0x5060301180b10030b07020a0201091d06060705070e0408090f300304050303031003120e0d0b070509030a030905010e0d0c0306021b0a120806120d080901091b06020c0613 74
    0x40700d60301403c10741e8008541020750b96205d842d181e24020f48850000000b2800b28171005004921210501103448a41100340d09411140c0c03102801c201d02500425801c891500c9061b0340852044000d45c5900e024501c1105001e40780d0064000300b0520500318440940258403008505100c409008504518000242000300000c07405500f19804c501c1143c000581500c000000e00402103002c09150301102d01039500c49007407614080003100d101660703140c0e5030b502282101544000c00c1d141c0e02c1c0035420804505042d8075000044001c681804207182094002c219901c03010469540c20080c0f0100080003110b070300855141a668940d0b090301540000303030002da401700d2500c4d441c404440041045030783d40f40c00c4403000c249501e060703081c50b00004e010800081c000c4001c60505d0912000d220410b06c1d496002c1c020003c0ca881040f25242001049206603640b14403500340400e00c810040000e400c80d4a0100e1206810080c01a10f130400c1c0300c014902800d0100450744004044c03610180c143c540440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 176033030 1250 176031780 176031803
    0x1030b010201060512060108120408030406050912060f040c08031c02030414030304050313050a0303021f0605040e1b060309100507050702090906070305060f220603080309030a02010506030118 84
    0x200101c0c010451900940c0d044400e9a692074401100010b5081c100c9060350100c480b50203c000072120540680d1080c052554000d00040c414613006401500300000090a05994054501029840c0c1700080d1044a060303c0c05405020910410100b0b041c003070240000110714004800030796500c23a180241070714042030b50201c0402c040000a49456000101c080c00b00c82d100c3c206070a02c07948a41c00181c000b000a010030200040c2d038100103201d1030480e50543c0260242210361552011914201c1c181203400c180c3d036020128030365803079120313030180c04c220000103005099642103640a016003888100381701d01c03001e10802c880b80000181610000c40c9216010841d51900e00040d00c0714000c030789001b94068003020400c0610000090381c5482082c03241c0e405c0c0a241c541c081480b03d16030002d03000c59080920041808030341c20008c11a5089081c0d03030b02001072078a0343c940780c545c0103400954494030560000104041016424040c558102c10218020449500c0110391020780c00941d000081482150f00e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 176034280 1250 176033030 176033051
    0xc1809090602120f15030a031209050708030c0d0311070b0c130801050c07061401050604090e0a0f0f02090123150d0c03150621022b1e0b09060103 64
    0x2501030f5444040241082081c43c100007088040158007210541d843c0150114010701500d00000c174017150b19010f445840700c0704160031001c400380180b09802e4981d0b120750f403000562200300308001c00110040001a00ca40c0901010060940792044c41e4600c0003d4207012101c0800d2000d00459001101c1d80b56503543c4440003191203043c6100e65100420b954070b0b0030104084078003040010700b0b003684038a20800c00d091081ca00203a126000b13000c0c1031b4200e0360501090094001c40e0344a001190460401c60b50004216510b94010710044e00c82100d681a02c07464110850074480000d6015000340031102c49003404008440003070f07034113a180b480e124030f0b400c8850316004100c20301150354007000710105104000d203c0c140a405089111000c001e94058900d002482c188148102d100c1400d92007118807400c42024043c6010307401c804003080e02805940701081d03d0107614101207c84c0d0024500104840300d440d22603019802d2210f01403040076090031034452a60ba02c1d4000300d54480400d00b400104030030003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 176035530 1250 176034280 176034293
    0x130b2214060c1c080a110a20070b07060f05010501140a080c070f0f020102120f0d0902031204060801080606010e0102060a0903050d02040b0415090f290f0903010c180909 74
    0x811070544842072a100500c54144c1e2195496119010b4404203201c01094220035507118400c0040040000d890b0030510803a415003414480540303803a01c000c44000300d44508040c54140d0000700101c1307180303956440c102c0c80e0790110300801d0f00500003400c20000c1e180c0345511401c060300c207407035501d4200b280300c07000a0004413442003680c41854000e1540c60f400c0b90ba529040412102c028002d03070140c8a0007100004101020044070b1300388544900c403034140100609510040e10064200b268907010b4070b2154000202140c01900042400ba0f542d0803503549019500360810a01610150404c5503007c1d203020a81d0700042e200d40c0041401c01d00240c5050360f414203d885005000b50740030140d000040004003c070070b400c040e005403100108440c0104408160545d0084c045200d0320310040c80c00203003000b030f6040380402444140c000d0410200c0d00000864110710075402401341d44951107010611010900302403044075849010360800500d00e114200d140e5124030090b00ca1303815100e4440325117038104080d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 176036780 1250 176035530 176035543
    0xe060109020706180303020909220b09030d0207050321010e01181512021318020904060902040203010f170d140a050c060408040303080f06090402010e0105130b2214060c 74
    0x1101314094a14601d4940140070b58003c020591040034080c002c07911641d10040e08070720401403202141c05914540c0d41e010f8492070024a0700075a40824132155624052900041030414070810145550b030420a00d1140001c0403200c982107110040030040c4180404035448a044d6002869098012401c69803507901070f2211071411106c03402c0020001a0160440400c580e00038821122034018003190340715102120300c00201209e11249128521015003040d504c11904980140d0020440c0903481e000b04060340c0c004e03801581c1c49030014408002d0940c01c100b4000143c410b0718042d20b6003000780300c402004075821203000d18036410b000600e175230340e6400750741100c0507a00741c041a40c0c56071400d030610b028260890300c030503000319141000060620358a4520b282c407d000c02801e040490315240c00440341100405002414048100003d501940060074964001c0c081c114441350340300c10110040d5640d02c401525440e0480c0c0404051219030419410118011002d8500580360040701c0380b26440c164 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 176038030 1250 176036780 176036801
    0x20f161b060203040f051c0f0812100612050f070e0a0f08010c02011503050604031d041b14070b040b04210c0c140d11060d0e010b0f040e060109020706 66
    0x400c000310008031660084081d004941c00b80d00200660350391941800440700940404030480e04142c0302400008424820180c112130240501e20300f01403c10000100c096819100f02d044082550b00420410390b000154416901e8007010900c01e030309207050900c40209000e85001c2c248040d40f42e1040b4203445e000f1110300201002c1c40c40740c0c184c69032000601d0080103543c0200005500740410740c1904c00d4540d07240c90840b54040300038840d030381c0e880c0c408441400c030034001ca200c2044440c0042d8000d81e61809440f015290100d9584c054403011240507240507190303400018205000c0c02844e01007810100c1556000307400404407040ea58070740c0381000c104001da1000d204c88024002c00707107070745943c4210341c44030a0340724131102c0b01515101c5104100c406440c05a19502c40d08002440c0000340070300340944081075011742447d007800c0c180e40c0307040d081c0c80c00c0244003515a952245070b1003035490178240c0a05001c000359010080800034890807a2510414007400042c580c000801d41c00b000103507030214009a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 176039280 1250 176038030 176038073
    0x92c011116020a060c0804030602160c08150a11120a09020303070f0c0e0c160203150109021c020906030c0313020907080108010f0b01020316170307110d03020f16 71
    0x3511000c4480041c424040720582c0034079903c07000070403228081c419210300a84c01800081c2014a15038640000c1d6110f0b408480b02030400840070000904002c51801c05441217038060100c503804a02c000d0a40c82c001010030360000c0c203000603111980a0041102c1c0c80c11059680200f0580d1048551009421034040007034142c800012914240502c08000e40ca0951081801117904c0756125501d841d500e200b43c9107007812040c20031001d030b100e002803c2c070140c0b21752024041d0389802c081d80b41514030800c400da018003103240d0000341080e03400403006803207241c000104034214180903100011480500004007c1400c414000000c103824242501001c035032268024a407440514000b02d009043c21003c6c8201e012543c00c044030303030f0144032031390198140d00c0c40c0603802035041036a030080f18218120141e0f815500d0900c40c40d021031100250200171441100d10381c40e50a1070166121021f072800554200c03101c101441030082d582c50b100800212365144031120821400202c070750401c841e1700200c607032010664 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 176040530 1250 176039280 176039287
    0xa1a040e040804030210030506090f090c0306010f080c010311040608040f080406050901080f0403020604021c05060a05100b0705030f09040f020d090c05031b04020307020c0a0b13092c0111 82
    0x400401000600070390781709a5440b01e0030940c0d100d09506544081d140c2c66441064140061501c03005800407a6210f203041088840b0401004046820100c0a130004803081c0300743c5c081400384030410400203208403800c1c81d00304900980101c071300103c1e0045016034000c1004410204051044500060300c850b078200300940c2c0c0d40c41d503424000e4031036409000f255001c181560300044071082080c0e03241d071255401d0b4011b480c0568480d0708201400c5d40c0c200c600c9400d0b0b40c0000c000c074046402008564403039500c0d0b0704002171505104550070b014034526400350a204c2c4042040c1e0002030f20110946e2486840304140c0d64590304c00c04001000362003d1b4806440851000c20300e000707003a40319000361020360301409800780040c2c1c6a2041c1510380840c050241400c0c8201d41d910492401c0a0340290f5010301c0500c140e84410410800080400c035456201d401300b18808500d94654000c20302000c4001c10714031008101081d07550081c80100347c02c03080011a24040310780700d1200300c0c0d020b402c04002000100360741b617038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 176041780 1250 176040530 176040533
    0x50c161202160e010609060c1a0702030c0f0703021504031e1104050f10140a0b2212210804021009030b0a0f050a020c060612011404140f0703020a1a040e04 68
    0x1400f038801d10a03540050003500c0001303400c500520398000e80c1c2e0b0b040500303030340840d0703a4059880300050090a400118803003000a030f058010240207405041e400c44014041a61946c01082611044140a0030110404000410001d0490807880c0744100510981020621103030030a0044812038010b11500030b411f02d020030130741000c0c600d103440c800e4004021031050961200c05415090352146d0006030042c4d4401d5080c001505000040c0640c145200c0344c1080c801480030304034610000c00d82c800d140094405802030200154a2070f101100300460302002c00c42c0450050040100710040c001030700480d1400c801d102c1f428414040000036540003249518181000c0002d48000c080307009103a4482da140001141d000c0005001302c0d00c510036907200800064070342c10100701d15044000482c40300c0e50360319604030100c40340454826100b103001d94a90031800000c030600c2802d000d030013030704046180c115003410320040c0d4891701c0c401c0c25100b652048060b2805c440c50000c120744110341003100215110b004100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 176043030 1250 176041780 176041799
    0xa05190b1206030d21110403050102040e010e090a0203070302010c0821090c030c0a03020405180a03050702100c02101211160303111c09030917060604050c16120216 72
    0x600803401030f01203c019405144040303a401d070355000c00c940c1c860081901d2072100f00c03c5402550000590040191815035a5501d4900b281c3c0a50f00c811281803941c00100114600384900980c0715006501504401c84070740e000a8403920640002410301000c00c1c144800c0c04424001c0d00e0080440d0091408114115a082c05940c01c081f944000140700e03441d035070031082c00c0c007040203441008050085600302c0d040d41c0c01c10015210080a03480002c180003080369074800200301c9408040d000307807100d0b40d940d13000e170040c081802041c0c10b50030305000701c100e1b6490058407404410f405040301c1e480c04040c400c290101040160600403940300000c040401e01d0020385860a000300301c0c40d0310a403020001e102204840ca0b40310f004103542c1072002c041c0506a40000c00c1541c01102900b403003860b0060403241c540360b906002229003004002164403110410809041038402d8507040401c03045918241000340c0001e813141c44a8190007003035505560000b0201ca8000c00a402e9500800c112441c2d415444402c0c22 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 176044280 1250 176043030 176043067
    0x30f0f070206030a1a01020313050f04020f12040308010906151404050d0308090d0306050a0b09010c06020409020c010c0219031107030803041203140c04050d020f1306030212010203060a05190b 84
    0x40c805c5d28464002861558000011640c04211080c2c0c400c00240c94001003100d40c0c800c5440442c0c000d90204005154498410000c008a012022050070241401e0030020300b0390605030001703051586440310900948100e010140300307002c0350b450114941c10100301208154022680302d5500201821076090406408c0542c80e0b124924407021107919031030350b0717500b2015224103104040c0c01031011003060044400c94001461012018101507107078103002e03a500c004991080d80100c0c1229404031708060081c1d006c2c0255020a80300d44003c000141d01d1500400401420300700c014240040003000400401049c0003000066800a40701a01c0c0c1c6014105070004c444031ba490800042d25013095500e00c007542804d41e6004809801403141840c0c1850f09010301c404c04410241da2110350000c028005580d07003c2207000c54900c444000c112186144140900002d1121030707414140d00602c2005540e80350490800102c03801103030250300c1c807184801c0c80c4c041134030b50350030003480a80b00003083d2180c3c4c89140c031007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 176045530 1250 176044280 176044301
    0x80c03010b09060a05240406030207150e0d0e040b0306040303050717070906120b0a090c0e03070b0d020901091701140105030d090608060f040e0105011d09030f0f070206030a 76
    0x344409880034040200c0d01e04122003480c4d000002110500c1242084200b100c030890b0701c0c40e540c8505a9561580f140c1d29000340c0e00002c0000c3e000a51281048480c1c1080c00e000454600c0c18081c40890002c002d460b18102c1e4102001c00108c1580103c9030b950301e07040cc0c1d00310040502a10414185410020007a140c11603440010541001c0c0c189044016050783c81c0c03091322950344110015043c09800c882000785500c98020543d2504075100c6581d4031030503100004d05600d0000908804000005440c0310300115a152090b040340d407040110310020750807030b001c160a0000040e5101445801a204031002c0c1e00140e40e480340b0281d0984100e031055104d0749070384411000780d202581c2d880d0101503651444640180c0000c10414041010030b0146030b0381d41d0024001041c2c50000103201000c2022117800848010040c0c0d16000100000804400c0140490741e084450400c545401203c0540da4071542d4903000352040005580a080b901c960252045140c5c001c2503d0340c0ca0412030480000350101100303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 176046780 1250 176045530 176045533
    0xd020318030310051e0415030212030f0906090406081b1c030507030c170c03130e07020304170a080c010c08070e030d030b030a05011d0601050406060801030b060a050604080c03 77
    0x840ca550444004280c910440c0e030035528400e82420181400f00c000c21000282c03d600c03495140c0c0d03c40e00e90301c85c0a4681460240740f66410010700c0c50040003540b0340c2c02514102c80390002c1110780c00c0715041d4002c41e00c20320030a656040d0b0360703c400400b003030084c0600e80c810f01d02402060f111070444d4800070140050707103608a03103030305040326040784c11103a604440c0c1008001c00c8080100100080c0105c040d5100f4500580081d802c0d080c1009086071a5440007d110807030b5000001c86d03c80548045410901904441130300468518000c000030356030740b20700d01400d80f0380c1ca00303034250b0b03190008101710b0000a01e610501c1c0949900c00002242c1c043c211804610001c00e00301b9000502d20303841501c1403e080d4400400403c8189c14288040c3c1c000d04001d28600c1d00740c020a4519408543c0900400145155404441030f100860000d010f080c00c0341a0000f620035400c2c244c00f081065030100b009415650059117800c03a035140c3c1d500013441c91081c1d0703001d41c0d04494081400200039401061039031407104142c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 176048030 1250 176046780 176046811
    0x130c0b0a110c0108060d06090c0801020a02100e0a1401020408031306080a09080f090307051206010f0b03010320030109060c020105100b043b0f15040e0601050f010507080d0203 77
    0x601403521110001002d90000719088000f031000d10b4031000d0b80410030b01403400000c1496151b160304410328560342000100d0703900001d480850540c1008903007140c150020041001000d107840c40d0743c80d403a00c03100142c001a180b000640c03100e2000c1d8111401000340d0001c8a035100c08506109801c8690b5118200102d00158001440c2d001a0302503000310ba5444a545460040c9000c04d140c407a41040442c103401d03200302d000c04515030b242d100c550f1041141150051185614000400c1080703400c9030411103841200307000400c0090b0f141c12500d0f628515660040c461042c910300824014585041e01070451402c242c8a0451180c042d0312003401060207283d0340084e00d88560310180340344203d20910200b01103101c2e02c0b08010b50310320102c0294486810607802400d542c880e0350403081e1801d44500d0044042030082c030801030840210040074200503241801001e00140351a6280c0205110342c0d40158070311003411500341c1c418021074104079403203a034042d2074245188180340290403c0b07078001c1a401802 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 176049280 1250 176048030 176048057
    0x1150f0806090a0f02040b03040f05010507050c03070204180503031006110309031c020c0d120206130b0a0506010530060303070c030303020f0f0c0109020f27130c0b0a 73
    0x2100032a22406001d4a1880140c541c942d0740c40003818162034501ca07030780d42400b02103031200d000e0005502940c0a101d1004960440b81003103821200094403160902104001e50400d880003c0300341d03050560100e60011741d00312141c0000310f003010300000c0103100740400010000f0703040e02a40d5940917075039645d44500c1081803600c1c1c0c03d076032445100b00c5240d01d40d0202c40f400d8070448800611080004c02807041c0c40c20102444017080c012100d0210841e0001030600202c1d402c00d034100082540503425a1030345507001000c1d00c540580c0b40016040ca4a525118030008646900480860303051001d0120028810112030b5040500c201220800c0a8100402000f00da8907160000542e42d1451304a8100b011191559509a000707501c6840d540c502400180207240c10700100c140030301241c0050000200300d404061042084524120b80018401c080d0b24041300c6450000302d0340407034518070001c0c003550703962100c50001ca1035001541d0001c281c00c44540303000c6409948180609100f0b800764070f40f903070300d03100d035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 176050530 1250 176049280 176049287
    0xa0308010e100506070605190c0c0f151b030c0504030c123e060309120a140d1a01170c09040b0402030a1b020706021b1201052404020301080a060903110601150f 70
    0x20501000205006c892501244140d0350389001d0b64440c5c024100910742c103252081c1603c106402111660311484dc0d9410080c1c0c06000310200d004261429903d02030071a55025029030071400341903041e0081e4181281004041001541c101e03c0701014414034680c04a80e81200401d040b075000310300485a0841e400f41c1c148030303098174041c1c078607640540005586080d10807410b800441e6124104865082c800482100c4003000f4001d4015104010031070300b1407507c10000805c1141c2301c1904020721a400c0c1d01240652140140c1c100030b07420720040d0b9501c0000c001901a111200e80380782d22910000c03e000100120b54803c0b00d000581c80404095106035200580e00c490644c032030800943c000b44000c1a0700701e4044055030240030005c0400a00005607800075003141c00c1245d048110084c040941c001300480b0130001c81504408481c190302e90342c14100101d45401ca410002013065072128800d800b05405102e0304030000d50701e60704a550561f91042181c40d5480001d0701e0b0700c0400d8600701801001d034030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 176051780 1250 176050530 176050541
    0x30a0c020303090d0c0201090f0f0311120a020105030a1e0b0f0d0305030708072705030c030a03090329040303050f060607031d0a1e08010c020a0308010e10050607060519 74
    0x483c50050207090f000180700365000c90f140d210407810042c0c0d42d80c0201e8080038200e0030707101409001c0c140000031400c40c40c14115003c4403a9541d4801c0b5072021000b0700380900000c0f50142c0d00e5080c6401d41d16511814602e13030180c0001d030700112409060980e145a80c585a41c480140040210b40c1ea09010b10000180007801d0240000980007400030000500568015000d10303800803010f213481048251010340102320400c800c2ea44511040c1154010820303854200070206485004801400b820f401c1591701030005541484020304c0d404454803520602c00f0480c8404010803440b00f6030700c515250514004000f058120340c48408518494049411401e0800c10f0b81c064640c103445801400940c01825800e1012200403280c1c0f11210010110b02c50308143e2404803115030201c03929868034201014207095074000c0110a04560000d030019011030740c000c20180c1101d01e2541100c525480b0301b47c0b94041005580c0210380c0101e4001101402c000e0030b60f010a1041c9804e510704074112000900f11001d545 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 176053030 1250 176051780 176051791
    0xf02090114060724110c0d05040605121f12030306140901030f0222090312020f0406080c040902070309030b1608180c031221010f03060c031e02030a0c020303 69
    0x1070900c081c0000604094010750b1480240e04c42d80414088481ca102c242c0c0c0ca401410b012007000464540e4178141e04202408480c07150f4145207080c941480d000411078010210040900003036480030440c424074406c61030801c10b07001403000c000d95865410039039100800320030440c00a40b408100186e03c800201150450010062840010303920310b41345c002004801030016644820b59102d14883c1c41c01c046050f4a9007009040c021480d04001c2c1005010310380302c285400000c900420600d0804c0e80b21200300c80c00d64042e81480e03a50b64880420004450280741c000b41c40d032520020301001450f800c004007a00b202e00c9000b40d070f0413582c4d5110300401c1e140a0030150b50302080d031032004180c46041c103c00c25150880c0c02070454100d0500d520000345041c642d005410740402000030000c400c989602101c2010440460100343d95514003030481601141e58400a0300d40365540100710120b40c400d4108080304445003c0c0c541030100c40b20340e000d00070752060307607d4000c107440c0000499000b40044240c03440745 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 176054280 1250 176053030 176053039
    0x11b08060a0b0703021614030c01140409090f080d050a111801080a0b031c0206160c030c0221061015051b010204150305040303050f16140f070f02090114 67
    0x798588400450399822409045080d805205101503c044a1903c0700c4010400c43c451010164401c0c0141400d00e01d01e08841da040000081801c05a142240100d504503040f0081c00038004c44c403030406071800900c00308000c2c800040052000000311103900014090b2021401c1006410719241494010303200c0d080d0015010b03c5e0003403c03450b0030b40c003800040e41c0c0138110f50f00102d000341c0704600290a1111580c2d41460b49400c00d030701d207000542d04000c030580c00042d6000951200c400b44c00040c0011902e894001c00700208103102c84110b403156001d130007441040c40740c0c24030f01d10b0020f0b082c1511214200d50b08810b40316071010000d50820b01805014a00060307844840c0340030146254001c48030802403080318a036408000000c2c12080424844205c3d900035074001419041a14006040d1580504039a1b0300001030740500a46a250070f510811000c25420082c80250801241c10a1390150701d1002501400100d248000d1182d4200500e40c464400c035060302c020b83c0c861611014103880310390240d401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 176055530 1250 176054280 176054299
    0x9030d14070f031e090305040e060a0e04080c0a0c060e03060f0c0912151303030b0301060521070e0106020708150f070f050c070308041805090303070302130e0702011b0806 75
    0x2c80e01950180000c1481c0700100c104407080041c40304143c46210600b1800207000050400131711404030100390300080c0845401c00703180d14101d49441c6060015202418114001400c1c0c1140c0d0400c00c02410307901d50044551500c1a51034074040d1103079111482941c024040e020025050041d00070b8641e12806800032090304182e0700b0420f201f03e500003000841100d208005030344410300340000805124140d07000c1007215010351481c008064a4140c04014060b03030500b90b00344651303a00c101340502c08046c0e00004903440d01316075001c6450115540d00100e0500300d502c0001c5007541d40801c401080c1ca080204031105c102c03946180421800c82122002039002c40440450041e601c107074004803080c4404e281aa0800d403100d0b50044c2070140590003254100c0c0e00060410941410f00c0100c02c0130043d48408001629140c0a555181e11000f0a0041010342c0000c00c090204148101280074100d51003907002d05241c4440b000e40204458402c3e4003402c00c0d011500d015662042d50f07000d101d40c1024024048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 176056780 1250 176055530 176055557
    0x403060f1a0f0303220e0c0a14070206030c090103021c060501020c030f0706110319020a0c0b0712140c030f121014010c03030204170c10020312060d0501020c0609030d1407 75
    0x2100e920380c24103080805e00c00040001c8603200c11181c00c2c0140d0100924070390300d0301a094081c02c91200654401c1d0407442c1480401c015a0782c201c180c035842481140c0c41384d81d8002510040740244210321012580348084690324800002d258060402d4400c03c1c4c0840b490180c5000800d81e45014403075454030203610203c3e00380f0484d0f100b07050b51400c130300031101101d05041c001d080400460b00c1c980010001644030403102014800c80200c003600034a8982507080c50484285c4441000b2a105552102400607002c500080c0044100845101241c0300040d20f840e0b6548900004240d80050140c44540003d140840c1d1052001484402103032030b0a9083d02c6071040d140f00541d40201d019106a00b4076500340030000350081400c5041249400c4c0001404200c00c0001c100080703200d001e40c600b0110340c000d11030a40310f051641c0035107411110440d403005c1c1d5403200d460701501a100d0205806914007840c0d0901012410000140514140e104018402c0b140d20307013800b03002198111080e2000440c400b0003182c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 176058030 1250 176056780 176056807
    0xe06100f0b0f090d0221192a09290306010503030301030b07120c0203071a2802041a04030501050906070503040303090318080304090e210c030403060f1a0f0303 70
    0xc5810018080382907402c0356030005501c6c0301080303100c0100342840c442c210700c0100701800304c0c0800a0180843c4081c030f18441d15848445c120345a240c400218514044541c4200110080001805142000c1c0128200c1401000315800084000703c400d40d03580044547d0fa2070f001c10f050b4140c0d00d0180045046a183d034a41600c0110b003d4800030604c4070400140361005030500441000740788540003140c1d60f030b120f40751a4181608005804031825540030070311840344041842c05141e1005c00c1a101900450054201d009202c0ea0340826200e106481c6496070141d5100058412039025400030000d42d950504c0740c5440f442c080b10a2400108100006000a030080e8008501580a841e012802c0303148548100510710b4a500440501d91012a0402c0000700c03600a46010380458005400c9d91742032028640c0b420034824801208981001c910380c14590b02c2002981c0041d07800a800340400c4500e01030780401000300610f0400d1b0700c0e680580440c41400c121000e402081c80142c010341c80e0503589800d82c1d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 176059280 1250 176058030 176058037
    0xb030106050a14090c0d0c0e1305240102100c030e0f030304080f07110306010306021b0c06120c0f04030305090a081501030809030f100b0f1804030e01030f0e06100f0b0f 74
    0x226017040e030502c510061200240300d144a5a240c51b2902c5550b4040c2000700320382d5411060703418800a05144c10000c0c1c0c0352034107400b401045840501401081c4000c401030b0304220004d001100003e01d01400310b41c0c0c443d419002468a28030042c00e507900b03060b1003141151a0710088801400c0b0300030802c0050035101d4050300506240b030103511191030350114400080e09100c000c1e0f00c1a0390031500070541c02d5807182c0c5011032580120b41030b4014040460584082000d038040c03d00200c00f814403120000e401480d09208840a00e2094104d159582d40c40746070142c419001420300c280100300b82040822a65400502d070b85c0070b00c8046d101c40405a203036580d046c1e050f1b4082654641c040c0203a85092a003504100301200c13400080c02408914000310509000e1485044102c03244140714910070f42c0d0700c0700004e0204640190301458500e03461031040006070040c002130f0307903803c0c400343c504503034030b8a4000d020402500406035005d2000708659951702c5441200c00798000c4460805040004050010068005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 176060530 1250 176059280 176059291
    0x110f04021c05040b01090e060609180d02070e180a0f020303090301020d1a01080f0c07050a0b01080a030f050f091e061603030513230c0a08010b030106050a1409 70
    0x586481c0885500603109141c008000001e191280d060208003c407008840303014100d6035504100b10700d00902195078624000c0c01c180d010f80503580c00300c0d00c040040c0c00594002c008046c1265600c5203442d4000307507125014410035082044140208011032507212a10740c408901c403004019503000f980b10503801c2140c0150482c0d05100400c2540d189807002c3c00627000c401e01c0000001842003a1180c2c450b072890b00007007040c0c10003845104006840040030714941e00103000c250780b07039145d031410b02c0c205117000c41440d40038103603510202c000143c0c070034001002420302e0b104e580c030060000300348076050318a40600c02d0300e80003028043c400031005040007809880901c1c3c900c07000340130450f108404a45d0661015901c45400021601f40105060305401040d03080f1141000c941e2090300c16480f0008010145045130360116000d071124034860381e040000b1190008000d1180d55540c1c0d5510025009103490040c59009500f0070703000007030711f1410034011001c860100c02d00d031303180300d62a1040140c040b400400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 176061780 1250 176060530 176060539
    0xf1803070f05060c010f110705070e0106020303040f050a0b0109230106140a03060f14090c03060a05060a03020d111e031b0f0d0614090612120d0b0d0f020a06020703110f 74
    0x6c0140c0ca40a41d0300441c1c1221f0a02c0103a0b030b42c0c41c807181c00c15904028182d00540d50000000c0010411145e0000c11258400c1c0c00c0006039001030041d24245080000c6480c014205069040010405240e20b5028601444411014840c05031946010740f000355001d104080201d100c03100a254540d659000414a071040b62800050041d06c840320881c450b901d0350803141e01c900800c0c100c0135550424802c070581040e10520000c0c214500000055032850b018001c4030702450003c00c0410180f8001e8055845c0c6810000f400d0101c20144003190403d5003200a82c5131080880d0b00303002e241d00380c0100803280610300030001601505581c4081421070341c00b01c00e81807008401000310034081200c610640007d4580402c0740303e805110502003081066024140340c1c414190000d0f6840b1102000541044d0945003824041c2c981d0700100740307500200070240d040d64008803080c40701010800154580b2240030b1013100c292544a40714001280e07034219134040101308180205d078000b0149051560181d145c0d80042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 176063030 1250 176061780 176061791
    0x3060604080615030127060b010309080d050417040e16110a0605040c171b011b05030c1009120c05070b07050309040506010201020a020c0609040906020f1803070f05060c01 75
    0x2a514a00a8102e51003d462140b26142040d240740c00e0007103002e0000312070440b0440740d1055018079008142180d00a107050343d100c3c2d1401d80ca0340241c1290030f441350020802a02e071250710500d840a000101c1741140e07030203100040d080c52068002e0a460546034440b03440241c55075000c07104807511560801107002d11200c00303095000c1910030420121410311443c00459076040c6841e10703c03036010442d0880094400c01d0100e107400e00300001740c0b071007e9549148049104410840040c0c510b0040ac0c0d00107109040110480c006010000008100c80340c1c05000b12641c542e4020881d8045402d402e200801c0d04003003c9a8420702482003200030f4500707000f0416590010b56854602c0d4140c2d110031412030300780c1c00c0852881a039217014420135a00030000c0c0029444c0040084c002522030618145140c807a0f800411042d07516200c5030b02074100140c4c4030204565402c040441500e080e0407020382500150441ca80705a034908001c25240d0071500c0e825a1081c10300d00308001c0250a81120010400a650b142c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 176064280 1250 176063030 176063039
    0x23183102070c030618030f0804080702100e031618050106050301051002070e070c050606010903020310020c01020c010e030c10060b0f03040f0f032105040512030709080a110901050d02011403060604 86
    0x284214040c081c40c1300c24404017545035103005401071000420310f2052064520800010540c46012686500d9044540d80320202580c90156100d030102c00c01c0300e8062249041840c0109400a900015107849200002080301c5080c031040640c1c109008440c0001c805200401a40c2406584d207020010cca0058070076058407a408180e000404a40c404c1c0010101e41e0000c0900100f0310000da0010740a02c3c001c40c0079070443d0007113a42e84048030507412540340e0010f4507002c801c40a5043d9070322010400000d2001c4a0070800103503407a040040341203032034011084241c42c059058070440080f41c00b016180b50804591900d4618a03400041c400d075425821200d07414000b4004861110080f446920341c003001c07210030b4100500d4080090040d409051034002440701161000030b401d0010200b0b000420350725514070404403078141595100907558441c18414904002d100c110101c4c910f8001c0d1a8609542c2c2d840007045401003000101030301003408414160702c943c8248000390760045018084602d0a503a6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 176065530 1250 176064280 176064293
    0x18060d0203070806120109020141030912030403120b01120212070909090807020d0c030f060b030d03060308090d02010318060b030d1e23183102070c03 66
    0x100c8242c0c0000b8025002c000d82072030b10303406070156044044000c00986070b8560019001003880c0d8462001424101c40108100e40c101c100f102142380f200300380400348031120801c103e86030425210034216000340c02c40c0c034450f4418001528455031b0950341e008030050405808100611030110f605040110717480386200004002d00090203022920700e5581d1041c6880000101610300742d4200d68507450800b581c040c0442d0b1a241940c02c03441d01124040c8911005141201c42c0740b010742c0c0000e000c0c2e401070aa00092190607800b00081001c01d03015100e881110300740440032513059001c0140800030034000034640b4103140000352030707151060400007044442c61000441d410001c0300100d9042391910300c01241390606010780700d072040b85810010052440564141700c89400c00c16a502000846107068112a0303070b1618500d014107142c2d1100341c1d07860703440220102000c8120045400780329588403a5031320254001841003c480b800700c40c11403c500080ba0100a5030000e9810307100c0303c40510011011a80 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 176066780 1250 176065530 176065537
    0x70e09070c12050f09090901020c01090309061d0a06030c02010b03030c010204030303060506090603130503161a070c03080a09030207031209060818070905040503120106050307140c0318060d02 84
    0x90303500c034421080c00700d140c40014090a14030003400c00c081840307522a110005810b40d14244421180410b50307a503003122082c028000c3d41744201640d1b08050540c0f0a06409c11140c0c004e8448541c0e9505602d04010741e00214054141c00c1107420038508413003040705a200fa401000c3c00764807840081200c05107400024510b41040b46210743c00c0e580020101708058052003210000d205c15140700e070a203c03095000a83c81c2c000245918003141c0e090211004200042c001c98400c103071100c50307040d0750180c5410441c94140c000d104002c54404080007103044140075000b00a5150b80c1669059040c0d520405064040e003203044007202988203a12000c000075005190702480388043c4d40d00c1c0540c45280800c001d050180c080c1c101c019060140d10340040141001c1003210644040d0071004c102c1e6151071070183d00d14030944060a0160744540004a076003907010001314000c21031566040300301c80705448031000c1807191441d500b000d544100024440d20b40304103103c401162008100c641045410b60030720080c0e90 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 176068030 1250 176066780 176066791
    0x151c020901060f0905030109020d0602160b1303030f1a0f01050904060b0a0315080a1b180518150f07020106030b090a0210030507050706050603160306050603010b180c03070e09 77
    0x41e030f0301d00ea00a90641c4006414002c2004800030b02c030080d802c0c3c010400492401c140501000e03000520301c0305100d07003030000f14141ca502c01d4a5203100c1c41c00f440c801841450307400c82280000e06080340303641c04030424000e0324001d01050340d00c0c6849000c080308100e20351488001ca01d0500c40d080c00300410950351482000700800842c8500c940d40d4000d110014112100300b07a60303803125501003c0078002a0400900245403580c04854203040c100381049460105105510109801107840f0455060710320a070000c074040c0c1600e4200c80386100121043c180c41d040302488100001c0c1683c00000c50280b6004005900800e00b40000a180c45d101c0d1900d210440c01101c0b02d0310341391b010803114421400c24107110340601810f03150820003428181c0b401001c5110f0301001a14194a62000c5207180c1d500341700c1c00035404110500411940e59a1600201500c0d0840c0c580c2c0c460b5181c200c502038641480d41220f1a006140494a02c40f941c80b8400a403032a00082c00c0d40c01004030915070b104980c0c845030340f50b5020300d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 176069280 1250 176068030 176068037
    0x609041a0d03050309060c1e0a030906020703050c060f010819020402122401030c0519091502010b090f060a0b0705010b0a0e091b06041a120106091d151c02090106 71
    0x2417a210052610340b02c4040c002d07510b40c0340b081210091185810802220409148041d560340c0c10450301e04034050800044054901c0d44002814410103410400078003100c0d0304501924015603454580403c40f40b42407140e1107a9400200c01c80c1c01005405000c07048183c0300510050801c40810114000283c0444d941c5542c01c6d02c880842c03140c3c88000030703805610507003480e040c060214204030003055409142050050b02141801d50741c00c0a010700c0c42c003000760107800b00e1084903010b0100002c0c0030b00403015406001c1e40d00c01011400300d01503801060702c211009011949024909205004035a00c50503041d60b1030755070b07840070a040d5683d00d1221b000a0000d208c11008608104440130300b4540007446210400b20f140c145082d5235111101079070102c1d10b400e01e41c04075051400740524528400e0741c1840c0c59000c180d000203e9200d8005040c0302c00d480e240c82404540382d007030044607640c0c020190b40c40760744600300200800325403500f0701c180c43c410082e007800c2d900301300314507404218071540a82110010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 176070530 1250 176069280 176069287
    0x7030f05010b012d11150f010603060f03020303041e0f0303050405090c030702070b0f1b0325032a150e0105100e0f0408040e070504140603060609041a0d0305 69
    0x140da40400c052038800400342c0300710710503618044000e400c03000c0164210180240804174900010b014840c00384850007044141c4964980b004c19140129030074010940468a48900895500d00100e0340c01c0c2681c0d80580194078042c2020885a03481c160b0f840c5a588181c0c08c8100403d0b00180b11010600031072081d26103607100da00303080400000c0e00d00104483c450600034000c20214a41c0040c440d01246c26040b90680d49507501508810b2034846c000321100d1450300f80044c50015100003006026610150600c149905104110780011201e803240280014051520136030034481c00e13615208641c000690a4211429541e03561595100c0341041e030010b0503070ba52200400780c1001e0241c0c1d41c2c02a00d04695400071810031a032101040b101500e080714030060780000604101030041110301030610811211031520300b010008007507078020301440170380450b441d40d520061705040c003d580c0030703040c0240700d03508124040717040c080106400420b13075003800c826100d4183c0e039890b0b81c04040b030210f0299851580d07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 176071780 1250 176070530 176070551
    0x6040e0c0c0304080a0c0501170601030c020c0a14030c030a05060c0a0c0605130c0503010c210e06090f100216020f0103061e03060e0304050d030c110a0b040e06030d02031b07030f0501 80
    0x602c02c4243c0c3c02281481007030400f0720005c009d0080c119505c1042424005580b550340d44040740740561100703e5a800c0070b6101004640168050503070ba6040c04100c044981d1040c00e8020302d07881e001c10050060403644014080740303111020002811452000b460403c0c4d8449450b00e030172051721000d0f80c000e9000401c00c0740003428080c2c40041c0780c0161074258000c0c01500d02114004046507001c1c110281480300140410500e1001c0d82c11010410b401041200c000e8182409410344914043c1d0103080349110301800100385405034000e44800040400e142c041158040e024882c1c842211540c642c1010303581c0c00f000c60b000000f5550b8810000b15030000d80500c0d07066190034003c40d00f20a09203801c03540288801c1000340d95003082510403a034145031410a2014518245012282188499901c00f540d94000f154007101c48005d030084402001d0b18003445c0d02c4003014191255060702d51000181c00800100c000b9600c106a103c000344800030480784850798940f14001981c582030421030709039442e08030408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 176073030 1250 176071780 176071793
    0x120509030a0606151814041503052d0705010e121005090d0815040902060403050a1b0e191a09010306020915160f030c0b070215010b0906040e0c0c0304080a 68
    0x21101d10741e5007060869102c0f0013901440c0d10b40f49100b510a0a0611040146c5030348407074000f0f80184076500c2030201d1180c0c91380342076615a00d1b03d05c500045c0032180e4403e0a1403201c102a00020084100d019004082c20000116580105850a01e13040b9410345006a0f2082d410000b549940c11107120000f21420714006082c1010103560b501ca041204032400d000000c0d11201c0840c2d075901c02101c0006a40711a031020501c180110b61026085001c0c444d20682071240d014103456500b512a02000000c5d9201e80c0c81d00700000050310b01c1e000c0741c82c0e02c030600314074400f842e4442c00e510380400350b80c2010b0302c031000005a2042400d803c200c5180c4d8001c5140c00c0d10717051001c0d050440c20407407050141050101c440c1d10107010424140901841d400c4082201494080c9840c3c82c038030f6400415221a5241101c4082d60ba420001003880d110000350000180e90410036041d1181120000c00c220302c0e2074900081c40400070700240803085191010088046a400d0800041000b041c0c41d0003d01040c000c1414800b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 176074280 1250 176073030 176073059
    0x20703142b150909031407030804020112090503070f061b09090501080102043602040b070212030301080a060203060312040609080c040204060f03093305130f120509030a0606 76
    0x1400642c00c2810354004840055041c40c152110458005982c0c00f0b503085c100d4941407048151130501c08001922024550f100c800948030b10f000b0b0306da1401c80c1259030700e4007088071081c1001500580040c45950001210000740306c044074002e07030021032050800c010190643e14001032000114000c00001c210b034070000e010b0701e801400c06a001b1402c1500e4484090400f6500007194000030100c40c04074607100401c01c40c8803000c891040750454459448982e0030b06142c0c4904c80c140d100d04882ea041d52141b0704004200c0c0d040c1c80c0c3d29000b500c40c02840355600f8010b900060301c565418041e080c41200d100142e00b010b44010151544d4440d10145440d003030b00d080030980202c140c0150700401092040e50381089038403554030100c0c030700051070a8983c1401c6103003150a00403880000c10442c0310f142c4c0c0300b60b03c40a19115a1000c0410012078485c0c82c107082c204200007000604d01248008154007144410b2400040c1001c1410000e2522280d1800a41080c11181080f54180d541350400c2c06800b01c8007050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 176075530 1250 176074280 176074357
    0x1306090b0c0d1d0c0907090e07050405030c0d23010b03010c02061609080c090a0b0d0c06030c0c0c050f0a0806091c020604020123040504090b060103150e01050402070314 74
    0x64090310407030300c220f076a20b4440000740035009403650b10200c0d802c10b00c5107900e0030041a40040c010140d0506020007403041c0d000340700b42482881000d108400500e00040b0b40649260b104000321b13241207425601240141100c5881e88040d540c846c2282c1c61130714280600024800d003903020b8400c91801000040461000720041c100300714a500c1d00340020103000a00c04140d000817101c0c50382e0b640c2c50201000191100070303030003500f0552401c01442000a4022560107840903a10180f00703200c0039034001c40e0075a0700c03d0405821003901c80300403c940d0501408460503100064003101d65161174009280c58100b050350701402d55401044a1002c007105200c0806c010181840541300c503090940000784109680318180640b1a641017041c5550b0802c801214010b210240043c8904c400e03c1c00c0a043e105000c840e143d0200b401c02d02c000d0010a4243c030032100740c0348112074501141e4202024880290005203046080c412032008200404032000041c0051010043e8880700503001c411410781c00b010040e89 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 176076780 1250 176075530 176075561
    0xb04020c01020403141f1a040e0f0609030a08010b07020301111b060c07030215061908010603050c0405070f030902011205011e0e090a0201030e0309060301030302070602060c040e1306090b0c0d 84
    0x4000c6c1c042c4102801003504e00c901400301180c4041552860465841020115076001d4606016001002004928501311302190410b6540550320380380e10545a2103907941c04030001d60541d0061208082010141c404540042c0c00001c01b0707103410040791456070052900045542d092440300442c0281002141c0c0d021405c0041542820320340c0da0042c1d640c1c00d031030103005940300b00078001503501d1700d501c484402d860b600b14258911403940d4000482c001d007828001541d440c01011540d0046040c24016030b0b0007440b40b42c0c1c030b1030f07100b00e00c241c0200c0080c15460012410003520003840c0750041ca070303030003040e0103048040e59002071071901c90300130341c40c0004070b61000090f850340c402080300e940c002140a0304112307020b0a0108030b0401c0f0b810381d80e0651061840c1142d010102000200c14140c1c0020084152104c6400b1610300d03885a004020190040d88211012005100002000c400384014020880d9218500c00300c0d010000f0360313035503600c090111481a031168000c1a11080074000b400380860110768250f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 176078030 1250 176076780 176076793
    0x7031506030209040f02042c0c1002060412050906071101030e012702010903020310020c07080f07150e0409060b0315060f0603040f06050a05180328030b04020c0102040314 75
    0x60102d0f120000003400605545502e079041801d548494104e5800546d03807400c03880e4031071500c2081c00b4800e1402c80c000322641c420f0603101b04080c01c0c488040172103002103030000c202070741c8e40342d6807005294401e903464801c2141c02e02010001d521984040e1500c2842205071016802c80d200c00101118604941c1d03010b01ea04002014194103a444240c400e20154134107011400b95490005803031503482a40300070341603c0350300c0400d2402c210581c09840d4400707502e030a0b1000c0d1350b40c03485056a9000160401c46450b000204100480c0d6504101e007510b445441c10071a40002c50140000e045500044060310710030384410900d00107243c140642017122109000300300c1c1038100039012403c2c065032a40c2d507a014420010102d0140a021141101c41c40e030b011f0014400c030b203480395002c005030109448d200d11900d52035800311051000442940e0361006088042d2a80c12909803440c07000c1c062100403e0281036a44d01c001c1071035252400108912840b14001581d00d51852605180561245010a4003504a41d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 176079136 1106 176078030 176078033
    0x510020304060e0a080f090f0909062e0902160b090f010c0507121409330a02060406020a0e1002010507020d0e0a050111030d0e0703150603 61
    0x202e400b07200100d40144540e0f0b903260132450013021a0000c0c40400620005030000d4610781c6002484400825001c1d00071545c40300094032a402590026020406a24000300040800081c0054000c00510318000d15051111080c0584100d850b00000c031384042499483d50030381c40940140e56140d0038200072954590b40c0034000d8070500c20b03500303010700541580d01980c19103082c04c0e042000000e03030303c000c0f400c01c40c0c41d03580020340200060000e01c003450f41c90312a03244d501c4440d64418006000a48190200703004129100f41b4106c0355442044007400460f03010074125001640010701680710700481e10140d0318000f444506a4200703101c2c840640724284c4c150000f500070101602074030185005148110b4030018802c25840e0407554031130342040075512400c564090905a02c05aa0074071000b66004400d03a1900103210415900c0500280140840d01641d080307c88803c080410190385503 = true := by decide +kernel

theorem cover : BRFrame.Cov 175899280 176079136 := by
  have h0 := BRFrame.cov_init 175899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 175899280 ≤ n) (h2 : n < 176079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
