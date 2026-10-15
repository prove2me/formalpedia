-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5119
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:48:32.104618+00:00
-- url     : https://prove2.me/submissions/909df97f-ce27-4f92-91e7-2652abdb1c16

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 920503597 ≤ n < 920683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 920504847 1250 920503597 920503613
    0xf0411040212040506011703090310020a090b2704020c1506031509160b07051b150a0e01080c130e060102160b030406060b04080316080c0d0e120d0813 66
    0x50422100702e0761603041c001404004985a0305070745915011110800e281003103c0d03034910598008641552040852824040c00c40d800f4090142052170326541e0701c4e955030074010b80e9030424506400700d00c507a050326107100310503600b4503185c05100740c0d400d608200d20442c41c19100d036242c0f0021340911800074000b070000d540a00c01c0ea00039040b66620b0206c1070420700315040c1e44042d104400c0404011000c00072803500c82cae04007511001030340a0010b2074201292038682d940080380490b601d17000707111940c03400d01071480c54025103111045580c519610a5132039000508240d4090f0144200a404004010f00d50540481017401d40e40042c8018070702d500e40c500100d00e4490590107a0030001e840101c007042c610300d00b00065002d240120700500bc0a9141c1c0e2082403075200c3d900c1200e03801e500c01c2000d13102804a50070030128440c012018241010100c224440c00c00c8420440040018800f000c5001140341c03914006e4040c503440002000700c103000c0303d00500355100191100340050141600724081003070726 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 920506097 1250 920504847 920504857
    0x20105161b080105061305060a060f120e0c010221091c020a12060e03040f060f031401060504080709050402010c02120109081b01140c0f07052803020607080f04110402 73
    0x4404901d048680c0c074000300f4000c00e0152051845440000c100059410150181500504009007070218007480c003841a101860b1041500b4140800f507980c400807051f0511404404c8100c81014001c104502e0000a0034008a0044115045a200351494030040980c0a541c2d02c04d405950380c894040034007182c0b0b601c0b05900b050003940181c0744007022038020703060320420440e0b03071190b6028860390f800c44140d02d4036801140100101d00030180010001d040c40341c032200d00c80603482d050004111000c0581400c02d000300b60840e001280300014100b11902c0300b044200005c01c00300750f0030003007401c1c60740c0000c208100000d006807207400c6024000d500384400798428408164032509840c3d40e800a061a185800c03558241140c0e254030340340c00008000060750707195218031300483c2886d01e003215101d809090782d082950140e0706032003410990503440515815410245840d00720020100105107002464460020f0000040001c5902802500b1101d132035180d070016481a0513403200c0c080342010500078015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 920507347 1250 920506097 920506133
    0x14060f160e0a081e1207020d02011422050307060309080a031d0703030c0212011407031a09010b03161805010c0206160615060e180a110a02061e0402010516 68
    0x1c000201180a2042c2d9140c103075070603040150b80c5507040c0040c0d15085e0f401540c002942003001c40030307908015071081c0302d4455001c124114541c02c0c95032000c00e01400c0700e00004447d45601102c0f1040c070692034100944c900404442c0b800740000511035803441d006000c0c80844070705160326000c95204001101000803450f185800480d0b0405030f903401d00900039004400183e0280544400b0058000750601801140c0c0c800f41d0660f00780c58560300da04600520036104006601c030040c0000304c4446d510300810741d000385039900e02e840d201e081801c0c440c44091341c071a0305041800310642e006250108400303210400c48809091030340c0c0a0780a400801c600d403180081c20481500c200001c0030401c041944864443c01c009a0626030341038a03603506650b41c44d1814040b5621034414048c9038490040e00f01a25409a5a0743d804a441d070800b002d202035542106030500003503001001042081005031021180c46000303d81c440348a81041d0700068428415280801095902c0000802c2400040c4002c440b09104c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 920508597 1250 920507347 920507353
    0x604060b04050a0b0105070f03110f0c100215010b090a15080907090c02072303070605191812110306010f030303060518010b1b010914060f160e0a08 65
    0x14051a0000040c021280840e00c254035000110b2007000c994410030703c01030f00685566281101c161900071140002c3c03130040b4100a0622405940900284003509803007007880010b25902d130031201006054118207904100f103510102c120041408a0b601e5241182e0031061900c2c2d560301400c0c04165a0b1545400800c40d0a07003e000c558140c55010581601c40c40704c07602980c9610307490342c5200041c0c519007144040141d1100400303005080b0580c001d07409000315074455103071154220001c2428008513601c07402c0800c5011428186880030407803640304040161915034543c1d502c0c4007403aa841e2500780141d244a100b412109000c00c4020015011f1045008040342c03941d41e500c0e440c00401d5980c42c00b040f40024100000001d490909410032491302d440740d02501c00c80d0b800d01c40c592020380c106411020032620058555000683d0038400c559195000350103419a20461440e0240f4100f4058410300c0140ca41d10208608400c06c0743c54103260111520f44010740305400c0000600d0401c01d50002c90a1740 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 920509847 1250 920508597 920508601
    0x15031c11061e07034206050901120606080106050c01142a03011202060a0512010e0411031902101709010518060c07020103050402040f0f090201021b1e03070806 70
    0x990039003180703010884164200c031034543c0c854008030151141c0b00e41070240010301c00c0c3d540c00025050300e016a0343d2881000b00f810b49442400c0b18005501855020310041440000c14114a50303022400e030034855140032092140a161440050800b48144a040c2c200403001c00c0c0d00c1c2d0050000e4221740940c407009040e0391200d08100c2d180c06244074003030040410411000b10404201081442628100e40c1007010b505030352003864090001ea43c1c00000220200102000619007250752480307558082c203c00741c402c081515040c038118901c80a4081000d02c00d500010420b012010001c6052010315415122101c03501a04142918650b81c94160110416180410031445000c15070219100b40125580d0300035504401d40840d4940c00c0590b40c41d100e400042100070095402038000d1034100e031002c0c20004080707141110000403550582010700c640c40e01c03084d40200390741c0e0402100c421a07000c122085c4511070311a00290b0780c1c072006407143d0001c8000c0300c0036048650b000e01041004003902400d540880c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 920511097 1250 920509847 920509861
    0x708130810050f07020a0302070e1f08030a02101103280204140906011701032d05010207050709050114120a02060a080f160512090703150606030515031c1106 69
    0x582412a43d00396140e40010024100501c0019803250240e05500070b80546400c01440404d8540000d00611000501100d42c404101c5117445e500006d08581e0050754440a08071002070030461064403140b2102d0404011880c00c4806100700da40040c00301001140c5142c088414000450b2100075203c3d025101081c000340c1c0030480300c0001c080c960200ca0a0310a50f4448005491500d00c1000b00341c5088504401403002440300c5886040d200c03900402c51508401f1092601c0c505030302d8241c1110540d40200d40c0d9401c0103420803420740a402c886170700384803035810100f02403d400c110001c060701c11803010070700c01c82444d028400c011005030054845603464440007806418120203442d43c06201644500289071502d522040200c84a01952480d00e1b10720b1845620903081c0f0042c0030080107006d90100000000c0d005070083c030042e0100180031918515000c03000d407c803070008200c1100851560507000c600d5401241c05516100303841440405080c2c000012a4840f01c6c6207600d1016202d46400c0c1f0201c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 920512347 1250 920511097 920511101
    0x10e0d0f030f060b071202030409110c100b1003020a0306030f0b0603060c090d0803070e0d060f060e0103050309151308030d05010b0a0e1c060f0608071a0708130810 72
    0xc82040c1d1000e100c800c0300c1d140301004440042c4210031103d0014440c0f500000d10703002c1c4000800d0000d00c1100d0500340c031418180304a500e120b4407aa0101c500160750440070800744081544403004200070000404008049040074030580c1d0040c3c1010f41c00a0b0328030006009510100c040d5803c03a180c5041c4c0c00d01031038422040b2800b03a5803980320713124040c0000c11104042003280d4140a02402804510025994145040c3c1011340030000f4000301c8102c08155480e044440d54409020740d00201d0f10000c440b0708101143c40700d4106216000c4884014004a1070010842c0c00e41300041d642410f044500c3d42d80c030040b130700a0058816240e007441c04e0000d911381e000009041c01024440d000c1015980c0c565006003144250200354010a13501521a00d4a04d40391b24009641d0070f8000c1c1e0400c020115075503107021074038000d141200d4039540c2e102c24000c400d420401c071400741c030800c142c0e1054040040c40b0140503015690b40284801800949101d24102074035081004203108800c079041000704840543c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 920513597 1250 920512347 920512367
    0x909070f0c03080901112d0a0212070c0e04201e100302041203020c0102010b010f0e0405090f01150801050601090b0d0507090b07050a2a030227101a03010605040603090203010e0d 78
    0x120461f2a48140d1a800e0304c4001c41d04035000f540c00070581d06410001603485904414001d60b440002404001074404610012030b1089116015042d0500301001800652051598815020b0000004c481140c1e0082d0400100806012640c2203040b248083c000c802920841e000f0900002101212004054000030150000b440c240c0092044180304c400454018448410990001c0d154694045403414650700c0685c000d012581038400034210f000340c1c13030f00307440052040c80880406800208985d600038410560084024038200000518006800000b8041d150070030315095a40d20114255034041e2441c0d0740186401c010740b40c0c40f000c071030074825181c0d01551000c0d2031812214400e402225008450554594140e10401160a0941c0c080c400c03c440304200b000b0306d5152499000e118140008011442515601e1107855920b04114000c80c160000a0500e09217600900050000a42081c143c505940311441c002a24440500009003d4401e003072142000d1300558540e1015640d0040b1540 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 920514847 1250 920513597 920513647
    0x70612021b0f121306030218060406050414030a030c022806050406030b0a0f12020409020a08161202011707171f080a05030a0c03110f030909070f0c0308090111 70
    0x246008543c44000c1e456120b03420288150000c1010b040c8540d6000e68050468154101d240c01c14000041003c10b403c0d40c02a00a100400c1d004241004450780400d0703e00da901209801074002d40b00c06503809481c0c040001c5000388983c071020182c195000381d11080c44002140c902c400101d25a0754040038110394031a00070280040d052030384007803039820300541d11811564140559182140b9008900c0040c0101a1040b41d0003611410b02c440942e49101c840009000e052015040700c512028016a480038154050210b07190400d0151000d070307820101c50310203650300318140e0b140c0b613440003011500452040c044005581d402407e1101000001483c0440d8044044542006544540c00c050b41c5081c1208020036075413040103e410f0b214403c51480c0b60781c500c2410410501040c001469050184902c8440e601d9400841e0622040c6003643c1e1054202c600c03802c101000ca203401c0380041c41802102005800c2c0304c000004690340103170035486000e80b00c0c40c00294640340c41c3c142c04140d101c02545400c20f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 920516097 1250 920514847 920514853
    0x1b06030f050f040c06080702010f0207080c0705180c03070e03011e0b06120a0f0b0a08010c0201050a020f030420100c0c0801061d0a110705010203040b010803040503070612021b0f 78
    0x200441c0034071440d0340c040d540045132016160301c0c2c0113088841c00c8008018002310354a506c0854481c0d40c80d8009080e05611440b1040d171240171415207140b07081020fa211307510440b00d841280002c010990012a0001250b40c016130742c0703644030304058422007914540960158600701c0719424038008810091145221700b001032089903928410080d039400703102045803d022200700424403060040e0f0003034070b440d001d50700c010418003c40800608003035411ba000c80d002d82d4450590401d00c590a200312903010440703842c00c60809401402118403030100401c010300030058a06194a951054084a442104020003a04400d600440c1c020654102c0240440e030322010307014003113018007041c0030b03410503200d1a0000801b1440212a80c0b0004c510240c001c419403952844407140107003610780242043c600440015030740303041c540f4010031811f405a104e1525508280002d00c02558082016030842c1e120746050314000300c03400c00760b20091242401c010341500040b00380450b515400300f05a101c0c40100f10507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 920517347 1250 920516097 920516101
    0x90711060106050306060a08100503160812040321090f08010213080a03020a0b041103011a030c030f100f0e1e0d0521041515090b0316050d1b06030f05 66
    0x105840e51300058859552002042c01241c480c7d5200d015001d6220850032509403508c0e076038401080c24100d1094103148080310002061040724030802034081d030344584060036481c0c2803446d11400e01e4882c0c6150b1829104d0001c001e07900d075051061210380c014003000d120140d000782c1e541c42d42038001d6200300c0e6151454070b01580c000440340030104881030400d80640141c00044030554442c44250ba0040c421203840300d040c3c01d8507038940c80c00d1107420780c2c81c2510b0103280419444042014a01400700208a201368400340403280316440200710b00700380c500d40400204442c1e80c40180e49010b07112000307546880d845203611400320043c20b8000300400c0e10341201036074142036441c0c0c0101c0b058401d400b4034815410084d01d5140d9020280484164004d004201e8980e9500c407040c4588261051039454a07107850040005010150715482048039114007100104090408200c0f00b000041d030600c0b41c03600c600c80c2090ba00c0148070150348446111005800f07590155030325140c0107001404414410800341e490100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 920518597 1250 920517347 920517359
    0x9040e0309030d090f26060408040906121a070507050123010f0f050d140d08070818070b0705071d04060f1812031d06010816150c0305090907110601 65
    0x81301105940c140365100301058240f102c00c4518206043c008071034040422181d6840300380600c52107004520504515694130300c0e10b2403840540e8026001034a1080400e000500002c241c140710154010710b032015009a55039421003524503000e0580083e00e15402c02e030031014840703240741888920a102d00c00d0020584d0720740f549041c449542c0e0242800a070f11900c010310a031724080c100e0014082c4a64425540400c00c010380ca4280b000c440001e502003440c00003880902a00000039075444103450394820a00502c1d00c8034541c0c0c500c040e00c01c1400610f800500d40c0103001080c0854406800d89100c2580354900d00b40d42414030a50480d0300307680d06071501d95907040010003406040b51081a1041d540c2d40c480e11500e840c0045103071401d080c01450340d135a20000c80c3d900d9203041200d004038010b01070301140d850300c01042d0a1211800d18107100c0200900e01344500c000c04a110020107500b80b4080c00704282c0c0d03150942c0e2600c21340c52040c0d4005038090410001c168400148042414141c041d00d1b11641d90310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 920519847 1250 920518597 920518607
    0x3040c09150618031a0901050a0209030a02040e0c06070c090b04020f040501030b22020a03050c250614100302040c020f0c1203070c14010f180e0c09040e0309030d 71
    0x52500c0104148180d04200b502c1c401c11940c803014800c855400e20b00d594039916142e52a04160f600c1d03210010f002d0400959102c01c0c0b03e0554407080c071000551620b0b00071400281c40301d501d8040244915526110516900c0c42089500007481025100e01e59a010300d04020584555038031424041900b07081070108281014000c0c1c50000e401010078038113040c1000010b5001c0c15201e007065401400800e984041e96425802c0034181e41d03805040140d5a000c198001416034a00501000c2d04010411035920045100515003044400c03804550540e0034003890311030068013055141d54a10b030103207010f01082d0038a66020070200c0c1c0c402c640403c04852148000ea80b03e03494003410700c031150045510440c140c280003810005600c009000d03245058151f941d01100c604c400d801011581889100c280030650304007041f00490003042c00c106c642d982d144d0b02c01001d546943d0248803100302c000d10100f101032511074251004024020b20a11040202c0a89650749030440b8002900c2131040d0104459828061 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 920521097 1250 920519847 920519861
    0x30b1605040603020c0f0a14010c09120807020114030a0b1002010507080705030604090f05010b0f090408030103060906090f051f0b06031618140a0b19030f2003040c09 73
    0x40d449907424180781c20025002500b0641401d926401003a4940003400404e0004214440c40b070842d40c45052591a01d46003101d03401c2d50000184041d40c0002d0100d50120015034054650103280340ba030b294807910040784d03100203508103803043c4540071051013003001c45504801c058420960309440200da40e040304901365007003030f1040d001260050b004a4400740c41080115400500900701080c02d5505a50f0b00350a450b01d001c1c00c0d92203035036540e4100700c1890401945040040700321002002c604054550044e54441803200074610b55440c03842c0e0b02000b240d030300925201a0407110088400f411801d09540780c20151040561008000c1c5d00391003101014828007548000241550341141e8030031081c020841d0b5100180c5040c001e4020300d61511030340d40e007604005002082c0c4030f2660810600309100e040ca00ca43c000c80c548000038482c1c1e10250141d0340c2c54500410712440c0226030b0000c86040307900201059002400c91f46e141e9090817143ca18107a0085006501c17404000c0c200301d541c0c4800703100b11120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 920522347 1250 920521097 920521141
    0x1c0212090301111b21070f05030f0a080f1e0c07110d050604060b040203161404150c03020d0207060e0603061807030b0117070203040501140409021c0c020d0509040e030f0c07030b 78
    0x10300000001c00e50303100c1f409a1042c42002243d1512044207041915074101109100002d806c1c1301c204904a07640c40802d0350856051401802204d1700c01c00c40350402d0100521241e2101400304940b4180a40682c00801035a000340200000080b281429070b11000101d50944540703003407031144003613800c151084070310070b286c2039001d041c5150311410102c2c1d184028080301034000000b41b00200c1c03c1c1c0d5054001d41e03074450213074641c112805941d18029003000c0d0080c44070002e5400000007040b4140d0010000214080211880d40e070b0380d550300c0c00043d01070f42c0c0c2311101c151400721001000a400d40542c0b00568050090300c031071131403250948140e000b4000841380b0800613041440308200340d502039000c00c00040c4005102d142082c0d207828510040341c00c81c0030500d8810310070b0b045240c400180741c402c0710318808031840034004150300e419020300103204007180c0340d000750740e990502803044801303100703a07a0b5040304d28032242e41d00e030603034121680c1d00c030103e0000303941c170644070400729082205440603201c0c44c0e09 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 920523597 1250 920522347 920522413
    0x109200306060d020c0105090a170f0a140c07080303190e0d0807051215040e0115140607061a031501120b040201090b070609051c0212090301111b 64
    0x81d61005110a0b0b40140c810705015a4007031061004001081c02840d01c500b1401e0001c00d18844203042c084200309a800940c2d0a03071000300005582402050210303038070070b00d10381800c494486001d20030814074071402c0072260060007442e2010610180210081d8041ea00e90902040c1c000401e081c1c43e03040301c0c400345100c10f40c0d901541c0920010b0b4000c4c003045038820b00c60b08005013000075582c1c070702120010072240701c0b501107071441e403010031803425100d00351320b42210030020001c4501c0e004d00040e00510740e01070602030a107084072070310a0780d844030200d0707880c0d41c0d11a41c10302c00c80034480c1060307007554034428400d0310a0089a1484840c1030078140e0440c101d82c0740001100c0400800c1e143c500210030041d105904010301c880c40454400c0c078600044c0703043e5200c7c1d100083c03c1c400301d007070050408c0c0648100c600f1541c80c19580260242d40010582c00d410122941c0c5966450b40000080c0100001066068030302c00100c2e40c001035041c0038005403400d000c0e09040c2c0342c11141201c1c804034407179604065120310784 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 920524847 1250 920523597 920523601
    0x206130602070b04062703080408062d0403120e0d05090f01031814010207080a0f08010816052815090b04050a0902181903060b0307240c08040e01092003 67
    0x400074a42c03080c06440b14051006d40d10b43c07607813a0758195030b0040c2c2080d0038581c840b0090024964000c09140740d023540500c4051900381c8a01050740100101410250030080071880c1c50381d4081d41e40c0d00c02c0b295986001c003100c0c0100040300d17016080780c20900700c1907c104550014182c45500a0040d4080230400a5144204120ba82d55100c0e4200f460320300c80b540b82d9801e10801e40000d4007040203200380030141e1a140100300d252000203000e03000581060f04039410000030280d0016a501d12201a1a400c43e84940421a01c0c141c0171101c01c0030003050700040e005030000081c8541420001a022440d1b641c6500c1030640780c0c2030f401820301c01e6200b45500042110803c11111200b030f40130b040c074251901031841c421880100003850b003900745c000000741c1000405040040100e2232048035100740083c0c000e0301740545049001d4002c41d42150070140d8002036005100c090318850201140f05036802590031f80c0350b603200c02ca4a43c1e00340d401d000307080480303140c503910420030090f109844810418648002c0d05d5030f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 920526097 1250 920524847 920524877
    0x509090c060a020a05060c030402040b031605060912150108060f060f040c0203092d0a15080709120f060b09240607060629030c0717070206130602070b0406 68
    0x142c0d10840914045002d003e00000002e003050040b54019512507000c2c0392a03041c940100812200d0300a25240701340d10001151083d9802d4290750790031204116403254a03006001e020915403101e83c203008000e8059030481d01030f03c4040030307400d6060740c0345803040390010750b100341c02100d00060503a103107588440701c401c81c0207151415800900700d14001c3c0c41076900785550180814001c500000c0c00c0b547c844140c410302001308103d00003200c0c040b1000c444c860411031400c0049002c40c071000d1020b9003001441e43c005903213140184c0c1a5001400e030b98031400310703940441c01d0a144440015804541e0b0740d0074149000c0300307403400482c8079020303041c8840c4890810131018921505041000c18058000d04184441c101050240c402c0a0092681c5078000d8180c158000e0900d821494800000005c40b0007441803040d56800c22041d100b969522030050400d10140014881542c0980000258006800030f105214030759010a18000c4580301d03001c403103200d605c540c02500c2034080e9006400006a00030352215070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 920527347 1250 920526097 920526109
    0x10b0108221401021204060c0318080c0307050304080a200303160c05030f010e010c180306090203030f0a03091205031306020d020408011d0c041407030c030b06130303090509090c 78
    0x2910990030382c075050100180880c266000144007401584c4203a0401c0180003640c0541c200c0601645002c00c0035401201c001c0206011107500a81862808179100c1d414040030001c8441c0c2070b41040849072560f9841c28800da894500c07000803140b9590145008908064440b0000881a0014041c60800c0d6281d019100c00344080041910741031240d001c0002c9a440a000c00c10b5441020303800401c0d1170a510340c01500f581d4202a80c04100108103084401403099404100c080d29880303580400c0e4240c40c2c1c00000d156018a1200c43d441e800001588a0300c0340d0942e00c0481c1d4148600c03070046120500d180280c0e454001240d90540300b82011b1130f9040000c002c6c0c0d005004082d0018401802c0a44424903603003181c200002000000a42c2203c000d07d01c2e030104116524448112800d0191000c84d0000e099002070103054030051545441c640941c1030701070380210001d00740140090380c40c3d44000361509807048040c8001d802142202902244901303104d140c680c07050050b8001004040c2064080c015 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 920528597 1250 920527347 920527411
    0x204090203010605101101150621020708030f0f0f040203030f16080c03031909150911180a0e0f07060804030908030f03100b0a021b060d02030a0501030302010b0108 72
    0xa07155503103400c08600e0350381d15000702e40506403598680e20100c014680283c00c4610034205075100c000c0c010f06c100042540069005c82c8080544040954400350380006e4000e801208401004080e010080086800c80040303040c3c410310304149024696281d020a600d1409000d69010390141c2040010043c4108039030000c0103801260303410b40c40605004d841fa814141c1107084107400780c0d003000080c88a00c18402808000c0c5c50124a800c01401c0b56545e220788014010391042c115458481e807104041c0110754104130068007001e00200da1201c1001a1040d016208880c280602c40c42c08401d40c1e0400c0002070030024811101006042003420a04151590300c1c00030f00440801814000114041d0000d10260200c140e501d000c0503100e0500704803940d1081d407a5040394090b0074062085a204580c0040c00300140400e0202d0000c0c010b030114042450380c81082d054004850002042c0880c12085038080307812640a58000c001c800703026001124042d00548568911844c1d106030403060600c6040242 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 920529847 1250 920528597 920528599
    0xe071a090a080a061d0c040504032f060a1514030102041203080105090115321305040522060c0315090c0207052b0c1a0a1107050d02040902 61
    0xd0621900c0c2002400e030034619040a41c141c1c100860700000c10880340114003403c0c0c0108000c40c07004c401d03050703a90342d00c2004000640c400c1b41c41d0404a01032501603801000c031002c0401030360805001c1c528103001d00b1040501984864414000040c442c28071901c182c450250030603d000001600d081c1280c158503440d1014590b05540c02c0100240d141c401c18a03856016100381c072005040e614220400c074480205a125040c0905400e42010743c2030f511103031001d6482210300444044525100303400c04103a0041d40250000305d0700040d10441490000c503500101c4000b1030703062055580300c00b0140c00c0c0040b140143c29001c00806840300004041d504a000b4003c0c0750700d00010b600c0007104010781c100503940c3c01120250b980f100e203400304070b47c14400f541c0504001d4800540562019003103512800d00146502414508060f07000100300901800310018145c0600100941609400d0700c03406a000d070398004040346150321300082040b000700301541101c0e0700800d405015515a0240405844d42103402c0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 920531097 1250 920529847 920529899
    0x20409060236030d0e010c0323071401020a140315040f060302010f08090c01140904060f0e01060e0d11040e0a12030e03041a280216090e07 61
    0x6401c009407102c4107250007542c050058090001c0300d5502032080e41090019009400418100d1046600308800c0c49003880280381000c80400c185c00e0803510204544c00680c407001c1c10040c0c00c070890468030040c1c138503180038034004074100051b490098204d1140c41203040c04101941d0002d40d103506d51501842d4030101264001c188101d004d0000b4040b103410a0791015510b039518414800d659011084040404450500c520141071400303080c0e40d26190103141c3c504111107150301e036620045082c19143c2d0310300f01610070301c0301640721250b14440b81c04030f02400014042c454000545103204103840c005601d0050080c2c141078910740c95503411001d02992691f00561103000d41000198204014041c103401004102c08041c40340c240101600c1e003803600d020070b551060005001402c2c0d00621020f200400d801c100b0342e140300d01940c15000c000d852400d908403841d4000402c0602c1d4002c214812000c003007022100030b6640340c100314002c03210400c83d1020154801030052001064205040c462200e90b001c81c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 920532347 1250 920531097 920531107
    0x170106200f031e0304031d0a090905030315101e0306030f03080f0106210e0a23060f0403081605090406090609050901110307050d1805030702030f010e0a0204090602 72
    0x10151801500030340703100041c1d00008000c0600d00100300748102c082c2541c03105900c1c5040944000307140c405660446541d80c4107564114003682c0d6961082c00c001c00401005001402403420041c0e01c0307410450301903100003600b9404140e14078004080c20700c085501d84031a0300c4526180941d50805800e094030b18249a51040007101007480441083d150611a81d5640c1c0c0610301030a8062800300117900903018040c0006a1492210030701500c1400b41509000001d01320f20003105082c5010001680505205c810200755201210516403440c0c00c0c0c1408021039441c5e440b01100d20740085c4007214081d00007440f28022615030050f03810004000811031400e00e0808078042c00003001c440442c0e1003016050355407103041111036540e0050b10b60206011000b000b41030840d0719036000c14440103042c1400c111000a030800168241d500080403c992018004041c075410311b8100d0f80d070360046070268413a00c00c070300142c0e03c01c2a050043c8101130f0f640e040a080240f10755070a210181035610002c4a2254086c04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 920533597 1250 920532347 920532407
    0x13020405040606083306030c0d0609020c190203070b03040f060c02120403060c180611120a020c01081801020412050115050102071503020705060f06010909020301050a0e0a0f1d0c01170106 82
    0x386005130b00340c440c81940c0e40c1101c049d04e03003102d485500001c0d4260040c04945c14a40c404207050f0b0a5159030784ca0601c0308680d43c80060b0070130341b00703810100d070004000c0140424000c40d140103485040c0b007820200004103180c041a40c0d100b484000d104141441080705000207040ca4002410a1a080c02c1c240391079401c40008501c0041960015400184450f4410b54030302400c006030f9a01466880e00b0074a03140e00307000c00071b4465803000d02c1c2a062020450108000303806000c034510300160030394000c544854448041600d01491840b0517141036003003409440402c0c00c2080c0460450381d058004020031440c05805104041000d8180740074540c1c01c2c00500c0105000b804058810046a21103a0380f41c9000b40000d01800c41e9900141010fa10600c014045034440c8080e020545120614825070b9130350340b4082402800c00e41c01c151400505110408981c0050000e84d000515405010707a6141c501001c011030345d0011481c4c1e1411001c10030401045400c1c00f489014038441c00206170b5602c0030300e0001d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 920534847 1250 920533597 920533609
    0xa020a0b0405031908061305060d0507150f1d120325120c050d032711130903020a1b0e070f0305070905030615010e130204050406060833 60
    0xe8090ba815040081c40c180c0100307260740500e00302c801d141008213440c14504041001100321400f091403055607240410034540d95a40b0b001c2d64294030808840c02c4035215007020030345a20900c103000119001d58035401006000e450030100100032100a2a00c1000c0601009a00c64030102504614001000000081d0300490912090004803402182040c4c0c198580100f07010b1036004010104801180103100250b4049040d511854262802007492200798440644d24019004001d400402d100342c0c241c10030020044401c0c5140342280c48a1103912007802c61015151800c0006006810180c51400054422440c025480c0310b800210f0041d240c48050f501e115031000d8846601040b403440c0305220156045c0a000d51052079440d0582e2040d1a141c04655544001b411400306505514401a85a441110044d600250090071010307928503a403d101c0095000c3c2c00380c0c8d4000e50810801084d058014031001740200c2428451425003601400712400381c58850003402034040d8507075040480d5079164 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 920536097 1250 920534847 920534851
    0x111250305040b1809070c03270905012d0f0902180607140634210e070e0c030c0f070203070303030509240703020a090b030103060b12030405150a020a0b 67
    0x940001213221300f03150401144280041803041046a40814080043e500000e985601d0000c0f00c02517205010884020b00705421036009901d450340740030700001e2030b0620303100c1c030f05c07148100c10314400750080100d0000d008c07843c1c443c0204800c80300348000420492550b0341c0280006444601c201d001e1600c03000001c0e08562102a05039494010001c0c034039000c2c0d100b4410701c3c0e005149600301e00e01c072110035000000b040f80320301418903034003d031528010080c5019040c0880b0745001110021701100102e10082c000b81103c0c41c040e181881485030114844240e08180e5002d014200641803c40c0d490040d649040c0d449a1840c1121003405c5c403032040140c404206c86009580f003500d01003403074035110004a2078070002494050701d62620b10441d40c10703c68a103480079080142c61030056501d05030090140d4500c03500754810400c201000000005004403035200c201441000c68806c1c0440d03041132000c0340e40c1c0c095401000e501075041c0781e00e1800007082a005120042140c0142c0717612030480e495048500c641 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 920537347 1250 920536097 920536117
    0x21c1103070507030203060a020702030a03120b090a0c26010b0306010507050303090d030e03120103061113140a061409040f0b040f091106040806040b0601020f1e0111250305040b 78
    0x4411011301c21480d00344403403944825441000c41c1801042e0700000e507078140030940030703007132012003a0141031030000758100b500071f654050f1582d8914108044440001d00c84541c030280054075240880e000e100500184514681943c07100b401142d003000c40c6d29405070f10241095050150402595000680600140d889104c446000c2c12031091a07100241c29a0850030004101d60020803d00141a47d0006001d05403600048002450180094140264440c02c414440e00319078900000400101d00001100341e200140ca00b004010350702d800a40d1944070030351700402c2080d0213100c00e4103141000c0d0721070303e906800511702281702d000746000700d4115003003210620300766030301c1d140342c101808051003809400b54815100f0f81d10f03052421200039103965000d4001000307616044045805a8400c01030556105120341c2a10300540c0200c03922a104060300d0340c0d1402e40c0d4240550203d05840c0310381075a0f248201d480808080007a54644900c020082c40c4048045c00300904c8003140c101c0100c4058042c07000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 920538597 1250 920537347 920537353
    0x20a030501020a1b0203031804060b04092c0a30080412051c0e0c0a06020f0106060309110409060f06090f0b040507200a0206030c030403110d021c11030705 68
    0x540c80100130141407821061603d904011031410005071800812990030782c1441d9035010b819004080010702a0000e036201854422020401061000186e40465113a64031360216184480080c150f061000349440c040c102150440b5015a004c40c081000240c441320b024171150750880078407200203049041c079490b00400500d2010400c0100310f02d2032403400d58501c050030018181101c008008070b2a41241c030003244203d4840c13034030500166003040016001000106102441900d4000080d542d51074849001c12030360a0100020318140a03218403848540c022581e00d80c9102d11200f0f02c8060b29002004466840c1c0d0703a050791109850703910500000c0c1c0f0460402040a80f01d40541c5026281d44280703141c8118034000500410a81000038041076080225041700c903081980019420440d6400c000380d0003d00000400c108040b14400651085210303442e43d1144c14101540c495071220326110070405644139010340840f940007060304480404240c0303042211109003108050940d04514011580e543c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 920539847 1250 920538597 920538607
    0x20c010207030e12010510170307051005040b0a09080f1c060b030108390a030b070c02090c090f091f12050601060c0809010302030a1d060f01120c170307020a03050102 73
    0xb103401d0601074204c03001c0340000d00c150b0134041c0c6810031104080c401ca0b100c4410300d00d0592900d25082c410740381195000000e0b540590030302035100000d400308650403030320000d800e40051503010040c42a00111504540014104158160407450075400420404421502824041241160b60140070050300880d60907076103d5140400441c58524010849003e8091a4500c41407130001307060102d01c658141070ba40032491503070101140c03104809400141802c80c03054104900c0a4000008080c00fa1007615040c69950b60b01b4030016041c040d101c55694010401c100b441d0241c5050801c2c3d90700890341781e04016503207640840000010000d584820076080c61542c6407418094140b264900500b000c1c20850003c0035540d8407040320f4400c0c055214145a4040301151000202d584080303209840d8194090122020040750390761503070700f01e403401420982a800400d0501940c0304031060a82d01c1030310110810b0034402d00d0000c0e224110754038030040c0702c14490000513075180d01d10f1000460040b400140c0d0f032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 920541097 1250 920539847 920539849
    0x31e060e1507030b031903030219030203010f050904020f010e0406051c05010c180b180d0311011116080304060f02070f05060c0412140c0324152101020c010207030e 72
    0x1c5180103280c041894508903c16040c1d440100c1c8881e00c41c1100c10807256200e20600e000e07002801041a055180c1401c16200000c55405500941c181c505038000000c0750765a076010000300c10750407113000750071002c180c0010302e2030f50145071400c0d26880c0c011f01c04030707000d511140841c0c2c4a003100c0500e6224407032424015030a2080c00c3c403d0711301420982ca00762074000c16200c50f01d20404054410308043c4140003501d00460f04003880c444500c1c0c41c7c0105119049226402c00030115408440c1030b039699403030920202098043c4000f26055035402d02c507a02128001030322000c1e680e400080c4192901903d901d880c80d9018510f200904a15100d06000811214242012468207a00524074900c074901000281b01740500916880d110540c030004480458212420050820380005003843c0c040c0700e00801240020707004038a030502064144443c132100c0d55419140c0e0f450f0504814902d0704101d00c10a00081e20701c00c903d40c13241040340500090f1410950b16011800c9a02c00300c4183e0018850740161105 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 920542347 1250 920541097 920541133
    0xc050a0212010b041107020105070f1511280206070c0303061a1306210506010c0c0f140102010b1c05070f12020a0801051e060d0f051b06070c031e060e 66
    0x5c1c4031601403006062010302d0380060000d109007500940b0340340c6442a24003c01c655004200e942045071142402806011845814280c0100d400b86602003909400410035020600c40c05d04c18031030399402404280c851500070f03200300c7e007a400c0c10303010140c5547e80801c00b840149641c1480c0d200c60155141c0c1e919401980152241168000740100581c1b0552a020262103400c01c0700810811307200080d461b26030344010783e248088490300908240d0901000560000045c1d504021182d6083c2d81e0108192200c004900703d0f5052aa111350040282039140c221030504080800362920407822a4003042e12551103024416041c0c1c40709113185141c040040c214100a001c03407001300441c0c4000e00403420321104014814807000398040729500d41030001245036a904180c111102d0b040354030841109090304180b911340000000401e61094120032480950410608643e0480c1e00805030800179800c41d0345290881c0d400020015103400410030300d50114000e4441c3c00c0702404000002c203811403000e220920707 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 920543597 1250 920542347 920542361
    0xd0807170c0a0e060304030f121d0f010b03150415060b07060b2409090c09300c030d08060a1503020307030b15090f1521060406150c050a0212010b04 65
    0x1010705030070302c180000641c002114080d09400345c03c1c001c04003500a00680300800c82c0540f20140407500c0e03150300302103d9000c22f640008101c040005c0c081b1012402c203169891100e4020300c89406100300014001c21111825000505c100342404102c00d40c4e26000404503070065502034590540c0d6400c0300c049441c02c2440d140342c2c81c0c500c180300c500ca032241c134079004040d0159030210342c0641110710010b150441c8050440b4260034008200081c296010349404d065000b4010110310250404030300705414150000300d00449401c000c00074076040c01171480803140480d003e04403c1e0000d031044000300d44400342c601650008847c5a40050312484c0ca110000c00307541d1945a00c6000305414a405030510b55903508407011080c050351691401e150400100d940d1001841c000d051032480815440451554a8000c241e01484600c400c0130f6510394034104012a501407060044200c2c0c40c402091160b4000c05002c80144d0048003566001541d5802094284039020160a22070755507051000742860144110070f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 920544847 1250 920543597 920543599
    0x40507090608160902091219060e0304210c05181e060f01030c02100204080f060a05072a020d0308061005120f041401090609230d0807170c0a0e 63
    0x60040d81050820000200780e015031004c80d40c00003042c04c00f9890700703000000ca1245030f00c200c45400b85001100342102d0302171541100c1e00c070700300705007410480380000c00d07282503c0c420180f0a520420032081d201201e4480c2e074080711101865074000601e85d0b00d1070765001c040903440f8031545851411b40c82600c4413800c00b04e03d948071044d0035801d12225494286040d00f01403000c0c2000a00c40c40c1c400016441d2542d803044404086000060200e074440010a14008110a110403a0110740301c84503844241c8404541000c001a00a176216030a48001942280c0d298070809414040344011380201d4000e03030181c03600350007080040007031016508240000005200301c0c0c1c43c1c07260410208480800d01d414006e005d0780b11a00c1110045020f001c1e804020b0740b0700b0440a8000c1001d0603a501c0d0020162000d040e081d0380c0c0030b000050050050100c80c40b44a03581c1014009415101d000c840300361090f01024004104006168010014403101d40303101d0380c0201158042d45803240e0b190513000386452514802e107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 920546097 1250 920544847 920544853
    0x6011b06050702061024051b070311190308031302180708310b1b0d0903080c040e24060d0504050d050424020309040204180e010c050711040e06040507090608 69
    0x2c044580c006c0f02e4a030001200d4a4420f41c4c0c0c41c4403022803101c0090b5401c0080300c50086500002c1003160025100720030180964019203078003102c3c01c40c1a240519172001510040c1d040000030541108918486100d6100038590102c1c4101d0020b0301c00c1081c8112800800300d01d0390360600082039904100a2030300103181c0041c1c56480c0c0741108000072030b440e82c0c0006082c002400302003400c2d00880c3c1d0110500a00c0d050645454800c460740d000060041c1340011340124003000c02240901200004603020b0394414040d500254403941c582c2285007881d11311841c2120502d29892403c0e45c0c4039030040014186c4c040006c90542881d00b412410701c4030703c00050041c44803c0100b04210765082c015498074480210080031440b884810581c114811100d000d41d02602c0040c0200d032071011424030700300780040f11000308401c6280d009214201d80516206502140080c041500000c403241846101240c0c0500041a000c0d05040031500c0c0900c144d8080302e480d0011001444018002e00c180e400501c1ca040003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 920547347 1250 920546097 920546129
    0x702030f0616120b0916030c090303090302060c10020310030201030b04090b01061404080a140c1504121109072a020f15070c090c2606011b060507020610 67
    0xd40c4411548482c0c80700d0900000c0741046000580c183d00010100c0400340c000b4809280c08011410815010310309840864a0314621034040f51003501032406682e1f050303c0704a8100d0842d02044082d41001c101c00045108451412220401c0c0b400a94006d1600b1043d10700d002e42148009010380e0744490350345001c2c501d881a80381c0030500c0301e1400c40c1110700c03038100f0181c2111041580e00c154800c60f08172011a01c1004d003208100310b4011341c0c0046080c411030503101141e03021030401038130341c1a0280c208640340b01880180070809806c5086984070b803090451074928a010000714856107022210500030441c00c1a0b107090b02400a4092910030004000d1200c0643c031641c00038541144604a150113842010461085170b00300c2001c541101d5001031106400c69030320854540a0039110082c0c100242040245088465400c1074511140543c44014103003540d90100465090308203407540c00c0c1c445601039400c000304645214903030140f1600e50103401f140c504081c6c040100b400c1d5610000c16903045175a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 920548597 1250 920547347 920547361
    0x91912090501031109090403141204170910050f0c15010e0c1c0f0b0402180a0504020403050718091722050303162a03050f03120703020a050d050403050702030f06 71
    0x8100d031807091701213403a078819817100d08040f540791250741d000001415000542c26001c813040020a4400c9102c0c41118541c03828403403080e0f405000d50851190800b044c0c0c8804101c413400740c40601665000384000508000c8186000352400003140c40c188916100700c0010701160201e01000c036488002c190302585060300300c50410030440240105020308903960740c081036080c00309802030003c842d002031003035440396540300078026a140a00c0b200b070b104214094000606007000d00a4031700b100c1d048005000801c0c50000b0b00d0040513601d05603d030f54640d959100a00280f00c9015000c0c91002e03d41c0c1c8507481c0d40195649010b80b09001140e4001d0040035801040184d600004541d800c1548010500c5454a98030b0320b444901c4400322172242a454889003d880300b1002c44031130301100c7c000ca0482d0260114149000d85038030924102c14207600713038600002c0d0294080e40040c40148000c0c60001d285c80d50304420101190400d660880000d2000103001d000e52800300040748441c0200301c090035150405607 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 920549847 1250 920548597 920548631
    0x60d11100503183d02030a15060f050a03050903070b01080708070504060b0a0c1106031509150109170a050616020d0e2812140d08040305040e09191209050103 69
    0x9055010074070444800c0c0c0b44c02c0500d0f082403058082e00940d16418201544405008680003403040e0b400300860004125220764814007200d50151142d41c9011300d070800440150100828940300c0740300811140d40040c04100d01035008128032070160507683e041c14111400c194460b440790b031066080c03000a0024160440481d040d0074100d040640d0441070303d03d08022016110080c0704d6200c8004003c0001c1011038289114811508640104030361b1303145100b03111040f020301c90990000c1e90325042030245034640c0c1419045400d00780100c80038013010782c5e0707420725044040700ca20714022450050b46500c2501080510349100d4281001c101542c045004101c1a90f2400307080400c144040b02d0241c45064603e8a05000c2c04221900c030301c901201d414621f09000c002d800654692140005198205100b07800041c000c0c0c1d496a207507031802d17181c103201c107041c02c0d000342c0040e00600400030b800c2588545868420b07017240c0700d0690001010500b03100540981003c0d4402030616003005100e00c248402c0c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 920551097 1250 920549847 920549893
    0x60108090a1a280b04060b0f1e0c0105011202150a0e0f010e19240e0609041805150703060810180c030b0613020403030503060d1110050318 61
    0x1066a5015520194008040d0703501a8101000c90510298020300400f5600090b031800c07816142841290b03502c4541441922034124500000401031164900e15031542c4c4100107a40c40324100c8a080c8145a803c040c2122400e0b4840110fa004940b002c0046040400b0302078280c0d6a1640000c1c00c00c0310040e80981402c0b4203041d0b5511a40304001048080c0c0c1c00b07882400700181c4080e1070300b1926041e017042d101098600340070392101c48441c1019007407001c1c1001400110845640d90359000c40d080e000a110041c1c004100903980b05480303210800340c10859000c6070000302c2c001d02c02042104a070303401c600c0b02c134840a407420081605140083c0310342400040c10810000070101c1c005000f07040c0340c031a820b802004040082440b503041c2800800d00195103501809500211480c2440e11010850701c0200e01c0380d80300c002e012a0003800099020b10701484804d290a001c0c00300001b8181c10710b00000e00c6c07034008003443e101080b00031051042c05801c8410307954240c4107040c01800d603581804440420341c084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 920552347 1250 920551097 920551133
    0x908032d04051917180405060f0303070609080d0e0c011d0d020111070312050a140304031704020a08030a0203120603060c160501061e030201080f1012061e05060108090a 74
    0x3400008410008204c408440414410312401d481d050544850425880c0c00303c14a44228140001704480349050740c0c002e8003040d0010b0003585015110f65618000d0102114165502041409030030341616a90089440180e481c001410301100440f0014020404003400a402d40400030340310000750725500c4403160415024280024102c0c11013141c24502000ca400081400074180044400d0540040103803032b01d82c3c0d41e510781002c000306150400c0070a000846001e80041d80c40602c9085144118105a41103130001c1c01100c00c1c0e0352941c007124a96440040c0310300060344001164551030000e4618150880380c21000390000d4204007400d200f075405002c6043c526050800410313810460254002e200400304010a0000ca2880108400190803103210503030118466200040b20fa0881e481d410344a20380051200d05058101345c401005912070350821521a0f940700c20b203015403500394410034651940c9440c00f007084e1800000042074038102030803028541d800030091200040e0049404020180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 920553597 1250 920552347 920552383
    0x81f0510211110030b150f0a11032214041e02030601200c130b090a020a0207050d150e0304080d0507030c12030912090503030702130908032d0405 64
    0x4074a0030440c401d020114081544000200141c503000c9805400c01c44030b030311301120007528001c6000101d000d44c1c0304518550050b41c504001b00c040c40d5010300c09504250b6410750840c3d060480d81c411198a0481070308100800000880c010003e1048003081c54004081c140c2d001d00140010b26015194041c00e04000c0c014190040000f58059102e034020960340790710303502aa00c41c4041041016280e01c4460041ea020320740382c035109000c400e0303140101d11102002401901c0035658507039850000b90040d490781030850180c00c400040594401d8000c1140d140a421803030700c86481c0704620002c0707607600c1d0144c950540091000f04480c1d9404510609600207a0030400e0f912625481d0031245032070030718001400c000740d40c4808483d10f5071607484900f16910881080120082209040d5000c00a5100d640d0b070542c41040a9001401c0c0384102510310460b00b440070500c02039565648500360001c9800c1607401c8059082d1200c401c800305640851904400540740303950405440700303a11030101c51300180f5009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 920554847 1250 920553597 920553659
    0x11030f03060d021c05150f0601301a030703050a0f060609051e01060206011202040e151320090c07030c0530040e010e0907081f0510 58
    0x2071910000300c0d02d9694000d09252003107a1440e04c413030707081101401c113031054482c1161817018841e0b00d890490098810b10300c01c90035a501c1c200115080000003e18151170760313000e24051030848d030800004055681220002c14050210158030308006101940e0038420392000034200040b802c04141c200c40146c0003e8500c2e803544c0b260030208003500f0075034400c000f6246071104001080e480c1030ba0f0507120b44050f004003070309641e0750320040340e880c0820300070a0300d605000f007101401403802e5403080600448207401d80d40d0040544800218103403040300c400407454800042c0b03100b044003912907020511510040c109021b102e84020445404005140030b80140f800102681410b020b02c0415050603404001c482a0000724030a0f008400301101c010307210180c0d07040c40302004441400544d02a02c0c1c061409501036882e12007452541c060260a078601402002e0004c14024001e0000b05170140d03003401c179801104022909501243c03c010070300b0728544800807091010314000701e0440450403041c44049540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 920556097 1250 920554847 920554849
    0xb03060607060e0d050307110a12030216020301050705090108010e0f0a09020f0a09020d230718080607021506030d1e200105070f180509041106030a0608010b0111030f0306 75
    0x20110981584168415a0740c44c0c404190701200540c07140c0c0700303607450760042d04414121980da144603210080015a448015084161081d409441040c080c154840019440d42d0040f9003192000c0c1d6180d070005000080041155800070703009801804458100310303007442d0160300350300b441b04042c1520b52119294151401556502d40904070303421401046940450b40c0c90010b0f1000b517000300a0300c2581814102a2240d070f0802a0031480901c2c90940f40201c29520366004403200803c284524848940c039880100e58410200002d521602843d002080d450f500b41d580e110310042c0050000d8440d9002c0c01200b194903510610070300100781d110b010030725030010740c1c1307030a03201c0d40c420074a4182c0c04006c0749242d4106810540199006241c90344030207420040250003110720041c0e1807141d501200c0743c2c05c41017100341003c0c0c0d04075601c540100306100040c00301c280020096407094900b8080951604010301660600707111b044042502400c0400c0b500c0441d5030101d40320301990800d00a03060b07001c03000841e6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 920557347 1250 920556097 920556101
    0x90e070c0605090705040b0d0f082109060a18150f0f0e0313080703030518030102040302090c07020f06030603120915070b0106030f14271c0206100b0306060706 70
    0x84541c0107400303002d82d181160300d89036105080c0c804c1a1050342042c003142c4584c00c00e006601c3c0b00319040351503540340305e1141c0c8560101c2d6100705001e62030980d440800704c0c4140007145280d402494004082c0c20f0030304015441c0015100e400f12495442100d8240f03520000d6560288010b2515034071201040203041909070344020b2010102c441c0503142010200313104480044000c16001d0480d07060460b0507034403040600d54618060000602246041100144045944090301a0940e006001504d01622540401c0900c6401c0d20411660b038004503100301185850440c402004409659180c29440e150700000d644e0108080c5800301c04600040600940d25034089284009a500306020754803461403034292000b06092181000080c41d000b25618400024011180700f00040055103156894180c81c0f44800030003d990140c400d0718010110201000c1441156080f007008494101100d45482019040c00c2c0010000c0c00040040d80081c414074080ea0306880d04441c041c0d4002d503e4010903d00200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 920558597 1250 920557347 920557367
    0x5010b0306090c190803040b0c01090c141309031b05010908040e10060e060f18130501080c09090613050f0f2b0806040b0409080706020301051906090e07 67
    0x34050003a40204428070b08001200110700005a8510f0804d40d01e02e03207941007450359400307110740980003000100300d1251418042c000a1341031303500005540600b50740e0400030703044560010f010b582078036680510a103081303901501c2c802d05290041c0140d0102e540c0c01001041080c1405e442c00109400d41000e0210175800400c1c0180d001142c141e80b00c5e00e95040e448690b204541c1e20800501c040c0d004a980d03480b45201800c002c002401107400d000380ca10b64501d0036004400101c41c503415140031003425644040a0702004000100300241950600da03040b420700030104801d0780111162802d0000d0b0b0b400c000b50241e07012220501d000c0815041d07203800d07420185400c5502d165071180ea00000200d100220310002c07400c5d030501c15503005618940f98001240042031400d400304008030005015400d058200154040c00100f002400d81c95954450f01c3d56049004241c1e051303940800148a00d0401498002455840d0410307440c03294074145004101ca0450b0040c040d580c0e0440e804589005e00a514540b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 920559847 1250 920558597 920558599
    0x1092c18010f020702040b0102070b0327031b0705061e0d020903060907061b05060a1518051905060a140d0c151815080405190f11030102040f1205010b 66
    0x220141c25140e8054003e5000003034164030031490a00c00b80001d6000281500031264019181d50035a603030041130f030343c100c0d92801040714021010440858030751741c144003c0900e46a481e09400480d807200051030b1a1140c1030700814040c40341080389541346140301d40b440410021781c500c80c582c1d52401101d00c402034010044000e40510510303050024600002c1224405d070381895581c40351140404044000841800b0009005070b000503010500189554110b007418200240340307103503e80d640305801c10611a80082580d480c60755003003845050a450445200305104048007403000d4180b200001c1c0c5014242d2044e805c0301c0386410f003c02055110101031158164200b041055070341d9907501e071942450841c2c0321110000b031140711750701c2c141d200d440000400d8079174440e5818020b02c01d01740c05842d600c00143c003e41e114403d00c4100e80380c944021605091a07445805140303080320140c40c0820034280b0480030a80310782d005000a200103e2000300d00021103908520103a00054181419801080c0300c0c4211 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 920561097 1250 920559847 920559851
    0x15061b12160506090d0e011b120302120c0c0706210203040b060f12030405010e0307120302011407031107111206091f090c030f0212031801092c1801 65
    0x124041006020084003600a009564080e91186039541e1201c80b4400c0b40b40c0496030360141944654804c0b5018248c2c40c0854008421004540c0c44204e00305200b52034000000750000384400c418860707162070980040a400480707003014500d001c1e66442d81b40301d006800407c5610b40c2c40d075109000f45040e00440d91a0f04e1004c655074146400d0082e1039000450314036001d211150743d80107690805015141c0080c503041d010714201420980110707181404011401c3d410700c2103160100d465003001c00b0314525184a9000000c0300c2c0c55a502080b14504000d22035000d151410008034071200b40c5104842e9075550055110342e0402c2c8031000640208101d00c460352a911030007040103030112000030039003095880c000f481595000c584890509650401c40000c2001d0f07103020382040050034160604174103500c02044611a448a51036603851a008580c150f2413042503d03000310280c4d40c01c1f0b14207030041c0c43e040040a60740c1030745401c944200d03581400080c2002c0c1c20840000c10b039442c0d500c69181d101000c0402 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 920562347 1250 920561097 920561107
    0x5040b01050d051c0e040c0516120507060f0603060c09080303010915032015181c02180f0709030302151510021605100f0503070302070605041a15061b12 67
    0xc0200b2805c42c0c41c3d4801d000b50b00c1c005599010305d009400740d441d5141d42c0d042c16503003414141d07030f26a00701101c401b51000307005041c0200800039456018003070900a01c02000140c0724a141003200c103960039000c0c000b0500c0786008003840180c0d004000c40741502c84a1201040314602c0c840d00881c0c0c1c2c043e0b54000f80c50702c07000c1c480100c0074079000f1142c0300c1118811165070f1244868106211407501c1981426140b41c124004541c46e20706042c00c440141d6606c003d00d0740320101d25074000c20310340800c41c104c3d074109002110410102c0341c1c0c000d10081e000501460301e07030085401c0da40c01941e0b8030020701100078842161000181110b02c03010700c401c0029005440c005211030070f000302030360320000c110010f05041e10520300407030386007003403c12020448080c0c0d41e4030501901c195400c1d505640050506030415408101c5800811418003c15000d14030074455000319000c0031442c3d442c0785a0113031088070544840c06100405940b158162007201c90541c0c0005004102544280d141003542c0000d45450000852 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 920563597 1250 920562347 920562403
    0x6050a0e0f12010c083d050901030f051902062a030d0209120c0303041a0403050a0f03020c0414060609030a1505041421160b0a1b0305040b01050d05 65
    0x240706550700c6845502003500c8960410246c5402241800e200040d00c041000d404c0c60a202800c1c007882155842501294980c0e000c21580754090b0001d84105a03010140410020704010551240c2003000e0216403100d411b60000709944900604040c40e032040e44480c0ca000300050741102c0c4103154100c11243e683c243c100511010350000c901107481180c0860010241c0c45000c29003a030002c100070301035490700c0d00f41140701100d021510f0500807080020b10000c80040c1c010480011076034010181c0d40c4a003103651800034a4800042c11b041d000c0c80c240009403d02e90420340c202c90704010304507070f181e07215100440868a41714070701102502c1e82c2110020692041c203944e02050050740200c40402c42102d1140c099907607855085000000f028101004602010000b070140100e070036002d43c03404001e0711035116040d00d1882940e000c022190b481008115810184540d0720241c2c04500b803e2000389001d4a0701201c0d43c10510501d03000e5156043c5660070450248403101807040d00d0400411203103a005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 920564847 1250 920563597 920563601
    0x1e0a03080411180702010c02071a07060203070c1b0f0902160204021c0f1b050708030c032e06031503030225080d05130e0906040f031814030c060406050a0e0f1201 71
    0xc7c03544025008100002c0b540107044034251510301c0d41041028500071142c6d880500a500040c240c0d4200460a80e680c800178900300429409400d9480004000d90705107500060980c4255100007011380c07040250721080b092042e034074240789404640040c1c49285090742d03d82c910b00c005003900342d00b51600444840d0858141c0c0f002e0280c2e010000101040e5108001c00e941307034843d6035002b525808080c00040e0490224000441d403200c0e07407032540c030407003104407021820006149080c10349102c91290203110307482e4148280c003144a0604001e08801307203183c802130b48410720010f0411140c07062018603020300c0d4035080008000c081c1402101c14203011080d00800942002d865030350a28900b100010b03444028288080c0102440c5c00904207545455540d0700308081d1103501102803100581d81c20f528035a16541d1103000b0400c000f10b503485013030480105428a0340c0c9184442c41424284000e2184650000a95000701d51504010311440a07450008061030320f02d0f40300c1d540c01280c550305169244419 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 920566097 1250 920564847 920564861
    0x140604060e0409030e06210105061c15051003051602030f0f2107020a050f150f07090b040f0612090503090d05070504290109360603051e0a0308041118070201 69
    0x6030351020035907600c0300200207051246050100480bd0003d0845031807212603444441c40f2521580b44001c0155208042010400d41400b12800710303544400300b00c0d00d01100d000321404000c151000c0c0d40ba02100f12a00119400f804004055400e070100388149034240005901c01402030b030500300340c2c5514006034000d41d1403140b604c086071140600140b4180c40c6500140401840c40c00c0800380486644d2800440c1c40400001c103510100008038000054030182c400040010b0a414032405a140381044c1025009652002c00c0450092421295102081d400b1050350840c1c0d400711444074100b603003801c0640c0741490681203180d0003894100c20304100c81140c5102c104808100c440720700300c25500c1006641e01c040c54450000c44201e003c1c89000040d60f04060310030300c80c2c100c0000c024080c07008002c51044468980044510368002c41030303802082c0440001c10007031607000c402070104d244940d600800d4200d01070300081030341d104421030a206640340c80300e852060a111039110b409203000709000340079200d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 920567347 1250 920566097 920566147
    0x160e0108070e0f0f070e09040b01080717030306120a080c1b0f01120f0f18140303010f05040f060308071a10030503030c18090a06140604060e0409030e06 67
    0x207400c0300000c0340c500d4880554495180c205a8650559402d01e0944203114000c26041c10022000e40d0111315641d920b10150180d030250910b11840c0d03041c091440e1030b0081607040040ca6581412420110350000000c90307600181c00d903039801101414400c0701d440c1c80803083c40100214404030700c040d85901d0006041013014420002c120b1030202e20703014080740b0564440103070b000480c0411081e0b03558240ea042011388a80000d000501d558010322500100c071004da04030280c402c080c169200900086418113800703801d40c00301035850b5500d042649042080380d0302c9801d0141d9201c1c40c580c1c0d11004564003c0e001190400320650380c52519107032a071000f020280725640d40341803240c0070544090300c00a0b024262540b00b03008602d0b6450340e61000e165904000782101c95130b030424801040944038076600d180149104500414a0760a28500d002d020384a602041d002c2d08003404100030032a03003c03241404508042e100069590750700c1c1002c030381601c1c1030580c9a800010020782101d15070b89103030300c00211030781c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 920568597 1250 920567347 920567353
    0x8041505090a330807080402010e0d03050304050c0a0e04260c0f010c091202040b03241806040f021905061c0b102304120309050306150604060f02160e0108 68
    0x1849600e0080f00c00000c2c0d030000024078035a0015000700d024020390b5411500506140310a02084000104081025070f0b04400064002c410310042100420001c000840704854118100e814000303401c5542e50000c0c030141445001c450f6025034894205070300085030066050143d5500040c10803603a9039003014800604a6203481800302c005407241700000c1c2907c4103150b641d00006115020400038022951141e079040c010002800b010011510100d011110040194015890641d400c140c10001d2079010400c04d4000004210028607082084269076604540d20200c004142c210000d41110680147e60440c00015044d48170165029540d14903106410040c00b44600f44400c0c81038a004145040f030110304000c0c400707040000400d11445c0707031441801c0380d00d007441e80e0307405040f12809a481c0c003900801c0c00c410060055040030302c0500c1d440030060900242c07040d4013401003941d52243d40f041c4010805280355288130144248515000014070540b500b81c410784800c80c0c0340342c54500303100b5110703944 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 920569847 1250 920568597 920568659
    0xb010905070f1d04090606050603070845100507052a06071115041b050f0d15060302090412020d0f0905010c060204030602071b06020a08041505090a 65
    0xd03c82c0c00302049101c44a60304000300c030b4501d0148000341c030407610215001510b0381800314154a906006c0c6118000b26585d106950808c42030b010f91081e600400c0080100c080291040c0e005080c4505241c04481e0b0105040c00105081031a8180400405681007040c00c02d401d00c550075a01101615140b130500300d221343e8212440b81e003088926545807038001075812200000380418020307282c48010003440c0d030640e0010103000343c05aa040c1c0e403c031000c8550407032000f207810211052060b002d001d030200307030b6450390707080301c88000915040d40c142402030103a910380110030517110141d00414000c60340504400c203281001c0c07030304400383c6501d550b42400501c1070704c984c48120341c400c00b103904202000da00c50316400303070400e8011100e203201c071001565180d408020000001c2c203c3e100420b0039a004840000900d450940e0500794120107911490440d4442c860500210306020111800c0710340746580c040d0400b203000c20698150041c680d4a690100c0c24800000304110300d0130b92484802400742070010340d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 920571097 1250 920569847 920569877
    0xc12101502010b0a1203260412140d090602090406030b06090906160c0317091507051c1d011b091215200406050a03050109090209040f08070b01090507 66
    0x31014001440d900040340313402005880110030399501046d00078503200a0001040350716011710380c010606000002500000c10050102d081c4060784000c0540c6048015140242504056405071b403003014401c0369545007039020881c1c180d04880d00c0f02e5001d0410311489589007050003100741d0860b240b500038070184001a40c2c03560041802849540c1c0700d18905541500007070119860f40607000100d043c424800410781c013098030706540c0b62003481800d00070280b00382c511043c40c2c040080070f054041444014042040d00345131940b20503001c14a0302c1000900e010030b031190b00c81c2d02441400049455403038513807511080b0300d8000c400c407070001441c0c9550701c440d0703070341e0200050100403a08083d20116061079503050384002900300030084110200700c0307050131010118001140d8845e03400031003c00c900044201c1c0c6a60140a05401486001010058803409401041207800010401015044042216810020304c203040e150180c4d007110504c060340da150315903100100010340c1c802020560200b183c4100d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 920572347 1250 920571097 920571101
    0x2090405010902070c0e090f06011403010e061b0a12061d010e06010f0c02040e070608090c0922050a17030114060a02210912010f0606050703090e0c1210150201 70
    0x41300d540810103205e91441c0c2140402c100c20041d003c003450b8003400400d8280340c281000560f0180a130072080704034040136101010b003143d481840f0105c4a820040811100f0720000303000c0761110182002c040d55030b05012508407000d000d41c60b0b06441c1a841e0450101d184c050320345015450801403e03074101b1507601c4050030314107050b040b18081d001034040224001080d20406aa40e02e03644090004a03681188400050818006400000005160104020b4014001c100e01c9200d980b080d91030602c0760030207031000c509051030910131184c00c0c551001c403102000801c010032b000080e00070118007113500305007070310042542c000c0c418003d80c01000c40200c0540e03e01082210007081054001701100a40701c2e490085070100b010070b1a40c00307581444144910344410340000304500500000186800c0000640d00c01c4401c0c0340c004004100707046c000301000036004bc2050b000da906ca4021042640c0d50000c0040032032156500c1c420040d0b10720000c2c4407440015040c00d00035100c0310045c1c03c2c4145400b00d001c0742 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 920573597 1250 920572347 920572357
    0x40617040f02010c02040207150b0406090905121803070603091b0b07260705010e16050607080310170d0807210911030a0f0c08120307050901120f02090405010902 71
    0x200050091101074010360040303040140d410f101400150412a4685a10021400d02d04041c8000307508ea4449030860300d8148114070103008501e004004100b02612042d0f658034014000c0c0c2c2584000151008150747e42c503006240c0708000408070f46000380c031100700402410b040c04049601c07003a8458100c000c0ca00301803204007a180141c0d002801c103502034480200d002c3c022451401001181c1000032101c0400344002c051540c0201c0001c5407000c0507406152801c010f14059441c8030803191024005070b60b034201103c81c0350383c01100c40b94a0b6102c0880880c071000b11644a010565041c04101401480200b1541c40a001644039040d1a070313904c4800356000340120400302c8900304460400e000003d1558003118200b03001c1c0c140815030000e070310b0102c0d1500070361110607500f41c4480882c100030003265001c10005000080c01030f0100243ca0030720541c0e01c1c0009094030090002c0070a845040c1d92241440858524502c0024440c01f260082407400079800160300c0b500450a09d00007040d0302d2034034000c0b94 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 920574847 1250 920573597 920573603
    0xf18020a05220e070c141504020904050c06160510060312120b042d291201091113061202040c05040e070509010e040b090708101a04061704 61
    0x2078642441441070100700140c01c568a201e0610291000c00d04591110340c0741d104900340c0e22004000c170020b040041039215000c9152605900000d40032038020130b4060781d96005a416107201e61641ca0302d190060408440380ca0190308005c011542c3c0b05c4009440141c200414080c0041d104d18100d03164109054558601014081d0944405c3c40804140326840790001c0c4942c100002440644c0301d000101a01d028a0f600c1c09038500d440c0415500050140038490400c020304410003c003901d191a45210868410b602850308038100116240354607011000c00b100c48011008006050706454076802d4450303101d81e031a000d416000c0c40400c980115110315070070ba0b1022260300e02074843d9a42007001501420b4444420003806100019400c00308011503402003a180e00c605480d010941b0005051140c1e01c01407038030850800620705015150f9010164103c001c0c3c2ca4070180039130380c000000149155035401007407c05000d0150000e4900000c02500a03078081c4c1e683d00d183c00400200c00e03c2400d038241d40203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 920576097 1250 920574847 920574857
    0x2327010c0e130e030403080a02010b061c0902040e01020310090c1b06020c0c1c020123270a0806040b090f0d05071112030901081b0d02071a010f18020a 66
    0x140c52502e4425164500e82c41030682c0810070f2101500718a040d074119520841e04141c010a20f001d04d55020f0041e880d50104c00e607005030411540786000d180b1040b05404101c040c40e6a45078010964a5031b41068260003000c0c0029551390800c1c2a400742145d0380380c0b0036070030f41918044200500e01d100e48c0c0340005482e440010503040e50020788948000b03500180105a5622440703d8101a6485d0022503040c4040310041003a000032240c0005422160041d40710004036113041c1080d4071164048007500c0c8d801003e00c0359043d640c0342c400c000ea0280c40c010314000e03500c40400000060450741c00031318141714034450041d201c55922115003080d680c0040a00c080d540f0707000003a0303881c05107125001500c1480c5c003481c5031030655424080400c402441ca64040a0680c0000442680d95600240f2098001058100b00042540c0c0403003004079034010b0820a21a01d60000b4142c07040c4001170b0040390300400a403410200340d5030f4030020b00143c580d45200c1c0e960f088400000e1519003a2181c800e452080d00030380c0324 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 920577347 1250 920576097 920576117
    0x82107080d4d030a15030f060b01030207080a110106090e070914040807030f1824090f05040b0609030609030901112a01020a05010e070f0b09132327010c 67
    0x2075416030f07401c02010011403540d659000c06aa406060701e440066020304e0000c60b07403495605004080c2c440480105040c1401080b50b4800241368030202d402c075060901e04401e1030740c60810480d02600859105020380d50500c0e051184498000c9504005c8583c502c9082041c0c0030307607594103031907860304803030160031000d050100c60b010074080c2d000c43c20020014500000080701c50303210300c0b080e103840750030503400d01c20302491141c588005c810b180f20302d21196080c04540c035898802c00c00400d21a50041600958461100c080b8a0729554142c3c0c0d9540b40c0241690b44610b00001c19607074a070080b9002c607000a1540c0b24036800130502007487c451944000c0c4d1a01240e41201c2c07210b1070304a0a10190724118841c410020002c24028400d0100d900c0030349000e8032483d480c2800b0003203100c0031038101024112080148103101e544422900400c030356045004075001103540f2960301c1e10754840110300c07a19a180002c200f0074056100c0000c440c000311409500114608200850072606039010400100d000140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 920578597 1250 920577347 920577491
    0xc010309080d09023d050702130e010e03070609020f010c11040b0f030d080105090601050a08010510030204080d020102130e0103022d0a06051201082107080d 69
    0x1000300ca0070700107031541600100780359407008900b40844480c0844240244060001d003600c40c0d6203205d1301001c0c07410500f03003001c0d600000e95110703400c10743c1b040c035507504c80c1400130740e01c4c00703420131504078180c0d1041d80e842d2038640c100040540007100040b03101d940c10a801c1211513004c3c00c07903005003540242061280c550f004090000600c0c0b203030040365200ca07140341c45081e83e40e400c00c403020384840c0300d9648403c1545410300b4080c0308400941110f0510030305202e4038980c250711109890441c0c2c0102c440300740003824000d043d002407040b90048203080c0a0020344121441d015002803070180f500003170b81c004280d9200c50603d507542c401c2c000294000802441880601c202d2080d61440d0264440010f1850342c0e40000200008600c0c0d012001151010645403d0403042001c07041c010f1032000007070440c032558030854a6070328060425602c1c0200c80031030032006200c1d69a0a544020300d030200c0c10030a40311110f9524000e48032810f1562038022101d4004a02c3c4000011401000040046520200c418180b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 920579847 1250 920578597 920578601
    0x1206020d062126072010051204080706110c061005061c06090c091409070e0108180102160227061e0604120209100e0601141c0e0c010309080d 62
    0x3419051101100202c00d64043c2c000200a1032907912582c1561881424940c6100105402d07076078141c800e06000030700425594108084841c203040020b0450900ea40340d140030141030044500c0900828038156244151440040c018002029080100e030103540c1d450503940d140342c0c41401641d030403d000f449268012844104960b100c02130009012070843d071922030100444da07154500400080a0302002c000a00c9003094100c0441c90031343d0004000e250220001d802d40700c09400c428100814030000800308241c1c1d40c0036101d082e59074002559210886500078403102511001a03100310b4031034040c941041c403000d910201d00040c0162000459450760104184090084055500d200181c21a44941e5440c00003c00c040c00725000320000c2c1032524014042810307030043c010340036040d10102c28803070030780ca55041c11f40c820000d03c0c02034210680100c00307400034041c2403c1104840b2300d20403000136a502e2508040007101d0101c04542035950294011410340c0d1444c0c002501c141020448100351014507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 920581097 1250 920579847 920579873
    0x50702030f0d170a021c0615110c06071e05060f01080609060c0c16082b12020a1e0903120906080612011808071b05031b03071206020d0621 61
    0x84c510041c1030010002100500c080301c40f5400b20b4180e560001032042000c2c544001020700d51a113418201c006c4001c2c5141d40e140c0c000060740d440b865010901c8803c01c803100c01c911541290111b1440300340364036490403581e20001035070b8884501d05240b0010540c8000011454820890400100440d441d000706600c80ca500c4600c1040d181d01a03e9141000e040da05056400180600c0b4020304540029101266242d801c64011b80031043c0302200c0e4800c40d0354070000d840c6c0c0d03801c2030200045c0d54800201081da000b900c18015031001d010341070080d030400c6400100c16030031030303028030400021500701d05001c4903d401a4001c8002003510760020440d9402c040e4001000b020380c090002034502d80c0d082d81003035081401c000c22180c3d03500c0000c241e400c11000c46101c024900900aa5101890410000070303102d18500440c4040100c1405821441e5581080f000d8020090481491107030f00907800c000010f980056048525903003001f2b0005409184000174284684d5920008401c192860f03540c04090865 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 920582347 1250 920581097 920581111
    0x3052e0902060910121503050303010e060d0b010305060a051522140f04030e03120714010906060b070c120203030a110705060f1b1203280c050702030f0d17 68
    0x414404140381e130302c0d40c424400f4070302d4003501c0311642c103601140c0c25810b446003a51003826544441743c0800c0064400029241995940001c800980c0e4410f0049058402401c1e80900152094000041030100200d200c07400341d2505030701848555a200c09103002803070407001c01a0004130302d41c40050002c44a10204150320081c14000c515050b90160714100c046054400205007151002032104064001c8542803080c101a0040d001c0b0001c0301d075005440b03000300c1130050003869180c0b0784801806d000307600c64503040c4e5012808104007030300c1c0e15004041d6080300004550069203107401045101b60300580b4071400364000d000f1131030010300b4401210f54014944e140e116600c40c020340481d407951440050080040041102501d40309840048a0b41c000d0410708200035800c140301c8a0225240d07207003202e5000c0400412010b284403104411b02072403500124040d02c0600c0c18601d03000310b42e88100205411402201112a5171366071920403034940303000300c0701403020444020f440c2c00851219100c07607900c404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 920583597 1250 920582347 920582359
    0x7080705010203040c080f010509030f210f010918111005041d040303050c09030709020a180306060f240c0f15090c0807051305040f02180103052e0902 66
    0x4103903505400da81042c1d83c11100041410000e204031603080208203000c0321031900034030103403c02c0101c0304d481e80b00e2a00035a986140014624030300d15a41c001c4c407249a2145c00d5101c1451070140d0400901c44801c0c094000818144440360141507203207030301d1071b410b00d0b000903041c2c606100c000d0802c005429117034800e10a1080600000400f41040f0041843c40e403843c2d08078031010300c0d040ca001421a04004d0680400d03100c20f0201d100c01e074400003a10b82c142c4002c03030001613850503808001e40305441c1e88500a03560314600c02c004000c00001d5081582215002c0504404068403050500c400d41c8150503401040065100c0184049103e0745080310403a0142d42c00401200e0340d51038054212004048410b41c1030b80f945540402c02c004903030300300001c6c106a8050701246080c10700007510380000301c91619460b038440707000c00c0500c082c08100021036a4020103030581d0b002d000340d210300340f0042440f0558072800340710300c0c0401004440981400c520780305909510402d03c0c0c8450100100000202642c00039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 920584847 1250 920583597 920583607
    0xd0309030c090e0c06161101050c030a0306050a0f06020607050313020d0f02180106020309042c0703031404050f060d110c0f1204050102070608070c230606120607050708 74
    0x1621400e514020700300144002c80c81030341d00840d6500e03040490507241c0c004c0c00208280401151121906d2200642c4204c428401404007130049038140101c52800503a804005132406401c1c0d0035920440840300d013540c2c9036503c240c3c1c50180d2551140d540c0300b8600581c00100004409503c02c200031036203c0b90b206988000f42c2c40c1c540204070300740f00300c0f03030221000c590420f80101549800c019009000ea030301d480030390b003660500000a4880c081c4070113290086440d1641060980038000d10b102c901008414a0100c021310070040c2d1781e0703400c0f2500c400d90102c2d00030a6039042c03070585102200c060740c0303014107003407414a000e40511044e584407400d040703e0207559101e0315030b54003400c1c80104000203d5500802030594640d00445c1448410201a00320680c200010006070360080703084408c4445500f806001980c480300c2c01e9580c0032284400805440c02d480e08240e85143e041050348004a41c0d50841c0ea6641e500c405224000c80d410005606070740c0700000240304c507441800240051442050f06500745 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 920586097 1250 920584847 920584853
    0x10f0c080a27151401210503190507051c080702120301170109170d0e0109112404150e0904170a031e09020f060304150c090503060412031b08060d030903 67
    0x124060380100c40220131410040042c0c1c1c00403082d5054208101c145189034001d2565126941d1003012800c80c0c104000841860500d4015000c0d9400715400c502550300084412012101e4064030b4180302c2d02099490010a0100b8400100e0038011034543c01910b1460342080c0000c5100d41e00362079461040c0d03484080c400d0004030f14001860580d140340c10400e85503500207284078140d0312030ba12101401c0c1c0c900182400440d441401c640309101c8180da080d409402d0b0710207072000480070f503101c00028600028000841c1c24007820350001c401d44a170340d1a20344010840401c034007440151006445000109074000344180e070b60004000c00d140e50701f40007a07002000c001024000b002c0c0c0410004a0b80c2c1c1e403900d0307002d40c1400309408014030000c8032024a1441c003a41c8101d607640e1901184c40741540c0e50110080c01ca8011042303080604030041c100c0345079140501c1c01016010030401c806000038141803001c441c100c170800c0c003001d402405455002582c0e0700d820501c040c0f0480044190104401c141001002c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 920587347 1250 920586097 920586101
    0x8250902120115050c0c090604090507120308160f18171f0207030921021c022e03020f04170609060708010302090105060306030f010f0c080a2715 64
    0x401822035600d00c0707541c58165112401e41544021a0a1003420803625400f4080814001000310040352040c555407940404100213011610008102d4850f83c24003084000c0c2c0903541180075846551204881e80e50030400714100120b17100442d02041172064845000d5005034100301c0303010140c04600d03427903a68400c041d80e500030b04569111066040320b00c404002d00c118444602101c48941c0096182c061140e40003031000006102d05a40041044422035000d00d9088443c071900e40c009110340c00f40003012041d40c0d81e400f1040001ca119442c065035841c0742ea051418250704401607408070f1103010603021002c2e000307503000c0f4001001802d81084086031800c2c008081c80702d0003c042c0020301880c54000512440d0200250801d0b041c030100d5001000181e580c021101c1c1510820385d1400c1c1c0f26240c45010a00e040d0364103160800a5007040140c03001001c01c0d50000745030807000e1b900c3d04c45a403901480341f001c1341d004004900b10544064081c03102c003840440941c2e40307180b15001c1100d42291101c1880c007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 920588597 1250 920587347 920587357
    0x3030c020115062106060207060f020a0501141e1b0a090f06020a142e09020a151403060d020114120406021b011e0c230d11030108250902 60
    0x2180040d10710104100451302c10150b10b04101c0030400c1010304084c3c0180d500c8882e486040c0802500301e00c1102c00d20b00c00d11000030500c2e8840000d00541e0b407420303d58a4101c9086032203044048036650010380c51504108518020307609401041410000d000c84100036501400194081c00058100000d00501c1c1d208950700504483d4080d1010a205280603070340341400c02900e4440d5031288100050500345110f0001d5800d41c0d10400700700c401c1c580d90060010306124030300030303501903e84240050200f50091855075841c090703075551341000c951700040016501060764016000600d90004030010f502030080b4806904009400c1070a201030701f10414002d4104503400c80d003550700490b10321070a18400e59440b0000324040000d10108a1803038191324199140842c0b402c09588032464110601d0081d51002042e500841c0104c0086166201044071544111104a241464140142517010050741a00d059400c24000b030700c0850450019008550003101d0005c040340c000d400001405520351000340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 920589847 1250 920588597 920588609
    0x403050315090f0601081e0109090c2411071202090606070f050106060e0d03022a100203041e05060d1e0c02010504050d080c1608070204090305030406050c0703090303030c020115 78
    0x3c1118588070340010051440904980700c11103002590864241d001d85070320b81580e0300508000b0b130140d510309190022598591000011002240070361100c01300c2c207500090000c80c00c0c0ca0300502040c0c0741c080c1e6179480e2030714403d001c201040960340f20700510b00103402c01d40040000341500e013804115125201e02000850084843d07039900d035000c100c00b0740c1011207010010b0044504602d66505034401030f40750026034010840d4041c00911080c1880520810891140340240c000b46076144a06000380d82e0b94014010403a404441d858040264280550803000f03940010349403a04084122091101a14010300f40304903040c40c0f060300030842d443c140f03d91410f400c1980d00109290405041641c10409541c0c50031042003504000c108136404a20220361001d103000303044210105035070400c0000d0740500034000358058288813200d000d142e40724001e180260b000e04020800c41c2c841c0011220030380310385200100481c94040c410004207000e8ae000100c10700c00b030b00002c10501d0f214183d002111186070490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 920591097 1250 920589847 920589871
    0xa1713110f060f04082b0f020106080f030705160b0436020a0e041116140601060905030d0201020712080c1303060c02010b030105100e040312020c0102030106030b06030f040305031509 80
    0x10010b00d0f10810494001003001080c43c0c3c040b0540003a01d06c81d8040a64505040c083c0e441700c2c0019540c400d51040000b0700401c0e043d40c0340070305005026a01c031344c2300807401e03146482030810510480d046a0b03c1d603000c803441c106020b85002d180800700404921300d903441440745c60180c44c901482418051403c0103040e440e0354010703a500b4141202a03c6000566034880c0120300d8010300881644040e401c80f20720b02568140c04100340c0641c070f0a26400007448410002d64001d901c0001003c45e009040c5005a035411415170306502c100300c0c0100e00301d000c3d44002602c0b0384515a421030016000f00c032003d40015241200c0741c642a10741035600f518548075807080310700e40c1d5180310407140a5030a20948c010601c04038000d02160504d448030072480c0482c0d00800701445d41e200e001c00e041500480a40440c8441c0800940d110740c1c182c82194000d4000348219400b084c201307800300c044d615090088034801c0f04146421501c6481c0d5481c01c80300780e00024082070200003e803031a1340241e9200d4078642d00c549082089 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 920592347 1250 920591097 920591099
    0x70c0302040507050a0c0615091d06010b0a1d01120e0c0a06050405150a180906080709090b0f0714040f0906080105040b041101030612080a1713110f060f04 68
    0x10700c000c0300c2d0b004010f5800c0100500c4100d50705a400641000d640717810440100c0c00f0f1000725520341701d581c0c903540b01000340c52a05d50712400450f0310030741d42030369803220300140c4041d681c3e921800b6400e4410082c0c00d07070004000c02c0d172018581c0c1c1c5164030441c4490041c98507a10072000c00c99407000322040c06401c050140d1207428040c842c0d140c8002180081c0066242c903509051a0402103038061014100e5000d1181c000716031400250300c41c404a20400243d00c0700d1120041d40c80e003180c40145218041d400903030042500c089881c02c281d0150101b16a40315a0850702035942c80704c1030b00201f1020f0442d50810401003504a48180003d015001602041108030383c21454410010101c84080c0d010402d00d0741800c08000104810541150f4440e8115158020764410321004070b0007001ca42d0000320a140070300100909010f141030161029075080e44503051008890286001908412070710805004007010099000079100c101e40c094002c0c014100f81c1030ba09115000500940201c03080205c92080814 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 920593597 1250 920592347 920592349
    0x1b06030203040b090d1403130b160806031204051c050304260a050304151b0f120306050307050f15040806101a070803090312070503100e0603060601110f0102070c0302 73
    0x101c03090300f002d049001417005022080014008819007003c00d101e6007004000a00c0300f11810740c0b092502944921003204520f00040e40d450b42ca80340c0303948440000d200c0c600003600d90600081940e150348480c0d9005080c50b00d882c04014030220200101d1100000404030100040d400300080d20160040d440e41c0e100001e602e0003014104031314007200c10300c65404191180c0101d00c002c801ca5050320160110030551401c0410300740e50741004044d0136000101c000d4005401e001c412070400c2041841340880c1d9049400c4050220282c0740c20b8058668140c0041e48100302d54906211301d410319202c00307424864000754407441c101b099003140d4003001c0b01c0d820040401c031543c901c04080c0ea0280c46e820f013001c51404c2610866000720f0084020044c10034800101180c5211010015900414440801450a0720b414800100550410307218002c03000702541002ca80036540803003040c400c3e07401600504e5143d8a00d001180c0c540103c00d0289800c0c0181c1c80030000c02c00c801e00050050900071009151183c0c078500c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 920594847 1250 920593597 920593613
    0x1602090702010b032b0507023015070e011e21141803040308040905060a080f010903030b03011e11160309060f031806091b1e14100c1b0603020304 64
    0x340038002088070822030039005070350350141c1b90a0300c0074203410b203050f000746000f6270603800749042c00304c05c0203102d80c8071100814000410680e105003000d56991540b8010f00c0c00540351410840800e0740c868101d1041612058410b0610841701c0000c0400500340752040c000703410440d40300e000c1c010351410380c1000f0800c1040c0b640e4100448004458001e41c64549540c03104025405103000320181d054480c40410995940d500035007020340350b904c0544003064022450a4000c2a034000110042411300b0701d80d01a070301d03040c4241302036810105070140e062107210303100500400c2020b8255120700781c10710900308042240140d071070b0054440d440760006c035420201c1c050134851035010030034101810200318841d54460200d81401c01c59203c1c1011507200048e19100b0b100c0c080c1e0820070380d02c13400100c0002500c0c64260401c8152403415001c281c845503190013650030180d01d00500d040d0414032101c00090524807541c145800180141181000c00101c1e004019100b0b0b81c607030001002030b401000744001d12080d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 920596097 1250 920594847 920594923
    0x12090b070c050918070e0c0702060a05031506090109030201050d0f1b031109010906050702011101051f0e010e011a04120602090f030c100c03030e06010b0a0807051602090702010b03 79
    0x203460801980f0313480f4001d1565400710780502e0001c0000c45010803120581641510301c4583c0c010f1096456500b052001052a00101c500c0d4011500040c181010350503c0000c4900304103041c0d482c846050300b07640041d40c2035031101e01850100390380e030a101c869108040c4504122a084103003d000003281e41c030001000d80e01c01548404c104101044514031aa0b0400754410843d00e0381d003000c035101e840e1400141d0340000300700c00c0304105e5420142004002c40c1d0540c00c1c030b0701081d003c0c00e001e030860391078402103021680c090180e40c2e0303c240068014004500d1180f0040244a8200482850140ca50400503643c4004010444142d42c001c200c45803107250450540f81031a005600501150443c440000e1808500000d14400c0c0b001200402040c18030980090003046581d43c200d0302c103035940b140020020b0344810030100010f454000072600e8075201d04221003030f4208124542c140b40742990204075400202503e920150365071400744419941f01070085140413882030072107040d40d030240c03020034040d10f090b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 920597347 1250 920596097 920596111
    0x141005040f030b04051c0201060f0b13052101020a0201060315021801030f061d0403020d170103120c060c1101150506030f0a090f050714010903030c12090b070c0509 72
    0x8280010701c400c22003440340d00101c80d00710090384180c3e00c0360b061041c18282c007485401d003200c561920300d2142940540000b4110741681160407002c540d51405011140a000030118188020001c104800c2c9070103100aa070402c00c40c40040b200034044a24142283c0c803030066880940d45078001081032081d408102140340398490000d51a144920328240480c7c40040340f1181411390300c840d5440c0040d03d55200401a18029000410343e42d000040c2002108044070100c0041c4a80312408242d28071600d01d901030700501e011503905590860741c604140c11885c1006c0820052028007080108880307000303822421840380c44060005806103440360a448203c5032026440030807000802081c0c0324401160750204030751128030060f84405103101d01a00c81440f003d080910700310710890501001081040460b078800107000e140d0b1700306100540d45c24205100107404102c254074190003159000c1d01802181140d0b2410111154448c0c2500010741c00644050f1000380d41081c0a100a040032805640c010701 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 920598597 1250 920597347 920597357
    0x908093d02120f03042301021317070303020d0e030a06050705070c05010e01090e0406020f03071707020c060406080718080a02120622050c10080601080f091b0a0b041410 74
    0x300f03440041e001440050f100074000c00203c14510b001c205040d110360440e580300c2c0d00942d991009a28405041c4003107026840c5004960051540005030000d0b00c1002c03240e02d0f030080c01c1007600211007924070625601c00e581c0c1500800f02e1040c001102886298400c0c1c00d2034480c0368072107415007445840224580c20030b60610260300f0514844d82c1e00300c4407403c103ca03101380d40b03114950341c1c03890f0207006809490610341d00030b44040180808141c000b1203c003e132480c0258003111954600c642281d071041303849030042c0c00c0703c410842400214418132102d503000c03000d401c21920000f603545030404140d0b01d651042145812480f440340451801c0c000248100c21528014509400d051a004000500f016020202c003129011000200305c0c00344444005c0c0c06004220040c3c0d440040e00150840004031f800c1c0d400141081d00041c40b0407507800b101d42c05801e4100c0103001182000030714400700c0c2302c0e01101e01e5004c0d4100c44006450a0007074010805000c0c0e02c0001c562018051081c0404181c00c2c455045c10700c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 920599847 1250 920598597 920598607
    0x1b020c040e070b09010201060b03040c06080a050106080103030c021c0c081005010509270d0302030610110a02012604050f190f02100e09160e040908093d0212 69
    0x2500000302c41d03050300c8410310700c613540e81005070060b80180700d01e9105900740c42001c810401404501d42460301164600d4480303414a039210250707070044a901b4011000852100780052021910270a2800da421748090301c0d040c51032002010f20307081c003943c2c180708444d0783d4403500051000c034105001c0e0001c0280100c0d8144000d506043c0042c601800041c42036060498101c0310090f0280821035807401c00d203411003a100707420060038004020350700895549014107101038600724214819240b5106039410303080030309000301c41030740112000049030140c500800b091032141d03d02c6280d140200c0d80680e1007640100300321440d0092071410f0190500791941c10360558410600807030b0304410300c079020030f07070484850701611403668007a2010f070700700c10285400404402c100304884141034400d2440d680b4944031517100c0088401044240c501c5840020442541130240200301d0070405003000c56090302001c2c810742c0800401c2d813a416904e81c0314408142d08a0034412800841c0c040c4000b400314035054407110b281c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 920601097 1250 920599847 920599871
    0x6090b0d020a03080a03020724150302131505040e0114060a05030607050703051306030b0103110414090a060b0c0709140c03070f111207150207021c151b020c04 70
    0x241150b10025002410000340c4c0c1020500c40c0d8111050268815010a17446804203003109c06c8101d2090400c2040707142240b81d03100644030403071660861754020609414a954021004c015001d2007004074040444070300c0120f520740c7c9078052644480b110200008508141d5a11038040090103001140195801c0c001070026031400b10340d40d80d01894606080742e84486900d41264980725004080880e0300050001092207503058121001c035100036a0b0a0062056030928001c070f0340300b14800c2c030b903803c180502244071900385410455030102c54150001656a52009119040d901501c2560711940146005010b45001032180a11800501c01c80203901e103490700c440005031001030050024080441e40c0350fa08540304540c0008101e810b0300075190800c0c000528400c240e0410401142ca075501d044c0742441d80c410034402d561119030020701064001c40c400a0020400190b00c005a5105da540300740707a1b081c002ca40c00742c00513401c8840950aa182030145000b820000d0484405124504081401c110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 920602347 1250 920601097 920601109
    0x52509030605090a0c0b040f0b0f042c090111030a0b01030f2a020304151b1208090706080c0703142203020f0906030607080907050405250512040b0a11030a06090b0d02 73
    0x656040980f115929002031501141c039000d03d80c0310090004454903081015075031440504032401c24444424080d8482cdd0300114243c0d0322040303009440140c1400080c4c48460140c01c15100038030181000140350014040c0d160948100440ba101d20340e400728020303403081289000c0d1040900c800e1002c0c5007080d003014204072040c40c0102d02c05003040410348500310008501c03620180d00f698440c102900f41c03407020801070000301702180c20350101d00a1a000048107802801d945200303281d541c60f90340ca014520380d402c0c0d801c00d80e220740c40a011581801a00000c11004070030350310982803003880f00c0e0014598410060503000d00c00036036001d011014103120f01038500003903080d000001d600742030f4490703502d602c6610b140c11060b41c4041d0380141008107000340c495250203e00d031000000c100714401d40c035141c42d0549480c800c140c0310b0b070746401604d0700040c04646040c00c8a0b030803240c50180800c00188484001d2003e41041c1d5140c07940c16524031040081580b14803540c1e60520003a2003403e0740070050b80000381 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 920603597 1250 920602347 920602349
    0x91109010e031f05042f130b030c1011030705010e0d0c0308131e0303051b0309030d0c02071d06030106091a060304020d0f050d080a052509030605090a0c0b040f 70
    0xf40d50f0302c40380480d04220f80007440303000c0c42c1c0c0901c0e08003802050400350080307400c2130460700d80d02030441000c2d02d040e07044250240805403000940140002460101440500c20250f0282c0342040802800b10064000610080101600401c00424074403101e65005060070000354442c02882885405030000a82100c007603a07001912480700700500c005810071910220240c65105804d0192060340780c10150554480c50051421411000140f03403a0103413802d552000740c030058650352080c13160f484499410340203e032a07910300d80306440f4460b070b9580c1102e1a04003410140c2c410101c00c0c00070410182007d103d0040104001c100c1400b0583c0c1d120944042c240d403100d549030080c080040082c055403602584a10940d50080c4584014140e07400d03d03a854a41c60007003503000400c1ea001144d070302e019600178035000f844c03c0d4103030445001d650007401e113400100000000520501500000100e200303407148078407680c9400c000d0503116042e403400c122888001d4222641208007400706000c00301c0c90f040540c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 920604847 1250 920603597 920603653
    0xf08010513020a0207081006170613260f0a020c030714040903031d03071a0402010e01031e05010605032e0302091b040306020a030c1d0609010504091109010e03 70
    0x180c3d01c42c408a0200e040039a56000030b68540f203000001400745042da44070038200e8900e052400e620001c0b030317000c1c41e0b11901d060310300021003402c05014801040480c04071030801c0f07a812051440b40c0c120881190703103607040390400c50050100030980140d81901840b201c5502c0b20224040c00c141e0f13040c03686002c076003d000b840d501d00459076825688105070080d80000415081704c0e881e02c039440c0c0c0c408469541ea602400d41200c0030030341802c00407a0480e000e68008c3c080c2c3e0b416100c2050910714440118014034155581c900100280303036401c1080030781c138407405020b8452a56510766034948400000c01010f2100130324400c100041100440c181c5010340303010141d079030449180303115131100007080743d2040f044c141c2c00004c000300040000410800d07600406180c20380740c03400c0c0011103101c030050780d10684100c94480003a804464103602480c01800510b2080303030504003d41881c1e210030b8480215244681540707801080001c401020750b81002c0c0ca1050480c04030010010220300311a001e110710f06007004c1ca = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 920606097 1250 920604847 920604851
    0x5070f230903010e032d09060f09060703091a041d0603120f0a030b09040809240d1d0303040c21020409050109020f1e06030907030f0309060f08010513 66
    0x4066400c002504071284603100074024484810700035045030310f035842195419032100e94408540582400e00c00c0342d0031045501c1c0115402d01000b1303424007031281c1c0032505103a2301000801030480301d13a5036180546035050080e5150305506080c07103058442d008240c15594258403042c002004010780401210700d1010013806006190b0311400c012074070306106000841c030044e0001c200b40c01c4807004040540300030a8640d07401d00180212109000d1044410764003d0b14045041001600e2170400e03070710550582120324a8600d141d4490b041c11211030308248501014580c540d009230f6080a01422140c4034040d50001131461810559681701529034148500721520000783c00d0208091804503c0d41d08a0342c000c1d10900c402d1400c1d281c00d5000303000d4084202d10803039000c0d40980550600202040e808240300208a4100001d00c0c01c01215400080c03a0100303500c14a44040002486002100c10441c40b948685184c5824110050404e03640031402d02c08100428004000941d10006130003810000d010340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 920607347 1250 920606097 920606147
    0x9030327070806011d1b070b100b0309030a26041202120f0306130605010206062211071709090408031f080705101412130f11010305070f 60
    0xa00e508181003a840714400f4000e0000004044829201c55240f241d002c0079a0318250345c2e03141c40006070304260004034510050900030f000018210030386507a00010311050041e04503655588480b2198022103603202a900040b840e9988542c00c00141102c144c03030052040311200d210070354203121a80c000c1024202c081000c010300505402480340c1a09542c1d910341742540c0d0929000000c406510694030300b4052000030302941400042813081400b0303580c0503405812180c450a04118095070f4460080b84c40c5c3c185000d083c04650082d1044d5189060410341c003d072110304509012004400744c41c00060028001c0054400f240d442c040d0182d8000e500101c01901c036100d00034524840700030303495201c070740e520205000314030010000ba0020480b101200c0b12405d92040d210115001d004000d500c6034003280603c908a012401d078041aa805826203044880340b4200e9100c01e041042c0841081e0389842c0340c89424182e03541d01d40a110390084580c100181c80d444107900080808481c8441c2004070012400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 920608597 1250 920607347 920607421
    0x603140f1605040e1f06050c101508100b03070b0c0304262b03060305070b0901140a030f06051c0b0a0e011a031c0f0f2312090303 57
    0x1060380c002c0e05600300302030500d00e81510a0125849000401032403141000c10001b1454407a10417684088140340203172540700d4031600c030000605001000880401c000c0300c0041a400c100700110403d0322540c100109009880000f818108001900040a058410018090fa03028008100c504840c0004000034880d910314101000341e20540d117020b41d05010f056401004101070094950000d001e506900800400e03402c3c0940403501c41d480003e040d500441f200b04001890340024065290041c100b036152030340307e89030f003e003075501c040e6001b00800d944202e0b20742040366911464014101c2519800c00040000790010b07050b200003c4000c1c02e00740b10310005040040c007070b0004500003d02000078070a00c9807400002c400405c41d07054207400b902c42c01211291002c0749030407103402000d160310f503040060b88502e401c448d070300030583d8408240898181c141807144c94040d000198010042da4490701c840c1c0080c04000800400351101002d5841441441408030101104400141d841c4075800c849030b901003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 920609847 1250 920608597 920608607
    0x30a03080403140d02030405120c0712021908030409060f06080f0a0b0604080703050609070e06010f0c08181807120b0406030602040602010923190303020909040303060603140f16 78
    0x403043c1d40c01c001c0440c81104502882e005180520303c40e0054519900300c241d00741c421405036515074030690340018800c2200200088010740014000f60000302c0c5485894102800c0e95981e074040101340d800007a040044e69030610550000d0030403040c03810545441c14900400001c4080c020784118200800820316498555101150b88400581100c2e101c564681400b91110650712080e5050300a8600055000310042488002d8400380b0040c1c1d40f59454000c011250345080c0340d118428411220722a0003c20b2910000d801d1101d0103c4c0d40e00d0107101c0920612030074502d040c08030090031f070501d024070407040d0304580b003801340b003003407640c0000c070381c1951000140a0300c1240d0018040d139100103400314002c0c1d0f06400c08020706010350110340f0300800380401c00c4014403000d948a46c0701e030010101c403600e50176040018003100c1d0180c50050b00b81011720000030304440e070a480880c04607a80304000c0043c140c042c020010340740146600b24a542c13528100c00c40b59010001c010741d5410303c10003902d6000c14094 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 920611097 1250 920609847 920609867
    0x91c0f0e01030b0a0303080108070e0408040e0403020f010603050d11030a020d08060316300305030403050f07060c08010608070f05090f061c0b0901050907050703030e1e1c02070302030a03080403 85
    0x604c003031034aaa60b4180038025072400c1c085e00039140501800810703105054006140229441480079162074607226104002c190042c00c03ca045004094500c1a009800d015442c0a180240301801340845031540250440311414002c030344940082c407110340c0320307a00410103041500c490708010601e40c2c0d92200080c240201c051400719a0515500c000c1040e1204808804050400b8010310850080c10350304040712220101c0c1c01800150100000b400181c4107201511880c50030403002e0341040060765907401a14001440c010018030618010000d9542c41240c0580042032802c109400d001003140080c9148101c2e0300c41401800c1609101060b038841030200c40c10300340401c0005d00c40396109a11840070789010407046205e41e18060010030701e0300d0700c604c0392805950240c81c0e080c0362030495a410780c041c28078800c8040b141c2c09a01202c1070400900c95070300031060314003c0500492260a8071a606c01c4584102a40456000c51400c2c00180c40000e40340d4030301c0341c041c108020079542d14034084031500d001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 920612347 1250 920611097 920611099
    0x30b010c0f0222050610030e121c0204080d030f0b030a0b040807080c060703061e05041e06120218040206040e0907090c03020403030813240221091c0f0e01030b 70
    0x1034141d00c504035018903130205004100803075010384184e090711170440a0303d001c10080880c0d500318007040314080901d04020920040404452844034000486040c00ca820603405484940c100103850000301d90706214400d2510100d09013004119000381c0800c0e610bc0348070303030010100b1000030042024042180165048143d00c0219640c0e0382400d40c41c5075851303c10503129030001c41e0400f000030500e000314641406001c0801c4002f100400d01d00300c2000003078012864503001d4503404483c5200c0107840380c082e050261014111084402c00c0600c10300009500364080d80364008051402e0000507520a030456044a0741c400403003980f03803501d4888605101643c1d114110b00c1c0c1c542049603c015030103402038011640280c6903242c01d5520105001e1010640c124028842290f100d000510031018ac6005601c2e281111001820080c0003030300c6030810300030140d54214202c00841009803044081143c10310103a0342c4049072904003d001006040d4188000b82082404031903804a00c05900c6603000c00e5031510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 920613597 1250 920612347 920612389
    0x10060e031002130815040b0c030406090c03060c090801050f0127180624090e070b04030b3327250e0307090e070b13090c030b010c0f02 59
    0x495003c51030b100000a1241051901860180d00c054055055000c2d11a0b9080500c5109079520322034070300c010341d0009108980f410765462101c40401e80040c1000043d61103900c1c005038003038003600050682140c1e940301091581c1003034100704089400c0d02181c0d04480d000c0a41c0741d0302e9402d450701513192010900200a1072031410001207101000b1807114081913000300d804014410820048a1050603021680701007941d4100e030410254904c1e0f40442e2000810a00380e88040e40c40301c0c04031429610035481030310441800d40034040207546210880000d690803107003480c80c0c0104802143e482c403031400b40241c400d1b22a5140c2031280000b0005140791484e41c0103440c41e076031619a00100b245590440014004240e8060048803240500369101c2a240003c004200c15444c01480c0c8000d0010710550111380d000c0c400002400c03005d4503001d01460807000c107007500028100702690301142d10400400c0c08141c18000320b020180d80003800c070160700707400111114445145001081c0c01078200c48070001c3e181 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 920614847 1250 920613597 920613607
    0x5031b0409021f03051005010f0804020a09140a06060503040312091115071a10030b040819050408010e2e090b07270e0708090f0d09150810060e031002 66
    0x3820600a01445a60130b8408000a0700c0740d08000c44c0c00420750044602044040c80d180c00d086006070407043c1c0c0244000c0c4442c6000d80c5401d010010707a56082c1c800c0f16800545028020307803a40f03034010400540454500700d81035140c50b4800804110007400411a86070b5034042250500100714001c440840000d890010001100030301d5034199489841d0aa4104003003c554027001454408100d0042c01c2400b1501029030454803417600d000c00150003101c0700a010400403040342d1600003c12409030060726090b84540c604050503080d01c01e82c8458524036040822500c40718a01880701d41e00841c410320004000d04c0c0344a003001c0081a69020140040c202c0c401000042c03980a1200f00e00c01641c5a1700b45500d421000c421074880a036400f404407000046800a1300701d0b4441c0d0783d5150311410720000c0b00c04030000d500034141000c0301800d1250014003e141c050241442441c1100706c020554030303001c00140b4105602d20701c01c00943c0101c4040004403120700328956010001828801408441150740b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 920616097 1250 920614847 920614879
    0x6060f040801050c0a080a0903081b0903120408060f010806011a2710020f060a0203040f0b090d09170a03230d060306060b070309060c0c0b0a0f02070b0405031b040902 73
    0x140d008481c11710005121080020701d1040e03c0e000310f0740c0701c0e80e25450b901034a40b200f009045901030502c607a40340c40c4009003d0840702e0356040003000020583d44466a0f55942010306890a210000b40090140c024000040184ea440040c0d6a811549060403c0c0740d24501030200202c07030301c952a9031314605c1d4148148a401d0030340e00e14001419100440310092047d0307400d0800da84880c1076200d031101c15000080085e0f4180c0e5282c00841e030262081884000300300d007594404510160a5404100c1d075032107c02d00c05c44058002c075003140034045801d003400e01c07020b051008558a864501d001402c02121010394510711912291440340c11841e0038815484021809910001f007000c0c0c40150380c072600705000051010300c3c00003103030700654065a0381c60b9071a0a00c502074a42ca0910641144c096a1032030b0f000503180c0101000d4502c1c0021503641c4c82501020040007440c010058000082e00e0804000c02c000603500020341c01000704000d842d41112030f020400007001400c0011020390410304a182c64180 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 920617347 1250 920616097 920616121
    0xc0d0b07211d010f0603031d030c2106071b12030e03211515030c0702040507021006080f031c090f031101060e01143a0308160806060f04080105 63
    0x1c1c0c2c000c034002008031000c3d915030002a600c1e54800a07003c80e2001420541d100c4107040c41234004c000c058104e41e1010b14100c00318403100c0c00c402030040900b02c1c000c1100c0e01c0c5003050002c142c02c40003610308103405101304000c100380681c001c88000d0800e85042c1d404814140a90031003018964400c080c1c9480d8800340130148a8000e2040c16032205500000c0044c00d41204801101c041c1900a000c80f060b03901d401101c800a5403024040c111084c40a005420060740d035401051721070704442d030140c50306078540695a4140e41c2c0a82201d02d407500302c998464102c0e2400815640e10030b0044800310351491107010365100070045020090184800c2d20040410b0540101c1c0800c0d00381030f800c1c005c0201656503005049401030a0090010741c1083c15032603e060300d41035403d11045180c40d44e000080c600300510045000078010002c49034980303030109075018190890800c551100c0b82451000c403000d00c0e4400200501d100406952261801160010f8010300c0031003502d01a00001c8000c000b1810a00f5040700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 920618597 1250 920617347 920617391
    0x1209020a170d090b0a0c0f080f03070509180105130209190305030a0f0f12051e010806070e01170403030e150903252103022203050c0d0b0721 62
    0x12828048001980c141004e0407500c6184a07960b501203007545554941c01c410211020a558041042c0500102590090011405084280c4805a44200b81c1051003000010440c0242c1849403003401004a500c0700104c00c024040340220050381c9544a200044805406589100301d651120001208018000004049a81490700e03a80d0507903110000c22038000381215011000140c405204134000025034210940110449113201c201000001d901040114240c0c81004540e10900910070460340105801031014000c2c64240c16a01780a054240c0920014100030704066a8014040706240188124903105c41441c10915050a1900302c40799039800584072a1a1914408280c61402219446080001394404a03812034051803403024201000309000103010700da0200503481c3c603142c145040410340d03c0c10f41040000a030a40c00d08525010b01c0c121900e000da85e030003131400e000c240340c442110b61100b913610f4801d014104101c51070340e64040507001c0b4901319080070b412600d00140c01e40401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 920619847 1250 920618597 920618623
    0x15061b030c010b04062112090b160b01140d0b0903040e040303060503070e092d010903050c060718090b0607150506092a07020f0d0b0403030501080a031209020a17 71
    0x10102ea611100c41c024180e4000c54614072101400c6d006000103280c1d0121254407048030b00304919603a030b6680140c4010f0303209100907140c0020022460003000041ca41d0399001d0304010204141090607900410110050080003400c4014141d00160748003404004880c0a40010265149036050a00d4064003800090044030311034050143d0200300c00715842c0c10306116008410042c0000c82510096207a41440600703101000e580a142a1540c07d500f4003840e04818403d9903a02d40e00c0f00602c403154205003024001000700807820310300d2405040440c0e540380c1542d168080c0020500d9000703002401d0b500ca01c0340000c054220042d0100c42002256000c64400d1005031081d0b1040d9461248400784008000c21904882c86074000a60054034000d0117404d400f031024001e807540c0d40401d00050440701101808840482c1c0a804000030107915001d0180100480750041c00300e0300860381c0c05802807010240300e0741929a1000014103650710714026400404130703062204a880c0c01140903644505a850940d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 920621097 1250 920619847 920619851
    0xc080103051b130209010e09091f0902211f0c02010c02060601050301061b06050c1c0605150304020d061514090f0705071505070206040212010515061b030c010b04 71
    0x81c41601407580480644180c2c0100960107403a203402128009420401040b4100214005030154903103485018601600f2041c0082184804440c6040c000d0801103040c0341065041c5024580141c84a0100c00c004e0031030404808154501c0764101498194400741d288003803d200b52003000d03a81c1c03141d0f00410380542c0750b9000340500942408180c2c2c1e03443c1c060b034940d07001036020001044110f05c0b408041d038002141e03102040c012400c585522068802c240c405070b001010000315480d00550b00008100208001101440034a00c2d00d00004c5e901011010702080c0030b800000007408666410b559007030724541c0300b6020880c010350b00c0300110b0788200600601620840711198010725241681c03070b90f4071485020800135200d66550100f00d542c0d4000580c101c80d07016400305041002400c1e405410b1007254180d0080034645024010054401c5a04c1d0300c00480fa4500750a005050100d42210040c4000c00d07103c041d6510750301d00001c0300c0c1c84242c49141718140004504a40e1051043d0071082910f0000c84007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 920622347 1250 920621097 920621113
    0x7020f1002070209160918140412020105010e07090e071101090b0f0a0908040909030e0604060f09060c080306010c030207091103011e0e07031104030209011805090708070b0903010e010c08010305 85
    0x4075032010744031845ca4002241e0781120030800c0c800602e24996942005500128040105500d1400c0304841690104c98520750414100003050382480765a0040c403612a410603181003206000e024500300717008a40c80903e0103000545000e008180b4001c0b00c02e8200000c000814443c1040c40c5031040966140c0707111090b040c003040d4850803038001d240032990441e000a24103840c1564400051500c0c0c1822002d00887d902078855a40d80c0101901c000c207556103924081c80201c0b83c0040c00c161680d0072000078450a000c018001c10480b405881d0b01c000282800c21400701d007410240e283c800d043d072101d800207003401007c14400b1034100c040c5040396070061480010140446250841c200031f402462003580001e00090021403190300b1950f00980500512480c20380c0740d40219400e0030007600310708c0e04602d00070429401d40b422407203129030113401d48020300000d1f0304251f003280d10341ca503600c220060301502196081c1127640039402803001c03071610300082008120b900d00280c601d000074071055406002d00f180c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 920623597 1250 920622347 920622361
    0x90b0303091011120a050a09062c0d020402070b01181823030f040e0115080f150316170f12090303040b040f0512070509180c0d050c03010b0118050907020f1002070209 73
    0x8240c0800049001a42403140c41c04d5000442d602b5100322290348203000b140c010000d6121383c40204580e40c05502c080140358101a030b5109102501c00411012078945001a900b9041c8c809100100550101108080000d00303002c0310100c0010358a0407050b80400183d44c208440c00e8030050040318a501c1d1450aa0703039840043c42d040101400c42c08012450107000191441c402c0040107074003050858160500a421902292a00c181c10040150b031a12a80c82800124504003e4900403a20440100076020b803030106e00e52505000144bc0c5201c100c04500c0c0c01c031a80d02401941c01424900742d83c0703034980f9034030b00341994540658400e0700d0080c05488481b404654001c5542415504060054101c1d5101c500f82c103904401e9500108059000d41b99444105e80e4900344003a4116000c0e00c01029580c90481c10542101c500328000d03418020320709d03003244030041c120785c941e0200d85045880b4003503079030b503480305034106001784071400c3c45401200120140041e055010b03103007050003680c11403070f150340701c0b2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 920624847 1250 920623597 920623607
    0x5070909110c0601031202070f030c0303080f13020103110d09110f0909150711010203040c1809110f010c0f031806030605010e040f0b0409030801090b0303091011120a050a0906 77
    0x16007402e010b5000f10f0014404201012655040c141203841150311003561130902030200000ca400c1103504a007035040800070300d9400080c50350485040d0011600c5828580744660201b4802e88000741890380710b9100703140281d203080036240d500500e040c1c14070802c1c28626001e440201040580c5200d1030490416455505013951510710410242000b4090034500e2030020344024001003c0310200300c132002100c0c140e51820b0010b1070080340f1600c800c880340390034502020540507600b1201c1c030b040e41c03a250b096000300c3c189500f03440c0c030a403060312490050860100100d55101542e0005091150b11801c0070301016130010203403080301e07d55800d890b06d20351a4541103060b1a0240b003030300e00240581c0000398041c80c00e5444501c640314002c0c1e0010b8682c141601140988180000503404501088010000e80d189401580c0f203003413048000c0c0d4988680c07400000c070701110f42520102000074041944052043c02c00c1003014030030b00c0c100e407207440f1942c00b0401031256200840b0b51001078402c10340054030314090 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 920626097 1250 920624847 920624857
    0xa15020706030b1507260c191106030c0307020105150a03020112331422021e0d0f060806061e040501062d0509060309100507090911 58
    0x55028003602071824104401500b0740c5003500d036025089401c81c081c43d9080100070800c2034130441034202000c10101000051020420352111007031410032081040c000e01080b008002e0115414102c48c5a01c5403e100781000c200342056a0002400014491322104901c003440c0b250682d64000e00099480f0a010300d400c0004180158011110b841d00703000541c054001e00780e1100001c540022103440ca0b4182028640c1e01d803448500e0502010a080c0041402040640c060312488500b40310703045e071520214000d8100d80b610046010f0440c0c4084100f95131940484400a600c0c01507002c05800410190740c0c0c55000d81c4062001c00e28062500800c6511030051f0f004948156001e046e250f914030061254640100c05250180e50800103000c8180d40c861149901900c444e54412025456001400d00c06614842c1454002901c6c4001902a180c0c8001200c00c0380605480030b85c2c82e82c660307042542c60003000c500d51040707407030520080001d2107500100c034004403a01e0180500554184190240c0e00c0d00c29 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 920627347 1250 920626097 920626139
    0x81e1303030e21101d012c030705060a0b06070606090609050a090b04140c030105010b0408210d090303020405040f09051603170c1e011505040b1c0602040519050a 71
    0xc000d810444090305a4010a05e103103d112151a1104d111000d070350854112110b40d4000b018242c3c00c0e403120180c080f2100031660076940086181541c40d80301c942d9a040000c100c4c2d51583d8848603400c03801d40700c11040d01e5030b041e4850410b00c80c6076110b403c0325000e401c440c010760a0780d900c0c02000400070441e41c01816825600100c413101d903515a91620f40101081003c0800c144c403840d82080e030749850901c58940245074081182e61114141066541450400600000e40d0000c405840340c10040d0b2908070303400c100c9001800203079010741d0700d0242c2c0603000710f40c00150b00c84d140c080524a001d201d03030040707000b8900c1344044d00d40a0402580114801607180005049030103000350002040d0a00001011009544d2089a5030200900c0005e01282d40b4244104d02c940d4641c041a160b85a031010030b00d01401007102c040c012819503e011406c0b1048400d40a0000313401070780c1810500041e40c0c1118050000a49546500b40d002e01000040c2c0c10b0301d10038203010700b084520010f8100007145e40042034800d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 920628597 1250 920627347 920627353
    0x30c0d0e01080f041b030507051915050a090e1612110a0c020303131206050604060302090a15090606092315030403110604030c0201030c02060103081e1303030e21 71
    0x80e01150f4a81c24200100b0450301c1919036480e4002c2001034a4074a03000750300c90001001824106001e02c000f0481910f881940d02200d52000d2000c070549001d464244046444c3c49921580c00500c121070640f29039000904888440080c000d440340d1141c01c903085001180c8503842c0203081c0102034404c0341d290038040312a03000c0911a115426100e420a070040900003401c403410004c082c000d000029210b03500007201480340030118020020303c0d01074180e101604903003c001451641e004a64003800c001d080140940e07981c0c0c0a020030040c11070000303002c0e0024040420919480310f00291444545025075001005851190401f0b0f41e981c0104451110b8040d0090a040e180d00031680d4150300041e0003202440210304000c0d1131020100440da1140b03000c0d581d10241004980005000c440c080041780c4110b4000d07000500200b00140119540c2c1911202600c40b2100d85514072009402101210f1102c1e400444002061603442200511201c4044030300d400a0340f01082103e015080101400c0d0150b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 920629847 1250 920628597 920628601
    0xf18090f19020a0309020306150901090506060910020109061505040e0105011203112a1c050c010e010c02151b03031303080a0621060b060f03060d0302030c0a05030c0d0e0108 76
    0x81c641e9000381c040301c0034500f40880d0004496000a090002c11031b10b4040081024011403928609400c0841c0100b982940400081c00c014000c07031020301c07460094a0140401090f4003000350320035030006c01010b030841010082034900340032010344400b052080b0340c4902c0c1400d112100700318061103140c4c1216501008003000045a54081d554090451001ca250707000d464400040c0c45a800d141c1c0e810b1400182d10022064084810050b04000180810b0803080700d07410600d0000740001480400386509080c803031a146503580040320030a101460094006450240224050000324090141d814452420310010421813143d1aa20b02088403940814110030b5038460100b802200e12030f40000e000c5202040a40c0c80d003683d0f035002c0080000180350b4101d00c86030f11051040340e00c110301401108a1b0300343d2810140058140c041e00000d008144284207503400744007058000c01c00c9419030080d100656000402c11306116890ba00300c803c107868103000b106003400d034140c071403580d040d88054145c450348126 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 920631097 1250 920629847 920629891
    0x210050a020714180705040305010c030509061911040e091e060f0423030901030b060414040e0304032306070903030f120e030f0901121b140f18090f 65
    0x151007070002d1960816140c0103898000c4816851141c1700d5a2951525030343c4034910b1900318210f0300c0059a0b14200f62030101440b885a1012030169040034074000001510486030b10030760000e04030304020401c3d0f1080000c0004240c10f0381d032500c4c3d100f1000002030b9041449060744080682c80c150910003c075030000c00014803c1c0c0d00181580350081d00a441405000ba01101408040c03c01540240d0300e41c0d00c00b003103400466903d0b000c1e1134a00f40c0b09448840c100b80c50500402546246101510306c12601c0e45443c40071000108181c400a41d00407165100b006004081c0640120f0032085070303000c50040c400041c038910b000340c030198110790303040d65281201d00b01110216400c2c041c450504100c15241c0310814079040e0100042d101c2000080080d594907048000090603a00104044503402401c02045158543c02c0300310031403295210f0b0400120354210f0b03104841e4184100308180b08118004500c041c001000800c0e040070402040d20100c035207803500303c151a5006405c8401ca200c100300300c0303406104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 920632347 1250 920631097 920631119
    0x18211c020c030d0c0521030130031e03020a020a1103390108011404051f0905061c0f110a03060f020d11070c0b09010e09040f0210050a0207 61
    0x101a0251055030101114140040c0c20704481c640d100d40003400c0950410144034080c0204145103549650300004540c041800011601051007902400301201c0c40b0204444424503c01c50b513000000c4600e0700030982850094046450081e8041c030360000c40d40000d020034024401c90703146603081d800030804076400c0d0303590f00900e05810751129014014181c042c540251109103440f01d00300b23103a01c4140c1c50991598000030034488200302d1410400d04100401010a010500b100d527220103480129081e0780382c19100c13043c800f0044030300c081b070310038030707500040b400c089030300040c050312049800212109240b0704403034030312103000d401608144690344003400080c00c5494407589007a015021303006442c0e590326017804807045541109155500003510030b1801200b8451100c920950303071203140c01d09070745e82c0714032103452050b024120850b200010460141da008403042400314000803e85445031a2618040710018024101240035401d8031040c0107046008100380c0303a015101d41c0c020a0854507040d11500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 920633597 1250 920632347 920632393
    0x7050a0b1015110d03140c2206021b100806091902070c0801110a1d031606021510180b040906020c06180304030b010e040312021821 58
    0x840501800000600c0960702d1034500c60b0a001c0351540714000c050b0140e26410101803403580004c25140c0903030100810984100c858001e0586a0380c507032661140c3c19181030003c2610880401810310710000540d0542c0081c40001ea024000044003480819405102222402d0514000070030b0b65a8002070080c145120010b510203e00020901d0400240780003400f01d074098603054400001c0040300703002c004070074014400c50325a41c0f0511850605101401021420301d00c50924102c414400400c4496408004030362818a80c0c0000c807006c503903070701d502940c0c41450411420341c10840400291800c5142000714080703840021520800c0480030345144000d0a100b01619840b036699840c15000c940c040c4098400900100001d01c0f01c1e08014846000070f035a064000304440d4010030081c0002116413104074116041c4140c25084ca450343e00e010703640c0f00c80bd440031200462001c5003401d00402e002c41052190142610800c0700503c1c0c162403c1d460f44081c68625555a108051882c48555613041241e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 920634847 1250 920633597 920633611
    0x61f0b0f071106041e0b070206161110030e0c030c150703030906060f0302011e020a060902030f010906021306020c09011401050d0c020105040b130c03020907111c0f020307050a0b 78
    0x2d120b00d600e400005800d500b10340c011400f914940001d03030140c00c0b49030f030450015000b00680d580c01c01040c2d0340042d20522035240d60300300c01c505001d1070a00f004400100710a07501401003880c00500640c0700018000c2c44051500c02c0548140e0903000c005060210303a4202e10180500103c4101c610f8107a4214103500c0920202d0805659600d01c0c0041001c51060f04003074200c910241c040c0d94914000146090b0380d17900c00080c0307040007106409010707030000b0b80301702c06580c4442c003c115a080740c00003a003070803103006003810503500342202841040541e40c0101180d581c0034080d8100c07a5207501c000c903500d88003402a0303a00f0440e00001071183c030304000211400700c001454040d20f0180d42c0c5a4031000c0c3c91803090a540940c2d141c0f4244010488540c080c242d009401201031080c1c40b000340c4555030101d12910010740a06910700104402a100d080c0301440c08120404484c10b003e0000c060614080d0307000b1880e400924100c0103440c03c24400700803510f5040e000001012684071603100e404107a0382c007030318072 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 920636097 1250 920634847 920634863
    0xf04080309120c0703020a050102030307080a11090301140106110c150903120f1e093102071103070f150f020304050901090f0506041b08150909061f0b0f07 68
    0x1c1a1004400c80042c4444030300080501884e91030b41c41801007a00a5400203419908140200100207511401d895804100c0d000f01040805203102010500e104a800040c0c255003032039410400d000003400054121a250303582c1c0c80c0522286030529444004001c5016800740010302c02c0074044450b180a4201400010207803031002440c03810644040e03001034803a004801001c121413025000b1100110a81d400c0901040d14040e4071400107900d448a0382005e100100c40140c600b0b0780100c020840c0c00b1140f80486045542d20820b040c01d08080709400140f500c40e12402d00b0200f5003954006000003207038440c45403c2012841c5400603214181c03403000d030508610060000148554038440404c0c02040d0b140c0c0002245250110306c03500b60381000f08050301aa0038643c01c05244520810409200e600c1031801007001c0c0c403080c541c2410700c40c0c410750055004e40c42c0c0d414000d20784004549580610403143e05144010304024681c0103c035894032403140307040c03400d010007400e507440300000f072404a10a0b108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 920637347 1250 920636097 920636113
    0x311070b0901110c06090c040515010c1515170102160b0705070b01060e010305090c010f0c060e030d050f10060c170c01060626010e042d0f0303140f04080309 69
    0x10fa007460b0850044d0307140c19406134003444a10f070001e0166800d00001a1001e1000d0300c0d21580d181402d29240b8049810080d00828580520100110607001001b00c01400d0100c001c0c661110b80003040c440c040c003210090b0041c452158404144200d4101ea14846446085c070701d00ea44500b030005000610131130034800c0801c0041c3c0001d409404180c0030b4019602e581000b290240e00040c1242c0c0c0080099203aa0b010000b0700400e0f0313030800c90328489403d4600d44451140024a802d030040c040768082c80f2810311010410301d03914420390308502d1080b0b000c06965905980d070440601d010180300e1180303802107030a01034502c1c04518100c00c2062180c0c0c41c000c280f803078854510f04060844180d54020300000b840c054503900e085c1c1c003401c214205031020301601c46040d41090b40700700400c580540000c1c5640000310181201c903103d2240b020a103000f54140840441050500d03c4642000c070f4000c40000780313008400050210709899450242446644001c2a683e07260b44507145940090801d0f0454420084 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 920638597 1250 920637347 920637371
    0x15230109180c030e210a030612050604110a0b030415020702060d0e0c010c0c050d110d0c030c05040207050d18050a1d010e0c030c210f04120311070b0901 67
    0x100c10345a00d0244400003118010182c0007401c550300c982200c8225085619142c500110039044003401030340d00720700c113a5184010441500100a29400904070000074041c40061041c08a2440c2c07107140140690b26000d40c051302004802c0d180c42c06400465202400403c02040c118102040c032130404603001440c05440703030000744803034000704113284d03485440d00205281d10100b0311920303210080070b083c06032051840350382d1b2959144450003a10f0050310b9140180d0b051045d400499200824085c00c00c200b50ba5040c104400030400302d00042d07600c503c02980015103400d0920850344043d8100000c0e000040803860120750810100c0e40c81040d606400101040070394030041c14078001c02403501a07444c000d441101c040281081603120604d076000d04020044c102441c030040f01e1b889401614000c0d922004260a0701c00c0d889499100006010040200a070b01c0140301307195070040d030088904100100304044100c00740e0784481c03912602c0a40920410700001c440b60005900906180d00111300300b50452 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 920639847 1250 920638597 920638619
    0xb03060d0609080315271504140108011b050d020702010c050f0706030b03030a021f020d020a0504090f09050c011b0f0b1f0308040302130b030604080d15230109 70
    0x40400c3e20f00300c4000080c4002d080d6140103100b250b400a8604242d1264648010b004020310400391002145240b00040c050f0032034206c049045800050007006484441d52107200e00203802d0258518039032030303d801c0d02c440c0c0ca4000b00307081801039141c0c0c1d40c1c0d2814a5007035241c0e000c2d400104040741405542c4017400b000400c140807103144150394070020001c8614088009080d501410341450190f0020820352402780d81c080303030414003050342d0316207480142e5000f00b040b4000c1c801c0b00503a01100340702003078512502d60700400038000c50b01080c038244000c000b1181c0b01d43c00c644080b24000c01541c0485140380c025401045c03110200302509909801c005503507150b064503541a80411500306584a007080146280040b07c507a484d0021b001c41e000c41819030b540d4100b5031280b404081e105584d00710000c0070388042a040002920005000c2e22083d040130302e071484d416000150007103181410810404000b03000e90400b002141c502c09502c0d449515031241d041000ca9541d5000c40c10003d85e6000403410360806 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 920641097 1250 920639847 920639861
    0xf09040e0102030a0605120a02210118020f06031e2715010b0a05030c030c091816020c0108040f02031507110607050306030a060b0102011d0a0b06010203040f0b03060d06 74
    0x350002607035030718010180e0400c803000e86d04600d21401303101880300c0e0040340005030400d2850307050f1260801447d8444800c00c142c3c4d0f14424607540c035828200c54a11041c41c0c03201d4140403038400c1d10001c400850120812440c6d001c1111180c2d02e120300306510f1102050311000c1c2030f41010251359250788a929520302901c010700050300385000c40c1e11002c49124400b00200582d8010a103e00126080c58410080104240700260862001d41c5021012500c00050b900845404505c0140000e021032410010b601e40c1c003000311200705c0344072542c00e20501100c0c008a081c2410010580d1842e4559130356a80d2610340b01800c04c0166010300c51650b1081600e0740142241d40500e500c1c6c0c8402c03440c2044a840e03a450400c004262204000c410320900c2469180050980d14607580031034045103010340c40c40100d004080d03841c0000c91019001404907110203000c2800c0f40a507008200b180450354500005aa50744540d00c5495000800b81c0420031500003034201071600400c00514860715004140c445100355200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 920642347 1250 920641097 920641121
    0x120c20010615090819020604050d060c17092d010e1006090c05032712070203010e0a02090619090c0e101716050702040203090a03140f040b0f0904 64
    0x140d03540502007440105004140b401c0a07203050305509040114440e182c00c001010703c0756218001c000c1000b199100c00a0341d0240002034400020b0892a0900101030b22880540d0701c04221407051002d0540302d0041070a1080c40c00384000e005908011898072104c0c01440042034240302c031075a031569040c00a0080e1a2a8540300b001000c1441400044808494040d844115110700d07050030101c1c540c0e08001078a500c04c141058081c40c1c3e203420301c0d400349440400c100c444418001c3c002200d0259424002800580740254002c0144012001480b90f83d1000400040c1d0300ca482e02c80001d1181c681051184003080082c14103141c205d588010b408143c0e180d03088008042945030a013480103080c1010700000a028902d0035100d20804c0c81e41c44000341002411030340300006114451890503008908550b806075010744119a41d10f000030a83d900c400c56800c089001800500d480c00082681e40255510000c4603600c15180500c0c1040a401302e5102d010218207090b418840b80006568500c075410040c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 920643597 1250 920642347 920642351
    0x3020d020a08060a061e03050c16031206050306060a0504090819120f150302062b050f0f0c0d18080c0714030102070309090203090721020901060c0201120c2001 70
    0x420783c041124645aa800240030084402d1203151240c806080501081d00e241c100090107894004040c0741c0c2e4890181c0350302c007049086c00c010007095880440c04400d80c6001300100410341d140c2c1d003050303141c480076201140d001e80348420030700803490194809501c691203030040a151079013118801c4010400209100302054041031400c2e8409518000c1c000310a1880c2c500300041190040741c2c41d840c68490001a0003040040350342003611102d0009a6840342148800300107583c094000b00700036000c00c48a10300e09000c8600404d00018051082900520b4401031050038002c8040c0c12034014280d00c1c0000e1a484150a41d41c0f01140800e0000c09484000801038503080f800d010f0164511424801c1c164043e0388100850400700354080d06003c15100490030242e80da464002e040c524081c2c80740c0101c4540c541d01c220b281d0300750b5010308506003404c3c42520a0003850781d03030700d4041c0c41d8100a5000a404913218503070382004400d00340c0c0011030208007410500701d4024124400403e80078007400c0d039112a9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 920644847 1250 920643597 920643601
    0x30f0a0615230906040e0604112205090d09050a030f0204060b0c010b0a0f0510030203091509070317031e070212130503070e0c071509050a06020301090b09012403020d020a08 76
    0x2042c070f4151150b000c030007660305104e018008000d1546da4600140040c041c03102d1003000c00c0d9540e4808040d078a500154541a05070003000c0c1c1406801480700341c5151003d0b1040c03c090101d40d9010b280ca1500320b41004107480031181c6140c41d8024640c0a4510499000703030740703180110b108402c64000c0c011220302c0ca000020b84034030310740c28881c550343c0e640c20a191800b0403031001c1001e941ea4459074500c1045510303001d620b076241c11f00d00c0707031130421001056a40d2004142c200514900c0008034007040301e01500110000035420480c40c0c4d4244001e5500a1a110022201030314075103511500d50380001013481100c421001104121034660049c00034254201e407840b20400c52850108070000c0030b06070400244585041c1120301554074071039070701d0040c410300d850a00002822466842100019000b42c20340c3d600c8840d034502f14009500c00d014110401d840c21020318440c0c2048284241038070064848002702075150382e9041c1400784400d425400b00b503001c00ca40e00216800740050401c079285904d4852141c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 920646097 1250 920644847 920644849
    0xd1101020409020415120603020f1314070c0c0f080c12030903061005033a0c170703110604030e06031902040308070614160c03120c1101050105030f0a061523 69
    0x300c081081b40749020741060414805a0b80b100c024010384003048448094190101494030040c3c90704008800105102404110307110380c001d01014149489245c4d4022616290340d103040c507806582c0140142540110034251030790030002803a40003445100216800c2c01b120708000b9290080c100c1303080da000c9031021000c100c40d040030000141030100e0881026000c0300c1d294444154040c0200704000442e43c4e8500510005000300740a4201031b402c85000d5510032007003c42000306030712107503044000a10361a1020800103001ca5000d0080350b156640349034000304130042000a070009031525180c3d0b0101c4890011800081c802400150b21411010341c841d401418070384101e03001d040c101c1403014094010040d0211070403480521800740c03030030030006846080c02d04407401d4245120044025140c62035a29056400024550782c0443ca90000d000350307a01d41c014140c64052040350240c441d400242c41200203131031030b0003841000d401c010501100503502c220a4040d010124030500070440e03038145040306 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 920647347 1250 920646097 920646107
    0x108040f111f110705150d110c0a110f0d05060f0411060c010b030709090201050313080d020d0902030609160b031f170115030818150301061709010e0d1101020409020415 74
    0x109412031b604c48139401500c2e1425014480c800c244c08185507101d04014001840b40155440c0600380412070351070380024034104035040d581e10515481411703d0030b5104410714040380001c018943c080080c2c0890b4481c04804805128013800803030f400040105c8000341c0e515600b0160402c06009000482c001c2c800b101418117114080c1c00180b103e80c1810442000360340c02c8401c494101c0490140300b4403100341ca050407013150042e500780d140c00500000d21520081c42c84d800a9038220b008900f9590aa2030305038100d40d5948803a0192104121030204c108408003510000d10352003906406900c0c200c80101030404002d05058001000d80401c0045620841009104032052001d06081091040d825529050300310300901803404041f030f0780020401c09a450b9030b50550121240d165580792207503100c0702c1c05805170301c01081e10300310140005c1c00244498014022481d10307003c01e5001e0542d5240a5104a071400d108807200c80b025074007080f00052040c0a440108000c2070044100405080641e0000342 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 920648597 1250 920647347 920647349
    0x61b090109260d090609330207031e0210110c1905030d02010c0816020c0f0409210e0d020d060c02031605010609110903060115140301030b01090b0108040f111f1107 72
    0xf401d0b440c7d0148800051000400140c0e0b17840340d110000f481e03658603030412803824101380c00c010400d01d06050040c407200340e403034110007945c3d100711401c0a60084444048030a400c80801001607035006c2c107401585414500002075002c0c4401140000c596110404603140001011702400140e64a603458502c41d0352011010340c01c00040c0c5000e040780107010318001e40c0e91090001c401d01c50f1944024948550b039590f0b00c5010215804034000c409030f00c9510411240241084038803000c070705104d000c10250310389101c0b00342c0f600794020500c41030405c04e9110b030b500524115042400317510081042d0070150901905600d03400d803145001058990900b2440810346002140301003030303403105010b10111070380c0224250341502c1c5100c00001c44850803003c1161910030690100200f82d03400800403044c054140003541c182c1d50804070a01c010400a03004440c00d406c2160082d003040b403404124030008240c10030b05562903074018a51240324803d02c60b001011620500c160010440b0007605145540303003800460 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 920649847 1250 920648597 920648609
    0x30702120d0915050c100b0307050415090b0111030f030a0c170a05071206060509150705060f0402210a0c23040203100b040305061b090109260d090609 66
    0x1000c40215000090b0814925002d100490544944102c0c4698452015118080b25220841d1170910700c2000c050020012070a41074000e0141d401e001c03070a410240602e024101c110794602c84501e190142c3e05c0000d2071401d003024104070314101b0b0603003044020005401298415404035aa03406c02c100e0750012120142600f409002c40740403400c414400c0c09949581c070002a100210780c1d540d41070800c9510094103811544800c2c40c060001ca5080d034000e0252144002c19144289210130300041c1d8a268010050000d240d58090000180310b00c1500904581151000d460801105c80141d942440c840045103205260303400203061800344003181d161040106000002c0c01c010400b0551010030200d45514101c3c00703941c00102082c00c0e200914041402802d062050a840740d4413450604e443d11020b039a00c40004031030140f100000c010348011184403020503180d8180300b519041d00382c5810fa568010703842c00003d22902c23503880a18181700006a002c1156120003106003000c0024102c01c1c00740e0412 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 920651097 1250 920649847 920649853
    0x708090705041808031e071808010e030a120f0911011b0312180b04030e03070b040b07030c15091112071a1c060605040501030b030102160311030904020301030503070212 74
    0x58482c2480002c8803600e40b44c1c1081c0c07500d64903525803e416100d000031a090001742d200d000204181d60364405000086080c0307074041824802da41e1801e040c2a240b804070b01003001e42003000021140c034042c07550f01410740c00c0568085004a4004d403080201c5250300d0013601e00442e02c0c0d0b1410121741c2e014441c5c44013071503e2003909c1c00500c46c544009000e002d50741a401c04d1030b56104602d04060100312003007480070342d2007111400c181c949480c1c018041c01c040c0c41c07218000c2c0718900f0049407822030340080c2e4041c8e6110501c401e0810300c1c02d8400b191000800d9100742d900001108800d080421640141e6038854000c1039502d006881034818481c11408070f0b0607001d401d401095080c8002036892100581d0440060300c4c490301d0350490fa0741d2035050310700350700600403180c50000c1c0024074980105c0604100c0328262420001c1c1c084110915080c2e00c29003400d000c0fa03810b40c00441001900540840b61444a50021a07081407581000b085c126032080c0c200751900d510102d00e240441c6400418012405054006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 920652347 1250 920651097 920651111
    0x406030902010e010201051b0319090c0f0e04050a080d18050d0801060512011716080615010503012402100f05010302040605040207020904030311120c130f080a030c02030c0306070809070504 83
    0x90860603512a4042303842c00c5000010800441c0080440b454040300c0311010880104035182c40c200241180c8912a06c2d201901c9000503030301c1c4140c0d0427912580c3c0041c041e10350f60341a030b955039049a2240d41241c0759141e6501c014504281707a042c03100b1180b031007040100112040640c1c0a010030710164004010003400308000d0130350315090307202c1c80d04540ca0359a4007107140c03019041e0541041d403c4071403240980310040f0700040c044400115a03004031140710f01d03248554542c2d4011032342c42c4424045c1c02e07103070b1030b5600c04c02e013890104030110086029503106a40c401e2400124000c00e80c2c04a1142102e403030389510040c0290f1401d481100002c1c081118214504242c641c0850308840004101a00341603803500e0000c00c4903010001c4510400050f82219440d24101c0041e440c45d401944001c002c07603486410120700300107542c030250187c82c1188001d0200e84101c1c0c0e8100c4071001d945e40101d030103010b420550302c096202004018004c040c80d8407061500d00c3c0010700079160074082d6200c07a00c200d0502d40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 920653597 1250 920652347 920652361
    0x308070b0609130201030504080904050c03070305060409020607030e0d17130807030f1e080a1101050a0b0a150c0605010e010815040b04030806031e010e0708060f06240406030902010e01020105 84
    0xf190648560a003408a19559141031424490080040039a0068103010822041c0f90034900114454052a10200065211642400201c400800300207400c020204040804680241c03125404c1044c01414031006480b145d4074400e03e80c070518800d403488040450011201e5081885003005455041c005048043c81c60b00c0303245030144602800f8040040400200200610180c406041c0d85e4100c1425a610740141100400c0340c0509080038045520f0310b0b0126841064502400201d1040184860300060802802c0e141d20321046504c070050190400707505001552500070705008000c0008512580d6140c035030160b040030f43d2a00d01c1450b480c03c61080000241c8604001e54029800d0f142c0400d03196601c00c00310703203842111000e441011081881100010030b05401001802e91500140c0f8001c0b40e41d49400756a802050f0384c27003001240300ca400503405051948240401518541c00e00030301c402120300c0e2070b405a0142e0046000203840340210025075070040d100c0ca400740000c0c80200706500c0d00b20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 920654847 1250 920653597 920653621
    0x2120c070303110f0316120c050606010509180f10060c030f0e1201090b060f03070315050a0912050403061103190f0e01060e01030c06020d0c0f0f0c0308070b0609 71
    0x3001c010140302c010249030008050410040c00324503000400c83c0d55078410084000d04130303400040704448499102440540c994424403800301441c0d0b0010050025840764401910644c102e402d20715042140300500d000c0040b001c0104e00d0045502102c11000c40c01d0a5003500c03042c2c0c01c1174000600748800781084070f00090744401703c040e80c2c0e403191610049050501c400603440b103404086503900c0c0e60821441070203105207503001b01e0140608941002c5143c0701e140c1855101c1c115488064000c01e440004403004c00010303042241d1180e07540c0300c001809203850742d031502c40440d01c1003140c000502c080740510400c942c622800c0c04005804030030504501d040ca079040400141811404142d648840d501e56402c4040c0e009102005d44c442c2c024016142c83c0c550040c00b24400340b105031003182640791300040c0300d0300100d440b030501e21b401d59406a501d015030311503103041c64071030008a9900c0d09010204c000b0481103c499000355100d2800180d0700c085c1e90600503a200300241600f0311501c504001e100c0031000c44 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 920656097 1250 920654847 920654849
    0x1b08071104151e030803010e0601031b021203040c0801230903190e0a03050105161b0c0b1308010c0c0b0f09061b0f0f0405180609190b1e0102120c07 65
    0x60b2048a0400c0f0710b10081d19040c02513540000d1001102000201e9030303503400101d00c2d101e444207990821030200b003100a11074459110103034001507000b007400c190142407520011503006020345441d01006581e6041c00d0300315011801c46201d03484100c456600c00f01c00050032250084003510056040c081c0d000ca5034100d52860591a1092040310312b41d40030140c0b2803e54800003190010004c20240c5400000030105448100019001070040c0b032142080c0c15103d0203ca20a40c1c000840c500501c1c00d000307180289500490b03100e0310101ca290400035007004240101c002c00300d070f80d5881e1000b00300ca900d8105003256004d00310920030390720307036003002014000003e041d6402a20b071454208a48012403900300a40b0600e092600c18050000743c910b04c2100c1d06004004840c01654160941d882c8030320689811039040d15a20b500000c02030114181010100c0c43c1e440c400313025000010503a2030080020850344100c40c2807480141b80051b90b51040da0180302d09140d00d020403015500d05440703a00b52544900391 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 920657347 1250 920656097 920656109
    0x201120e190f0b10060e1906050733270b0a0204093b0703080d020405030102070b04061d0a02280303030e1b1e011b0807110415 56
    0x81c100c01034050000c444400c00c0b0540e00800003085a0908821406440c44203008000104100b4219000c40781019864003c8440a0494500c14581400e4044035a644480e400756030031110185078640d103440480c00036402c11500604d400b44070404001100607902481c103820440f00c803a1a22003c91004411403404c65644450102c40d140c2c0c440c0c4803074000340207030303040388180e240f4020060b05030065155606814210200040c403009200500824542c2c0b5459420b15868020010030400102d10700c021300041d55104d81c016041c1900c941c0441c1c02c80c2c00c021419510340c046ca9090000b0300105108401d00c481c845407640d1409a45140e4441e5140e140c803400038029080200500f2140f40c0056403880b1640541464200031603403800e0080140c1800c21000c000d038010107031096941e0300032070f000c11041d1502410000325a98544140c003a0403048008203814001000e8400041854099070703801d2507440762505030340fa112241003800b0f81c00c0c108845180600d00e00881c00711040d1020819108a0301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 920658597 1250 920657347 920657383
    0xc03090415090c02010209090a06050d300c030f050901020d0c0f020d140d08070e130b19030c0506040f2921060d08040b0f090a120201120e 61
    0x828914035145104560b01100c5520301d40001c0600b0355034190000c107a8810220b41908460f200c05c0d01c8041161a00d00c01e00394440480d805c0c0c0c0e00051856000c44c10702030841e02d01008500c101d0812111106c3c1d240598074009001e401c080700c101134011807243c03611141454070505103006400040d6540715500c0d03501c010707c10401120030030002c1c1c2e04400d16032964050151710200c070140c03400f0752030316034100003c02181c050111451070242c0b140013101c0c8552000d07501c080403a10f8641c20710103d807402c0045c1c40342a035120f0410307111a484901d51684a05552502254400e00c0c50400d494111041e4021501ca844100010801684040989000c0d94880b81005203c56244061645034040c620150300032036401180603080652883c03010b05500c000b09c0345111850742c4400401c800307049070000081c5480c0c030501003032040300c0304500a81072405041c00e070716207004090400614101c00941c00101c0c42a03415400b0702c11540d100000403410010143d041c05085900e02442c0d4484000c500c0300d0207902 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 920659847 1250 920658597 920658611
    0x602070614251d030c03030c0607081e040f0615030b090d02031c0c0507050105041b081f0e07050607060f0b010203071e020103020f0c1c021617071d0910020c030904 72
    0x1036428000c402e5a1700b03000301140c2c0c0d04c401c00040039454150484084010030030981c00070b249008401780101400560b01c0c0d90718800d90f10384e5110710071044508000c0d100e080d500c0c0306900c103c00000c00c1e03030b40c007071401808a400380f450484442803502d148095200700b1500140240d8000a48952031200858011140410400303444031080b600c43c000e410003d4041d600b032500344400c3c083d654103031405101d04800c09400719502da0030880d58032030310001410300180304a50908104a850f03842071804050701c070260744415950320f0010700a42c12a0500342e4005640d004041e001c05c01500c41d40300311003020b001440c2040310f80d0320345062062142c070a03880c0b01f250885403501160701c2a8100c0701e0450350071204903110700c0c40c1940d00d40d5074021910034111180d094203032a07500b14000074030392440b900700b00d0b9070348061418480380b14401b4440300b000201e00d00c110708010500701802110480082c18100c007460070b900c3c0c040e0ba001e107452124100c4290482c41040421501c2801004a615900c0709940105403c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 920661097 1250 920659847 920659849
    0x170a0806150705030f04050f041a010305101d18010b0631061d0105090a0b0c070b030403050a0216180e0a150204090506040e0601030f0602070614251d 66
    0x20b11441d02c000345240400610000603510700c4029005071031050307071445926000d803000d00c0129a0071900c0d044040500401000b01036110b43c0000c2da003c40842c41c590b05c07a0742e586e0001e000d21085224041f4042c0d110b041007103007841a80b680000d64540340c0e0300034072003000c403880444e60754801c0c06000040301c0e241165400c1c52034400600d2030001c244001d981120345aa03643c00a00315980d0380b0340900c403d241c0e1500c0701c69030b621850a5403c10b84004001c1c10882d4a0100b01610b0307070384a60203100b080e010b400c00001315144200051840b441c0030340c641e266030315442d0701c0080c1130400e0b0794000040d844100c9801c1c056140598003041c0186e401441c0064401c03158600e0628003900800000e181e251401d601001da1403258007d40201c6410060600880d1074031020401560004030100d0480e901840040003c00d2614031010302c01402030b0401841c04506483d41000d0780c88842130f611010000740300b4071041e04882a2660701e08204070540c0c8a07181c410310401001540c0906040d4030b901d240c1c020035052 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 920662347 1250 920661097 920661139
    0x105090903160804060807030605030d03090507080d110609010507020a0b071b051f02090d02040504291b0c210c1f0606020703211e0c170a0806 63
    0x4100c0710070740d06007100c0b14a440d004000e684a40517410001d11400d01003000d090190003800f0580700000d0207441c41588840c0200d0081500b0b102c1510340d0303c6803442c00602090140000f41c100102c0d5598440d5030340807220b2a620b061405003250580b03a2420041248055010070700107400340e07011040003401d8031000c0d401c55050550790741c0c0d840d1408801d074030702d000c1000000300402d01360803414803c0e012100107840402203000e03134800b4540140c8100510f5005103803d40c46140d005108407041d100c5140c2e01d0038403c0b041000d1010721104400c41505000e09402c0e80b500c10742c0e07070100700000240340100182c134031520340112900c40121212084080d262038121328040d600400c244000729180c01070855211040b40103034218403a44180313040c1020850714800704401f81540d822030466401d50301030400804400382c1d90300c410f1003003044106140307000c0e00e0328450b03100043c00c3c15a22002d00060310b0424103456680024140d02d1010100500840ca03a042004103611a100300c031480040d0901a056620b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 920663597 1250 920662347 920662357
    0x1e0804080c03190f141b0f0a0f0606050402042304110c030403060605030a1a130215030601120e0c0f040207020315041412040b090307080d0c0303140403080105090903 73
    0x4080e0001150383c400034007800c280681031101aa41e0381c5180c8980d40800e0300c101d00a400c101440d11420449500c40c440e281e2040c3e25080c183d43c08840d010480d40e40603e0a00500510440d01d001005a0620a0104034020341000d000c0480b011881d052a000c100d4104c5103882111441d051410541030415903120780c00300c1ca11960907003243d580c441c201c1c1c40090316640140404c540403450000007164500b80003039501c07501a4454840101e03503244406000904070000c04071011180140f2080005171940c441030b149050340c0c10b1a00345c49041600014000a000c0c0e40400c1c1e81d1850030446058148000505070b4a09000381c1d81e440307a900411000c10043d201e141f1000e50107102d480501c020407400d50101c24443c90041c01150240c4416001103038403141404804408000180001d01910a0050003807901c224024110f940c5582d4510105041071004407400020540c111200024190940213500c00c65112031580707406d903c0c2558000d400d109060042c00d0003444044005606900100101c403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 920664847 1250 920663597 920663617
    0x110a08040f1a030c0901050d110a03020d0b0d0c1208130305030316021605040b2706010e0f310504321b0103020d021b0106061e080408 59
    0x69510341d01c0e14807a00c642456881045241007031080c0c0301142c41d074070b5015070740201c48007912546400341000044900390095503030f0300d074003d1351a0890182414071200820f40e128640d00c0250f1540e0001c42c0c980d0403910004921303400341003c4105500068401c10442d0240d0700c9a40000d88000c1d80307400c01ea999070040f803c01000aa02901010050050010240d840b904403142c15281c05042d0f0441240c0324120390382075440d484d040c1401800240b0f040e070040b4048000103007248851440780d40120b80c11465550301c1001d034211140034400c2550340810b0000395884140c516080c4103041030046480d00022680c545c0d890318490300000c0501b0803641c01e204405058540a12243c20142001d4030655a0340c05034640b20340820190b026030340c8200e42d160100c00039030406000483c0c102100c0c00c000f10410038005040660810905507015594400751000c40d82000c550f021089120b40707541d007142d03580d80040050021151107880310101425030100c3d10a0f6910b48841e542e00e592910501d64051400d4403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 920666097 1250 920664847 920664863
    0x306190e0709150816030f110d0c0603051302150a050f0d0c020d090b0706050601200106030506010e0c0a1b0c0902030402090a11040e0402190b04030506012301110a 72
    0x50b510942e421810b4000080a209032410f41d442c150700d692528003041102c00030b5601441000440c0620310780034101c0f4080d60407803882144c0a00003450701001010200c076a2908400c050092540c9071192945c40031000c0307480c06e690030303003500000c0c2c0100b821860f440030b0705000039041e12018810303030aa80d03c100350300300305a07140c1011609200240c80d00d040c032000140b19100158880a200b050a40101c030b14074841140392009544820014120042144c0e040c0040c54102e11040035541c41039030101d000c28800001c85a06525000b0308100040e8454032100a8900a105100310543d089403000e0b4103604140e280f100034103201244050500c4000391010f0054480043d0480a40c0c00840c0304520880d03144d1560740d524202241242c1e14081198018201840b00788011540c40300da454205000605401498210700c0003c0720180382608002c4607500003003070030010480e040101e2405400c0603c881080c10b00d00c81e100c180d418a444013214100310360481c0d075025550742446129840c42e004029 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 920667347 1250 920666097 920666099
    0x10e1302090307420f1214010f0602010509010b0604060818010f0c08161d0d0b10032f0d080c01381e03030d0203010e06090a09020306190e07 62
    0x2c06290704448040c5001c1d41c4040250008900e07134080e00d205100d4a50b6000f84641a80c1200c4071940c0740e00c894141030b6210025a9031911104071140204620681800300c281040c50003825980c000c1e03c00b0301907a041c104080c1481d5a908240e038161880b80c80d2403207a956039045108070802d12080c07500c0b075552030300001030b20044050b00b01c50038240031900c44408503159400c0c90f080d103e81040300440016511400d103003410f000840810795140000b45440c020000f1503c0f48201c3c1c2ca4266440c4c0212803e4460420030000154810405003c0000c0c000c151000390342603120400c00c0d5600c4075880340c800d00c140d14040118050075601e00ca05031700002c03c80044005080c02824400c260001d04080c040580d140903074041481120b4660000f8044024150b401c51104400365140580554140020b0121102e0900244065402040c14842400c0941058806d000c42c00740050500341207203003000f240501503140003402030f403c14114440c0180c04200da8041000514603c9179441c100c1c0200a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 920668597 1250 920667347 920667389
    0x20a0917070608090307051c0c080f040602150c070201050d110a020c01022a040e070e040b040215040518060415080f0106090605030a061503060f0905060105010e1302090307 76
    0x109807007621800e440788003290b1504040306551b0300882030010425800004003890703003400d02864141c850610300304101e0518055486198a8110f144100da9180b4046810440b032581007007080c8801d800c1c181020454140514005458461000f002e41400000140c0300030f00030880e403001c031002c0303c5071440c9030700c1d0240b45c10029140c04021a5050040c031803440360542100001884a9200002e5025400807038441400d00000d030a201c0c184000e64000c5240019401c522041c101c0e03c03031441000d495031103240a204111081d8030407240030007102070910050165440b905454a116890a14032801c965103800009028180501424124043d0040d0010340000009034040883c14040020301280c0d4541c046c80003100c80c0ca110780e40e4580d103c01ca140c0d0220b4417544c881e00d18400034100c585807050300e9841c0c210544030714402c060303d056a2a107506d01030003401d00000e805400700b460b00010344100c640018940c1c141c010f540403e6140d0000c0c2114079507808101f8200142084600c500c21b24081c11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 920669847 1250 920668597 920668603
    0x60905102301050909070603110c0601080d080a0b13050411150714060402030a0312091b05011e02070b0903030c0a06050907090b03030f0c0102090409060b040c0e13020a0917 76
    0x80c1100c1c00c016074003000480d6903d852007003e0301c60120742c8010516103203007445c201c01820510446401d1a50204000280508148201c1d03000c0c0103010002e04441c200200010040d0307400801c0a4412854070040c004103580d50344c00e518218100400214090300e543c01c0c4540010a0b07205c0543c1d02540c141c603810351002c0c0c0e1402400d42036000d21070410b010700031617072410785440040358005c1d45a04188800030009004102d40c1000c2442840d000581025a5461014403042000300c0c803004150310360200a00e41c3d0101c0740c3d2000580e20203000d0201c41680d51b0180d5a00c00f1802982121180850102c0b001e031130800507100100c1c2d03d0400c07111204982c0c14014007c20301910209514003682d100862400807900640d0f14160300a001985000640b6031007803000d070003042140c0380554003005a03a001d03903180c2c05003150407805400c4c00241c2c0180c80e410401202c0d100c103a00414017005020f1100c05581c1d10030b4140f07104948030005030fa10641100c4c1200d8848181d082516024004c0b00140d01e40c02e000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 920671097 1250 920669847 920669891
    0x30f0d021b010c0b2d0a060e180d0e060f07060501240203032202180a380d0206030106031a18190b0a060203070b0601050c030706090510 60
    0x148103064040d0621200450711980c2c1500f020304040000310120b20a52600201306203800d0307860a120310f0fa80d001031006582d400d0152041c62045440340e0060240045a240031908869030b214201c4582c0603810005032118015941ca000380b155104c18128551100000c403403400040501031035031194103240048c0184420300a5038210280302c01501c400482017080001c006400703400a6042d0741e680100341e83d0021004641d211a400b1800304800180c889a0f460710041d05c01e500c005116280400025044071041a1300031150b404549448440201d50400e040302010380c11480c02c5441080030101c1d080000302c081c000d4005800000015155034145c0c801d540310f20840c0c01c00303010102500100045205151316140b0f02030100400720303c0c0b142c014a01001c1c4c40d0050b1801080d01c034000000a00303040003036802100540c1001580c0010404500c40247d03102c242403c001d802d10b002810915a80d004403032005086554559034107003404000c00c081881501030f04014000349a21034107401c1e0000f40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 920672347 1250 920671097 920671123
    0xe030d0503090124031b05040e01051e061503060607050312070e06030106210b040c1706180c03091009060c0e010206010303120b0f09040606030203060112051b030f0d02 74
    0x81d003440001070b04030b2100104e01511008610801450964603403040985050780f0001c1442e41b02c1c0c1c000561503d45000d50500b80881800006141c90a46000c000d50040d810381055840080d001b0001d40f40c0d03840e42c03611207004002040d65102c1d507944001c156680b1400a02904a110108040003000007130300d00244258215036a581614404030280041d5002c04c3c0a20b00100c0c0a4890400d120300440407540308541640d1404030310081100041021100741010b482d000440b22440014102107402d45103801080c2501c12408421300c4480080741c1290281003092005400800300c6c61b090000c1000310040d088036041080004010301c0c2940003014501802e01c08501d440c0030758009036001003821ba04881e01a02c41481415120100e00c1c02445501c180e43d0380311001507211503c944802030003d219a20807180090b1860450041602d00751051380160765684200560200241d0082054001811410215241691540000790074591202800325540c401c40c001130600c035a00048490100e86 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 920673597 1250 920672347 920672351
    0x10090f152d0f0314181014070e0f1c051e100f05100311010207030609060f2a030b0a051207090f0b240708130e13020f100e030d05030901 60
    0x10507100690a8612000d580d902d440c09090024030715031078280140c00003544a40a48082d0409a081c038007c903a2400403e0300b003401e242c810442c036a90404000040d0000440310b4000210300c000014181400c002c21540d000c4001c4542c60041007410001c0700d0b4813100200904000c035080f4050076541b40306200300c800c06207041103000000032640788141c60003500075030a450100341c00c40d1200c0c0740c0603910000a0741144070705e19000010038418840c02c1200d40c400d40000c40e062903003451180a40394807100c07540840a500902080c01c5445021307040f800030503030801045e444150400281414510360100b5008806a80d014881440104240e0b080d00c424103c100024a03200c2a18012140300441e00d6400c102900c1d40c652894407911200001d402c0c103280600d182103040e40d11500a5040000028000600d040c0c0138402501d038810040d0307028405540380f0201c90042d400080d160045540035500a540b1002d140d0300c401e21403900c541191f003003d41120101005090002c0141c0d01c11240480313254 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 920674847 1250 920673597 920673617
    0x109020f1e0915160311070b0414100e06160c0302220f1503060203040c0b0f040e0702030a090e15030f0c040e0d05031603020d0603030c0210090f152d 66
    0xa6400010344410540166144c107940d401507409540100e410003a0694503c038548002649a45400040019200d543c0184003145004c00c1800004400c030300da80001d101d20040860b0302ca44036031082e00c01550300c42d00d06501c1c1804c0c0b03092941002d00581c101a40252a0405014907100552900000c43d04040800c10900c80d001b01d510089400503d40c14171089c581401c00c0020a555030061900b10380107440355004182d50b01d0007600e440d8010424948019800704082210450720340f5038944c40702c5071b400614074007001c2000003000c000c440c4c020344c000241c1c1d101c007041d030408210742c03843c1401c0c030080c0858441c5007840c0c074015a038801004000703100d20b0400586c17904d4142c010034040e944441da61076107801c41c0c448600d50315180f9844800141015030038010000090214000d0400950098507203685445560062090141103800c00030300b8041500001c0202c4100100d0550495180d03c6a40380080100481162500714507281c00d0007042c09002c0b03440240845000c0c2181540c02512030328084 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 920676097 1250 920674847 920674879
    0x1103100e160f0e01090e01120b0c0f040b0f0904060306020d0c0e030d1124042001090b0a1b08030105120f030d0b2107060e030c06030109020f1e09 64
    0x32007a441e084400035016a0b80d010385240100c061040d50f00e014100340c0189502d5500900c50100c09a12440c039a02c0e041006030140006140c805401560300d0442c140303000c1c005e40a000709031250307104035041c1000c0000c8400b02925800e050303400c1008014014026146d0b2030130014081c0d0813030f1829400040c9042c80501c0031078007884080c03409070000b4000e0b0a40005030001036034104421610403105016031031400c0000c10a4200404104d2005c4540d8001745c2010b0a010800e88009580e04000785103544110400b6030b0450784210450b03a074084807590300c0428a0007200c0000810154500e1140350380c0f24801000b2241001c0c0d0f050300d6003900c0450442411400031031b501d0350b502102403181c0d082000241e24400342e6421514554002500014942c104041c80148003803000c840d80d01c403074001d03100900c41f05901c0031308035000e603108800400100c692030b000554944810f20030394155a80c000f441d0580c15080038152682d0410400d582d0582d094440400d210715449940c003c0e10a54a8444a00d24 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 920677347 1250 920676097 920676121
    0x105070207062604060209060c060403090608041a0405011d07180606050d020901030b10020a0b06010f02030a031e0908070302060619090507121508070e010b0316031103100e 76
    0xa0040f818410200e040d14601050b080701c03e001d030090b140070b5002c201c16140d80d164007008104805030718009181c6494242401080a00d07070f90013036408c102041c028800441d05600c1062441150b5602002c4252a20f05e131280c014081020301c82d18140e80e18080d54500000440d4840486107894489a4141084507114003103038414068a030208105101003000c41a01e035014101070a0181400140307600c22800060491002c40184801039002012000070081c0300c14980e82c00c05805e0030400e07403402c060071020307489010710000d41c410075543d000200791840f4503840c04410085529002c1004088609220985a000c4031050b0054400e00010400500380b185000a200e403030340394005440c50900301c0c5000a000090600c03c00c214148581c00d641800ca4840c3e02180c0745180030001e0507511704000c0d581017806a82c04141c1ea007165070300410a400d61002104c0e408202d1072888160440580e10136001041843c1e20300403005400f00030010007880e0524641c0a0ba24040404801d0355521407032406 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 920678597 1250 920677347 920677367
    0x61a03092e0f0c1b0503090a091b1e030e1207030c05060f010518040503580506010215090706030f02070c03080d0b060d0b0f1c260c010507020706 64
    0x840f41010b031100d989844113005207040c1729605580c40e10708900c0024085821a41000c42c0459603074102c102e0064411861140b0040c0300d06120020780c0120350700b2014110030540c03232403d050722151103c0841c84284404880d40340040d900301c0d00d034400c90130010505082003008582901c0780b040400d80311407030302c14001e040310740080030031442050308480da03200c0003000717070085031544824400c0211001d2074003140055100b0721a41a4101c4001381e1000c1445086090b0010500c04894a20303841d55607c0c85a4801724000310001042e640c40d0100100d15255811151f200000d2000043c440c1c0304030b002c64010b0498819950a000d80903980707400d24200d00c10300b41c0050000e12361300700c200300044000b0b02800844402c0400003c60030103e401207201039209804503030358150340302030800c0d4514000691920310101a00d40744000c0d1100d0b150190703280c498100c0a0b1051030200b1011002403e103860304800700e103a2003512625030b456102020b001c1d22050b60a4030150041c440d0200f145445146401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 920679847 1250 920678597 920678621
    0xe12030103060908041203030c030501120f080a1b06050a0b0a082113060806041401030c090b19060c0b06030607090603052a04061101061a03092e0f 65
    0x9185910710303502c25006028400c0b0480300f4038814000014010701c1550032812403800303a2408603111407540b0b00101124416041408802d24000800c4045892001d4181005500449055075400340200c01e07650b400c034504410182182007a988070800c500f9402c940d014064054044c402e01c0e00c20400c020844a9034042c9202690008020000c14a00184039100c0b1315440a4068070b403040d96003a005800b10690440c0c00440c9141041c801281080c0c85641a05800509010f0884d415651a50358031a078034031481c0100c645514903a0415a00c1540e4400035240300c0841d10801c81e6101c0b8090308021181c441540c031403841d400042d00604000c154148200c1c1301d40e4a030380141d4103120302a4000e10000d8202500c04012000d40100b8400200400318550402541e40d6110f501d00b4800420480c9003030465503299041100400c01c8100f180d0380e0000c51070361481543d8490b91076059a1b8948014820103080c00c081d14000e60842c060391028100d1006007a001c20b11803540c2d2803034000306031051841c80e5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 920681097 1250 920679847 920679883
    0x10503010317030703141f050d020a0b13120b0403020609061618050405100f06020a0b0402130209040c081f05030c0108100b0c010f0c23031008060c0c010e 68
    0x10701200e0703100e000660b84800c080c01e000800c1404240700268122040764044140b000100ca1f003410140301a204400402c0b040300c01181d0f0380700a5010034103000d107505c00e00114140c04031b1080f00c2d411901c0035200203070543c58985c04241c0f0a50a00b04240c91080d43c040d005030180001103180c2e103102103000c6102d601c0382c010038140c2c5078000340e080350a4490a00d0001482c0807070400402c05580d140502402118031440d590036141c20310030b01c82c0c5595040d43c401001c1d50300803c809400207102c2240c1580c0250101c5442c0c00090700d20842c40d020340b103041da40d260301501d481140c100c07481d04400b00038060001c90300344e103c4030300d510320403181000817034050264164041c90090340d4641c880d50a07658024501200b4030080c075a5160340701c0c515003000341c01081c43e9445030b070112444411481140c0c484040c82c64004801071595600400c28004c0310320914213102c00000150114541988000040c03803588211092031070f16680840c0c550f005403801010f25400c024020181c1c3c9000140110488460035272 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 920682347 1250 920681097 920681123
    0x614192312061b09012307020f0a03030c060b060d0e100f0b06030121140d08100312030c030204171f05160807091a0903010f050106050f0c122101050105030103 70
    0xf41e0385464118190040c10415002c40c9507860420001c2004030140080602c5a1a02c0051040090581c103018045001c1e81c0200810004650300455019226412150004c1c0b0001d2850100e070391413207141041101b40d428810414006400002c08800e16403160740d0030007212050480b03610030740d290b04040075804030080c40148070501c6442c0503405600151412924a050035903100c0340021300881020350345030171400d8411126a041440540d100407402c805440e200c1c2596200070000140030f5411003010340d03c0e44150000741c0603504441c054003081c80e080d5120f04c07202615540d41c03054500c0050490007481c254601c04003441c001c05009859411100d800c000002000700c4500710024420b10400c203100400003116242d0400d01c02c0720381e00c0c0701c030415503c071512002d2609540324040450503041c5004010014680c0c40340a0310a142c1c9003284040d61100d83e610f0305481d18400d20fa0720820b5110000d180785808640c00d9102e080c500442d0b032044035030381e6650010356580c08248030183c0280400c00d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 920683453 1106 920682347 920682391
    0xa030c061e05071e02030f1f02070b06130f020301030f050f0a120e061908041a0702060f06061605030a090504061419231206 55
    0x7400164541d52140d00a11601c61104040c040409a5040c0881400b203140e2040216400404070f603201c100002e40c1d10303260880076042e888110408030324420340c2040c40c0250340c3d000390424030400c0135035200000d0080303039401828103862242d40c0f0f14960030388038440d202a41c06035002e001a00f81446041c50070601c4c2029100391061980d21103400c0000090100400304e52401c001e20b400000c40c0000c00c041384582c001e00640c00e0401981c0f000c3c0030511603008030b0b0076124600071b110b181c1071102c03d01c100c81c000d090103446001c0180c10050000e14108600a11180c01030b5000d00160310380303500b61030300403030b00c04807690112155007000840d030441d242d00045201c05440103c0302044680e280c0328030458100071200d1218001d2003503982c84c162080000c01d08200802013030b0440c0d1104404115445c840c0c111150340307144100703160310000003d08030000c0d40714424248020b0014520400c04 = true := by decide +kernel

theorem cover : BRFrame.Cov 920503597 920683453 := by
  have h0 := BRFrame.cov_init 920503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 920503597 ≤ n) (h2 : n < 920683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
