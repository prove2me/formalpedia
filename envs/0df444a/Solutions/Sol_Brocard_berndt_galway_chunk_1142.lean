-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1142
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:25:35.917981+00:00
-- url     : https://prove2.me/submissions/04eaf1fd-621e-47fa-ba98-f2e1c33217a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 205215827 ≤ n < 205395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 205217077 1250 205215827 205215833
    0xd0e15010806010602060f0c03060f0114040803030f060d120c020102010204050a060f03060e072307020405070c051002090d060e01200703030e01021603050d240815090303070309020a12 81
    0x6280c80c162076880d0300310380c07183d1f940424950502d103081e10328007008841040403800300e050507880221020380604002d10058002004145036510a0b40484550b410100a125441c101000c01d20b4102ca07084507161203804c00f82e15010049070039a6034803005e000301e40c0740c0207045900039019680180001030030034101a94500340070348080a1000c0580004c0e03e040d0012819060500340c2d58058a41035984410080d8000105850311205d404c140703050b5542804803000598540c01400e01c15480c40d80c40c2d81806081d490f046181c03a21203a5a0703000ca5005100404031601d034600386000e29a00204041111500140708500500c0a1004124007004010f040b1403148801d50007451254860f540403c031407404039000710b00300d001c1e40b031101c11568201030880340440d120320041e181e140481140010180500b10840b14038089031103814200c81030b50001088884010b11152441c00d020010300c03070591400c003110540741c2c40f0040010b0181981c0c5d4400c2c9080d500c41c0c94401d03010f001c40e0f87c0340c8000240142 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 205218327 1250 205217077 205217083
    0x16060203070509030c0d20031501080109050714030c04111201060e1c080304080a02030c0a120305090615091503010518010606050c032a01020a030c020705060f0d0e150108 75
    0x200c0c024020700c5042c0e60424642449000c48405031f40160300c0c1041100d400300a8000045951800e6505100d0090151200c0b01c4081c0d01900031301c0d086000068030171551522600700030041d40b000740705404c000120511038602084120019200b1280010b0100101c00340c056203019401c01c1c1094406a24008181d4640040740d02c074141108032100c425140c0280d00c80d0303806040c08000185803420600c040b60001d50072001070040c807032090041d00d0401078038481642c50240f40f000181d5006840c017014030344054041c400c90350404a060060843d03450500c5024150b401c2c540480c40c050f00400d00000d14211406010041c04c0780700a000303201606184004902c01d01440c07403009034552070480000354540c000d000300c84140e040f100c007450500005508042d09244d214010b83c01440311490704a01c028420720060800910a40300001c8c0750030031140003454404241c002500a51040000e003186040c2e810913194034025200c40411243d6460940b030f403d015041008080442c00d110021500344004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 205219577 1250 205218327 205218337
    0x17070f11060405011505030d050f070623010303080a0501080d120b0301020403110405011401021e010b061c05150d151112070f08040c061805030d020d020c030c030d05160602030705 79
    0x701e03031040400c6481b0070800d03465503140e0b1443d20211303408104001c4d209000e1805824060f025000c0054006c00602e8080f801b14014075449000b801d0210042c0101500002415001900306c1c10800c000c3d81050f80d000d9035044010440c20a010310030f03c3c100c04032000394105200042010303000f9500d07240d484c9020f41c0700c640c1250b0042d11070b40c1000000b0400c003a42c9040740c440080142d004102c1004060200c03100d81890300d014403e65501c0b130030750001e280c45480051010b040c0402100042d03d2184010300700301c41020740041d080442c000b402c00215920301455010701034020465a03003194403c0d15502c024004c0c4060384203980c00106203031806180e0240301300d1081410340c5800000c00500a022901048101c800814004005505002c0503101b843d4044c20b1540c00c0b0218040f03240c441c0002850503850b81103c800680c0102d86900701c3d19030501c4034103050304098004082043c442c0700001d4136904042c2442e420403402107150030300609180e0740c1e80c0400350054000c5540c0c1c280801e0081c1503602c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 205220827 1250 205219577 205219601
    0xd08130911090f0f030d1404030803040f0218060603310821040305070f02040f050c0a020c01020c06030a18060f050402040c0507020a170f010f09021017070f1106040501 74
    0x100f0301031031403039050120104042c14030040c06441900d80c02d6074181c403d4610b00488107910070b011302010000801e050001d500942c02200c010040440510401c550518101e4100d0113460003001403101c140c8651042c4d98102c07025030404440f0440c04605401c480005c11010b44485600a03281030512103018010203020b01d403820380c0540b115081c00c1206e0303242c000b614002d0000381b041100300301140c1c00040510303841340700030404180c3d0840d8400c1e81c01a51416a040c0145001c0003c88601396a010000f21070350745000c3c0050908142d400c0c00140c55400020f0460f0760160f10781c42411700380441c07c5041544941d000341c04015010404011384000c0404480c2280034518020035031603602d010750169101c02e0303802040c0030f4071141008040f05c13144002c0b61408100c2d110300100c000d1858401c1c000d40611380c072107050004c0c3c850701900420900c07294040c001d0782070206d141d030140c0d458548411095807101c41810043c00c0d0003010041101c4080c0c4142043d0000d000341c20510041203019049009110a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 205222077 1250 205220827 205220839
    0x30615030f0706090b0d0b13051602070806180a1505010617060f0d081c090507090203060904030e0f130b01020d0e0604121401060e070f0801050d0813091109 69
    0x740480442d03039015207010304000b0502e402801c0005024110050507000741d00c940102c0c018000a000c00d42100c160b0003a445c1045c0c0f01e004000044c2d0800d40401c1d031002c1188010f00b001303072900c1145034580801801c01d070180350040384010300c1e855040142248403580101494100054292450000c040078000c5900207942e0303409000c040517814526601401c00100a200c070740400d80b003080046a01ea000446480005200b0443c4c514446005600d08080003a0086010500c0d4584103003031000035089000101e1040c0280030b40d0362105541c1d680c0c4140d041c10034402904c1c0c43c00000714040d00469440354081460036050070215419002021032000c01c2c0c003201c00484250100ba84c114070300810090300640140401c0003034400180707054049500540e81e06040c400c0d000549400d40c0c4940c0c1004e4100b000000034417100c15071106144040d00480d15051070349506000c0011800060402c0142050001180c007540207101441114002e2011810402c0201280074032203000e034211140b103600c625 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 205223327 1250 205222077 205222093
    0xf070b01151b050f07090c020f03031e0403020a050a0809040509070b0d0c03060f0b07050613020906060708090a0611100516081f09020310050d0c03021e03061503 71
    0x598003a001c001503811912401104080c0503035100301c00c91144415141e61064507500200d40c001404400080d02184201103a2041441ca0103840d01401464020740d0b07034070410400003041c642d9275400d00c5408154218a101e0780355424200e02d000d4514202402ea4010000392904000d920002015641070070343d0144003550751206074588480c058420300d000c0081c208402031200e142640050b841d44410f0074006800d5440d80c0600004034825003200d0032200c0c00107440030034000d04002e40d80e44203070b40301c008d044105110380c0412100c860150059000d000081220003c00001c901039440303096000d0084250a80d4a01d00205400c0e0407084244031350090f00032000385000180626031140b41c4c61102c144550381d080804480c580710051040707a40c1d0f0010b40c182920741841c90903020060000803005a2281044031044102ca196035010901c9044042d251000003000c1e680c1a0040b41e404448021044d00500d43d0041c280408000040c1d142c000c500401c00001013903403410300d209005a007120514 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 205224577 1250 205223327 205223339
    0xf0105030c1e0d08190e03030403030f18050d0f020a0b0c03070b04030e090108010c0801060e0d0f0204060b0d0204170106030308160909050a0b01030f0618020903030405060f070b01 79
    0x103008410191600406148180c1018800050254a03060000b03800c180c4044000c1c4c50700052500f1500040c20203040c003682004800c3d0380100ca00c04850003c402071840c152031039402038448007016000c041400303960f0341403001c004003a0303c1c00e8004040252401e20b1000d194a0144000c401900042744140820301010a035400d4440c00d03945500c1030000298070b40007082d120700c21150401041202048030100180c03050392161403c280c000e09480001050080c0540701c05014104140c1010080100039003c079070050b91480f19280301c154220002d000c0144550022038050082da401210103088001044519a402a802807080362a941610344003469040d9a8601740c1e5854400900040c40c80c40100d41d10700b880c05482504001d550401000603030382d0740403c9051701d10072240000015520a0184d0455825005a0f424605256402c02903941890232850403210242c01541d4029030200c0c0f413002ca42c03010021500513001c0280311545a069240303c6883c02d40c403881d0300f15800f4602400000e89 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 205225827 1250 205224577 205224583
    0x204080c18070e0904020307030222050f0402091f0902040b131a040b03090f0d030504120c0510020901020f060103080702191d0703022209060b03010e060d03180b030f010503 76
    0x1030070460740c908840c40c80d5141080044c80000c0c0090303a050081c650004016542c04070010440c000021052101c007451850220407242d0090144820b0b80352035041000580c1d90894032507003d4034003410040003985400071500d10b50f11542040212510025010904082e030750b01811200340218021000e061b00d403a00224114845c0d000940c20420600c418040b8000c094007450f44140010300321080030990440d1145015250a800300c0460b9880d000c0c40240a0b4909889201e800c1a0602885540f1180d0b035495a8545504840c0080d03030303010a0301203260307201340b014511240142040361190b5840e41030019041d40510401c034412103210000d0107102e00c0101040086411100346401000d8482030028105900105090201682080703005510382020710403e018a80c1d07015072103d0b00c1d00340a0b210701241c0c0c03242c00070100c8210920040150031084a45180d00510542c0d0003c03044034a45000c0d11856030360201d12002d40003c00e00412840300800c007a52003801c14020042060740d0f44e0040c192 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 205227077 1250 205225827 205225831
    0xb040902030318030a080f09010e040c0c030809030c100605010801120b060405060f100c0302010c020a200a0f0b0a1e080402011d21060a06050a0306050a06090204080c18 74
    0xd0550000e02c409480d851602c0d6042002d114090b00381c405c444a50750326000140e000900d00300200c000403584212659100040b03600001c000e540400c09496028000317032100c800c81400404110343d07880000c0b00c9840074002e40e28841c641d103040741c01003540703100750340f02400d05070085e50700040c031050000450714a0f64034080980f581251070f02080d900c0b80c1042c4006464014441504003602180c51101074688280300005004241c0c0c8403030b04a203207490020300355043c0940c210115403140744e40c44041131910f052107507900305070311410140b50303819008a82c44ca01c0c5a480100511000d460004200740d480e03006010f008440d6962104480c7d00340c00c42440c1c0404581d807540092640c000140c01540141074203201030800800c803c540c040a60300161500d022054404980305441d0754000103404100080c6420403200d03e005d004050074078001c200d4003507003440302810180c1c03900040b5001e48000c0c1d001d007000c2c1208031801c0d59219100c180260f940d9208040e2140604620915881d1648129002078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 205228327 1250 205227077 205227079
    0xb160527040f2a0507150621030210051b16080304051e060408040603020c070504110706110f090613031e03081e070e012106080601080703051f090f150b040902 70
    0x25003400c249817240c0302c20091b5441c040d450241d0322000483c60410b10b04410501d0320030440c003078102100b0351130003e00f455020a100914241400b05000c44a130715440e03481000542c82401c1d98490340d84000b10884048115806000340100005102c280070300400c0f202022030f46c460002e07036280d881c5150300341e840b10b084601030035821050006102d00d92181e0002c101d00c5e105201184d211984400c0003601720f8000510110098000044050030020f00d8011110b212141c41815400d00c80c82500d400c80c03510981508602c02c1000082c1160845510b4081c200690342021541c07050843e9450981c0e0b003c008840b05070f01261001000a41c12845068541c016424090004405865070306003030701c14000700700102d418000f9095140d03084a542c0c17036403000031800c1c0349404203840d440d100384076081003410382102c86241c20140e014000720f84002102210700744550300312102501007845080c021326058000070000440b000c5180284007403414202c144c07184043c030030800d18007464104801c45110050007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 205229577 1250 205228327 205228337
    0x3070b040204090305130b0d0b03120906031915061b0201090b131e03111005071509081b070501020c010c02060a050903190b160527040f2a 61
    0x40c0050a10390040301401d4400d007005030170b02c5031a00d00c1c03941508103900000c141c1d0001081084003010f480c011002c94000c02d8010704102008203c0603802441031001c940e0003441300101040000107103200b0340032040c0c4200750421458030100b0a406140040d48111800510080000b640d15801c40040340341c26036050b150182c00710718240740b828880c1c000100300107003407a89210024004901005d15900c14103521601c02c08942181341024080ca22580001d008010303030b80811032000c0d00802210101a002030741d80c0c4006045010803005099812001000241e02088841003a007060800710508820241645c500a8450004994135811110841d000a11946c04500941810401402c190009261251510752040003207850950032a00ca404065813199041041c810b20b820049e0b0050602180500d4110341000c0003071403070181540100480708a403600e4003004c0d540c051620f450f590064012b000b100040d8240100030040d01040d85040d840c80f11610000140d8460060030020580d150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 205230827 1250 205229577 205229581
    0x150806061002010e0a06150905010305100e03040911090a0e0c0f03040602070b160908010c082d0106031a03010207080703050a020f03070b04051614040207020301020d022a03070b 78
    0x40100300360720003418a095540c2c8022500f10350400788498072107030b0300584e0b001c24850000d02c030020207140c0c46d92140144034502001800022404a400581d061440c070300850a90300889030b0758118407803607000c203015926011814102207498000fa00c4400c5003200c00d104031683d40c0e280fa480000e02100c03005020310040041034495600c5402070b68110303010b07850040c1084c3c0d8695032018044000d1307600307810190741101800c3c0c01c039a01541d036802400501000b4440481c813504094503110000d00080c480800380318103108080e1418418140e94081c0c40c0d0f10610030b50350303254064001c00c030448900001848007080321000d81014021980641d50280f1400d18101c0c0c15107045a5a4202100900450042544000c07800d50104040d19105000d1a0700d8010f606182c541180b420301d01c0c0b903501c00d0074214040c08111001e80c0b07110900007424280c074050381c2c511036880080d009110b8150096007191001c0f4243d45507080b00034098130400c3c6000c40082c40c0c12a2405020303540d000d05a0018620194400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 205232077 1250 205230827 205230829
    0x302030a0f120204080304180e07050607061e0507090902070b06040914100b12210a1404150e09150607240c0e0109030b04060e0c19060315080606 64
    0xc4803400555942c50815810500c40384003000340d82c0b166000300c590b940085001d02c070081801e020402c03120b0440c001044a80b00d0b44641c661604203c0c8640343c07240308049221800e1040542003c05c1c031202ca80c0003030360340a501d070f140d0000800c4103484801c001071445001081081d105d100301d5070900e0304030f04100d00f81d40d40c050401c4050024900d0450ba108080f822a013090f030010800f00055403c00c00d004200c0c086080c4c20310051545580040007944d2015090100386031814130a1003501d0f01605043d603641040d094152002d03400c028540c21002000079002030004044024a00c3c62180f030b5440c7c2006414801c00c100c0c1c9200b050f142d22038544986204d020042c60824010001c0360720401c1c2e4a004040c019400c5e0740b03000d001851802440e901d40c207511040580c4540d40c660b00d075009003407034004a41544c031261404240203100812945e038130b00514519542c02c11000190010007001c4c40e01e01c0c04001d01c43ca6410076a03115500101e4200400040d2905e84c292011041d00c208200500305036030b4102c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 205233327 1250 205232077 205232087
    0x305100519150c0506070201091a1905070201060f030b06130e120a0c0606060e0906031b010804050c060a1701090603020d06020a0c0816050606150306011d0a060e03060a090302030a 79
    0x4110b101881480080000042c82c1030211910031113903078000040c03181e928105072048070380c84d911904a00c0fa0b0343c803c00200702800c0301c0b50201c00f03011703000004250703550460a80c01040150040c143e4004501030000410151403940c6216200983d20445000360360aa82c90695000c0070f04201c1eaa004000c00d8070f003d8442101603c0c4216061620030304070246911650103d40c0d85030010340000700ca4441d26241802c001d403a040d0854001e40040c07141c80310309500c8098423211145043d0410000c0004501440700801c64aa005031008111346e239103050000700a800310450600064001052030000203400c00d0314403901cec0840350082d244a60310031850f92210000c1d030080c049102807208001c2e0784004115403c026041509815510310003074542400c0c0140740080052500348108480780d80c00362000904e00c00d60b40c00040c203091448010099803201d000840007400400c0d00406420800102c255104e040c43c2c0e02c00703030150180d40294807406010303415607075905030280140c1d1003040300e4900613120b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 205234577 1250 205233327 205233359
    0x103120203120a020301090b0d02010813060908030c0702090906090604080a110d0518030316260a03290a060f0504030614040303060506030108070509250305100519 72
    0x50300c150380c6811000d06001e2030090041d220900e1095010005000d01c11413480340c140c10100858443c2003590066000a20f40e40c0010046039081c100c0f02c0404040240542104171116440044240c60b0f141407039a035030031130f0000030050b4462810040441d461030404a0394901075500303800505a140d803a9200d44c0401c0e1702c24040d4604000443c64000070740c4006014200c03106815949a81c0c0c2c0b010103410b031444208a20543c14400e4108011070340b01c03000e03000d0074138807040c1d030164500e00001500c4001150000b100d0742141c0f04154000740c0c0607485a89035202240c400481049110244035092a1031403080b00941c119030460141c0d64140b100501401d00c068803c01c03e8584242b81c1a00d039900c0c2010380350b082480d18004100b07002844109905400341c0c43c090702d41075034040d0a40d1300d44032450351703221000d1261900441e51080460142000c030202d90400310419500030100e6080c00e2001001000111640394007101904000301e001d10f000b4002c0390300c84600c2c04000d001282004c40a012803050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 205235827 1250 205234577 205234613
    0x601060e06090d0b060301050a0c0914030c3303010302010806010c170706021207080c041404090803190b03033a0e0d080a060b070f14061303180e0103 66
    0x90000003070507a904a460b0f82c0561050130680300500340081454251a0040d04400c4070750b040a05566040783c1c400814000c44500d14818002c001c00c000c0420306080c14200c1c887e030800140c00c00c00f40309449400014085200c0301518010b440c420040b2a5001c0c0402e00000f4001003110000c6401e82d8400c94a490b1850701500d04034103136034201920340080d94091101100c403260040f4641d00c503017001421580d40703c80e03281401045803521002d280e441b482140a42c406001245100e1b030403584895000c0c41c15541e01200c22030b40ca06080c80a003540485510480d00741034200403000c4041d04012094400007507982013825620203180d145078840700b08501c1e03001d6684201041240d8080001d014030003c0d0400c403c00f400c811a01340400801d405001851908030b2400c1c9007007040700d0042c54080350380064103d00d02042c1007041d03227407044072022041c6089429100720400d00140150032504d410395940700382c4582140d4059090716641e100700a2243e00c0084c104980100302040b002c0c85803900b9075003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 205237077 1250 205235827 205235839
    0x504020306120303090d080f01080a08030702101e0b030d1d1201021908010b0403080a030506010e030d03061e0506070201111207030f0e03460807021906020601060e 72
    0x740b0392403034030f2841d001240c0071402c660100c40454016900400c54a406c44075004507624198100049039940304413201004013031480003c0011480c601c01d200c0244100400b00e02032144000038a00c052013440b07590060850b603842d1210f00350b01481c0000c2c8a968401040d2500410a0302c200301104008944102054203c880303202c0f46c402e20700c001e200800c4c10303031070071042c80420441c40d610041078680141c0000a0080f02008140302050501d802c0d202848000c1c500800c86039104c0c00100c3c5c180c3d201807045500344c401c200044071000c0d050f810034800c0c0c803407804100d0912196510741c211448218070407103420031020840c500140d445861454600c00d145400ca801c580c1301c000c2a80b400d0343c0881300546c005400d00d0b035500b907450b5005c4218180c0140c110000d18001040b01c50310345000c0c050030242d2907600441000f03a50a031444018422104031107a14003100e001641c107020344d0742ea00c100340480c4901c081c0c0c00d109800c1905152908280c440075402884142c1c00e01d5000d40303200251002c4164481 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 205238327 1250 205237077 205237099
    0xa0e0702100b0f060d0f0b060c0c1e060d050f09010c050403140c0d0c050f06072f030304170d0203120a0b040213030f060b01020309030a0f02040e1e070b0a090504020306 74
    0x5113800e801041d803000c1030070b40060070541c0c00040d04121062040c56511a000070001c500c0c8401002a0200c0200303000c07140000f00d46010100e6051f60800b01c840f00d0740003100070032103c1350f000c5107910003482442c007000446ca032940d40301c03011401c0703c1484504030301050041c4001c0c00460075070b1068010203640d84c42240c0801c45110300243c0c210080f07c4046031400740c4d48605001da8146805005008581541d03010f08010159860020301074003014603004401120b103041050041c145095041d1800140a1b20758454460301040740100900101e40070340d200380350f54488010310001c01ca4040c0a11400d0602082d110881d550f00a044003114040c0c0c4070ba0280102a00011103c038040000c62180001c110911411310700fa10582d514000b04d0f80c10364000780100c40854501041c4141c00d50b50110803a00d41440920004006111f24030031105184a440d03010021500d40e03000d0441050307548404c50390741690310016150544140a0807000040d40614100620304094002d140c101100502a100356 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 205239577 1250 205238327 205238329
    0x5061f050a0b130906120c140604030f0606030204050901021e0703020a03080a0b0a060f0305130c0510021006060f1101022529061201140f04050304080f0703020a0e0702100b0f 77
    0x1917000da801c08006004407213044005c2255042485005040b19041c440c640381034207001890390b000ea40b1015000e59641c2c03100c801008600d1380003a01541c0d0040c01045181001150207000b9080380d4001c9520980e005580c031850701b0004252800340c0ea044d80140030320b60050340e00704c4035600080d05840c081ca459081001080d43c034038905101410b0a41d490704024002da00c8003c0684001815002510000504080228038062204800c3e14400e664003681d130703030240d002280b40c00c45c11803001c4101840c10101081d1a584000301031582051660b4085094084000d85400c0b8458842c030b544d81135905e410b410400030750b0403c8040005008191510302070710300030880802c407400c180079103420412103003c1058611b00b43d51100c0100605100811061500c42d010083e103003000741120203a901c03060006400c1080030411100605024010345404102c85903046035034114600080b0700c16058000003181e012400e120701c900c22601c0d40d000340350140d2200980300c01018100c102c1c641081801c0f07400d00e45 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 205240827 1250 205239577 205239581
    0x711184002060901140f0d0507050a020703060c1701090207020906060c060f06120105070306090615050403080d020c030a050d0c030e0d0f231e04060c030806030c04060305061f050a0b1309 82
    0x4507200c1b4505965650f50301184000441d50010040410b0140500c4032000060b400a43c50b001d90703a00650010f21820981019280380169001681e580c80c241c200204100c1030907005001214420346d0608420f443c4c40c1d003081000c0c014825150142d07401040001c4014022041c1260418405451411240b452242c45070039034804a800d08040381d02c580040004080320301c6503100504001d80408000f40c0c0410000700988218030015094070b101207000e80840040d581126800c9660604896460340c40c2400500b1540100451400c420300e001c0c10070038050700030300960b002d0074421009004048541001038854804643d510800c000b40304440b0003028080c0100c0b2926010181c1906407102c0501845240c00a88501a402c60180502003000b8064100c5a0030f00460386c14101a00fa99841b1404a8a0300304c1090703809500c10304206002041c010007041d0a8019454454101c2000c3c4141080b84030030030f8244034050b04005141d00400941d50342c0409805401e207007a4800001c0c43d9614841c8007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 205242077 1250 205240827 205240837
    0x3220809060708090907050306030d031d010e060412030501030f020103020a02010e16031403071e030201180b01050f1503070507050a050105042a0605071118400206090114 75
    0x20f4000c0e00069001952810101c0280e000c040351602c01d180d8074240700030944802d02c500034003003410307100c0c141900e0b69803421581c20100c0d05404000c000c442070003140c042c0e58440956040c0c4000700e00100700d1003d42d1090140d541a41d800060440b0b1a50712680110b0017903010314030301c1c8110f541cbe4039120b60000a061182032010500255106902070550620104644502009581d030380d000300800c40000b01300c0d0444900303811003d19002030030765150409a016101c00f1042c0800710003603c4600c010001c07915122030580e4016504500d52004c40f10600140c03402120500c91000800e1001440d0a44550000c01a4500c0703241500c0e0880a150b032044c0c25540d00f075804031120603080428140120f01e40704200d0703602d124840c400303180360318000c0050454455242d0240c0b995408410500b410b4942c00c10420003401c0120382643c813480e08500f0035952140112600607030148401d00d804500b5544204001040103c10740d0000d480a59400c00100e40d00c40c190803410f120f884243d201011001e480034007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 205243327 1250 205242077 205242083
    0x20706050a0b01090503340909030f0801060e0a2102040609020301330807050f030907091503020612060a1a03150108070c0b0408040f09090512032208090607 69
    0x482d01d10081030015244000c40c0e00920b000741d10980a92000e1001c4060100b0291445001440d110581c5c540c6c102d50f03510181c20851000e4240800c410800d40d22416000b160a00d44eaa03102d02a44c0350345040f9411000b150025070b0007486000e044c0030b1703015400340842c00c88641591070340711050540d02013802d45805600c03004203994003000402401d010031300b5081c25241d0004200f810700001d204401c0006030f03444590410011305c0000201c8070b13806502281c1c5812900b500782030312464209503650350740c1340a00900c2c1406041068102c0301b5070751400a207059036401420242000c0321601c1040b08010003c1c00142d2100700d5120001e1700c25045046800402611000c0550300e10b8003840300504a030003005001c0c100310060040060865014211590035940402050030503141c1e410540a64011a0001ca03d0142002c0340003955941b9680204210744c4074100343c61900c82311310001c9603140001c5412101c40310000f40f0181400d00242542050180b0a2070700f54100700d0450042221504164021 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 205244577 1250 205243327 205243331
    0x6150f03031101060b0f0301060f0e0a120212030309070504090c09050f07031406130c030902030d050a090b0f030402060c070909060e01150b0d02090120031902012c01020706050a 78
    0x480c201242c00e000e0350000d026008003051620440020400481c80144900c50401084140310740c840c40c45a803c44101c00002011b01e2400740c2c07540c811840c040b0b03040d28101e200d0b0300c804100c2d40a6400110a491040e24030310050f1108500e0002480040d10300c0f01070888420364018004600340e45140301d518040d43c04841401050310f41980050202c0d01d131010701040d80005d000403c8000d90750b01e101a0f200041e040d00100f03810803401c0d0258003400c0181e40003075040c0940200c07200080c2c0e1000203050007181c01c2d5240318003141e0b15070411850f8840c403080d81200000400000700075082050081c0303131000102d8101e40c540e99031505004110bc0f000e001c00c641481d114403c03081840400d0040c40ba51b41001e03d85000d49600c1c229030102c0c6803080e500c0c1040f00d190042200427980c2e0158801e040700c50051000b140e400d030040f01120b41c03217034001c0d1011a500500282c0a80e4007030f10511401c0004034041c1115203000b00b401c01c1650000600c40303112505590200450400900c00c0d000b00381c040e210784e000c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 205245827 1250 205244577 205244597
    0x40c0908010912110304050a18090204050414010c081509040309030c090516030b0307090b0301090204050f07031d0d030f020412050a0303060812040308030601020c030a12030c0503070c06150f0303 86
    0xd043c42c64202c00408503601c06e000070302190341d4401204003180c00f80110400e50000500350307000034004442e0041e503c20703d00320410051190b2102419882402500200141c094840090303525240982d00304440761a1600c61035440d0400d1a02550054081d0034445100c0380d45e40e48207240d490300c0d504030079081c5407503030244120001c0303c0748925400308190500740080e1b0384060100365101410b00c205101ca030b807211901c0d18107480039480400f4071134001c0d10521140ca0840d00101d07801c0c006549150000c2c0c54200401c048201a2901c00c00d00700c5041d000c2c1003000603c1c10b044000e40040d00082840700d40c2000005888400b1a0020b41000d00c40e0020303200043c0d03281400342c12120140c0c020001e940010300700c020458580011a001d4039408042ca82d1607445040040313181c000d801c44600d8141c030515407501e043c03001c603401c0c0b884824055682440403448103882200c10b40003c5e41d40b0004204019609400148150414141c80080d030b10f80440c0260380d41c0548010309819401900800c02c0f40c80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 205247077 1250 205245827 205245863
    0x60f0307060c0213021903090816030504050f0d0512031f1401090e01050d0f08040302090711061005010c03030903022b0909050108070b0d0902060d0f1802030309040c09080109 77
    0xb0143e022010414001c50a02982946d05a0000c01000081c0b0400d540c2e42e100404003e003400c140c440d005440e01c8101c192000711b14000d40203074824001d261040e0304240c1901c0c0c0610b443c40050030480d5208000c0c151100c28180480281d401c003400c450741ca00c4125125040c60b00000200c40c0080c141000717a07600c8000148009842000300f5000490120343d004018092a00d5018140c08010742c48181c802d480350031400c0c00f00880c0100d81000f0340c001608820b03c028160b200482c00201101c0d0401d5820588400d007000c09014030510900707000c602444501400b080c06580190042c50007801550344151984038075001c0c3c141220350711035902c8450160f06c00700070742c40321080700503040e101e800704071369410301e8820f0781c1e41d180610500360310001c0024282c6241c0503c1e00a2301c1c00c1c41e4050f00c03413134403805065070302c002074030305c1c0c20070382e45040d261255240384810702e02001c08400d50040e01941c0742c00008410300c000f804080e443c0d50240104140d0000e042e420910030444403034002c5403030418041c600c00e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 205248327 1250 205247077 205247089
    0x8041a070c110307051c0203010618090309240806040b0307060809070e0907090504080408100f3b0109140609010b0603010e07050a091206060e011706010509060f0307060c02 76
    0x407406402540100000e00c02138a50314200c210300c2c0004606d040c022030003803001a000d07080325040311018540c2030110b504003a4a980020340f84c0f074070039119a4410b03500c074002410f550384001360303003080c0c04501400e001106000e40c540700d8100d20042c00102e001d110820209180120a074401c400044d0904200050900d052005e1000b80c0402c014004150800300c199a955031501d00681ca1a0307a0f40300045410415482e00316801000d84106503044005958441c10041140b0321000b81040c0c2444500e91800010800c400304501c0b15140c40c0c4c002800c9804900e24182082d2000b103025940c80c800c00d40031800407a00a00800e0800c0c005142901e0b01e4441103081d03540c241070240c0504001d1006000d8008041e103038541c00401843d2072900c86030700c0d050071680728040703034410750000754103c800da8140203c6400100036107100c0c1a403805283d81e0703503104042103100d241c40200d0f030740c1020005201c9441d04c00b40301600140700800c1c0300d07040c01407c00001e007004d100d5809000881c492503504011403c1c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 205249577 1250 205248327 205248353
    0x40302100e0d0c02040b0a030b1008011401050310091401150305100902060d0507170903120708060a030213090812010602070b03070e0108040203070306020d0605030708010209060a08041a070c 84
    0x1c1019012941e51080090880500c451009118a4680e00d10f01120780714045c0040c021034104000c0381050030414440c00d1503c14ac0e0264003c0f130350800000c01000d91004038014101ea4002d00180500c090394002c02c2e0003030050742000c4844031100e81c0460040b1000340a030201c216405030060380190303d1407400b2407503e40a0a406c1c0302c40d031308014030240540d1b20b09042d200300030941c0c1c10115480c0d940080881c2c0140101700e0380b41e40c0052200600c1040c0400002520050700c62003005512511020001e42e8846c00c2200e905a100703074289001d0005050039241603c40c421249008940d2651661700d80c20340340c00c0b20400c80c1c207410381000100140c6504201c1300c0020500380030700c5440c7d82840d400090504e02d8901299050209650214085440411014000750781040c01191109004403040002d005103101d018403e101c1d10300003080f42e41c07044c401c0300d0490f180244800d00c1e04181580a4078450700040040d0b5000d4810301040d159181100c080c0c521030705540d51074020b140d85500d4454000104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 205250827 1250 205249577 205249601
    0x21f1d0409030e0607050f0703080307030c0201151a0409060603020a0f2309011b0303020a09061404060f020304170c100305060a14040e010608070611030a0801060c150504030210 78
    0x41039520710200750090103469001d842034a146545078003a0a0280c5003618005070307504c031440381a10001c20320240602540c01008280d42c1440200d2044004a003666150000500c00d04008003040001c0c2c1c0c00c411402c0000401c54444500b4241d8900001c0300b00e48080d407111000c40c0d00082c000c00d11341d03805654600d400d0500d0030050b8401d1100f21401d0305010258000280050300040d810006a001d00580c00700c0681107503418040c690949030080203500054660804101030003401302d4924010441c0400403c1c00c020f04c5414103281030400c07070300780443c82e800e941035000800000c2500b5000001030186c241c8024003d1100e0304d985024001c99110700303080b000405262909100469950309009402c44800800040c048498100020024903c0480030700752036280c80000501e894001c1042c404861650303c60b404101526404aa182d119107259000010003080c018442240513502c00b50000f4011360301c2508030350601e01c0c051b0071900c0c140d5054002d68003000142072600302c039009a1042d80310b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 205252077 1250 205250827 205250831
    0x1e12070617090304050411040b0a09030209090f1209040b06040e0714210903250c080c10080903130602060907050a05010e01080a020c06010312021002190804021f1d04 73
    0x1808460b0a80c4074012030049500c10381e2514400f00c4c40f005400e09650240140c48030392036440311510740181c80400e442c0300c224010341c41a0001400308030040790074910300c512107024100000c2040c11034045076004c0d40407135500c5030380c2e4108103006898400c0a400540303c4030f0210451400c00007005000d10784e00403241d00004108200300e60b00d0b40e1034096446100c841d03075480e0130126100ea10105082d80503038150a00f03001d0392005400c500e03002c0030094032006030040c3d81c040d0200382c46e5000c094440c81921803080d00180c0b03000000d0640c5110b03ca015500240e0035064a00b09034000380c40c1005000345034004401a070040b02401152101404088010714003101e003000e11904d401c00180c540f070141c42000341846120000205030b0441d980488195200200035282d156031a49484440c41d00307000c03212401841041c0d00841c50412920840d408890244d90301020303540071034000c6071030650040c01260004032002c400c4101d8030722452140344120403502c4180c900074a5080e462600301940c0c040c18481e034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 205253327 1250 205252077 205252081
    0xb0c01060905070c021009090e03091309031b06200703021e1e030c010e06071b020f150c0604111206010308190c05030a021b0612061e12070617 63
    0x2941013a05211070540c10f9455050905202c10251500b101d164010055541807001c402114140031000b07041600044944000e140100c262000442d8136260004001c181a4070110440900555080b06000c1c42190b02040d0080c512100212400021310804218140803c1c6402050b406001c41e280c111000c01e00340c492200f88464180d03486050b6038204000c0c0b40e0307005017020782d22000d00455280c900314070b000380481d50039409c030710382c0e101400c85400000403c01100c20001e480482c0d0011196078004107007810440b2500c0800108000b41c052241c0c010b1030801c41114611001c0c41080d03c03443c06020410188019074092042a407030102640000740c01a00040c00061900c2c42550b25200409070840c4102c50083d005680200c3c80d80300117400b900c00410383e03a441550000f042c2c869001c0240d980003000c02c030042032000e0303409009540090070100074000346050810001c4d0060165000da405488000307940085660a54a40d0302100c1c01d4111403000e04c032054020b82690300001c0e070658600780b40c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 205254577 1250 205253327 205253341
    0xc1203100803120a0c2016050901120303050c1209070602010c03020a0206042d050c0a090207241d0c0306090610030b190203010b1801090f0b0715060b0c01060905 71
    0x20100081622088030707903d5017906411803082a500200501c0000c8010110801c0101d880e80c43d088034601140242203e4400701d00d50401503e41c41c12550000789554040c0c440e41e6098024044c01860f00d005800c00303000c40c0b180180440010740c01014414090400c0705c0c20400000e0035184948081c105050040061034082c0c0c0d070028803198425001030641c41c0f440c001502801442405d418150074a0038100c0108041c420041030008d800501102c40b0191503507107003a62001c1c0c2c00341c08005007102607040801b00c000081d03203519041d511145040010f5001168010b9031000c0c1c0001c04000080c0d10074141d5042034242000020b03040000d07440101004d15144001c464440301c1d80c08010f26694600000c0740f04881000004120b421010780155100e40c2c5409c10b0715000e8200c41001c0700c000031200700841d2554090f4903034000352080100d10514580c2480352200d11a0302083c0100c40c1c6820407090401c10281510880b005490354501080e44c5454003030003142990166000000018603250a2104c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 205255827 1250 205254577 205254607
    0x109050c090d1a091018210e030d030f11031b0a0309050a0b06180403020d05070807080a0f120b030a0303050a0b0a080601090c050313170c1203100803 66
    0x11000445248004014030b25264009041d0490074006080503101402072025010895081032885000200212001c0740ca0a0702e100742072240142610000307d05540c0f1503901c2c0500a00d20180343d00309070352607120324804246008000f04001001903690850081180124000d905914402c2c0d98000e0650501080c2c5206c541d40c00c1c0d042d000c0029001079485481806604900043d80c0c00c002a42c0385003d46040a076041070080390316034800e070b030030403003103107030b1401600801e401070750103a00401d840700541c4000d036050340c0090010345a40d80c0034400b030000500c0307070002003981c00342c655103940100c00100b401801c0c2c91088060000d40500340000c43c7c070183c4000500e01180c5805140100d0152104403038403005000c0800d00c250404880d0a0104040c400085c945040b503114803c104039031002031310202c900303000c01c1c0ca4031402241c0c2c98040d100421903190f1310800c00010300ca240f0780f82000c00c4051601e040d61005004100740008001c02c21002c1c405030414009007011030107140303040316030480041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 205257077 1250 205255827 205255837
    0x3010b0f0c1005040b060405011203020615030f100b0102070f0608040b0a0902040504230705240c06310201120e07080f03070204060503011509020f09150c01050109050c 74
    0x1500d6001080580c80948204850015031402c51030801a50820381000340c00040100d0301e80b40140c0c03e00e80000364140715a64985002c03074165000c3d01d066101c0101c510608000303401d0450f40b5201d0003c6103040440e09001d41041e0064044001030040640000a03040030340340e40c05200341c44507410003009002d400c00a07155200e94050600f25142d85e903d101d40d0003c1c25003420180d002854001084200441452041411150421112203207881c0c00c0ba2195a02d00d00d0040c1034010725a841100490040214200c074245920100790b030800e05051030701403178590b04480c4021a0800b4610382e022405064140c00050541100c610500841a40010f0310021203041c0401040d980e820318014000000d1020801800441007510740d81c6500783e082c15030300e0300000e9040c1c2c86a882c180c000110751a0520a6090566103c400c2c54544c502e8812010002d4005840205001c2020071000c5c0141d60381560720119480448140ba0300d8026910b0f400e401c4800581020004510f004180041c0c5e80100003614 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 205258327 1250 205257077 205257097
    0x18091005031b031c050d0609150605160219140405100e07090e0a06050f0906030c060c01020403060612050607090b1c020403050102030c0316020706080f0a09050604200603010b 77
    0x258821402c8008285040400c00a80054070310111541c40c50650144c010002015010070600070030352150100c808031001d1030240040c40b15003902c10407444c0c7c001c00190004901e008842d91007060740e6000304192803580f9806910001e4200028040e813640e483c0c000500090a4408011901d0840325121b140d4046015200802006500090980340700e228900007514120083d10043d04200d04944041d08440c0940c6109509031450300255091034a200c1d4801e4400500419540b90244140302082d1301826002c1c42c0c6540801010000c5002801341100800150100003440c030b489044c03c0703051100c098a000200710f80d4100401195041c0c0c429201240d00f800000980010703200c020030000c2c0314540c0010455400481080b5a028000001d503100b1100c822030318684031b1203003004030788400542c0110004030b010003000c244010403030700d060759000b4628100000d20540ca074451078a0035004403011130384810240c039124006030b4007103501820808203581283c21941448900207440c007516200ba = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 205259577 1250 205258327 205258363
    0x106080705070201120e031309020c0d0201090c031205121302120102030f060f2d010906020f0325051504060605040905070e041703100302010201060b0301210311031809100503 77
    0xb07440306e00400e2084441c080c2d03e403d503900505944001d0880a900943c003c00120300656140c140c0c400d0041c0a91003800f076002030707070b496950300395540c110764020044581800c004041c0821144030350051211809504002c007910740c900407134410881e1211418a051041e80d006006000b2010b840540d1982c21680c2140c01c00401529240420030020707403107840b03824076070000c80078000555444440c10308810082c2d8604400686aa1040e680ca41164134441440c2d401040850004141801d0f00c00314019140e0a90381000c4450b00d85500d0010120b00c0089a4500001400204100c1d84104001440b054409204540d12621040d44406c10751180b8002444044006001c1203260f602180700da6110401c0341307880e82022440314000301f0f5a800304901641ca0400f02284811440003502e0407100190503000d2480401020002c0c802600c2c5011802c0c00201141c41d50b041905202800c601c6164007460b280362094081000000070028221012862018500740525280498104d0b0740400c04690 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 205260827 1250 205259577 205259591
    0xc190b0601090308030406050406151d100303090e040302030409061401090807120f050a0507080a030206090102090a2303010c181a120414030f0403060e06090c041e020301030803010608070507020112 87
    0x41200608440c00b411400259107181c0490b1242058070342141b560081d05013346140e07203210440012802c1400081c002c903000210400c074403074282c21188c1e072261080c41a0390400d5640d140c0e140554078a07030081d0313200c140b80452411065074000002c81c0185400360080007200d150030000c8048100c3c11700d01900c1e004403c0314070418000d003046070081d8a075104003220806aa5444003540320540c03440d0841c01805254049080444d050081e42e01414000b070110035124540072203820841c4801007032040c000c0040030454600e40c0d0a1040c1140c0900e6078a601d010200c8440c80c0e0700341c0d08001e4002200a00d8540c1c1001070004045080e543c1420031150300c3c1040c0d0715281040d074101d503566280100c16100c000f51506481049070040d0084900c21b59040c0030261012800507101c034400c17200a101c80c1d0042e440c00c0d800c4e14240c4c1020300b10f41110992448180340d5420340384184d030b000760000c2d1400301f4000010040c2c1a1300030000399010325107140060408155a000074001035003891348070102602c0d455 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 205262077 1250 205260827 205260833
    0x5070602040803030a060806092407020a050d02011a030a15111c0c0822200316031109012111060304030908070f05150c030c190b06010903080304060504 67
    0xc1160081c014960440c0c0d240d2424803030501c00b805041c05003c40c180103000106101510018441060f040c40000c00c40700c0c04030325162310280b03001c010104401c44c8188650180811014000c00c08000c04503400818032400b240740d0708507040d1164040b41e010b1790100c1543d0300818403013050314a034030030400e0700443d08800081c210500d5000c0d00341c0394041c0700d001600d245000e6100740d0286592069546807100e06070b50f40a114070a0f140b00401640c1c2c2007840c900a000085d05518030441c1084000301074425521002e000b1900d045240e200e0051030140c501424014840d2041078050381c584203c40c5605598105443d60130100c81241d2035180e15540c143da010b041154180310055401400ba01d0360f40c407803a150400500d103620b41c1c41100064040c5940204a103014070304e0500c190b5101410000c041190100d000c941513121514080f0300380410700500c0703000a81070017a200310070540c20b48038148031003900b41003410139800303407406050000d048010000180030b40c0075a60701581000d000105545e682c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 205263327 1250 205262077 205262081
    0xa0602030a051c24031109040206090f0a090c180e0c1b101a0406050103020c0a2003070303090e0a1b030218120708100504111203160c090b04110a050706 67
    0x11103503001ca041098041c140c1c4c01000c1ca1650704070b074028110588065840e0060005005080e036000c0d401000c10440303040b0604188010401445000c0c1c4092b1281d03950f01d10601c01c039940b0946050001300c164000614400410141c0406000c070896503280a091011080480f881000c80701d041a481c20545051865070512012100d02501d15061290520400d03110b90525401498a4411840c0000210700c6510910a413151540520020101e5406540350b00c5140c0c4070106040d61880b0f2a400c841c116a02d0a101980056200b6160040903900700f99400361060030040400034803074640000a076014170800080792200e40c0301e040040e954901110441700644109440a0700f12801e40c03030108200c0000a00700e400c895266090b41d2448030428581d106580f02564060021032150116042500d4140300c0400b032001c4900440b490318404100f0f43c1201c14404406950004400d0f40400c17940029002d881c442103021031b010007010f411030345000300c240546c01803001040030118250040007819 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 205264577 1250 205263327 205263341
    0x70312090f090506100f050301060c23160e040209070c050c0301060f0f06050f030c0307091a090109080a0203100f020403020d080711180f04060b0d110a0602030a051c 73
    0x2050788004030762140b9241d00507100903a4010301030050045010920380c03003000d200c10201c001d50f5800e4a5a40713051021100b400d04291705843e90700701302000c103948440042c0307007a100341120400340600303a5920b01c09080070038140e4080843c0065800070840185d88480940f50b12407114242032030300b40000c0c00e09030701e40440c8500c03940d0150f2900501141003210600c0840c1100c072813441a080850712288121006d0154444202c00340800344082a400200e503000303554407a040d45821400750744d880c00e2604c4200d60b070f690080e054820001d9022000e5a0004654010b00035600042c1320b07007502980401c0c0d60320faa030341110703c4031540d07085c61089403526501120003c58004103005c001007800c0c1480c40241e440510121051041d460048029040c01d0119a416001a0340d0a14a5540d903007203090600c2d0b4011702c207c0e44103645908051042e5216070195a205015211480c2440581d40031301c21260303201c0d080790065500601403024410b034860222410000300e148071011700d0004208010280000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 205265827 1250 205264577 205264589
    0x121503010504030804060c0e0a03060b0f09070809060c12130501110a18050f2b061a1519030b0d05070303021507050909040f0c0b0c030912030c07031209 67
    0x205410b2100b807590041c021030180d400b07080d08000c000c100c0041902e080d001d4050007900401400b8040020540170303070107400c0030600500700c0c21042c02d42800044140784120b526001007100d0300248400350310b00b00141544014400300091606062040b19402000000c24000e400580303245141c0030042c00b904518559803000c400b03152120030089001d07019802400000381c11800300c0380b000405203041c0c2044081d46001034844a4000c00380861202c1100c1c81e00511408000900340301800101140f181c8d008801e48034800c0c106491080c1c04002c183c0c0b180e00010304031707003100344819010402d8403040e2036241c0440d0305000511404460100b2074421010b980601180035903e800420301d500890502c1801c20341b8203880441c2d603104101070794603000d158062604180200c0c006400941602c0120034910302594612360702070369a40b1041d405070700a00008401d9080422184000d003410000ea003039a014440c051418a03101800381580c40302144000f600d0401c030a13403401700a5000706118000340c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 205267077 1250 205265827 205265831
    0x703050303190e06010302010c0f060b0910050f01031a10030b19060207060810060e0d060f020d140c0910050f070507050a060305070f2703050a020f030a0812150301 72
    0x5032041000309201202082840b0003401d0000030807003190f012507268140c9605841c0c10701e01b202c0c40c0e211a180340c036050a085491031b90710a0320a030196640c8104030302c103e6001c006805454100b5050142c0b200b01107032120305041c10040400803449081d103410300c0c400302c15200540c40814050741240500006140d0302c0c2c1007400407002420f6140c3e21860f550945107a9021905c00d640d440200301c580e60f00450700f14001d60030f200c80500c0014030849103902c7c00d03c0010004000072009840c1c40007100d1030700065205032a4000356500b48500c0e9406200c15500c03142c074139181d07180b6002400c01524030941d8001403003090f400640e800c07028042c0d000d4800807007000002a40740e1107645080b5075624628010644039020035003002926a00c40c3c00380510480303103680d070b4507002c4c90720788070503200b0181ca010100101c245103d8540130000c4100072240046000d54000d01151420340140703d20070b6a000301e907034000d0300640c4080010502074000c46000c03a00090142c40256591048c03d8110140070358080e9040d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 205268327 1250 205267077 205267081
    0x80c0c060d06030c0f150e0a150c0c120507050904020a0b0301091e110910050d0207060605040606020109120810051203180103020a170a15171002040f050603090703050303 75
    0x201d42d0300001c00d0740e1107070901030002900c60b107402080700181d2044d541e0400360060040b0783c0390b10460400c0044400038204623031594803443d8800c500d40f01b000d080c3e40007071104000c0f1010700040c8212103005140ca240c240040e007180f034071819210b9001d401050b0107603041002040842d100c0254040003050742d11030454030f030b5844900d008040c1401b8508140301004d450500c1044850500c40c00c1168800d01e103205d45054484024080c4000c0003d05043c203002040c84040324164050000745001481010009504c40c00d120400040361140d82049003103a1400702ea000002c0c10b001600807603840141842d842035607c0b507030018107044d610b40080e600001c072503403140c0400c600000501050044005001e142c04100c900450481c02400d005800084844e440d900c48440001035581c3c119180e92400f0038031030080c27111034080c1445d0344d0144004008080507100d178210148400124a10501c2c1c1c1546040e00d4404522020a070b00e02038284914000004101071803130800500e00296442019641c50b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 205269577 1250 205268327 205268347
    0x51e040c03051b0c120307200c0a03060b0301110f0901020f0601050102032704020a050d0b010815041805010608060601110d0909020d0b0d05010203060f03190f05070906030b041518080c0c06 83
    0xc215150840d400d00344030f40141149a908c040388d200c0c0c502d02c2c0030f0901d55025185031240805080554201600340d540c0e03c5095005640c10f10051884010f4007010342e40c1c910603034000910301007401489041c0340d004030005208170fa80c04421100c9402084115440440c3e6841c0d128903075030309510703c0c65401880015034110307080e0060040e01c1500c441c1081042108441401900c4001003103c15400250560b40c83c0e000b2840c0541c03008248503d6024541075101c4c00b43c0d06c19003101c44980000d1119072040381002159070780090ba200d05583c0c0c4c0000707002c00d61b5a00101803c2c215032802030040071a00400c900110002075030161081401c02081d43c0394580c2036041660003580161004c42c0603e00c00840c40903203040000310009080e2200c0c404c2c03c4d021110740c480c4a40c040300403408450501880c3c500240300d40d070350300500c4003030740c0076500340d0303400e800c00e490003030f5080005a1071210400c0c2414041202c04110007034414400d42c009a00d56551070500e091103090400d1a04402ea2202c0041510840c6c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 205270827 1250 205269577 205269587
    0x18070906030614101a040f0e09011107050604030305040f05030d050105010e010c0305031603020405060d05010608070804110906040f0f060f050604080709020d0204051e040c03051b0c120307 83
    0x1141c1c00303024100542d03440c2c640b1200300442c04841038154081300c00010801898100303402040740400710320481c2890f859111407150800c095020040e40c40390300b020700c01c09403000e100e4407241942d0a000300b46025066900c00e030f00c5850003071002c2c05050392080080d003032160305000111640c1e441000d580c3d6070400c001c4104001c002c01c0c01040d000a41d0002d5a0250f5405500f100c0c2d012074054071847e0440e903880fa010811500d8050101c3c040503000d100000d81520749001502d4901076482010030298101035009001ea00c0042c84c1008100c60f100030700010509465410141d50401c1d960002c03195124404103020302060b4049010080c5071070300c000f8110446901400a0b0b5100203400001d590f40c6c0d500308407850299004401c55500300c076600700200c80c0f19034000c2c00d02520401c805401c0540d01e00020b01180000c105a61240001c082040f05c80e00d8184617000c84148182001c21640c20000c400800220750b04101e280c24074000900341455901c1000360003041c503a401540c03650391411410080c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 205272077 1250 205270827 205270829
    0x4170105041412040b09040902100c03080c070b07080a0e1902090123102a15140601030f0b0d05030c06010b04050f21062401030612020918070906 64
    0x2c440d04844041145618003040c515801a884244181000e0404058015a5119001c541d500c580da801010005031a0304a040c25841d44580724100c071040d5604000c0d0480000418030044410704102c000700050645140380c2d00a08249400e840035692404c1280040c0301c1c1d0f0460001a1207150701c00b01f0001039801e20051814425100e28500c2d0341d0700d122140a52141504000041e1005d41c003600250030301d6500e05c4c0070003103185800d6a10010052001d210009401e480c08203114010a1040a0103202044180303a140c0481040200c0e410303080005c00c00690140c040c604040d1034070a18131f8240340c1c0d0b420442d03580c030000b403601e65101c2c19445d18503902e920070100da000902400d000080e440050b2001e039000c44401805031006282418104a0381c079171520440c2e03c01c110341c07070082c001c011800c014103403080c07217254104800c2c803060b05000d400e00240d5103000780c100f50520109000d02411000700201c0c203541661100d105450b0344000e5840c40205000e8000741c2d1240b1840011001c1003900094 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 205273327 1250 205272077 205272083
    0xd050109060f080c06040603050615030709060306060c03120f020d02040e060312031e0402010909020a0206010f080705010e040b04140406020904050a050c070308090c0a03060207050609150109020c030417010504 92
    0x129081c0da0f102c800940340c200b00c589860780920140000c124050103a001a03900100090881901c4001641c27048002d400c203a58150001e4000c0c40b0620255030035218590141000d410044581410343e0740c006d01c2051001920700c103030303625458440412110703501aa009056100c0042d9103a60301d81c0492a00290300711600f502c203204c0c903648480541f075038608a90103043c03001080328424030102c0301d41149581c040c104904002420f40009410320f007610151244241e0340d4050001c0794907003d40c402601105800152040e0031008042059030b80140c01d591542905540c08968002c89500003030040155242071548075034100200000c00c00564010404488100c0b410007803611584003040c11074008848203600c1c02400c04c80080401e002c0d08020798082c4294084a114040c60008542c440d01213900841743d480d004200c1200b044014000c46900c14611402449541c010008003d500031040c403480c013141e5070005040c200d266080c0102c0d0f000d07100c413030b151b50032204042c255a8001c1000310303015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 205274577 1250 205273327 205273349
    0x10b030705010801030c030803060f060307030c0f0801080c01110a060c0c03110a17031f120b0c0a021f111204120c030206150d0f1a0708040213090501020d05010906 72
    0x440e9940c0244151810780e60046c0e01c82c0280c0d0b05540e20a0125880681440e9101e506600350341d070282da68000a51085042d950701050104100e1000781540340b03040904000e00100d02c2c010b0210441c0020103503458003013440d05002c45180c410b0043c0c207040601c580a000c5904001d1362100090b00281000c030340c00c0c030a0356101c01c00c0141c000110740354092041c0041840c8800c1100041e050880409103030082190301c0c000080f103a00ca40701040d00e40301ca0303000306411082910818107000610720311a900c0385800240e64605404114000c0d01da011406086101014200102d00e00b080c80b5032000c0841441e6141d800d070303520001c150303d01600108540403200d0500201a1036074080c070403030010000b190305030020002030302c5885140c801480900501600880420303581c10200e0108102c0060a03070199500200c145e107440208504600003e02c03001c1401242c101380030041c0c81d02e100030303140d900f0030100c0001c42c20750030701d483e502901c5421500c00e101c0d402d200c0042030b00071144d40054100c6506000f1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 205275827 1250 205274577 205274579
    0xd150c02031b0a0804061d030f010c0e063a0c1e02010911010e0d200a050d0f02210f100f0b0604050d08090d03020309011b050d111e010b0307 62
    0x29040d40e0f0900750b50001c064401c14041000018056036141c10501d5250302c001c2c40d41c0c0c48000200e40780c814405c803100c0c031030380d100d805d400c1d4420b82100404213840400c2d140c1c18601400482c2042207225140071800f108100c0c440070940c2d41a040f00303170008501c0f1f10308080c8800e02d688040148811411810070b402c0d080382800c00c0405e07500512551002c29800071100703074600505801076510340801d100b441d40015445140c070300001d60180d0040b01507080f840301c01030661111b030184460100d01c5d801050185240d002c00e01c1c08181144080ca000035411504001c10100d40100000803d124104101040c4200c02c0e0840320360348085402c06100f08100000c11510a0400352710080d0b403110094150410b0b01040103201f0b40c03c00c03402c086689805948502d02d000000c00c0426000950708000744e0040e0008100e44c5050f607801480c02e68110748420b4500e03429031440d1182a190340500312944c0030300a07912107201010105101c1d40202c1d03d42400309007004100350010310301070704840c1c008611030300540708 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 205277077 1250 205275827 205275877
    0x1c02030f1b06070b19060b0a090e010506091503070c21021b0a03020d062003150f060f07020316120302010e031303080a0509210c030c09060d150c0203 66
    0x410f4900c22500301004402e152079400781c0300150b1818021404d0500e88564011665002200c000c254440700c0742d8134000d000d45071401c1c2e61009001078120510406003084010f08503a40c0d40c0c03006008240e082d4038903960340c0780d0b048107a0b403641000c1401003040b0804500c40032905410819003102c1c00c0035800761041d1b000c090411a20f13090380d144c22564401c50903481400941090005011114070405000038405402c1c80307088040502010081c072450000010005103422112a14050740c6007520000c8030304c0700d008000b606c0e0b40a4406080e078150008100d100a5640402a800c15200710781c07815294144c0303898078442e01c41d0404005401540c2040c988280d50b0000100b1684655403013074800c1074250442e641c00c01281e1015200e0410484240f141032015682d8202c00005c1401c07080042440d1802e0764003460521b040500d80504c0398104011101c0076845091615a00c034000f25a0700d138641e155031070103000718454001d14411181ca403661509a2980000c003d00d5041d2406602a000300c0e1404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 205278327 1250 205277077 205277089
    0x801050103231f17061801090305040509060f10020c03010c081015020f0303070207140303030f040611040b19030e060103030c08091f020a030f0516021c02030f1b 71
    0x86400d4104466a00099801c0c03158143c20450720500d41d0802822541d104040c3d549543c1c003d10840d4550088024014400801503503104c20200c0300000303020821554401900074021441080c0c09200740d000052244c0c0c1e5401c0303030741a44010040803c0c07020440301d28000d603100d50000b640b80c001c3d841e0040400d02d85000380c640a00c10854514089501803c1c0f074400c881403901b2440c40815482000400300010109101551060440d503004240003032500041e00d00340081144041e00035003041052040d00354904000c1a1302940206000ca2090f62940e03256038144103640c00070a00c404041740c0841c290314113110010130316107503942c00d00840801b140d140303486107401c0c80300078040744411000c0c20016400c10301410f0000340007070030f6852a0144036000181c100b4000200b400580060714040c0c201900500d11400c2c03610700d45002800c3c41d10486403131340324601c0958040c0c840d0303003000c1c1900c02c548004a885070040e43d028050340c01c00c0304401601699400e180ba151040f0340d0706010800c010b4241a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 205279577 1250 205278327 205278371
    0x12010e01120c18020c0708030c010f02041401031505030106031a06040509031206030a12200c03070501080619081f0911120f07080f0111070b0402130605030d0801050103 74
    0x4110451842d0785040070010401c90b0424143c240035809002d8003006036814003107071b4010036003400a5036644280f103c1d507130b0031182c80070070502403940706100902020144074400002d880003070900044a4440390803100702e88c1069400f1950541c01c0074408801c101044900e40450b1180801404482e01c03610100310a03904e0480e03013070115600a1017074041c00040d84490390b402c241c0c0039054582c401000d44440071034602c070b00d920001140742448039070010200030f00801004080200541640d001203000a9100e505500c1158100143e20b0040b911941e50b50614052680e01150070f034040c0c035600c14038641c50743d803c000e100081c0c100c40c404800c00c030f042d41d024640e140749d0710201111585a07400200410010021524150b40c4180b280d1240c11110403c00c400282600600401e440000c600350130782035070410070000765904c0d024800303a0000380030306606036000b0341e0407915100030341c15900c030810060040f0351110b5450703c1040380070040160410040c0c0e0581c1d0003030703a0074400500c040042415800d81 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 205280827 1250 205279577 205279583
    0x106050c1002030108210903010f0203070206070c0203060106050a030b030303010f0e0106050a0c060e190b0a1805120a27050406050d11040c1101050a0b09010611060f07050c0312010e0112 82
    0x40031b010342c1c4081c0c1e80c4551451900e050310b250ba0034040c0c900082421a021076128511081d80041070202c0241c040080c00c7c1e104059242504020f055580469110901881048144640420103020072406904003058a940140c222512581d5030380902885106610900c40740c500740b000003240d01c5101d0803c4407040015926000402c2081d41c3e500c4000f0402155013000501510081d0143c070341d407004a200802c0d00038503900f411420310380304280031a25014050090f04140b0000000041c41c04140802c40340c1000302603e4540c0903031901921110810010f00d09030781078150651403055410440e03001a190709803820000b25440b54240700c0c43c22010b003400303050038642907228849850540c10005040c8013500d4207004c0550803640300c44c00e4130b03800d40e03031b1410403030302c4401c9280340381005501c0f00c0c0103140c0307494490200c0820341c015a86400002d8500b1024100e201e001400c0d580c000c0d800c0760360590141044039174a021500b014034150000b80502001034640000003e00d24001803200305e03009030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 205282077 1250 205280827 205280833
    0x30204270201050f090316050306010f05011706030c060c0109060c0e030c0f010302130f15050f160305130303111e1b0a0317070b060618010f0201140106050c1002030108 74
    0x200c940c006507282d4010800115070000d003004a8421901c06009862180071401141035509003840100b6083c100140c0091004241c3c401040000381c1e400082087c1e00410080c02020949031800401d080070f64840140341c00c032900050800c01d5400550142440714000d800c00c03c149441854100c50b40004040b60582c140d000310700c50031161a150045803540d91050400501d00b0700c0a040c03c1261589650001c81030702c00c141d1081003112140c140c0d4141208003850043c0c5040340320449002c0d94000c80d1403071003044241c1034030081094003c800302d449143c5918001000700f65a032800411541c207001c94020540601c1c112502c005120540941e0031112050103801940b404400c00c8041d80700c403805031a4400320310500000452441e101000c004908451587d130364000074248420080b402030052801144100302140780360039000390180445009190140d60010380000407800740c4104920507040303201801c000508a9040001442107070204011703600181c01400c1024100e000901c283e50080d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 205283327 1250 205282077 205282151
    0x30f030c09180e100f0608070503030909130c03020303070c0501110d02060a0b010507021504150503060603011701021908071206030c06030c0203070501050708010f080109021806010c02090907030204 87
    0x2c6180c1c00000303070b8090803001c0b03811850300884824252240340480340e00741c0d03076165018003a1110912020000c2d1400b13034011450f00281c02e001c078500b008020400c1c00c103150038814000810480c41100c000454000701203917103c8010b400c20648181062203010301080000d540b4094000d004a074100c003280003900540307410765809801c100505a40030303000b4100403080002200580e1524800301000c02000345194440b401c141000b00c4c0d1a1413008440103002e814420400300390b0781d400459056900c0100755102c0d00c0e49100341280680210401c0319400a10a80d00c085c00c5607000c9501c62041d8001d1740c035030040032440c11003401200e1140c04083c1050710300c8941030150a029403c02c00b0840c032641704591400515880b11400c5580948407240041c811900410600140c100d111f006052244001c200c01e90542e400145103e140345140d0010903440e400003405607005440c40d0f8a0303e6009001303440c0f9441c0040d41700c0e84805682c002288030b18504404546800c11013083d1403400140c1880301c2c0c00c01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 205284577 1250 205283327 205283369
    0x408070e0a2a0f21020d0c050304050d0f09090207050c0a0519030f0302070b07060204081b0622120b0a0f02070c0605070c0f150306050609031002030604021204030f030c09 75
    0x40c11214844003d10040101e40008000c1c00e1390800a90940c0e00d5006032036001d004c2c00c190549034002c100c0347c04c0140502c00d0001040c80410709a50b01192414400c81c601d83c00d09056558213240d034030551034640302051003c144800030540303546507801200c2d4201d440b17840701c0c10807424148110003030344007034400401400000c5070610401881030290046034051603a80b074443d009540040c00c110342683d0007040070480700000f0071100e0855100e41e007010507180b10450208666004541101c21070040120000d03082c01da440001c0340c0603210b8030b04040803080c010700f01801c00c03610580710703450000c1c98060411380800c0741c1e1080e940140d41c00300c0e8144105180003030407241078021031401d49904110010016000d20400c1034000145420400c8440309012154003504855542d031180c1e0140808002002e0b00740d81c0495042c0da07200421400507101e444402c00f0800a000d080034007075940842d9030500c014190000c030480d60f0b04115980034000f80d00c25000c11a110310b045e2103142c420662000c0c0080794 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 205285827 1250 205284577 205284587
    0x15071202090a09090507080d0e01210f060801020a02070e161d0306070e010f0f020606130608010f02031b070201020303010521060c0918010b070212030408070e0a2a 72
    0x2000400901e90140c0070307100d41552040360307a5504e08403840da014107400c004025050004e000d80c0402802c10310441d112610029044c0d08800000c404207500c0110a0200301e81160700101c10700c00c00107401c20030952244130040c000e41c0880081d402502c62444001001c000e0007100d1482400d02e01c9034400c50780071041c8140c4111008c00c000d20410160304e450108262800c2080c0c900c68216691003840e0a0203500c009008411503a482e0307010400201c1000c9200794000810303d8108000f501e04100394481144c04000404480d00950015401c004039a0030b140666000f43d0301480c2220551820200580c0d00d0581500c20f20708001d0140c1c00c2480100082c3c0352111601c3d40174918611005c0652018802e1603040c11750458a621011801060348121414850541c0094100040901035194101108100d1601034020024443e004500480598240a00a880084c400760044844807602c1d0204580484000c45220300501d203040c80c40c1c4080710807015041100c03055a0208142281c8145040362 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 205287077 1250 205285827 205285837
    0x10030605040c1806170f0a0308090f01020403050115050a0e010b03070c120921050c0904050f10020903011a0105090103050603010b060403050c0a08010903091e0f03030e0315071202 79
    0x1d0440d900000005589101815803241d500c8528000202c40c5c0c180041c1c940d606480980946050744074405208800c200065110303d2641c150030910b4480d0303110b4128526048034540c240da00395001103000020088150400c1c5803d0700d145030a11400f0780c40350140b00c0b0580a80c40b0303030702d29420b4400041000090341d0008642001551820191840310354656101c2000c480c40f03071000149503120200706c0031006a4952000032140c0c0030071080b00303129071500e03599004123041e010300c40d4140101140411100b0040313090b60741903c000703581804128040350b00003034000d443d401d07000c3c0d424408840301803c48441004450b03101611105c0c24400c4074401140180030061415400d59a141540e641c0303641c480015100542c804e40c01003002e81d4111081c44103040b1658402c2a903a2b040100003c0042e07041200c00c41a5600c2d484e1441c4060842d65548020348550703840890040e119074404401e25a0003015401c40f10800c2d1700700c82028803070f034036584003004089034400c000403919141405d02e6030080d00103103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 205288327 1250 205287077 205287083
    0x405030a050f040f081f02180634050606041b030b040902091302010306120b040f050a0b0430080705130819020a0b0304030c082d1c051003060504 64
    0x43d060540350307001d007803c81070960400768250f030000c1d94000c0500c103c081c108401200c40030055040017410700d8201001280a550140f21700d07000700700d00e0015014090020140c103441c0d84030440100e084810049098444401a1130501075500010840d082c1801000c2642d491104046035400c00300000310000c0c21241d00e507641c4251566030b6680560f58a98400c2c1c041c19008120b42030218982c8005022a20070303910065084812071050381c00b0035600800341b0360040d00041c0ba441c1030000392500500f40442c440c0001c1c220507a2005000c1030200c4d006000f200c605465540084180b4440c0c0050b0400d2030401c072000002c0e21110000390303120720550141181941002d560746a041d104c018950900a40c9a6810007441c1720a82c140190720307100c03194400510b580c8407114518102910001c0c404081c03004040d00c00900022028800700404201c1031609006107921a030342d220000d8450380720f40c4442420450700180d40442c045000c601c0c8190342c01005910311001085155948650241c00000e0081d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 205289577 1250 205288327 205288357
    0x9010212010302100c120f02070f030206070f020607060e0303010306241503110c0c0301140f152e02070f060504030615080307030f092c1b0a0c0c05090405030a05 71
    0x44d400a00140d0206d2101c0442d6103a80310030724402a4000e1030214558841c1c010010444010030150b01c8440032641082c0e0403034501e00601d605400410030358450b0300320042485180c041080c52084d80440038506072481407000340501035907225010004400c13072074200b034801c400c00000c02080211403007000c00a403280c2404660b0305581d06504d4441e030000300c2c6524490b0070180340801289400c0c07007030701ea0069000241a21038200801c480d806804014401c03000700780700006011a50b0f03181882c5005214040c02d282c415041c11001d10484903054040b40000b6124040c2c0200d40e0150110b480703000d0381e009558036418903165441e0803019260207544000031004651010404620920041c07203428003d860f143c41130201960001d10703207400c503840850003003034030110142249465140c10600f59804c10080f03030725807945141d402c4008603101d8101c0c02d11000040c80300b00280c1000f920141c56001c1c00e11451019072350b50900040160448001b411900200f2000c0001c0d0b014102405824600c40c0c61 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 205290827 1250 205289577 205289597
    0x90102070c09202b0e0102040e16050307050d020a0512010801091406060d020f041d0604030206010e0609070309050106180603260304080c070503060a06090b1002030405042301090507080901021201030210 89
    0x50182240d00a410507030441089c841008032019a0055481e550344151503c0c1d032441c64075840081c0079000306035440b016141c000460040c411f1060041e03031003c40c440801ea00403969241001c6009040150742188c0b48030311207070b81201d01c4101081051180304040c041c803482c8641c99081041c180c845c19041c075409a5103581035a440d00101203040e0000441c00c0c0280340320304050401070f00d0710605034021500c901160307042050580305c0b46280703500180d85042c081542d07651450905d001d40b00541044a1340071030050103d900e0320681c0c00c0b070300440b4002d02445140c2c1560a0701e40190f840302001d500c140000801c0420001080f4000501101c01d4810943c1c000c15115800a418074600b9250034800540381c540602c0500a50320800100d0403040b1801046d1052115003c1d44a000d24407401d48200d50b10f90742c0942103c14090202d451404254500550b0340c0c4846540004003000c2e5500c030b000611080000300300d0907052003222100c44040740e0088950f80386500708981c00582814030b400704044055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 205292077 1250 205290827 205290851
    0x30b100203041a0c070b03010e090604050d0c020d17030a0f05010b0933071401090c18021b010f050606030c0f1b01020c010c0206090c01090e090102070c09202b 70
    0x2401c800703040441c2400f5503e514011031102c209c080035100c400d80da04180244000128001a1100c0c00403040c1000000680705000085c00340310026009007140c03083c034000316030041403c030085100b003c1102d0204000194007115004a400174013071880a1002008200c07264501024032002c48502c0b19581514041000d13580c0344100c03900b0f000c00c51981c40102d04581000846042d4260752511100204000011030300e40f0b011401d0a4420141d592018000d0f60b003003d00e80d5011034201c1000c3c28200c280407855140e0b468000d0031441e809808542c40c2101013a405d1900e070b0f088a015402c4040c6503802d25040c60b11100403640200c5001e2004040030505d20b01c2c60500f800038090800e018400010780083c16180681014002840400c0d250025500240c040e80c1201c04201581c846c54500751140e03468055250082c810140058000023900e9000900750070b045e0041b4000c1c3c0c480b41c1c3c612581102d03114400201e400762203003100ca003810b4120810100e07c050203c02c0900c0c0403200000c81c00c14200c1c0707 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 205293327 1250 205292077 205292083
    0xc070507170106090b040b0904030e0103200909070e011e0210110702130c0c06020c0a050a290714070609080d020c0609160e1003020301110406030b100203041a0c 71
    0x144101c0036075110401002850500c2c03140303c020000c15141840004002000a2401e203002840141808030001031490070340d10980c40100c0407180440c405e114004a1030340c1548a4005020031403050300c1c0c10002441481c0700742e00e0040b8035501078503045808040c0191004180142c40e038070400b14072901181130285d90460091046a042da035103115a996550700500411100070034410044505004001d02600e030b00c40042d000440d0000e20058495001ca0303450b1341085035103d0050300340e00c6403258201c01d01c142c0c180352401040506110304c081e1244000300d6041c03070700202e4194010071146815001c3c0c4101d614002e0611a208850009500d0300c140c0d03400195401c0b030b200c1300018550100b0104464201000419005007a102c001d068180040e182401140e20a0190640c0701913094086807804075120905409194010028010b810503409400600c1d001403058038002410b0000b003403114244103800b4482d00c07155a01175481d00f8100700300c41c6180151159010001401046018400c100c18 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 205294577 1250 205293327 205293359
    0x80f03070e040c08060603070c0804030c060f0206090703120c0501020d0f060503250302100c0605040303053103030218030a140c12070302212b02150c070507 69
    0x181c403980010307603505090004880303a800101040c020400284100e9598a90942e94025810b02d403080108015107000207035401143c1c0b0041c034203180070310045031701a0449a1710401881030b900f202c920382e4500001d560742c0e48452002511060601080e1102030703110f149501e800d0360280d00054581060f000c0c10300c08031284280c411103500c0d9a078000740100c1ca428408007014a500c120203580300d140c0c503030122360725000d54070000388200f4846612120550040c11554841c40d0031505c10041454903080140160500321506508000140400c408a0b204000e200c00c07000782e0000700240c1203c060b82d00f60f00a501c640f00f81000b0084031043c100c140c3e902009480d00b2a8850b00c035000510031044200c074601901c0d00b10b13683c480d9090100b41c2c01460b41c0010b84c1c00486c0d4049907400100d08060b505640c0381408000203030360a002d00302029514504482c59030a45d1042124100d08068000c80101c0e1212480d42c3c40340c0049500e10045140500c406d800341051a000e001a07547d0035035510014901c070700c90 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 205295827 1250 205294577 205294591
    0x509060420040212090c1201020408030f16051f050106090608070f180b070b010803040312140706110705250306050402060f0a0908010e010b0a0510030902030f010614030c090f04080f03 81
    0x6c00b2030071440d0f0030020703400d022600030070000354245410310b42a80c0c0c9902a0f00c00c0f42da594100030500351640c1c8043d0614465980c1c10500340c504901003043c00180d4002c0b4070441804d0541081d00002c0c606119501c00e004881e495902e0510a4441da2412134a2400e0340c2c56260030020103590140c00e00071542d108000030300c9051825075070741035070746000700c1a42c5059100d84943c0c3c0040c0020800303c0e0701260101c5d408400b80c5070125000480b440301c01c806006000c0080c20f8140b501302c0900b5040300c140001c1890500440449030345814102100e062400800c0304282d100d49a8401040002c034241c000c0350700306200412050a244e200c0780d1003100c0da041503180d14005103036910104040d001c03c1c030948121034400c0c1d000b885030034500408906014034512900340980d520030448001184258420842e0036401000d0b10b5080d0340030038a09000c0d24203409211008159101c407100303280340000e03440c8100007025003007034000d036507082441001d6000107100f034401c03803c00c0000b800f5140243c0001d61091403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 205297077 1250 205295827 205295833
    0x90a0611070b100f03030c0c0e010f1815151101020a02030a091217090d050a0b10050910062303010306150803030f2413050a050906042004021209 64
    0x114900b0710034104003029048100180941d84180300b5150a100000c060780c0d01400e041076800070321302e401e0781c17550465031003047d102c4100c80000c9182c000005400d412944840c5003084048100191202290107c0032010400c4c8030300792007085400840c0d50407419403182802c1c003d0f460020b0301022402ea9002615800060b080001c021401581040803100074000705101910400c030f403540c0e42800c1c1d06026aa56a00c0304010a100601d81c0d01c140000454540c400290385038803a031803401c1484550f043d0380b0707000420a000404030380c0f42481135105104020580300e00d20b10360324210f03050f9482e260702040c2d8190003155105e1005450b02e00801540218030401000a9404481c503140060044079001304032550420030038810410803180c1c0117500100010103c410184e42c045181168641c08001a41c01031401e80c0741c4243c400c1240e002031311031310356010148204c2d60f40d903403540e031140c1080f100201449000b0300612001e00795194519000c10014000504d094200c00103080341c108101c8882c00264 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 205298327 1250 205297077 205297087
    0xf04090902040e0607210b130608060702030a020a0807020114040e0105090f07020a020f011e020601090c020718020a0c06060b0a111c1202070c06050a14040605040e090a0611 76
    0x82003d204840303070f2880410140c046030920801c024464a05610b41030300344018805c100701c040219900003030000e0401854251056000070f816009030003a072051940c640104c0e0300060300b080c008011507140e10300a6000d0308120b0519034130410160400780041c1d0400030700101e01d80b194900c02e8010f0000d40114441000150303d00020031801c220000d001e210307203403d00740901500540009903480e410741d040304c0c0740c1561f074110302c0103d4035140d039001d4034003507944004020300c90a40c0100380281603c410305014054018100340a9035230710713414414101c0d0340c030940d5081560124194060b000b032001601d810000310340542c45800a072070340c0d9080403013000e50000341600344503001018100110052400b030840c0003480e804041986a01c500440c2c1803180001e1440f01080da80d90450740303000d52201075484032582341c440003841c0342c20008a1001052108120100102ea03c40a0702d04460340c0340d450621341400c0c80100006008003070040190b81c802d24000d030001444602076015442140c8204076269 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 205299577 1250 205298327 205298329
    0x3080c0607091404020703031b0c06060e060105031618060906020d09080d050903010908030a1401170309040c030b032a0f131d150a0c05090f04110f04090902 69
    0x49000030700801c0501c05035000401c40c8032402101020390f0b8008030303001170315600c0381d043c00e41c0913000c165140c1c0b181040f181204111035401c036a10401c82030240300304203c0942c8510441003640070030381c0c076070b40403400070f1000810f00c1c03241075140e000f0f10b01c281c40c001c40c0d03280b03407032042d04101c24003a04810040f40302100f05101ca01c0c3d04101c4178005042c2d03071414000941c54421481e44403d05480020100b050010356425162800d4001340045036000100075980d14024980d4030007400c8045c2c0e0031215030201e2000180340d410341c40c540700c100c010843c082c5241030098010800142501090360060503118105160b4640d014800a0018034104086900015011a0b00c1840030842d0b5a801d02c626648840419562104e90b080a0030388801c01c1c0c0061480c420071200d40142d82041e80600c0b071407049202801708402401610303801041c15a1007403241d20300c03805040d0307110b000f41d0f0b04030344e0084290158000d20f880d103504240c5c1105080600d49107405031480c0259200d40c040d8011408140d1104000c0d411 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 205300827 1250 205299577 205299583
    0xc0303071724030a230c0108071b0c030609060608070501050715151802210105010c150f020a030506130e0703060902060f030106021501090b01020304060c0c05090103080c 75
    0x19034441e403240d904680c5014101441d26498400c04911215640b4200442d41c1d1002c2180d1800c058001500c5140c0c004160484501e0794950b4003420868020580414550350080d200395010f2056510f45026076101d070a42d03a1943c0081c098141c5070b900c44281c002011500310320030140d805006600c0031441e142455030903442e01400c2d5201604008007040b540d4003089003494000724130348004030041040c1d0105407030748985012a403c040203020b0344881266801c07115034010301810741040c8510712051112440fa00c80030300c09100d610702207a0344005203000240072145800030340102d40c40026542c1c80d1342400000301d8010010801c00b0030b98071001e01641d0714045d2007a191100c4007c0c0300303101407050703255080c5e210407441c8001004942c0360450b1100b19a660000d50700107081e4a14226103940c3d480100079074503490390360502c0b000721943c0000300c1d150b68180a0403c007204117800640c6450300e000701c00c507006c4001c49000d80da081c2c200d5030007103282d54075441014004c6005983c542d880303581903401203003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 205302077 1250 205300827 205300847
    0x10501050a08070303050d09020303040b0c06010b041a1605060a1d24040c09091a06090123010516080a020f1c050702030f0a031116380c030307 63
    0x407040c0300803402080445000200745040e203074103242641e01d034406082c4404c0034054111009506020218010644155440141c42411900001ca5486980e03a140c03140c1c0c0b03803081d40a0701010bd10085801300719441148000d0040d11591018000f95440030f403101414003100b5a244010301d40c07a0785401c02481941c103541b0082100100c042d115401900e48000030b231f00504c004410595212030001002e1000d000e141000030840c0c0b0303a060110500c2031600c20303020760140e00c0240c00c4501000100b010b0b030821100540c10381e02d60020003401c40b403007010b00140480b10303000628100b100812804001d05e040d1414207007201e1152103010380301c0e10043e1010341440080351a5a40e1f0b0781c069440461441000c582c00002480c46080076035603500d00b400824140403e6807103119492045414045c03c16601030514548420140c05070303031401c2d40c104085281c16002d4407921441c00c04440e8041c00245080200e40f1041d13254010644842001000b2440c1a400c00c003151040c58001008002c0c80d140c000b02514 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 205303327 1250 205302077 205302079
    0xf070602031809060d0f063c0b0a12081b0a03080609041a1003030e04020f030a0f0b130c03061d0711070503010f0905070f06050d0f06030204090506040501050105 71
    0x150402442c0d8500e030504042d245041449200c1c00408034281d615180c1c0d612483c180c00009005c0903012904080029041d00d0141c00c000c049400c6801d2140d52110000c5418010042e141031100d00e1040350b03c20250002c000d00c02d600144480c0006010300c1c01404c040d1070244100080c588420303410020500404d11003c20400c0c54020030540c01c00030b940040f01543c800c038101c1c0c0d4a5059161400d150300608500010038448011080c284071040050b5200c403c2264401d680301c1680e4420b50003880140e000708444005110700920100c2e100c1c150542140d402c83c000c0c403100084080760440040c0a104240400740c1100356142d0321110030a40c1401060081c0251002016a40d03498a08070a05a080203000310104a080850048444010700c402001804010b00a0210200c00b80d081c400070503500e001180c1500c241d410029620707a44400f07000840d01c043e21502d0404856030b104801401e1183c5902c00d125595560100c01692640701e0040d00070b002e070004003040d281a2500324219001a004a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 205304577 1250 205303327 205303333
    0x609050402090f190612120f020d030b0d0f2402030103020d0204091b0b0c1018080a120501170d030605060d0e070b0d090b010605090117040206090a080f070602 70
    0x9038075440c04090f0407076140c000c00301030750b078a8110254018030b403039546110711420703d00001031201c0207110b5040030310f001c0c41001c011101e00c3d039001d0701c07002944d10044c00560004642c00302064040e44c0a07581c0064041c29295051348580c0d2020510303281020100c401d10007a903c044491900c103044191945845c40085145504503000102880342e1402c0c020b20940d15420302e0b204101c42c0c03200203a0941907180d1f1101441c4d8446240c11542c0c0c1040c26400344910421440743c841000ca03000700140385150038400711011800b030f11003007299401a0b41040c1801052402a00300003036512490b07000b00114840780398aa81a055941d0405485001403400c242c2094810301c916034400044484500640070005059072880038001c0c107100e0290710071109c520003c9a900e4001020b500001d08441c8906030009c416a2907007000c0d20940154294503000528100d21001d450b609001d10b25001400240040d082c044039800262007278070150452074280e082000c0000f82a4010804c81001c1c000d00d0000e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 205305827 1250 205304577 205304581
    0x230c060c4801050c0d080a0c02061b0306060408061003140d020706031a0603010806070e0108070e010c03030b03190501062306031b12041703040302060a05220c0504060905 75
    0x440c18900400a580120100804201c94581c0c1c081e0049503607800000055490000b00088040c0c4181d0040311844c3c100d5044c4402070041030300c0481e12910a0608601d1002031041c00c94082a49400080c0309a130031590400c00400c0212040040344d102d00700c4500207200c2c43c4e08518000e0401c1c0c20400c6d00980a03404005c840f120660041400c106441c01860700050440c03003800e003080043c4245550542240001001160035030001c0fa42d1413040c0004d40b90704001d0103840c1c0c0115030414086034142e00082000c070400c04290b109400712401107000380b502040d0610a503001030f007030480c40c01d403480a402982c1d40d420208a0203000d140b00500c80820010444540784019460480300d11040500c1130360000b00291000444460024103105400080ca0f196020262090300c00b00b01940c040d912a003c001c1c0d40500c014419045078811503069000d01500c2d162400f202000c0c040245c0900c0020241c4000300404059400144070103030700821003020828988018841154081d41088480c2030500c81 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 205307077 1250 205305827 205305913
    0x8070f06051209100e0c0406080a08070321231027110a05070c0b040311010305130b070518040507051b0102040e0a0c1b230c060c 57
    0x1080e02e4040801044500341d41e5521035003142801c0c0300e00003440049160403104141d4900002e03000e0140381050310304104403521036201603952070320300c02d0040c0216020862200080e105003421a82254240c0d03450390b50a50710300965050310b80b40d4400306802c4245c0c00745d1061403155200c4098120703040c8070090710340c2403c1a4038090f010580d58034030341300700b200c21b504154541c3d2280d100128005a80c401c640e211001010001e08560000e03070241c0740e000c1c481c140414180103030710460f021a40c0c042c80d2065809800300064020700001408400c400101e00f80180100d1a0f0001c0207202d070070b0700d556059a680015407941c450800d01c4100c40e014903c0c210030410210381260803a00d1300d01d2108001c00704403407074030245406031260360003d1b02c0d60400c0006100d242082e64014803403840c4251a03102e48180141d50100580c041790784082c0008146010800d100d1450b005004d01c0b011034402640d8589820300007040c4145d000300c280c3d020580c002003501501c850440b40300d18002a00c0c420b5050380b800401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 205308327 1250 205307077 205307087
    0x6090507052502030d0e0607050111040315140402210708010c1106040b0126011b0f0305043305090703030905060418050604090f20040902060412110a0f08070f06 71
    0x20300f41d0030502502801b8010300b41d48210565086540c058002c1c07208040d11030340d40340d00c3d40203031008172841210b2281c0c80081d4032107409002c000c8803550b06182a1036580f9020802d040c114054501003236854803880c4264080f06000140150007104000308505084d41030041c05900c94800004554024409100002d040c80000b9411100c1d160740740500d02e544086c840402090040da031100961810750300d44410554481440420381c00e0f500c4401646020b0041601550fa0442d402810000e03239004500d83c0d010703555811446100688410320312014120360352001c4070826110465903510510080007050b60140b100c02c05004107941840c1814a004c945030781d400385601d2a01031301034554000909c1e988a55202c01a44e07030b000380c2c002032588200e060074850200140c5c51100b1007070803110044600c2c1018000c07015242c0d80500f06c94582483e122813883c0040c40b0803402c4680c10001a01c81e81290f6a210700180030b0714039006e034004c02031701c0d01340311900d8000c0e075a111440d402c1044070308028045d045 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 205309577 1250 205308327 205308343
    0x42a0e0409050c04090503090315040501051005032a03030708040312021207030305061804060906151208030a14040b0108010f09081801140f090a050f100507060609050705250203 78
    0x1d0b240858845c2e01450464254000c0030b42e0f0540520540401a400f00b404103480303400b42e4083c00081095444005039503080c0380440c080d0300e400d0b51052030b94484e81338121030350b8180441015451005c1540f450700090031544003810076142d466000c1418801c0c0002c0801c0b04540b01200d000500403403a5003141d845007030185040c00360506a940c000241c060319002c10300c8241000f0a88074444500d050300c3c080001707000303900d01a03030728510703000210100810580001d410b681160490780c06101181d591012143d01c010b0881c401f40303844114254580044c499040c0c0114811622a46c0c10340c10444c4580c21203c0d15030034040400c1c00c2169500104bc1c1000844441410303000030400c0021034000181c0b58018500002c0f070340390000103103901c51240b41e44081c2c100900c08440203128256610704100050440c610420351008002c0f1144031682c4c082e100170001c60744070710740200c2c115035283b014070304030740c011641180030801c0000c0d0507940d1500400f445100d4078019010038403c46c00d54021035907035114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 205310827 1250 205309577 205309579
    0x12020307030f0f0203070603090b13020616050102130609060210020f0f090103140c180102150f1f03080301060e1206071b0f050a110a03030e0f042a0e0409050c 70
    0x4800d8001c060049100710703e0b48841e000303030488901c02d030380b60001002040e107204107075094030405003c10004015600040a4140c0041441e0700700030180f58940516800c1c103800f110507660801c94100c500d8102d012843c000c100c15101c1c0011603150150207410400700103109402544100241241c8001755001d80d200142140784207038036035140400580041c407681c00e07a0741c2010035200c02c00c104440c00100030120005c10104110088a0310001640d8404505a032214100d0100c4009525014030708241035100c00440340100d1841c5800d403910044240e81d0700142c3c1c20010000043c41040c2d0000560071800805a60419013042c103259890f0300c400020b04050f08100107400300426000d0404061100250000c4004000e001e6620704995148480002200d04419a00c101d02c103510741021500200d98060f10b6040a031444841044000f904062442e503000c0c0d034a2240810500d25810300034001074036130320300e980c00c115050005098601480d140c02c0c070490501c0050390025a01007068500044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 205312077 1250 205310827 205310843
    0xf0605070303020a03180b06030d020f060a0b0d0b07080a0501140f0405040302120d05181c1110050a0203060f040b0d080d02070f0f1209050a03021201110c03131202030703 75
    0x2d0031310400c8010f0014840840d5500d2542800201404044040940195000c400b25036448040324026071b00c59946851140c01d03134004e440044c9645841e9008068114402409800060200d0351a221100000c0e2160000078640d202000a0204188600760260039460300009a520003580040d9454507220016800b075625980070030b04040c000c028680f00082c2c07182d08a0303103c00320b80364600003e1004556401c100580c030700e0310103080381000c030b4101c12210082401e228510402d81c41130356076a0040c201030246d4403916240c0e2880d181a03218640c0203c0c0d04a4016a807824070100700318500d01203032030b110b01c1240b074080703607440725035a40d10600c14155001e00b0b010b882d00195040320000380180c0b64040c29050850b1110000c00242a5456071005e2041d08041d28070940b0000c00c4544c00e1040c011290440800301e4140050300d003901000311500ca40c00e0000c22054846541c0c8041a08014408100c6610100300309a58500a0009074090030f61942d052220498903000240d540d1224030005d00001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 205313327 1250 205312077 205312087
    0x70e07030e010e0f030901090b0f0f1308010507050c0c01140301140303160c0303020d030e07031707060c030b03101b0c0816230309100e0607020411030a05010f060507030302 76
    0x41c00039000b1150498410007502c40711903d480c0307144e40701c0d80200d000c1c0340010510400890303030031013000944903803e5400394414281100411030041552081811030038003507071030304000384c0107109000742031040c0d24640c1c80c40c0d100c4c0c181e010120316007002d075400c5c9414003404500400d0300400920507241110348a40600b0040c01350f40001c6803c3d4030130305009644850f8a00c01c004284900001300b00204d0307100c2d600701c40302485154030490403582025a100c203503400c180350400c0420f10f18032006003400114041075251400c9540d6a00403608000e036480042901c07550582d0403440e081c000280102c418500c28880b200000084003602801000c1c034800b80700e0180300d89401c0c0841f080c01c0c0d1358a40f840340218642121141407884258801c11040604918584490040b000d4017006942425102402101c01001c0030b040540359070710b00340600340c1c019030244850809a580d070300a00c504251001c81c12a42c0b8100710340150140d1f0300507007100300e42c00d00086042190560080450b0850b0b501450016215 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 205314577 1250 205313327 205313351
    0x9010e06130b0c01141f0e1009020c0709063f020a0f050a1502030702010c060f0c0c02180105012304030c0905070f02011e051b03010305060711070e0703 67
    0x10907025001610640c00104030209621815404030700d003c40b00300b560180582d20f5043c858042e520b070b030640208401600780c00b0058030b0100d02e54a90400008100030402da6103401e045400c03a04980442c540c1070307101a0f01080107021900c504030280c03400200c17104a000c080300000c40070710310074a140101415500764030b02b04203400c201c0b940d2141d80d0003402d03010030344d0b42c6250402c2c882080d0f005080c4034014510000a02113211580010030858940140d42404440e4005440704408143c09982c01e40e115042440310185c207204512002e82e83d0b0b00d030f50600748801d0041c4a070b07014244540140c401c865000521680e030700b05041e100c00401c2e1a6004c200e080724901010164026a88000c0c251008418017080030912600024450301840e600c0364001a00781404900360341e001040b10300308038010303440c240d8001c1c2e41d0340185502110415001072a008007406204203540709a105032039a8001800744010941e2201c40c8442003048080104185c42c24004140e110354006002d040a040c5d4449840d118 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 205315827 1250 205314577 205314607
    0x80c040e1005060f0c070b03010510050a02070b04090c020105010506090a05100e0306010905150d03050a030b04060f1203201b0f0301110405120609061b070f080d050a0209010e06 78
    0x60034001e043d00d07403a01d04803844000c140d00100300c240441e00178007101007080700c0741d174050300e040307031001000c0441840034040281c482d58001a030103021030044090220304841001c00900041410000010352a00d00d10303002802c40d030040c0c0115204180402c444006950b030b050602c1c050706d03c200e84201c001189003200303890b602203101489800d805480d0001810036070f81c1c1e00591003004011403680c645540041000388590000e0b0340200032480c06e0201031032907407003503000a80000e00074000007101500c030344140c04010002c1d4031649044200c045014100b40d0310194240740620038044440900702c444100a8403000401070422007080000c41d1403201c0d40d84c40f41c01707800d5580054000c220010030301c590800107a03c10f0007001d0090348140300c98044003000061551086e45c0c0c1c1c2010744139a40310008005201d00907001814110320080c0041c0010a44500000c0c08841c802d510b0030b07640742070045e0204240c5000801e9460003c2c814451640c0990700030040040c001c200b00d40341f665480075032000d204 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 205317077 1250 205315827 205315829
    0x40e070509101e030b060619181a280e04020a09170d081e040210030207080a09080c06190c0203070909080d06050a0503030a030f0605120a12080c040e10 67
    0x10309000011003181d100c0e40955143d802da80c000c54945036681c0e541d109000880c418100c082c40d0f40381e0040c1406003454843ca0324009101e00c0d00020415195581c003c0f48044501902411940c0700009241c000c1d24654a42014190142c0005c00e00012911000038004110910805005640000b42018000c5c030940c6454003400c4119401e2040c0070b1100805651056494100e202180010001c54403248081d004064000301c0160514440e54a070340c00d0100c2011102d40842c2850307002e02070f29002513820006030184000742d80c1e810062038503140c0307420719002c20b49011501174071041000c9400d0007441401c00420b103081d4141650401d0580c03000c00d190003220360211400c90b01e0410760b1000c1100400081c030541d050314000348615034441013041140000ba1103441ea256001b04118404940030780c010007280008140c00280300c6964802141c03401c49450004a03460704001c1103881000007030500c0c20440c40b25460102d5103860605401f5003184a030b80070300b035941502080090b004140c2d50450760 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 205318327 1250 205317077 205317089
    0xb15040b0a15020d030608030702040b06070b01080a030207050a0605190c0b010902090405160203041e030b0106090e090c030316020a050303070807120c03050d09020f0a0303020f0c040e07050910 85
    0x144090795900d5160b0380d91203520001401401202c069003007451090003198162031280300a1407a0010316420440141030320059982c100000348404c0021455801704503000300f80c0700e0b0181599040b20700c0c00a007006080d80000f84640242a81800340070740c46400c2c0d8001801c0c89070300c2020109014016140219101402800303140400002308900b0b440ba0044c1c0325001e000e503010702040e11440403491808021200c050b006920601c170802c002c41d8020151008030301c40d20301440190f5107945807180c00301e070300760448404110f09400812029010041443e841090390025100400c03001001985900c40c0414540e4003c007151104070940d1b803141004002801d00404980c1e0303403406898042c806070800e40d01607a00e440b91000f0782c0305071030180d11074034420741d0f0580e60350b4a066440c52502005001402c01660403005002080f0001c0d11018051070103035009800130403400c3d003020403040c60f001030032403260701841c1004051141004005038020940390100d03030040e1b955544843c07802881d40158828 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 205319577 1250 205318327 205318339
    0x813080d09090912030221010b1e16020f180a050105010f02070303080c030c0c100902091f050d0302120a03020d0b010512060d1e0b0105030606010206040b15040b 71
    0x215110001012030100800780c664440301c07a901d00b01c0e10200c4440060182c09500c09954034000c1610960050984510350f034290103a0948110b030381d44007100260040a0103080000304400d801682070b103241800802105403d25002103403049032007114213058001d025400c0c1c3c0300c999010742d880514044c034502010b59502c240d894400540d402503c001e00c12a80030582007484445014400720b40c0c0816250151a20506a12031141c40c861551002300049a00c032024000054079030300510244410030390900c40455100818010040e54000c0a0702c1409034021388a01d0904800d0211030300d20840340210760341d4082500c14202603003008040c0d101d10a400700d0004441c50010340503405400d030681115020082c00820600649003841001241c0c160090f103000000c140d032601d94070b0218058890318804d44003492140740c9240c1305031340c01d900701c03424650b0310014046814104070003a40038609100625840c101900ca210b0014800740140820f41035044c4500d5083e151501b00800b885806841 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 205320827 1250 205319577 205319579
    0x4080d020a0c2105030f040303110a0206070e0609032e11030117010c050d020c07030204020a050c060f06010e01230f0a020118050309060d09020405160206011d0a090813 74
    0x904010ba8082d084983d01801800104003286840100c0140b140c02e440da1455900c89148516019034000c104900305038841040440140016010301811517041d00203105038102050040c21030061020300034090740003840702c0d80c40c03035500150b0b42c041580c1480080e181d450403001c500701403018200c604041c190400c8003042c100c00e1114021070480e8030301c0c246031618005450f446401c1c0c401c509a0700c00000c1c0140071200d40703184240e0042817001044070403518000c0c2e0f40e601103000c2c1d0300003000401c04100701298201c1d6401d01845510f0340051034a942003000e00d820400a402c11488100b154100002042030750380c401039a0325184d0300c0c0840720b0403158603200103440c003c6099014004100c015400c0c69162100c084110003402021a404009142845680c0742441001e030001185c4d0100f05403a080c4d1000540c50f0f61146034080c9111040240190903400006481c00c00e040e449100c24041011107424408403140107550844040c03803002c200d51840342000c0c140f41c0551070341e4441c2035400d02c0c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 205322077 1250 205320827 205320847
    0x90803010e0907031205361908030a030209060c0106091a010c020306010e0a0212100815010e01090f0207060f0b0301060f0e04080307020f03070308041a01050d0b04080d02 75
    0x594100c900110002105590301c0904544883c428070009041004c103040655078540540c007e040607000d440e1314020349844007440202102c44503045015840c402d400803060500b003490300d83d09980d01002c203c0d1381e100d20307114075582eaa1155110300c104055012071340d1141551403c0444460004400c028402d4903220103070300d4020100704444510280070129881515406582600030958000340604080ea2800142c2c145031000100340350089603007000700d4500d94400c48031142c01001000c8007800c4040c144000d01c0d140010090f1782c120b180030300c100100131044e142c14007241520502580411410001c41d804006401540c0e00203101c2030070540305064140e110384c4140240e4000310300912605641c0e11f02020140d180340079000361001d8590002d4041a80c0e40d00554200880d44100c403c0e4800000c40e03141035800940c0110001a0100d0038041440498500300880601411900041c0e5141900241417000c0d11600100417040c1000014240580c006c161408600c25050942d66204122 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 205323327 1250 205322077 205322093
    0x90903090901140108041407050a0311100203030c041a090607080711010305150f1f05070606150c0f050109140703021815120a1a090105061203030705070f0609 70
    0xc1401255400000a20f01c0303000d1004010700c03036060b141d4825940f115110340d0003942d250400e400091081c020700003034903155400d0203002107004070480c40001612004000c2034512401d4403a046500a0003404050484007080301c041b24100000415128207114110350240074003083c950348220f0210f1990b007070002d01c0008000c014400d06200407411000c10040d011107a040c0c1d00e1240a215428032111942007007044007151280003810128150860210201880781140309400003a2010074028200001d0b8082d20380500301140c0d140d114888845c1d0003e0154540a8004c1c041990180c1203406114080d030042c24040e401041104a0a0042400b1980c0c1c00f41d61104a0040c01140d010109100c0412460340c0941d500111401c180300610041048160000407a107202d405100c00c0c601c0010184141c003076440e10f40031840c1d03c4900e0182d00c29401c4850060089001d400e1203080c90030720321008801c0b00d07407000c0182401c035104d01e4503060500c1c07105c508540040c00280303480405010b1110308 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 205324577 1250 205323327 205323337
    0x311030a0305071209150207150f0b0a060903021311130f0f080a08070204020702130510050a0b0a020703080f070501020c010509120c0c040c2703020108070908030f070f02090903 78
    0x1a032030f00b0302e500d1340503588107040300c07440c800291035400042c0ea0581c40101743d800400c4801d00034a000700326030390075030010000c80d400341880385601503481801d0985810034142c044010007983c00c141c15010301e10b4010891115900041c901c6042d900c142c03000216400c0030545011183c24800b0407000390700c0c4c15960048040c00e014400c50b0101000c00020303414800555036041e280c1c084501420000300f81d081c0000f9401c1785400701c1c0d11aa090305607088044040c452244035080f5060310034246071400050040c1c0d03c60607001089890f00030440c060300d89400144030030841f54000c40c0d40380d40e120886200b600d603003e5400018101d500008494140f60015000a4003801e402c00c16544c0c42000c004020402d0f01c14031320010416001100c21102d23a2505074401d80c5a0b00560030910842c801d03006024500d50050706051981b010010402d0040d0b5a00c814619442025410440082402c100c9502e9803801002c0d001c1c410b8a10016001c010003d081108101056000d0300103169810100c41c1da81d129009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 205325827 1250 205324577 205324591
    0x414040b04030c02120d080421051801050715060536041110030e06060607050a030807210207050c10200a052407030603020a0302190314070513060807120311030a0305 73
    0x10391040c40c404400402a0200800c2c010b807038041c601041c0b442828052f41d0580368217410b0000071b010070300c0030800c280d04902c03071400322200000d42c0c07e040034204207005c0e0b101c03c05d80351000d03c40c3c6080d00340001c020064484080305090144616030b1a450b0180484021401c11074120b07801090065041d50544c0003002180140d50980740708e5502d010a02149000b4820042c14580c4404880d00120340101e840c5900002c15103803000c820488030031042d1084208948401c0625400501401448424411400204411030300e010700560003400007400240d004403c4601c0101c0c404201e40640c2007040a103031031550040c1560600300800703410100c014843c000f4101000010340000d00740f10b00c0703403041609480d4024000c924140c103640900403940074102c0b6491440c0e0f5880e4020001c556041031129070184040000c010315820b24085c070400158046103807040908141052003540c0780411004e042c0c48480d910700c0407403859400c0444400350024804880c500000605801c5d04d41d15403c1188240d403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 205327077 1250 205325827 205325843
    0xc03020903070503190305030c0d0213080c030606220b0d23060403080f0702010e15150d05030403020103020a02120310031202060403020d050a18140414040b04030c02120d0804 77
    0x83d551050540311135031074a80304061400003103e01c00090280014540006001083e41e0414904001003000c030ba1008105202c0aa800034080010501c200a0b920380c0c203d060340900100d00307010001c504042821070340c0038080301d102840890303508002c0e40400d003652402800d9400c81d42060074149003049c01441004051010310b042e07180d800b20005126030049a05541d1444556034285000740d452001030700400455489820900d510b10341004850314020843c11a00074508103c82d065181c0b554a000142c0074045da2245080400e4012040d50700f20313a02800c2c00359403103620700c80490900c3c0c01200d141064400c0441402007010304200100306592040b00700401841c08800160703500c00044600800592111104d040c100e07216070003030721491030b8a0424221002d261400030500d025a074101c0100c103004030803100c8485c42c0c11300610040c0540d003441503055062503200c0140240c4000c00140521070344404250854031030741a6985180303081401d5807070a80c00b2020041600c00292002c1e541e0b14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 205328327 1250 205327077 205327079
    0x903101a031603052d0a050105070201150302060712200304030203010b0411031303091a030a050a060308031302010e04143301180333020906070201030506130c0302090307 75
    0x4410380c00c000300b5290088010821011050392000b817441d0003000034501240c0240d07012074410400c02032031448601c10000800d1515025070020700f103032000195440da81e1600c0d0020030240e22682c080303030300d1160003404000480130080401c0e40c0c0165140e1549400745041c858288403460048003510a5a02c22030003405072108070000c103c1945c01e5074031040300c6032200b00003180201c003058804030f10541c0719081000880d1750700c10307142190644030f204440314007000004101380f01a2078483c540e400161510104800741c1540c403207461f2808002c0203a01ca1b50b101c0e44600301076a010f408241e0025000810500c1603246184a1105150040d99592456070780304401c54100c035980700000c048030701950b4040307008000080044524a0381d40000c40031030240c0140c00b00120380d10550000e04151440c00242080916140d03100010030411001c000700c610611500f8990b68840d012100c0290302440e010499498500005842d001a0303405903040034030346124001403541540142a0fd190202c013659055 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 205329577 1250 205328327 205328353
    0x5180a230d0809040f0e0f10060f0f231003090201030c210b0d08120702060a0c02105c0301051210060b0409050123060903101a03 57
    0x2101d81200030011842032248a01c0340c00c1a5200c8880140044008640c84001c41412800c00440080281c006d80010f07151004526250140000606800f5510125140380c00030070000c0ea0750301d020742e00d07090355030040d0001402e050840000f8910030081c180140d44140c40b2002d801065689022808070303052038826200c1d84e00880c012104400c101454400c41d1140303019400050020580c203d5201406800c500c021900c9440541465120000140d05506080e00e01030f05d4098000c0415050300d007041c4071b07000c00f65400b28606c0103141800714080394111a1214419840d5855448502e5141800d03985d85031400403804010f0107403100c0000511010b44c507010310300c07501d0b020303000078072800008000402840c1000a441090444490142d070052a40c450303294040d9030081c0e00098207440041f400b44030125032031050b03034010706c03030b00045611811100d05039546104401c2d41081c400c11011480c0111614103100c00001c03507407608030420652410b0344040180b00c0420004500922500d2007034414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 205330827 1250 205329577 205329589
    0x2010218061c05070314040b0417072d02060d0b0108010503010209090f0606040527130f0b0702160e19021608030406020d020307110105160c020105180a23 68
    0x90011290300b0a042c18144000240034003006040d040405540746001c0000c0d40604294038003540c8614143c51590415081100300550240105402214204000000204600c05510260062480c00d800021401c9580c1014914480c4040d411181c0028802c8a01d42547e1100b41c3c918000d803500100759803200c051508070300500e110250401c4884000c500b150480c05030582c0d010034010f01052078141c5460204544046002051220f910350307402c226564000c4c13030882684559403887e41c1089082e1515504600220202c01610310340c0003030302044902c6d10074840000507203002442d01c0300d0300d0398a428142d080b0100301d4000106105c400071203460900e0320300840e240150401e140350900c0740c450311038a00c075034005401158034039030030007035104c94400d140061842040c50b51070311605802902c8805003511002440f860712406e1183d07600c5034aa4001c414402d0041e0207207070264580b01000c4d10822403104480d030180e4012002c0304d0004160034507140b2014042d0000003040d0f00655800d090243c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 205332077 1250 205330827 205330837
    0x1110405010c0611130305030a030c0503060603010b030a0902120f060907030302031911010603060204090b030a030813081b0303160f2010060e100503190228060201021806 75
    0x1c000340d420144070000c680035801c031820b80401c84d2880c9140a59002140129075103031380c0704561503000480d100445a4040c45102444030281c03c06034a5460314000003440380c403050280202d0250084045100040aa4031039000d680e17020345610a6007006200086d510041681c410075284101d400180581c1c2001c82c600c02102e034590002e5041105455140c40750740101c40100f03040040c6c41d601c01c0340f191024064040290301420006a681c0e05106103003081c1d0382c6403080c2501a0f80725109140001e41d0180d10a0b42c0118903003240c00c050990b910b4100d049100c0c402500c401e1b40402c010408400c58040011402090b00010b1000a4101b015040c0e4941010301511408508d20710300c1c444060501800501a01c40c1c01c03010f81c3c001203a03c401c000101c41d9982c00c2229016242c80c00c000744244048081005042c04600a0800d102c0d907990109460001402c0240900c00344445840c2070006400c0f40001d00f181900703680d1f001a10350100a0003500058210b400440c0f6070044031807181040b1040760703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 205333327 1250 205332077 205332079
    0x705070504050403050d020301030605240a14040608030c1b01080f060f0109090e0c040e070e0417090d0303020903070909050607110708010606030e0d08010e04200409080c01110405 79
    0x41009850801004000e081c010b106405200c1c0400110051205501c01180a517115201c001103d0400794001e000340b0400401034800074090760050782044c2c1d6041d40d4a805c59884000103240703040600042005040d06511050080c4004500311101d06000b0400d900d1800304990204803000c183c600464111031300f0b49240450b503405002180480c02c1c40c00900300300c0e12042c10140c04031592038518004442c2c1ca100055020f80015415901900e814020504415600030060134102c2c01d00c61080000b68010348020210480098a035903d61140c100b610887c10000b80711555001d0b041c20054069031100d501284a80a801c201103140a41d62191401413038024000300a1603585560940e65024200c18440080c8204080044d1210007401114050211542e02083d0301c001c103110a454803e4140c909818030002074018040c6451240d02c095205400c102c1980c400a8410803883e8242e02c3c0a116a8110781408601000c0c8000240100748800740d00d002002170200c00d03402410345010b180201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 205334577 1250 205333327 205333333
    0x1219090b01060c03020a121107090509031c0b030d0203030106180b0304030305060f040c05070b090d050f07030e0604030609120e031c170709030512040f0501050d021c050a060b0705 79
    0x14800c2c0c0d40315044414009120f40116019103405480f4184031101c17050031a00014100d8003450801802400380b01c000341545407050200d810700b01e4809446e40124030403607100d4021070441c41e852100f1a041711035071200180a803820313a98000307402912a4000d020745400300720031500105055040c140c122040380c1180e5442402c5840b00c0e64120090900a007100e1341c809403103081800140c1d034900c2100f8000c2010f4540340c1d901c040600d80fa02032030724018684c0c0c4160b001080c04100e0140c0100c00c44265410b800310030355880d030443c50182ca02e001c0741079070a6003101e000300300401084015400200500d005403032a4841c0040c24504450301c1d1901e207000364250300403900d10100e070325114911000015150501d690800711058031011410720031076410002905041d000c1082c0002440b1065404a400360141c0c82c060604d002140c0001c0d1a10495040160001e441700c8d00101319070540c0c201a036100f12555903281c045500c44090501910040720320b91800ca03000440038251000c40f0040b039881006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 205335827 1250 205334577 205334579
    0x80c03060c0a0e0415091802030a0209061801080c01031a01141308060c030403110a170d0209040c0c050c01020304140405090f0a03050c0606060a05031611031219090b01 74
    0x201c46908000886018091031404100040d511401401d4032058240e0917815028a010010001c0c0c9084000014007035105008071009a2001b1810040710b94050b00d90442d9070321004081011080300c0382528001c0161a80041074944021954041d0100c0980e030520a081501e1070396103000c0a820526030100308910150102d1020003409081c1324010100b1440319956910342190500f0011104051522000030821040641054200b80010a40030003400c1c4201d1551741d2120071120341d0520030b05041c001c1080c008400103030b011280d651402400610107141c25a03c0171349540368000c000c0b5210700582840d1401544000706a07002c0320804102020610100001d01c0010a0b02420b468064090705a2049406c002040301c016003511941e2102c3d91240c60700402424500701902080c42000204440c200895110060301c2e04100340010800d0100e165520986580c412100031542e00d0201041c0320301c0c0340d40700d00ca041c0c1c4514001d0a1340401c0c90800303c031403811611100c0004082419000c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 205337077 1250 205335827 205335841
    0x30703091a2107092304050f0609010608040602070606120b0906060a03021207080307150b04090b07050c0703150606080c0301060c080c1207080306030f0c01021c231201080c0306 78
    0x61043c2c00280c903040407450251665150200e82c02a12102d0003540102070560720700f8201886802c0c1d010825507042d12a9080c0800001c00004041c80307904100072080c00820244a6182d0450340c0d0140e100e40208841d50392641c0c40031403c1c0340c4a01c181c4030a0f01c1382c400210040c1001c68400d1040c070f8000e014007907690940d070801040d000d003400221660b2107140ca000c540c841e82000108007850103810990001506004004140c48410b4101801941001d03000030000d00460082d0350003030030900b0b0003a141c601c1910511700c2c004080e8400b401e8018002c21100015811340d00c401c060341c000c0d68540d030083d600c60700000242d103c20b105403800100700142505c04607007018081c02a01c814081950242641c1d1212000203401807034013503580d204000188141c51908029890340d5641c2c0e600682031800c04500003030340381e40610081e85420102c0d007406031a258442d5114008822b120b2103030f48844418854a08956049604011540940203001260104000514090441000b0000e160b42e0b55805 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 205338327 1250 205337077 205337137
    0x60e1903030203040b03041704120b09010b15070f060218210d120219050c070603110301060c0c09050907140910093b0105060312180d080a180501111c0c05030703091a 73
    0x41000d84003031000c400d15400052e510f0005042d441c4020701d404031100701d424104000300402685c0001c0c640d004c1b2071540034119000c40e00c0585200141461042070310320849d014041d10071403020b03688402200010703812280d000b07006400007114540c121140f4544070300c425000c40e01d0301307000c4c000c603210144010040035115080c40c42200d0300c101180342a459803003032408107848060381c034504660001c0d0414402c400702401410200c0408440a00c01802c1c5001d640c111903606018003c0318a807036604000d0400070781134039042000c0d086d4154910081040c5e0303280b00e188d011140e0300201135080c8004101186000100b503040003c01c016050b01c0c1001406403100c144506c08080c5070401403001c00d4101084441c0d01408110034145c4454020240d440b801241018298002d5811701c07003a4690310082c60300c0085d001621101c0e100440f02e001d100c2c20025614020f4980004215200004d0f141c010181e000d0080e60448442c900e4044014006100210480c01100d4010043c4189540386410403d050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 205339577 1250 205338327 205338337
    0x5060d0f03210b06040519030b090a2f040902010905031002130603050105011b05011107030f080a0204080a11040b09010305100c0e06030402100c0c060e1903030203040b03041704120b09010b15 84
    0x40c80c0310301f01d5607565a00d280c0700c948221590102d070b0300f191309500306000a120941016000380741040742e10b00c0b0564410315000350301d44009401a03a89814000031640205070000c050280181103400d1014503081c1c0708040e602010716051000c2201d200012094041d0244038140c4105845440109a544200401d00218020203640540d00d0f000c0750b103001d03910b03c00203007480760003a075070b0401d48481103a0292041d031020f00140c0c00f0b030f44100801c104103100496080c1c030a41e4021442089400c01c100020068401000301030790003050000004100300c0000b420071345d0b06001580600100100c05001d68800104182c59604482c04100280040c80c0100386014112618282003044802c0d1340c40342c0341080200e40002c3c01050325000c3c405e00c40c0c40c00d9100c0342c2030004a20410852a402c5030750080d12800345214071540d050001c408a0300f00141d07011029105600c0d104025111503503404003006910f40074000351000b141d0100401c220107010300941d0f042d01005401301c8a5403031812001c1440380e000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 205340827 1250 205339577 205339609
    0x1409120d0609060e0402030105060d11060c03091513060903022b320303130b1003120504090f050f04080c030c06040507050906060c0606010305060d0f03210b060405 72
    0x501c550101d6118035901c00d18024003032036544a801e0780303403d1060508680c00500b18612070310040380408c000861505040c2c101000035541a5120b503001c0807104e18502800140701d03481003014007080c001c909440080d00c0300d041000c1c4109000d40d0707290025a5005c446002c003a422171004c40c0200b411080500400d110b42503046980c41c910307001c1d9100e600d004440c203a506055211042550f50000314103902240342102401c0c051451410000652260884800401007201410000051400c3ca07030502c4003005580041d25260800743c2d02d070000305030354010702070504003614140394000d401c0003501c2618803030f9081079280c168603291a124942682c01c10035801107948010421811246400e000d5140900c0c4a10010103125042c00300b00041500c00805807405210240801565210b0014100e6003080080c00d0000d001c2e2140c001041115000000c080c05ea0010802d00c1d800705070348203014075104080145030340004030485460308140d51030003010765480041808103100300c1c0b410140c01031142075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 205342077 1250 205340827 205340831
    0x2304090317100e06030706020316050a020901030c03060c0507020f01030f060f090f0b030606030303070c0305090d080d06240302090409050a050a120f08010620100c031409120d 77
    0x14000590280c80712045540e410400c0c4100010000f042c1c00d0083d65401400860181c8078860800030000c3d42e84c00340c080340d0182e6550300d018000501a00340440e40c440c0350054142c1c440f568403801d12800442d850301c0200c401314582174009408521500940769143d0703000f006a40700903030000c011001b03404000309581695035500000908070074901d842d90000c1103040b030b000c01d01d20b200c4d80c542c03000c5030340b94192240290060b0f002c2080743d07a804421207a001040381003241d041080790500703d400d40142c010041d0080581070600041c424000080c1032010f990728010300549880c0c90703a103509003151034400360304041800e8400713603128000e8002e82070400300a40300150074080344d128980b40900c4a401982c250300301d0041c1205000e0999207003203240795103040140c0140c049600041140c141445010100710800841d00c55070200404200c08000c0e00d034046a81c030b036840301e0503903006125071504040802d00d409034240071840341c0c081d0980f06842190207003680c1c0d00404031340c202c280d000003135a1001503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 205343327 1250 205342077 205342097
    0x608041a01090b0a0906060804080c030d020f09100212031b09210d0c020603220b0108010506100306080d050c0a08040902030604050606070b011a040305070b07050723040903 76
    0x42101038414000e0010080c0412030042c4001885481403240c0c102080712810700c2014440903030000c8820f5041035229004555694010f1001800e600921080746440382c000030340c1c18015a503120107459400b40443e0107220781030341404140c0c0d4848101205040c44034007403000540d807405800c4c0c800c20941d04180101c0c913040c558800941c48054400031000300c2c2c0c0000c42241282d05080015002031a610308240102d404181c000aa4074080104865001c41c90040c03008000305030551031410042e0300c0220740403039507160b5140602070082110001d0265640e102d0a0125505c039000d108102c0f0140806880b034100d035840300700c0ea180e021800d01172461082c0e4120000246500008000402403e8001a160304000e003c101c02d403000900f496202e50002e0081c4408500b02030b007024115076044d220880301701c3c0303102b440f6045402103a2020b0014025160000b41503010040101180d903c0b0700141d811180d12000140b03408841d4080c06e4170001c00807030100b046420a0b034400c991290081c18412485 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 205344577 1250 205343327 205343363
    0x611120c090d0c0810050106020d0c02040b06070204090f060c0c230c03060103030f0801150e1318030509040506190b130f0603020a030c0801060c11060d050903030718050a060804 78
    0x104500c3d0b110048a40c005e054041c103142c050310466024068900c040c001d881410781000741385441c0d404c4068030441e541c01c00c0700401d0303580744210b94000d90701a01c00c0c05140a9810300c845105041b000c183d45241c281580307070301098030410780d449125074030100c5218682c140b8041040c103111000388100d800e1145030107400e1142d40801509000794400d03510f00b645002014002484901c5c10392280c1012804101c010807840d030092158601c0407030035500400c1d200c8000031200c1c00b6000c1045041c1c038480b10f003030089080c558030000901140c44107480601190312420709001c4400b46800d548240001c0718001030082049000080204407449080d10f20341c0d50b2503009224036090a5805100840d074005003010030980c03d401a00f006103e6411b103c0348541c0750070f80c090b08030f6031a804020092031a440765403c441c1e603a281507910815045c10100818500410402d0341c81c0c5c41922100041116441a2005102d054a0007000e5544c042e0062501c10f240c10341c00e403000c100142040741d40c1e0103443c3c000c40302 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 205345827 1250 205344577 205344593
    0x50303030c03041a010b311403150f06060c030d0f050717010f15020f0706020604150b0d060b04090203010e071505030f010308160501050705070611120c090d 69
    0x1c04000c042241e42c0e0500740f4108244010b0900c040048040003001001016140d50684404208402c144140c0740501903100c0750310224042100c0c00107030206404900701d00310302080000345109404070b68280d04c1c14030030010f088030304640d82084034000200043c03490411401801c10303c00e10104880c01c0950390f41e003243c180c0b80315034030320102227940d1801c004500b0f900c44400c080002c0e103805080059418003000b002c604100c1e0045844208010b804029030030f100700706160105602906030794259403903910003034403020151401c0d11820000440e02c3c5607040344e48217000b54000e004000145401442e610341024015185601703a20990342c0d0004000b42e1000c0c05115508080740380981011400d01d46144029040800e450081220502c20006800943d41816042d00d0f04807403015181c018454810004854501c0024559405c0400340095280c0100181961701c1c4684414015907085130074000049c02400e9500000c1e00c1c0c500c1c0403618100001c0c009040042d0054441d010b421402e07112000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 205347077 1250 205345827 205345831
    0x5120a0b09010519090201090618030209010f1a0a080402040c030e0a0308160f090e040503040f06020304290d05150a0b09030d09080d050c0c120a03080121110a05030303 74
    0x103141d4640040000000e90f501002044101126082002c5c0d240e94000900542c0741d0300234a024803070408000828802d5411030300d0021a801088091150785441c0c035142c000501d0701c04d104103904610a500d07031003045482910203803141540ca42580e950b49800700009040fa1209a030305042e610034a455919000788294480640a52103e0b0041d00b4001000355484004d00c88503001c114600785200c91f0654400200002c9840400480f05161910b0814a095100d2540148560041d00b5000244640c000c0040c000b00d9046c03240004901c00010084a030004110301421348074082003028014800b500c0d07200c540c0043c6403481442020300c0d0700d07011818842c10b40d00110143c5a0124030b100261804208126035003c20340307091070720546800c0c0202d039102d0102000d002407100206080106240c2004544c504850007001e40201000382d480b440d0f22100c81060580005d848140007090011100110400b420710202c680003031600143c03103510904429003112540301c1003c00d00081c0903030b0b003080514 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 205348327 1250 205347077 205347091
    0x315020913021b060105040209060d051e1008061612020705070e190b04150501050708190c03020f060708071d0604090b0909010902100c050a020d050607030606020102040f05120a0b 79
    0x114080c400e0703d0310910703107481640b01c58803c9004000340f501c44c2d2500000d580d20198001000705442d01c0d440e6011501380070050341c200c10300c3c001800b008012880c0740042c104031031040c42a070720561684448a00041c00d803a0551703000c0345080d64540c281c0b400a40c0189216806841910303d860340301c1500d18021001070320600700e00342000801003501c01c4144220544c491080b10100480c81c02c0d03242611014880e442254103015001c52070304203221840080381c1c120400d107114030034204030055010303120050130141034005104195114803041e50004010740100040e440300b00d2190307a00041298038420b2107444120240c0d54040000c01c3c1e0321050040d0001e8a00a540410010200d2092001c1018020105625a07040282600158035003002d144c6004400d81780c074080100300c0d802c205d4607090b480c00000350040081d42c42c64040c00404100c0c03501a00c0c50395810320084c0e0361680300b00e00781d000314090407541c52048003040040b0b10f45281224015098503090300e010301d80e60f840d104102141241c1c82 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 205349577 1250 205348327 205348357
    0xe030a020409063c0902011101020403050706140306091602011d0703060c080f0c0d1805010b090604090309090903020f03190e0406140d020f03120405100504031502091302 75
    0x4003050703480181c011313030403168024424088114014034078030140c881c41d02c82c60460350b4414809003564400c007003560000d401e040003550344030395034500540d5603207080c840c0000080144081c8419981c0a1089a0041900500030182900c1d04000c1d0b450423401c900382d40041d0365942c0c0c1061001c1e80c0c030100940b01a001039016104031843d5007040f100b03444200c40c41004018142d0301700030b05a5019452a90042c20025055483c2c00a03140280c0042c01280b2250074055681d0208000b0014150007082002c1821b840c002d025031034500c10301058480e8400e006020410704001408030a0840d8010708103240203104440c9072409841c0c890b0b0943d40300c80000380c8034200c3d80b2082c0b000076401101c009244d80c1c0682d410440c01d850407003410f070380c4000d505056101c4d021499442084d5503a0f60070003000c14200074141c603e0001800003440e41e0b584240309041c0140001d401b8000024002d1b01558100d0f504044071041ca0940035400f04002c0d88240055035000f8510401d610040342c4910140c40c64070028451 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 205350827 1250 205349577 205349591
    0x903190209010503060403021903051e03040201030f0209060f180a060909051015050a0207180605030f0c0303120703060f0b0d0b040903050f0d020904020d0510080307030c030e030a02040906 83
    0x1400400072058020324045d42c400424003000907400500c001300b00c0401411203402c0201d52504803080d1050300c50710000160b07584c82001d4220402c40085000d103100743c808200501403210040f003a800f0302440e448d440309090050140d0115004010101d0060725800f4140825601000554800c440d0300316800240a41c1c0d81403064280511440303400c02c000c400c0c0f106685242403011101c45494603207000030840d000c030384003a54600030844003000e400d249659081840c000c007034404c000e00561250f248644500301d4100c1c0d10a501191210b200400900990324010500c0c5841205a03406000b03070b000c141c0d9488000036640c0f041180301e0050515592407556480e0305500d0701007520b140c00c0b41c0d01d01c0380780340500950001c0d411a0031078541c0c0510484040d110084c5141510080c015180c2c0fa40d0418000149031500ca0306961056105010a402000b404c6d03803507070f07100ca80c4c03402600d10050204007400704400c040f038042c1201d4030101c20010300300c410344a842c1c0d001c241503d66041048401d5611008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 205352077 1250 205350827 205350829
    0x1f0902070c06110601031112031c0e07140a060503062d1201050603070603050c040e190e031e030402120a0b060a05011803060f110f03090601050a0e0403080c09031902 73
    0x80c22030f101c0900d00400d555415512010204080b10f07444d14418450300701c80c00140441402a600e241c40c3d6000c0d107c0901d003000040101606000031051940c0c041d5420100e05900b620121003440e04010b4032100d070090408009076442e91010300426802038400d04040d080c05000b0340030303a4617902c103c0d40080c2d540b103140b410300c84200036484010b906a414031040144c16200020301204580071450040b910380c0f5030350303440000c500c180d82040d12040c880d0000c000040700e2049415003105039400003000340e80707001803c030f0f9200e0191140f040758040c1020fa004c40c284a4400145070001d000422007080002d900385220304e084401c100444a944264081244c0d529041ca03d03000141001c0c01d186500140c0703085509690082d9020003012a07a85405041480c1c682d0760007245035500c1101d6469565076020b031407000b2034008649024451250200100301ca00344031134080700f07c03401c01c0f1414045803100d40e4191400c02c1d00170009039070b04405001c0500140d43c1080002c0700e00c1c620071000e00705094240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 205353327 1250 205352077 205352087
    0x903030703090f0f06020309010c0309080d0e12010e030d020922090606090501061202210702032718090a15150902030907030311101103070210090305031f0902070c06 73
    0x11380404d080d207140305002c0000540102c102c8500c54000d01e818181d926561400340c0b0040e05917080303601c4511591007060420390b01701851100907041261051004100c3e03c0402e03003071303d01c0300415915a82041c030070078504034030350f802070006060b00408a11100c1d141c0342d0f4090040f4480d130740c40c4c140a03403200741070020301170b10b841360a01404a03003c09000301d60400c2c4028010f8a003587d0141203203540003030000d90b03045032042c1c03650401d0a000914042c43c284260006d5032900922042c40003040319901c0380c1c84400350611600d60749180a000c9180018000054008020005200c6071582c0201038540c000907444a09a07050748c0c0107640c2c0002c20070f860700752203040c1c0045500403030081c901c1003041c48040300e0002540307001c50b5410719124072560b80e180d40d81810100c058100c0d0790040e003804103400407205d0304c43c00355101c0d009030b508941c00303c028501c12006845d40e100001c4e011902c20804208030034000c105141000703250300e80303200c0b4503a520040d0904070391100000780c802266648060080c03907401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 205354577 1250 205353327 205353329
    0x10c0906030b0a0b0a180503070303180e132406060201020a0f021b04090203070b03090706031107031d1203120f100b09010e0d020303030703140a0c05040e09030903030703090f 77
    0x2512407502150400841c504c82c0c0c86600700b19014000300c02a00c41c0030f41c0da6503810202038500a01900e9420703a0b28500603194202d2007100c14000032603007030f010601c0c008010300c06100b8014805d006600f243d0584507801580b0042c298018600c0b1030914404003003e0300e000c1c540017001641c0c001079940c403501c40b00400d26092521070204541091030389400e441103c01c0d41c194090b4045400095102a03440000c0c5495081d41c003600c00002d01100300080340a0125004c42216401d0b14107204030402c40020008a00c40c81c1401800324402c040490342e0021702d61050300700041c2c007601150b40d0303900000d542031854014009003802a540c8000308049d00070603150f0103801c0500e8804015006007800d401402038001e0401c044d04000d000102055603550740c2e485900c02a4024099035902e04101c04003c014121030042c2d040c0000150001c142c500c2e15511502100c1350241e5038250801d030034424481100364000d041d12078030f84018014030100741d40500041503017511030707100c0910592804003044911545 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 205355827 1250 205354577 205354579
    0x90907020f0715021015030b100807061e0804060605030a05010f0b040b100c020d0f06050f0615040603050405070803120702070801090206040902090a08030c0307110a0302030d0f020a05010c0906030b 87
    0x2c4980c2640d01c16400180e540100e8040e000007041b15041c000c9800f01c500007960024115462800c2032126903541010710340309448440c800d0710640e030346940007901c0321000f850b50003046402c190408150a031041c000307550818803910300455865a01c00002c0d20b04080110140da150350740300c07030390130743d116170361140f40980c0c2c40689091203010006800a10f1400c9030003c030f1000e101212512000315030b24204030114240c0d0194605042c0d010302c1c10010010007040341e500071046094004180300d40350003282d038881e16014901300c070324103805e042c0b084002d894090030072140c62194071800f181000c010700103000b10181c0c0d01481d101c28a8040e00003444c00d11150321980d640e07490300c41b1a1001d601c44a044400782d03401c8500250742d50807407101240300d8080aa00c049540d02021441501400c40800145080c1c0c0c080c2c0601241c85940104203d41c49049100081d81940004508141c040c060760f2290340381034850058a046d200a40c4078142234a00034991000040d0815600b8041e4a8161041100c6450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 205357077 1250 205355827 205355849
    0xa0c020d0606060e03150114010c03020c030d090810060b0f0d0f181e021e130e1c05030f060907050c07030c03150920150c0102030703051b030109020f090907020f07 72
    0x1140041c910234200545510b2810170200c11200001d0600070000c42c840800050304480b904049018010300d004414018052240100c26000702c000540d0f01985042d03034404d41545e442c164000e15045019401520300b507a10701d81700c98201e140c3c45540d02c5450100100920984000c804510349284030032a60f0031130544070350284050801503140c2003d14080b51103541915a100b2420b000016009286c03240c10851960078110500401100414007a07242000b10400300003c0d00c00440690301c03404210350f0140c0303003000a0001002e501d0701501c0c05401c07801c1410102c0c5401080700480b414004070f50029900c0d212103010810800034212242040d41c040d83d44100000600c0d0f0341c41c03101584411001d041007840880e0701c00d4540e568024003182d0805990390983d500e8402c3e048550103034004070303041004686004001150401d05110414518684043c124a50fa0800170300740003c0d0440c0c0f01c5038800120910138807941d6203502040a010785030303e03001801c010028040c105e10b40a0a6000140245 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 205358327 1250 205357077 205357079
    0xe010308030402030d05120f040303090503031009051003031d0a0f03060b030c09130201080907080a110301051302010f0810090e0c090718030206030a09120513060804080a0c020d0606060e031501 85
    0x10380c0c0703440301d1390403001c071342c115414a460b8ac0c20b00300c1c041c20f40540098550302001083c844130220444e1040111000d40c1814410356503041c0d441f50100c0581e102c00f40115a429640704400e030b00c0c00703284c4502c114004103585002600c500e001d1403401042d41044913034a070344011502c9d240c41c2c1040810014901100d4110b060700d001c2004400035018820002d0610000c3c5001c034241103070901152001d080d0100490300b0300300072030926210380f10a51540c81c0c043d52030800130a01455410115026440d0182c4402c00002103c1400701d407065002800307104065841040401c070b04905014040110103100018881140243e00700701403140094044018003440c0b40043c800401c0c590041001c89404031111034807655444601405441c1c038100042640340c4034522104403d420402038070020129403508600b4540b603520030b0b940a1025540513041c168240010b1000c148540c4401902034406406400060041d070346043c252105900a180803410740001202141006c00900400320344500040f0915 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 205359577 1250 205358327 205358347
    0x812130c0e0709090f0b04020c03040608011203020717010f0f020909062e020a0501090501061d10090b120f100f05060607060c110a0b01060305180705190e010308030402030d05 77
    0x804a20311800c00651748480c0000380d46030a03540100c2c07914201605c155517494410781d0864030380d032150103003601140030340c0300116070100a8030855403951380c16001008003e050902d12030140c044103400c2086503494641c0340c8000d4240c1d0083c0c01220305041350141e00d4850350030070000c4100000700103034010035481005507001901401c0d034541071080c110341c000780d24018810881c20b08013020301c0902558200504c0c1e8041240542c03001c3c0440c4c2d60709041c02d0107002140c030421640c00c0c0540722844100100e01052121141079440b5444e0312400070320704681d1003501341a050510107001c43c0011190050100410010058000c0f4101609170980400035441c007840040c0160140d41d1000c0e000780e84e074104550079a80a00c042ca81c0701c48400e400c440b008a514034101c03c820038240240c0001a00b0711020824546580c3c0034407100488c4007020344406802e01042c030100c0d5a0407031580190043d030090008011940300c2c03410b400f81d4001d0401594920300f9005040c07800320909549401c01030104815004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 205360827 1250 205359577 205359587
    0x506031c020a11041b05030604020d020301180b010c05030d0c0e041406010f0306030506040f020103110d0b0312040e0f040312020406020703110a050105041a0d050106020c0307090e0c09040812130c0e07 88
    0x4203441b81025520303070310f03800c0c0498000e0142c4501d48a0880c40040041a00d0030b052440c0020b02040503402d015240b01d8a004450f50b41840350020a40d51040c0725041014015801c6403281740d034030749420700381c0c80d021724006010790b4034014195500949074001d006030780d41e0200054040c0340b2107060a010f030074070310341c2c4596503610010005010605d0603009803045a100742c209504508001401c25102c00c5241c3c2058020302d42e882525100e031140c400004659459038095070201d61050075104600e0b562b000801d03000600050007102004800a441e005100c250720180029103559802000c40c90f08524050581e0035015144a1081c440a001048660307400f170201c0e029140035540440c940c3c2c0c04801140068062072045032580c40c00d00b0b001141240c1c1c0040d0700e08880c04202c0855844035551022281114080082d0f0841c0d5008107101c0c400c1030030b106000c4c0d030300b2a218000c4549041d0111010a088020982c0d6031120009010309000030301400c00c0b51000a0a40300074902c8090602200241c131b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 205362077 1250 205360827 205360871
    0x1203030f140906060a06020307031103040b070b010f0e0f041103152404060308040b0c010207021309020415080615060405150a17010b07380603010e0c09040201030506031c020a1104 79
    0x100840c2f441c22008100c41402690010898040019202c00e00c1d4a85411641800d0040c41d005010003040007500c140b00380c44240c001c0301c03c10700d4046a81c581e9118000c0c402c5e03540c80b038150540f040e1748000d0300d514560003807103100e68442c122074240307201c1e10190320400842018003148a00d05100d0b081c000320340c0503030440e000c440c010115590341d001074612007400380c014060083c2d400340c00360f550142c1958031504150701103803007110100044000180401c42c180c1305c50003001c009a07c8280041e1160300180354035422442d0040c42c02d824207544d18005000701004010006103100080741900d0219007045100d420041400e11003003040d070400c0c00000c1c0034040e044000e020850050210180c44081141540c9050030103a8580b010707102c0540103103421601078a00c20300030740c60035444903648000810105c1e038000c001050140e268a864004402a200150885516001e090000d80001d200c036040505192001e4000e450700b032600d828100304040b02041000d0245080105000c40c0542d0b1684d00e072 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 205363327 1250 205362077 205362083
    0x110c0108100e0c03071416110a0806010801091101050403030f0e1305090c10021b040e01110d1e050705031303030e0a0311010506010201020708041203030f140906060a06020307 77
    0xa2a5600940034064560550140e10a0400c0704188615903e44500462045409480300c8044840c2420107449070301c100b104240b000d401d55001c03100000c42e0820001c030170250040920754aa0b441c0c000360390a195083c4e03c82c151581d5510380c180c0170030400c0983c1e030000364000d0070000d041c10310750b803000f62200c107641d0042d008100c580344405020381d0b140c4510220b10804000100038500d02240714a035a509070003200f600c21100b94042008003440020805814200010703a0707065002d11401b48006001882c005142a5480794030003507103400b00340d01510203600a035001185650150f051003160b075985110403501c140c102010800442d400c1022a900030070312130110700701c4c54017031705040740280150f110f080d40303a02a0342007403001c0c107600c14070091180310120000c00c40ea844440c0164201d2259480007402c01a050008000d58016a00030305035941c040d00f008982e05003d207841204660000d030f0b100d1100c3c00040700303000350807100304202751340048180c482c504000c0c01c0141c040d42d07902440c02e0007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 205364577 1250 205363327 205363337
    0x30304050d230a1817102702030a0b0708190216140a0c080c18161d0307030b0f181f1b23070305040905040807021801050a06110c01 58
    0x8841d01e4031525001e00544c1c01c0c190003070149074480d80241681c41c415072065220f44106100900840a41d104200c000c4c0034400300100e10f0343d42400100c4e01d10038500001c0e607150089072030140211b4204100340348a1000b96550002a02c0d1010000e418030400320008900544180414080030240198260600750020b00380c3c04d0b207504884840d403400c0c1c000b031002081c141442c407000801032000a2016069030084544035079100740c2000c07115841070102d03407801d142d40c2046000b00b841406100001025000150b80700404215400071030310300790b070607802150700403000c00c10000340922810329190041c03c00c0444040314050800380c0c0e561a0f10020385040300c51007402041d001071a0980c825805802e030001c40520760146290040c10790f0421202d50a0719035100342ea0050148040012640a141e168031410700f8503003001105401441c00520407580310304100008000369403038001c00300c100781070302070086641c0d81804240030180582e40d03c0741c018031680c0f5108001c01c00c000300308806d05150a01c0c00b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 205365827 1250 205364577 205364587
    0x1140601050f13061d0108090c01050c07090606020d260109020d0209090a02280804030507062a0e040213050603150d0507031a0405031209120408030304050d23 70
    0x2410b25200384842103094100012000030159040f07000d003101c0f0000000c0131019002840700559141000700d40c81111608202d0080700309600910107001c1c2c2d02c4501045511082d10741c202c0000711a95900408050b910203518100d80c2ca034030001450020391b000702001c0004551702c80640d25800107000f2508050b030045608090746829a059503804440141440054105114907500940c0111501c0c03182c3c400d114224050301c041120707000c103c00c0302ca40d1402610740d51520300711400d42207103c080b244a604e802c414009200300c81403400c0800d20074268900754075510400503000c2c01100e04128082c5005000e44505188410303c0a0304440040d03031490364035901c0580f42c140110781d03400416882404540d8003000d002d400603003503041d00e205152a00c0c41000c1c00c90910b50100049a0051136503204102104403e4855074603284c0042c907080854405a8402840c032041d500a030704000d00941c00481080244101004aa21108080d0a00d040251400a1295080303000c0e206c000d0300706100012 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 205367077 1250 205365827 205365847
    0xc050406141e0604140a08070b071403070605041a070f090306110702090c040f0806010b030a23160e04020c0c091e0a02090108060102010c0f030c020703080309070e090114060105 78
    0x441d001e0b5022006241541d944d80f02c3c520030306000d00702c001060194044030717008142d024000030b107041034400140d649403c004d82d603aa4911808220f00c0012300901003070011000003091405250302940c8180c061080c01102440e0054041c0380044c541400c002c6032010442906401c40704240030790350000008500000c0c0581040c66501c196900207401940c51420042d2110007800500191100c00110420700c42c3d4940d0450798440c401c1c010750406c0ca00c00c00104816a00300d0340700082456a05200c0c242d0000001c40543c0b070044125101d114080607010031035180c50f1710003050440500d08880c11400c1c031542c484ca05035500442c500c414081e0b20719402203041c0704402c19070b06c41c0b00381c50403007407180b035240805100020750010040c844c00303d840040414051342c0180151a07003034405503a911244445c240044001d071540009480a50152203030200104483c18010f40c843c2036400000c0103041d150007030b21107800200030007503007040e450820441250341072686a40d8005e8000d29080e922030351405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 205368327 1250 205367077 205367119
    0x105150d02040f060f021606050d021b060f1f032102100c0302070c060e130c030908130608010b0406050301060f26041b03021507060e070905040c05040614 68
    0x40c0200383d06502d60240068103a40c82094402019065400e85810004130040c00c5080100f07401050003007902442a12066500340d805081940f0291010f26280e001c824130881c2005404d0300c031031081c00d00190410170440700134000034044041d0780b80b914003164910340390751100e06400c05240103c40340001064600318403c05c040c1c00a02400d0000300050010071501800a61003400c3c2255030351211840052024010f14401207181c801518407201141c2001029006160440442c010300d81e5030805440460381d0300003e40f040182e4809581c13911414810702400288050b4041c03681c0303800c1084207200856006d42a40e0440d049410b0406601e11000802c0c0e030300140f0a0307000c80240b40314a502030084020f4001c41c900540c000c510b140440c0c0c0c080c0c2c0d02c80200c41100d020103900031780200036400c00032803400010704165010b10000180290a4500c0c0c03814110250b00400a042d251018003003400b030514261401003804a904100b41441c0030081d442c5450408841c0b8401d4201320404410002c0384 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 205369577 1250 205368327 205368329
    0x3070306031b0302011214060d0c080d090918081204030207051c060b09070905010507150509070612020336030c030a09050d0c03020607142d060105150d0204 69
    0x100b030100400b1038419201c0d101c0ca000034403090740060466504001c03620f02a1081444c901d9140305200d10300da850700103100e099111000202c500c980146800940840c00340203503450851640d48150000c2c0c03800e2824411386100c0040c2000380c1c025845c0102c000303400c0d0402c850006e40b201c00d02400c69550f80c20107a042013200d910a5401c288540c5040728038000100c0b40d024200c0c0306036010403c0808560600040e143c017102c14101084c400c000030322007580108054010700b4441c082070505000040c0c4254117541c03090300c0d2440660b001d40020700449401510109400d1543c4008508601c0c24914510b400007490500d510100c01e080d9243c800c1c4802c107428450325596400850ba92405e18140c5503550380c0c01080660005049035001141c0d52406111070707400ca68105480382c01c200e00395001c0120b80e52101e40112005019801d1401009006000444c0341c000500c4100054402e042030042001140c0d80c580c0007607070030510041c4200e81e264603052240f0406001e2240c2c40d02d5011341010000d10903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 205370827 1250 205369577 205369583
    0x2130212010605071202010b0f12100e0a17070308041523010603060503060f1b0d0e03120a0b1305060112240f03051b040f0f090209010b040b0d020307030603 69
    0x304100100d00c0d550040c0c0180401e51040c03100c9800344040c81c504a0072120300f491200c1e80801c40e110700032550b207401103110210403541e105450705075600c1d1442504449191850190075045842e80b038051090010000108102050500e031509082d03503801010010000c200800b103491444113440c0403d055030000d401c03407240000b204038038034954200c104400001d11943c0d0019040640100c2d0604000c034126002e80002c402c41c0c41030f502c5002802044079200305481c8c40c0c10b08244110041c03040c043c050603c400b1a1480a90790b40e442c00444100f0600d8000c01081e1002c3c10b22645406a856401080301c1d91400d5942c0000da40d2035000048940a42c00c95802040600300103803403503403000c10514515410443d000302e414182e42e42825990800c0386220242094010584080d05003680c8201c0c48500c0a0041000031100000e4101d0750490300410107003030a50340d88032144411410300c200ea00d800740903010581c500341803620700c01c01510310070460038603000ba8010000c0bd00c2a402500040040e5034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 205372077 1250 205370827 205370857
    0xa0903120908010e011a0d020f090408041a1804050a0f09050c0a090905060112020604030f060e0d1e0507150603050607030c050a0c080c0f07060c030207050405060d021302 75
    0x80300c0320010809150350144016651030302603000b0103003105106558078021002c14490003640c86608104200d8680030b01660001e845001c800c00ca41e80d4980584d1180f131203403001c5c0d511507041400c1c103400500060400c541e5003030104140b100003115006c10043c808000c45020509540e1040508050a130210095080c2405d20141c00101314000c503101329508001d44031000c80310b540d1410a010b50342d6200028016400c00c800502c107001c80c04449003219070010309500d140030794a54030740e400000c0c2d40c2804d86459980707011170202240c050100000b4200e1500e00a11309400a01049190361100e441c0360080c420b002607070f80200a410700c2c2e0a0350840410004000d4150340c1c2c00c1c542e840e40e070308656242c0000d1a00c2c0070300d0032041c0503105032030400e011036a174190751000580c2e5103045a40f1440c0080e01d584109560003128990400a0001900055aa04011601618020b4513000a907004144128100360400503a0349419060030141c81c0c0454174600b0103151081110002c1c4903422000313038954 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 205373327 1250 205372077 205372103
    0x6040b030a0b130e16120803070509030604060c030e150106110712030302030403021207080d0e030c06010f06112a0607080708030f0c12040b0c0409140417040f0b0a0903 74
    0x615601401d035401c201d40c21703240d002a4011007840c2d035020600856010110350b240840c0411178540107580c0c4105281003840c074002052000900c0c1c5041100c003150210344072a91842e010b03501d0b01a09403031a425200070031000c1601c6c00a16112841400b5400420102c50303042605d11004029907401044203100c402404000d070b060080180d401140d054016124164625207013809076801c980780250007130302c0107041601160342c0601400c1c40e880140b52034031090291041e80710050202c207000f0003903000c0e041c100e1840d048018081118000340b4140716040351010030706100020b45445c4d20204602400000911203e00041203401030303482c050242c401c041030b404100034204000394018061201c00c40710640e2802d0810f0401d12a0600c400c000e4010705000c10000b50f102c0350410b802c10f00082d09181056100c011443c12101c40b5030319200c030100c001c1d091205200051424903104010300c81c610346070a00301108c1d01c440c0101031203091412400000d00c01e030018494145000134644c0004154060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 205374577 1250 205373327 205373359
    0xd080603190b04030306060924050721020f150f0408131806050d02010c020103090c170109060b0108160c0f140a1b0f0509131202060f060a030206040b030a0b 69
    0x602c1118102e01080c94200003060315402078400500321902555044400c1404604035040d440e40e940300c0c6800d10100b809140009046203a01070b07822200052a42c8000e03207101d000a240040b000100c10240d080300e541641440030b11642c25900041c0e68141c00420384962900000c40e100d2110747d11100008500c0205069a00350000001500150010b110941c0c882c402c0281842c04900b000380854109180c5800550107a0080703c01c440c0205c0c105102c09540b4440001411540020f030311144c3d42d607075509404c0110a1060740300c000c00a1170000094900020400401c0044000e1107041c4946401040e08008421030900c0c94a0b40c07182680c1010312049409a903605810380b000c5a96a89a2403149911074101107494101d69420504104c12480e11040c00210385002e0700340c4007448601c0d2242c0000c9501020444d81e2140390303034001c1c0203600d404914070302003800140104c1d218406030081003000d640c440c2d003034a060314070410741d1543e2621441c50075002440030503400364102411070385035144 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 205375827 1250 205374577 205374593
    0x240e0a060c0f0f080612010e03040503160803030106050c0a020637050906161406060a09090b04060209010203070c080f2e0e0a050304030606090c0f020d08060319 71
    0x2480c818a81404204007410040d54100c1e68009110005805030220000062140030216003145000d032012041c4011182200d00350b40314a0386582841d0700009003003210b82020070403486485480c20721040c44030b0905102c15224801032084008204020034001120b100c10b00c80d0b4030b40254000d101941c0c60340030307400f2008032481c01c02506042c00300d02c014031100340d002102d0302c40d40c1040304d9850f00d29100e0f40d28108a641d4000700000301e000041c69410328001402a00041a4007480100900041c90600d00704240c0d00e2003500b203400395074181014200090307001710607281c20907480000540c80c3c880080040b443e6029500010b081c040c42c0e400c2c0011092000320340c6031065007620003650409201005180302e04445080c1c030820150b00340740c00f00c0036000d07540e0120030800054001d4a91000781511044d140d60800e40081e9030f096501d0004000b100440d21a1140a640c41c0c04c101802d880041d50194072010354218107400d0150500004039950340c2070013050901070440900c15151740f150b0a18201c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 205377077 1250 205375827 205375843
    0x180b070b01030c140d12090302040203100801060b0a080a0f1b121a01020a0b04081e090f1c0303051009020729010e0a0908130b0901031505010c240e 65
    0xf655103440901048003c41480c1e0382c0c000c3d40026004840f868450741d6040d45c9161a02d00180400c42c60000210040e40d45000543c0907400c201a1481c0c2c09040408140c2160200d60001e100140704000780440b450700308180c00d500c005c85641c005169001c411856020704001c40020050780c01c0003d90b08059a000940b0203401c02c0005004c2100c1c0c10020482d40003101c0001d0b046016134072000e0a0700025101c0b403090f5a000344992541c40c28010b104d00d528a42d0415200c003403910300800301d06243d140c10441210900c034807044030382c200c4d404d290320312030795801c2c10442e40542055112000180381040130401400200030b0940308564411180c144010440001000541d00009121150b01101c0180154505942140290600a03120341004000810f1110401c58003101c0901110050440c6080c81000070011000c24940c0e0304400400181114200d60304d2048424a4020600090360b02203e020200f5074841440300f0141150414484090311090182e6552414000031154041001c15401e0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 205378327 1250 205377077 205377083
    0xb0703030e01051b0f1b01060e0f07020d08060607170a0201150b071106030406060807060806040c030507050d0e01090203030d0b0907050702030a060c03150b1801020a0507030201180b070b0103 84
    0x16501c55113a0252890808418402c5540742400011550050b07180103001c6510b402e00c00464940400051390b0a507903459001c45a21004441003000c1150410404c2d0307400350f400e1001d4074000390780c008054568400a02214018000030400234100605c00d0300d48524090100282a05c3d0113405000a0103072800d100c5004186102c000b00107210100c10040d10281c035444444242521801001d101c81d50300001d2003550f031507494400024100100340482d00c00ba10490303803503054500e00322040c4801d54007090344d6081014500420000c0c3c0e00d41c0202070722060b038814180818002d803000d09590140810020195050000040f46042d8650a50010070100401d80302c40a8554640c0c40070340d6180220130000c1e4041d00070b603210500092007588842240441030800054555003400300600580680c1c2008807801000102485841004a9012a8800c00348018144d20140d0780e0703a16190040352000a06101d441406400050203042014001c0c204d42c0c0032484e00d40300c8604289410200070300c815 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 205379577 1250 205378327 205378331
    0x81605131e1a0304030305130f11150c0c01050309031b03030402101404030201050f0f030720160306230c120114010806101b060203150a0501021c02070b0703030e01 72
    0x381c0481418848814000210b0910304507a01d6071002d03001303820018841b40b014007840c0d800c0c4002a005c2002102c0c1c107070145000204284491003440003010250040c80130031001480903e85503400000c1c00f80c050340c0c0c2807034440d849455250358a45180941c04d180d6400f07030001b01c80044041c1001001e588694001c40d0f41b00c0d49100521000c0d90503000032440b02d020000100011700c0035502600c01818844410440340b03103004030160044c4050b401c2a109800010241c402480001002450118102d038000000d0b14000d6128030031010040d90302d100062040340c480118804d07040034540e40c1461440c500106410300d01d00018840d500d0361009101c1402140100e00121b000075920603440c0380602c040c0c44e1814141c0315801084404031000301e485c000c22508012000030320f91048540903816114000258a9061152000c0980200401c1d29070180031140d1003080030340c1c1c1c005000302c050400160303212001e4002c060103c0c20070f102608a000d5400d070000d81c04c0704141d07243d8030042100c042c0c403000b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 205380827 1250 205379577 205379579
    0xb0a0e1318170408031206030a0f080706060806101e03060c17010806061c05010608030d0f0f050f040f050c10050304060e0703030207090c021006030605040302060f0403081605131e 79
    0x20b6006009900608499500034002d02c2031515442d6045030300044000c0884130030103851b80d00c05451042c211000c503000c00b0041070a10802c0094003078030b0080c281c004081c010f00c0c0f4100c06050070300781c0241f060b00c4421041c6d80405a1503040951910061508181c0038000c41c05000005410001c06044070075000c5003440000408035001b01d03d10740a400c004180207464401401c00328804140b0190a139410755840d04000740d201070030401080c815648170720104440d440c48074050201c2d0910314527004811300340b1080001850b4102c4110342d200d0341c058460f100c103020760300b07040d40b13041c1082144940040380e405404004d00d41040c0035500c928440c1405200320320001240a403103020f5131000a016074813a150500004260b508903000c189002e10450708a880026010801e40340d00d17501c103898499941050009050741030109643c041345031032150203a41081d0380c0040c100030004003201101d00c200e111904d1f140742f0800c02c0300c05d02100d0a0055602d141c03500601d00288000d00e101103030706501010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 205382077 1250 205380827 205380863
    0x3010e061e040b040308040614100914040b0402091305030c06060a060f0e0618090a060504180c0905070306031b0e0610120c0507051204060e010305010b0a0e1318 71
    0x505440b50b03a02c0042d801c07041c1c440341d90548200b0300140c01181e005440f0301603082c94a81240c0c16500c15444400d50070050761400301c0708000c42c1c40c0c0f07100382d08403400c1c276004000104a01c03000c0035402603410359001d2000d03900d01c081e41c0395408000c40000c019000001d201c3c40d440000042c81402100219811050181d440c00d05580c0179050a40080c0800d444c200014018a80304010300341d10009900d07004e2481242400180d05182c0403503000b92200e60f91841402581850f00c10080f0b01a0b641c00b142180c1031442e100d41c0e421400510410f400c4540380c1d000100554440d0300584c00940d800540184660303d00a2420a20310040c0584100400308400040051810360603510300b91506480300d60040300546400030142100c100350000303001c000c02035000041c500304070151442c0080020705413a1810882e0091585201503900b074101400d00b4014020303008030034203d442131030560400034501030b0781d54085101c402c01c103400f0240591511005041100028502240962042c81c240030410103200e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 205383327 1250 205382077 205382131
    0x50306010807052115060609040e03130b0a140c0c0a060815060f0a111905030406030509060c18181005040b060703050301030b09070b0307110f070e0a0b010e03010e06 73
    0x2140b102d0254095104085c59000107507200d504184054103192400302081c0100c0c1c181c403040d9400c02200e500000d09800e20020070070a0b4000350410210703a502c1d00c1c80c0100000c00012030b034803a00c0c03820b8500041d00c0760301078420051011010303400342c034800b0724659440e8040e0032941c1c2150030341e00340c4848090312942450110212560807000014043c2012a1120202c3d0802d851070700d0f01c94144640071b40b941401941402486d1442d110748001d6a0700c1e4140080282561400b5051300c0e00c5a00078000d1200c02c4a048042c0d44020540c441d810814040003030000d0305042510140501410045090100300b082200000c0700707403041a1424060804580207001e024030403e80041c0001d00c0610041c8001070201d101190004d00d00303000c031410140c490101841650007a00c00c14003041484100a0389400c0600811f42140360300030103007408518040882400c08001000503d40c103030f841040f000c46a028031103082401c0400340007000001846030740550b6920058410b4210a4412601100400644 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 205384577 1250 205383327 205383379
    0x40e07080304090902030a0204021209100c020c010f0201140a0204060905010824030703141506030c03100f06080304030c0501033204020607050118120201020f1c020405030601080705 80
    0x24000070340c9401d141900c82c1c001022a00f800301c2c0d040c014280c1c588007698840c0060300c40c2c0303007062003034800d00c0c24008000c0f4500f05d8000c00c000703461800d11080d058580e40100704000098020700700300444500104040740100302d0702d6080c0d0803c0c1040070038030500910701d0303010b0310507038003aa10f07544002c40d102c40041d10307201d03004c0384d0f8131654008220f160b1910600709002c01d50100c2c80134048441c8292a50350312108215560412003071a8002e15a030b90800c09001d10298010b4022340180000b1603a035000b0079203072007811402145058603a40f80f9401c005443c2d1280c0024003180c0d05483d10b07142c80e486c1080849040f8407480340002e003003c42c0444403c9010030050300c400f9500c150940d00364801d103400402c00000401c16680014140600300200d1028003c2e8902c20081400449915a96190032202c1c0000c074401541168414000c2004110076030084443d42c0d03210314071010540e0741200003400a0704c610740000740c05004140c00003d41c1900090540305036541202d00c0300c03000a060400840710560 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 205385827 1250 205384577 205384589
    0x20d1d0f0f03070f0812010605070203070504020301120b1803070b0906090d02031207090b04080a050d020d090e10090204032003010b0a0909030e0402130501080c0406080c030c0d060e0402040e07 85
    0x1040044000042c004503135061320b90320a4408a0900921948211080710300b40c1c00a0301085e0006107020441c070701131107205c000d4002101c0031811541040741c98801421043c000500c2c80d02d41c07901056503603444c1c0d40380d0190000031a0441c2c1d510131071807904848101003a9400c4200e880340c100800d0300d0f944040341100140310140d00450a18080088000090101410700001c2c8200a0301c041204081103004001a142110090207a0000c910303000b840e14a03207420202c00c42d00000c2e10010343c075905c64000c0044402800700c0034910b8460a21803a40c48071a80d105001c010301c000f50000400031205851001c5600f0748170369400200080d4240740c00d9412484034070350b00c119401310602001649070f21101045c0d0081c41d242d04003099000c00304040740d024080c1028407090490301082a5a4040555507021000b20206e5080c00e10b409405400307080054810388034260048005030722513080c5400d840060070002004c0c401c490340d48600000a00c030584090b40510300301142c00c01260000604001101c41c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 205387077 1250 205385827 205385833
    0x2090405010f0605070f080d06030317060910050f03280c0803040509460b0a030f0308070c120e1201140a02090f1503100510020a0213020d1d0f0f 64
    0x170f580d07550303442d450004035400c0f91200420311806119264900c15400907510030303203810a00060400e180c9480c000000d040324072a001201c20045c0d00c010603070341d81048034002d0310f2041c0c41c0303504100000e00300312042a86000319100401419030130400700e944414100c2c000c0220090068650000c10380303a03c80c9000d0705e600a001180030429650f1036449144040c991200c8151170504032044040850b103481842503104074140d401e018018145124219a400c0c08440302020a440e5039139a5120426200e0b0260901c10100c0004114074000c1141000c2c055000c4140140181e001c50041c00001000c40031a000743e50150446002d9201480740c3c40000180c080c51604903590300f14503001941c403c440082d04070010140c1001a900d90081d141c400c1c0c001d001410b80c903841c0506c80d051050160b90720651103443c824110320070254000c601c2416158044c1c40e003510200c0d03146804e50203071041804008070b480c50800034040303d0925401c2c0d910100c420005643c0340d038122504496581202c040c035009260 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 205388327 1250 205387077 205387087
    0x3040b04120c0209130b07020c1f0917030a030b04050423120c010f050901020906030a051e0103030e0411040501090b0c2401080c0d0b0109150302031002090405010f0605 74
    0x18076903900c008500421441c02c52040d182940c04601000e100b81c600170301c04626416038104020590000640c80b4059100034a80001030b440002d0840011903540004c802e070f0040c150718041d208011101c0540f0544180030742404041c1d99a50f541d60020f101d6400117407524031501c2c26490315020703c50144d42c1201081130b0060303074201e002040704e519401000492080761440581203208201800308040c011000050103620fa00c144802c0c0c9200610006c1c45910401c6481000da80301e0701602d810121070003002034982e03501e0008915588210a2500408184100000802d0362003541c3d5103030f5010903201486250300e41000020b427805030340141400701c0d507100d5050155841020190030b654803050100c6242c0d00e4102c10541c120003c082d491340c10f001540c0c0052103807200801030079200000c244c4806c0c0c2c03076101e5900e86640121043c042c0c1c0480d69141d80d4100495100c0ba6118809541c0040a440b061000e850b034141c020740c40041b1030790190b1305110000ad01590b51419020072113000751159032403c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 205389577 1250 205388327 205388333
    0x1b0d0210030915230f04120507061d15010806010512120c010c0f0504060203090105090301090b160912050303040f080d060806040218060a17010e0102070b010e06030303040b04 77
    0x20035094504240c1d80c0c800300300c040b901050b044184510386201c00941c90056a03c0e88100003080c18403502c2045070a030520454055034040113034030039044403032a0308044040c40125030600c508070010701960308145140e649107041c150310b9a24810200100c070301340c502c80b41401d61400d0003441100000e400050042003141808a02d021608070042d040d1100c806980d121b0b8011038200703400d000e40300d07035440d5949075440e40c2220701d0200c420411308280e0300f8980341c2400207559109502040c3d0420a01107540b845503142504540b0f440e80d4014031142d4103141c990505822569203001c85400144140c3c1c00142030a007541b440c00720260402c000d580b46035102d41f240342000300d00c89801c458403407041011101e960a0b03072040e0805400000051b001d64106070040180d0400c00e900140d080840502c2408410780e101092030040b54581030003845c82c0e042c0c0000b414010001845180c02550000900030100900c07958500e041e2078600303d2000d40c6d51110011f0580e6400700310b40c02400d1441c203030f0108004c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 205390827 1250 205389577 205389589
    0x24070e0904023109060c11060c0706110c01020c2d0705040c2106030302011a180604060f080a060608060c070605060a05100809010c021b090901110703020f1b0d02 71
    0x8201d5204110389007a4240403a10001c13070f003400c0c00940c1e1440c0da4510405d2a10340c40704119440d00e8029008000900b80701c04040d0b014440d02e500145082e507295145a00c81c2e60f0b0409842c171005520000b15202d0480740145078407400c0e030031039051800481880304d20f29504488034460558550308014080035080801740402819001900341c2031200f00c04415840420a506400f02c0c04004003020400d80d04c0c61070080e09642d400360300170a15014010b00e113151707902c031076016024201c03102540c07503065110040802c004000130b40000c45030703001c1c011002c80e010500142e5040000c2c0f080c842040030b207030b550340050b4031800d050390b0522009008000100c0401c00310f820103a008100107202c8840644ea4100051900b10a144400b010410b02d0081010040e820320884058405a00243c00b40e440240d112120300e02c141c482c6a032040d029030b400701c2e0801509501030080080c07442034803a5520f400d0305002e3740e82d0080c2d05d2403194034891242e4560145103035584015405074058040400d10110f5800c02c48 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 205392077 1250 205390827 205390879
    0x809030a1407050a030903050705060702100f0e0621010515030c0703030b30010608030301090c05040302090405060f090c0303030a0e030c1f0c031404080c24070e090402 74
    0x407012000784124030202e4820300100300814460303101d0135001d034a14a0024100310050380414860f0405100c0785003d625841d00c01c50391489240b42040601c22100c0064130a0f5041402c002d410907404500c0354054203001e001003d400e030403011101d12a07a03881d400c103c808040100200c00c00a002c0c0b000c541121070074005414a648a814081001201c03100403030340400c945000e8031000c04450081001082800606846000c403140091020030f00b00080301c0e69a100c180700303048070b140d95040503820302c5200340150ba01a50307008080704090704181c10501e580c1d0005942100e042c810500100d41800400240b4070f04d03200700500510b00f0341c2e841e140c00000030b203071886c980607090100b040a03c15124051000100f0100d03010303480b0045212003111241143c80400911041c5860301d940756180700180580640c1c0950701000f00c540e10100400c07210700f4400000210109040c0490b0000060300100040d1071240c5140c2c6e0700c80d00603509070010465140313020781d0041e400000007005601d04590390150340b1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 205393327 1250 205392077 205392107
    0x100303080405070e0f07091d06010806040905060115020c0913030503060406090c03061e0b041e0f061101140f040f1106040b090f03030702130f0603020907030e0c010809030a 76
    0x41e0506544d03005001d211030302110302d0307403d003c0f201003007012860b04003c2100c084c01e0030031100d1100c203540810841030401e000d0002c505221a400001e9140d0f0784a400411134607600009940719943d41d000c012100d0410302040b41c0c05030007103840c040701600300142e90606c582c026514102c1d401c1c00946040d44c07660f002030001500720f9150500464020f1140c090841030039050354000424519000e4078070007101500740d1080d502c0c0301d100302c1000311000c003100380d406561191a050720050280241006c507d45039a104040900c1500c1e0b00080140c1c005480b00502001c010083c084d0380403840f82d1614105080b00c1d2905080e1344000880c01094903080d811112611801c222070010010400051480d0403a6002d00e07145070340010039461a04201c2c4000b80010802d0f0700850401a6503800030b1f1104058a25020009503a01080d41c0704000307a0700410011a0060440c02c198200740d900200a000c0d10b058110445c8140c1a4000131548140c03141441204031001a44c10440c0b0b061040b1080c095500b04c00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 205394577 1250 205393327 205393333
    0x103060b040b18250f03020c03040e010b040f08010612080c01060e13050115080c01110a02040c050c01050f153304080f0d050f0a170f01090b030105100303080405 71
    0x4550703140c85106074041150312143d603548a618081e01410311488075091614520f458a489500b000c58000d181c140511166080c00f40e00c0ba104259010326501580d84072030403104440c00005000880c000c024016640700c0701c1f540c0611603d8a22103400d031501441000b481d59004d555034000710303002001800e1400007000c000300f0341c1540c45c0b000d2806924143c61107a02041040c510340c0c00c100003445480c682c5000300d148601003d00c0c018542d615426441d4000b0705114416a0b8440801e405010180032603500900070414420303480001009904072070340c850000d40c03078800407401d10301c1050078262099610308a1102503041a606000340034000310016008101e601e280003481030020179500203900360f44a2410b4469150a101341e00e04544985880020780090065070852a0310a04030780d80641c223001a90b82d50305200c4d03404c40d04440a07080301c10103031801c0e009101c250f1404100603412940b20200038801b0701d841c01c0426080712415070741c041d402e0340124800c000107400b48081c1907002d4040c00513 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 205395683 1106 205394577 205394591
    0xe0a0c050c0d0f0f0216121403040e010603060b07230a0c120605061203030601050703201b0406050a05040c0309120302040806130b0403030f020c03040b042c0103060b04 74
    0x9500b0107041f1101da52002d000d0410340100b5145050001c403581c1c0c9641d103205290001c800c0c09401d002030b00b0480c0010b00740100500761128580c1201182c40c1000c046429a100480180400c4000307028010030300c008101c6800d40b52000f002051a505000300c0365240840898100404880c8108001c00088910101c00002d03a60300c141d0a0a00c030b81d8403666824203403400b011701b401f118540055080c0e100c4a903080480c1c4061085885130030351603a505102d04010948441c1c0c0100c40e00000c0c811b2003000f031032420303410071840c0303469604002800079040d0b100c19284007680d45e50300010030740020341000307105001c1110341c3e80103184c511492113441d02d660b200f03040004094400742c109034550000004c090080e604883ca8405400201c039601d50740c030460095990440e102d4641e41640d1551181d1a081801081781d0b40104448a1401c0310303800e581e01c4600030b19140001e00c0d00299140c007 = true := by decide +kernel

theorem cover : BRFrame.Cov 205215827 205395683 := by
  have h0 := BRFrame.cov_init 205215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 205215827 ≤ n) (h2 : n < 205395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
