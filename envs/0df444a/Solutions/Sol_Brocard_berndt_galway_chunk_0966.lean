-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0966
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:32:53.042396+00:00
-- url     : https://prove2.me/submissions/64f2d23d-ba5f-4905-aa4c-e96039c3055b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 173561151 ≤ n < 173741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 173562401 1250 173561151 173561189
    0x403121403070c140c030601061205180316060b0316031401140c0a111903080109050c0f0a02030d060b19020a08070f0302030f0a030f110702010e130e100b01030c0207 73
    0x105601e43c202c2c1101c04d08440ba21480c05001074200842a40020b0204940d50070701300c40b281560044a81c0300300c504a400b09034407030103041c0740d03100c1c1300345902600100c0c6980d0000081249941c0104041e16025003101c2b80042e185201811031402804251080b9003100031f600340c4440140204042c03e005001d0b990403540341d44045039060342150503e41d090000c000880011240100502e0b41404902000e04080c0c41960038050314540041c0c0000500c207042c04200415071004c0003c0340c2c0c9440f049003205030740d03441910f0200c7c00c50242038400325409040a20020b0400505000341c041805000c171441ca002c104c2080903a59101c1c80c207802072454a06110140204901030400e0b02098005d005072460900c500500c1030340f540c441a1820302182d654a4110f0544000348149019107860308820381c81c00015030000b8000340c846107080343c0f1414110020b0103590704140c108a1421102404590303402c041c10821710068040520315900003840d120703e19a50920000340d41c0201c03108404501015902d07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 173563651 1250 173562401 173562413
    0x7030903032a0b10060c0c06080c040521100207111926070b09180603190311061e01060c0602071401050f0f071409040f020403121403070c 61
    0xc507088042455844000c50b086100060b20580c203152280d98501d51524090154084100d0a9000a410000e0804101000174151809603099881c0b500704043c0d81d80d194091a40d031172023140c0209422588058101c100c2403e107000081c01880039809a40030780040e5180c1d40200c1c0620b400107060500900b05a80041c1810f00182081c0a41c090201403590341b0b4034401c050150040d420b8406030048910070880f07812041c80702a026102951041c0e1814050000140310582d0340031040c01620040008903220359410003107004845210b1307002400400650502070441d1610706411241030017014001a100284880c85036003804600301854000e1f424081d046844010200089a4641e400c110582c0450242a0420404c0c000080040b0b20b6142c481c8401c44951409005040800c1e01e142c00e201401c0c0e00710910007244580345860300e803503c11120000f0040c1c44001e036400301980c030015000c000d11008100319080c5500c25200e2010841400e00c50100b103202c129081d10004a01c4000c41c3c0001e50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 173564901 1250 173563651 173563667
    0xb09030a0311070e070801080106050a150f0c150204140f0303071401140f071101140a090f02040204090501060f0c050c0d06020c0105100602160e040f08210103060b0301020703090303 80
    0x1510800b03c401c4141c95401d0391a8404065410a01140e400f0004110303c840034000c00c009083c1c00d07101540c403d4503101d04d1500e000860443e800038090001c02d0001000c1c0714414001c0403580042042408002d1140101c000354028081c090440d8001044010381d400e095400c049401e0740a002107103460103940b150081d0701450241202c003552240d0b4403107400c41c184040b1038003603c05c5c202c00002904041d04090a41601408032401990421001c1c1e11031449805000340e0140e905040416014901e20b00740145825090000354028404100460035100b2680201d040c0c1d82543c0310a01e1240b56036800361040380c0d9080c0000c04681c040c3c200e5003141e0400e8150001078a21502e409030500441458842c00d40f030b0100d688000d1942044402c21001c4c1d0304001d0600070400351050350042c2c90808100380c4094000800240411203060004400c104e01d080403188038181d040201601e120f40c03203000350502c45080c8800d45d41a41040800c015501d03040c421941a15815140d0109041c0781d660150b925071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 173566151 1250 173564901 173564927
    0x5012c0c120702030c060c0a1b170c010b040203150406050a030b0a0c03090213090507060c0c1a07080c060f0f0114010f05040909050705090f130602160c06020d03060b09030a03 77
    0x80800c5c00b00251403142080340e0707030140440c40d20039a258611050010724041120480c2a0a0b14406040300c002c9424540702c000107510f0401825074a0f03080b903501c130703000d40724400003079400c14400820807084c0300d5410600b1040b481c04450620240341e6420030001c00d00d2141c000504000460b00204204003126408070794448400d05000c80c8050403500050340c074403508040b00302000c1e180c40810040090900c00c803000b42001b42040c4181c0303030103515803003808076041c0201c42040803010305c83c0b443c4800442c2590001640051101e0ba521204111280c4415041c1c0b0b0003070741d0b5020800855181c00026240b20b040e0385000c60160100b4804600460b034000c1a15049000d0180800c0042512942802019402801440100945071600060205801c802090600d0000e00c240034011002030500d10549100d4102b0405038803619004411400203102110040c64540384040014800360013240000320b01c0c03030a807420480580c3ea50f280ca022445581d21980c0c0c550892144403000a025088a01c440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 173567401 1250 173566151 173566153
    0x8070311030a140906130f0609020604032003033415020901020c060a0503191b0c020f03010e0c1507060c0504030c06030605030a02040b06070605012c0c120702 70
    0x2140c000050680390700035204010b21030780329200080041c4031045110f803c01c0c0d00b40000d01403454240520071500500200050000040070703082403e000c00c0390000c00809800600c4940d40c0ea5581c5070401d041d19400c2500603604204118413003913441e0100030350312a080c00b80d1090f03101c089142451b980c0b1310184007050010303443c1e800c070610104040785000052218400c40050351040400d002901d04002da5040505c00c0108002030791802c0d50040c2940e410a4941088034040043c0400780400761812015000c0385580311b0490310f240b01d50241d05204524002d0fa0740c00d551546c1c0c98141400e90792001c403110002d6210304440716150900186002c40c030304044500302c5c24003026036240d4007901d0500d0003400001d140030509009101d001d000680082c5090b0030100b0416203007a01280e1146031817100a803086981d49074200c203640b6030000701e9141035400b40c020040c640c0c507040c41d840058441500d24142c11540c3e0804d1214030541026103004032190940d0300d0030b00124246403824484020408011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 173568651 1250 173567401 173567411
    0x40801061818020f010201090501052a0313030e01090b07030e040c030218090a020f040807050a05010503070f03050a140a05010303080a020901020604060b06090a03080a03050c0405010e10020c031005060406060503040b07080703 99
    0x210b1001c2c810302c1e0141d146541d800e40b580b111102502030306201d801303381081c0c038010024017404031008400814040e03454182028010307620343c01610310007400e62108900c81030024403442010390180361080e820008070740401248080000440c12405023000a01d10000d080100c105185091644658400c03220b000c090700c0e10600c81c40c100c4240e04154040c0f03840703a0100e00240b04c189081d903040000341c0428a4400d0031443e280600800d60b00c0400044001d065656020a00c034100725007100c08020800149441c240c100320740540010b2100744826000a03d000d8080b0300418060300840e80ea100050b4005c0c1015180c507110800108809a0005c0d80003808000114207602e50410741d500460140d8003180c1c41d0286a5000341c15600002c2035000007500c200400e00c92680c0042c8070803c802d000780d581150759400c0c030000307914100100c0a001e5051041c00c07104144414140c04c020b10410b019503061101c103545507c20b031842e020559004100d0101c1c507000581310352240250b80da00407140d140200c2c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 173569901 1250 173568651 173568653
    0x6032004020906040905040b1308030a05090c0d0302030903010608160506180306090a140307210903061a0414060102060105012601030b040326070309080906040801061818020f01020109 81
    0x700f00d03403003540301c840490345410402007030100c3c040d501644210701500c00c20104246988210b0780f80301c010100d03607110743c0d0b40d00820342d10902002005100f14010b070514000d0880341c18069503a4000d500d449109608011000c5001d1340003042c0c0c20f00c8a41c240c15022007040c00c1904000450300004c41e5000f806906c10020010b5660410419001c3d26418010300740040050411212007a02c0b2a5480000d038400c00c030310400500350a0030f80e010201a61003e00d001c8010b158211900ca0f665800607203c1401c1000110411400256080200700d049804001c0c64a003803d140800c04411030b84e1a02507049000100219405445403202001a140c0c0c8141148003440751b8502d600401c1c2c000303032506017044e0100810103410807d00d21800c01214000c1d900b2102a504003150b540001300352030201500c0c1c5284008104e414820b4030740c0e2000090859440c1c94641003024004d084611039000348480c18074122080c20f0407072181582843c0910113040304041d0503024003500465035286030341190740e10b109040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 173571151 1250 173569901 173569909
    0x90306070c0506070f09090b060d11070c12020f0105090402070605090606010e1504050103022503031a04050910020f04030b16020105070801060203181c200102030a050d05090f06010303020a0302060109060320040209 94
    0xbe40c40f0104034511648466140c01e00d80400c29a0350481c800152000c681d1401603a13034160281aa0b0f50f00346002075680d0840b0001c80d000e4000c8650040c9000d0805051000e040c0e4040399062148070300303a13201b80f4140c284500700206455101003449568004000a02040d4401d8000342024a185010a03c4080105003141cdc040000200140c0000f07a540c031845d403e840d480b0000310005181220280f04500305412070740d0300e07100b2251a030944250f001459101080c1280c01344c60066410814140e843e01e409103042c2507903011140000010352910000905090103524054169450b5500179404c00032000380622003842c10108240d84080c103141d44060100b0b00380100e0300460b01c55106122000e07186a040740480c10ac1c07507800d44c107542042c4078072044998810305440c07440c0b03051140031034907031540f999060070070700c0c54001d550380c40c01020008418190002401d41d50035202e031f821201e031aa80d40751580f04450a600000300380d404c804001241921440c440f841d0450030040c001441d01081c0000a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 173572401 1250 173571151 173571161
    0x60405040f0c0b090a09090201120c030e0102040b0d050709030c0e060a0918120302160320030309250b07080705120c0a020111210d02090306070c0506070f09090b060d 73
    0x840e0300190009040e1380e540c10404058401040d49501c244801001c0d83d00281883c070a610001803480d550313691420f00c80748260040e51a0601000085580b10b0f202c00c00c03510168402400740790040d00b000c0105654900c160350030011260080c40300034605042c52255003e0460180810340d0014003140040b45c020100c3c41107244140681844040080551410300d0b40060b001c0106801e1510500c00f03c2c46024020b20101c101d80d50518244c0d5145c41030001c2c100b0a10641d44e00200d051002008100c0d084000241503c9035072001c180001d0520141e20061540200501955100210a00241000806c00c0d005068114410b10517541111050040341c0915003180c052a4080c0c4c1c819183e210070f650304000c0040414182c040039020f007007024000035804007d4002076004022000590307912400c02d507030641c1c004201c02025513503641800707031005100511040040d16a4050301d008100c1c414081e0100c00e80036051a211011105c1c9000040402004042100d54100d00c0c20840501d0000d039070302c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 173573651 1250 173572401 173572409
    0x2060c0123011502010603050c0d02030f060703090c0f0302030a0212010e161505031005060a022e060e1306050a0b0d080a03060e0709051009030b1302010e0117060405040f0c 76
    0x700c1489503152420a4418918010600b41964500300c4280b0116601043c042003020058410b0380010b092440800c3c581610b10030b041942c0d0180e14103100919905800c08241a4001c10b031902d6040c2e21354544210385141e512000358181e00c004a9030b401810401d4091040c513a43e00000a0002c0c503c80d605800c3c1601c042d2030028032004608180009801105100c1c0744070003d2900505500c3d100040c0b5048076200c1c003589108540103c1c0728041c440c400c10040300820341c24070052540c3c0344001c0e200d008200d01e00b030640d10840e00748003000c100e45c686900314511a10025107034603246585511880010b20380030340ba006a01391078a00c401551303100e2100709110300d0301c10000540d0ba0101c41368010308450403a004004410350310414170514580c400349900545404981c80090000c243c1001e54032140180e000030001e02c050405c0090440101d210250414000c2e00c0740c21210380d41400440d15007180301e002c20509890000890880d0074941c3c000f5622a124505a42019020ba1142ea0315090680c3c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 173574901 1250 173573651 173573711
    0x204080a060c0f0c1a0903040b0f0306010e1c060902040209061602040605030d05030115020c150702090601030510030f08091206090f060c0714010f0e01020d060f0308030402060c01 79
    0x4071440059600c1004188078003410302d0500103c0c00075a403040305178030041c82c2044402c0c0c00c00c0c010410721740c0107004031030003820004e60a9035110725040c034030340030783d00f00b1100c083c0814001d410100503814000350b400403041c910f42c10718402c1c001c10350300d00005000d0420140e030043c0d400d0042e48016103402000f0103288070010701228040417644100810340310710340c000310b000c0d40000904282c01a0030006982c1900e034075000030385508600d25012480c010400c0916136003c001d03654003811100050005144150007550742c2915175588000550607100c007642e14414521420100700040344000b107050700f070b042c81512a00c2c9000300c010002540a1256103204580750005403c3c0815040c041014610300c1c950345e800b0381058646690380180c54028000e010704401d034100803500c0d10348000e50094550450005081103612000403240d4000d404c0501824030591510201003101d40c1050184800c0300d03070000c6864595603c0f6030a1103515000100b40c00a40c1d134866074900c2c002d41400e4131654882100704 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 173576151 1250 173574901 173574911
    0x6040b0919170703120606051312020906010503071b0809180606180604080d0305090609010e0c0f01030b031e010b0306090a02100504090501031101120b010c0b1b040e070f1106190204080a06 83
    0x40c495008164065102040c0e031585a210ac00040c0c80750040282c3c001402d0034482c2c0c43c0d0b5110101030f030718070869640c00340941001c0200c1004001c00c880c00303000405001da0300807a0100100e010f242144809694041d405001800300b03407500ca02d0305440c05102d507405882c2d05d041599443e40107140c181c3d40315100000c00d85034005c00105030030070000954400b020100904c00790011401c0c4c20386401c8500c161600400300c64030000980d901981080c0319000024046540d81007001c80480c11400f10011011100d50800d2582620ba15000440c28000d0a00c000504084c2200d40d080007a09018400070000b4014103000005034160a441494000d5008007044801c46c015400010420000904015249803602c124020180da00500d6607008a03804020b56640e500c41654180301401a5050604a480001808150220b071001c2c044d02805d1035440394040c0d038081c03200c00e41d4400c090910f6174035541c0c440c00c000f850403174003c404440e600b00442801807400c0c0d118184942820200801511116151 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 173577401 1250 173576151 173576167
    0xc12010b04030215040605181203030a050402030606040e070b0711030a030306030b06010507080313030e0d110301152d090911031621021206040b091917070312060605 73
    0x1d13031840c184048020000a140134181035015000b40640c44800040745a240b0100c520742d200c0903140b00d0385e08008004c4030f8030b9241030703940c0e40080d00d0700f16012400f82c050075000c915942018000c500100c40a003015040260070800c1c100042d4100340401e440c014140d0010200ea52018803443d543e82d4020794022550f81d0441c28004458000901a1410441c0400c003202c0803440181c1640e4001d62080c040c08070701c400d181803c440030031100c00e0099124440341051020001c0014200c11003040540090101150079241004d9210f000c1c446c4102210402d101d00449a4854000c091804c824100e0b00c8c091a1300c0d185100101c0b2241c01e07088400840542c220003461a0801042c01c0c231321b0142020740c90036800d00c0c95624007600c042e28032500b2810504944400c5546028261248212aa049030b081c4d00c0d083c1400c4482550980e01000fa034001d00000c1c00c50061407243e07611800c0c0d0040b45296207003049240c07180b42640159010340c100003440c054606a94a1401030030000e0815a6541da100d07424 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 173578651 1250 173577401 173577409
    0x10303020607020d1b060608160305070801050402063a0203011d0601020709020d020906070c06170f1503030c0f010606030c031802060f070c15030e01150506030c12010b040302 77
    0x3018016a041d9070220303441d450095402050240010001c14101030b05d44050700e4650041e014503000084517003d06e0030218103900300c042240303048900030412a21800d40d640d0f00c0038201d03203080ea4082d400910400c031001184081b07040d1029402000e00085207507a00400103400c0400c91000030001003030300040100030000710145045c951407580c00807404182020350011b0360714040340c4600e00d042600419403211648070343c0d054803d6004054001c0ba540c4490345445860b400319409000041202410000441c025030015076200d1070303d07020b0b0300c80750b6107600c402e07440c400d003072407400c15450300c8104004080d60034184402e080b144508400460050300309034000d02074a600c1000c2c182014600300105080b01a411500d015158050700c200740d440400680e42107551080100150404600c404001500552808000502800f50b9020000e084ac180341440c00d903041c1400a100004c80c600d02481680342c114000e40e000b00d4800b08643c0b4010180600781040f8409a100d0070042c01c0120b410815418 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 173579901 1250 173578651 173578663
    0xc030605030d170c0d060807050a0b25060605041e0605060708030103110a1a071208010308090f01200f07080114010902030403051e1309020415080a1d0601030302 71
    0x200c114003811440519650090030200c1da0004480c24030401400f15032440c2000b001c96907409010141848255110094556128440d100d0140113021411001440900041c00d0f00d490340e15581a42c1c04008120051118100050350203a51700b56882c4d0700004c003640e5900c222030703030140306440e1031004606101c0804120b0303a071a4401400b8001c10025000020481411030b810740364886607107009125800b0100c0e40704101a003000350440044c0d00645c21003400d44002d4480c0c180b1030104074524110a181c00ca4041300d080c400203001d607005000304401f0307240201d44001000d6040c034280c03000349580001c0f4505440c0b031219160f03440c1c0103c6040512000c0c02d100c00005010040020700c86852041c0ea205a04c11052151405242d80400803c040600c54001ca440d0460703c40a1003151b00c081d54520507160780440b51413584846840d10005483c2c0a40c002d4400315800000d40344118200d4070030540f04680000d0080840c981e5030070210526481843c50114511003010050640d5819480d000e480c182c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 173581151 1250 173579901 173579909
    0x1d061603230f0702060c1204120c0602030f0703030b2814040b063a0203010810150603110706090804080609010b09011403010e150702011a030a0f0c1203030c0306 71
    0x4502003004035110081070b0100c51500d41c2c1641c481d5991194180510705240c4561650001a440020001455414030b9400d100c0f0700d000d049507203c45a56028103a13524130a415100706070303140a11915012038003c3c2e01c001d09400d0040e080200e64801c03c0284a41c2e40c106041d00050446400304c24058481d204000891080045d0740802c0b0400c40030f00083d150340038040102840e0f03842030440440516520711410650540e0402801c0034040d0300c1d42c20320184d0030900846005115400301200030030355601500d40e018034904800700c1e1240c2419411070144c14207052001a41c3c404111401c000784d0380340705c0c80b04624040c032006900c4504000f105030804002411030f00c4540e0401c8140c01c04d07903030b81e04205811554001403d89001b4000d20100340034001d174405041842c010050160301c403415030b00040e8401e13070440d4020803040f1648580264100d08044503241c1560203420500c0010300210f1405e41c06901461100c65030540e120800101c004520070308400090301e6840c10042d1a405026644c054 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 173582401 1250 173581151 173581217
    0x906031104050a03140f0d020604210804030f0c0512030609010501080910050a0b0315011e0819081201080304050901050405071d010509040c090f0b03071d061603 71
    0x1003460680010f69481c500e00001e800345d0340400008510402c00c00c446564a00100c080d9000308280540294841804540c2a2588400380850117114000b00c2030790000116692074420490b12103480880d155503e55801ba01405903894115011800c02c1100001180c035240046c0e550b807030054140a442281a403190341401202014041004008240801403031801d100c002a9540d41140001c080c02c0d4103403501c2d03010300403607030300c1801c0781d00c007a01709411383e881258081d020341c10502a0a81d5050140301c0e903902d1750000f0110110030718146201c441030364041e2307240b00c1c00c000001c450183d01d039400b0788c0a544c455000003010407032810441080b9006241c01c960030400307883d007440050f050317242021003001840c41c0399040c507919038040c6080c2d6000040151041096541c40310001d401c940981c015001000402d5500285c100c481c0d504032840b4034800e580e03280714000b0481180c448003040740d0b0640d42c8424140010b00500030030800c84260b950207903a50580f1030b0310448844841d0290f4900c0810302c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 173583651 1250 173582401 173582407
    0x504020a031712090c030706050307121109040204080d08072102031b0309030a0e0607050c222c07031e0f150b010206070806090408030903160309060311 67
    0x140e03603520880000c894201901901e10401000036041521440b02904802c2c802001400803032030000404121a4005808030750780a92a40d500307450710b000032904e4400040c0d813803212030b43c8074150386c000715010381d2101d411904140040740010140d80040d0400c2040b82d01c03603104140f456601c940140e03080f004904180c181e00f20610b440c0312510740c6962020500e10b4002003c12054a24102003401000016501d142c89003046034459460341d00c09514440040c40b1510303100c0300c900d4010700310380e1072691090040c03111452501c00e00072003590385440c0d1000002d1180c928190618540105002e20110b400034602c0d0000c100349000d42041d0100b40c4402c1d5501000050001030142c40300c41c41500c03000204a0080d00c11450305400c0310001090080c241c03000c5404031000701e4000d03080300c1a07442d400d07002e54a8550700c0202c03c545d041c40443c0e561b0b40c04090200444c000c100301e0340055800c0040d080559281070401008900c0c9540c0007407040340000c994400030801551300d8400d400071101e00c4d01c0054a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 173584901 1250 173583651 173583653
    0xa090b0a0504060e120a0606051014030604051e280e1509030d0603051e160306050601090302040c0809012304060f140a0509100203040807030e0109050a030f0507090504 74
    0x10007405070340101d900740080181e160384c1ca0350f944600b200c1e00d224143c003182c0d5015610301e8040b010340362500c2014043c8900311480a103840c02004d060b500070003055a02802e694500040102400c000707030419240080c44020b0915144540032024801d000c40300d4441d00d42001e042b1401211071002508020307581ca440c1d51603803901d001140b03800b100e041c21100058151503042000742588214290030400a217003e4002007000000310324034004214180c481c6000b40840c00d411610b40440c816800c00c101400391050000842c1035000d039030000c0041c505000c00d0b82d103d07408541107460192461003ca0340710410048823030024000c513004103003c005a40c90131b09014411a0f03514001400040c9800e481305200c0401d0807940d88600b0050501400050003400c0c02d1a9600040506071403100c030038090a80b1144081403980200c0f40260ba100040c80c1c604440f0f510101c03502100d0306c0d500c1c1d04100304180c00040301d50b14149400080c44c0105080d254007891483c149207408004e1b8008034000d814501008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 173586151 1250 173584901 173584907
    0x40b0a090b0601081b0d0609050c0c0a080304080910080412020c030a03081e0106090602070f1a03091c02030d0501050306010609061d060412030206100e01090b0607020d06020a090b0a 80
    0x6070402c80030308103a000c1e03403030b10b0780f400054804c1e400c40b42034203060100d40c01c441d070025604007404039030b40410704201c0c1d5100d007400710301184a40d442004050f03100c5400b11001400740001541d010b03000d034000c1c90802142c50300080b840103034014040b000403086000d01051054248246180f00d030036000a0074000c0642011a40311440440702805100000c0c000555400c0c4800b54a400d444800c08251420360b1501390103814191280a0140103115010002c600035050494043c10b44145260003824022008170f8900141c1c0018066012809610341461340000b00f02000c603018407142d001b03541c9904480c3d250070210b51050707102901c203070700200040011640282910080d43c07090700c2c040780c0380c1c0d20700c2c1d40d40e04000603001a4140c0042c00090005030400300141c0004a03241b0075801e607001500c1d420100320f20105140908841044080010882d041c050b512407240e068010309036a0a046030b64001890705030040b41d0940c0c0c0d050b00040e900d2042c540c4248460040c1c5801180c0c0e0f41010505c1c6001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 173587401 1250 173586151 173586173
    0x3060b010f0c051b010c06020a022508060604020a05070c0807060e15121e0c070303050a0203062116030f0c08070311190b160516050f09130b040b040b0a09 68
    0xa142c2105403015104d09640f09004020045030040d0f810f650f112440c000007581c03001c260300d0f5000d07809030048005102d942000e07003200803114541e008200c0740e01c0b68400c21009610454a5009225007080305800040807004044000d041c100302403d0380c0b5182c6030024158a034040c0c3c83c40e124075490318400049441c2d40f0280c1d85503e1030003407902281d039103140284500b07140e4100d00300740c0400c012041268000c4c003440100042c0c1d02c2170344c044c0321a0300c0304010038059010566980d175102d4008607401000c0441d0301194842d8211b030104482c14440301510307440050714070381c20546510560702a24000c0c0004141c44000405032503000300002ea2460701c55441c0402c034242241e10920781c0c41c0618840300b6580d41c480c00a40271400000c2c0e620712005001205144440d14121103600401c01002c0f06400c2882c9598205c502c043c0a414640c60f03500104458814000c3c072004018200162207004200328000051150b803154150300e06074200341c18504911140280881e09586c107291420000901001d48 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 173588651 1250 173587401 173587423
    0x4030e21100b03011b0c260c030c0c01030903020c010f0207091e140103050a111f0305070306080706120203180304060507030207090c050f07050705040213030204061d0106050c01020c010603060b010f0c05 89
    0x40d03260410b009007043c580c4016107032410810347c40108000900c1132020006010301200711003100c550390f120f10f0064003542d05000380600903811001e650582540a01c014402d500c82c1c070b10684010a45511506c01282c500d07070545160040c40c41e803510300e001014494440c0b4520004241c1699601d50b80c0c4696655520752001000c43c41c001e10601011745454843e21902c400c942c102c0418511501001801000c04a81000000341444400202004081200410b584e00e940d038007921b42c0c0e40368100708065400a09124209501c0c4104800011014409000545030940c0c0306980c895003418000d2038071b01c1d542c020f5001e40f880c1031070f02d0710869004000c41c1c1200039100c10b69500c40d00c1d1402d1850034080d859000c00e42150001500002400c0c1c0e00c201082624400c880070000309031603600032030040d04905400008000c400b001401080e0240004d84080f41c1004005440d000d0703500012401d40d40b8581c411030304140c803106015095030300f001e009010f440403483c040c80080156291306075181c0c91007030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 173589901 1250 173588651 173588663
    0x6060e0613051203120a2708090409052b081006020a0f05010902090411040e190602130b0d09120c0f02011d0a030b18030304030e21100b03011b0c 64
    0x2c81032103503036004d00036505003803031004103800340c1d140250885024000d05452140c038610303840b002c516400a01400c5206c115040304030725040400100501006210810050361544103050203c2020707010040442c0350135580217100c07007137a411150050501140540358441254000c2c0082c0003281d170000d440e611545d0040000c400802e02c6040c05401040c1a07407010b9040740e2103408000a1006140100441010580341000309081064096464521080100c42c401c0060300d03400021030346a070064580c000d50080c16003860b60b51084010f0f180d034403070320032802c020780c40b4070b000e509100c56003400f80a2844c00b41015080001656205202c0d00c001d0349009041c0301086c1305d60750108048201c89140c2c90000b42800d2070a83c0c0764108640c0000c1b04582d0444ca0029200c40c00b80365070404000d0328040e039855102c5035105500c4504004020b9901d02e0640480300c0601c0b1340743c49a100c00c01c5400d4000c1d00b0a1000504600c8032418142074600d420600c1c1c0502d070108820725060750b407005c00103240b00d030000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 173591151 1250 173589901 173589919
    0x6020c0307350901172a04030830010303020c090708060904060c0915091403010902090f0a0b04020f210105030a030e030a17031504060308030a020d0902030d0306060e061305 76
    0x184c901d80001c4400000e00081201000206c840141c04507281840f10b03002d007025800c503500022400d01c65400020b02406c0c042c052010150140300203402003c407041c0500b0100d41c18540008064a0309a20940069000496103256403d00c502c02d140c00407403600c0c00d2021031404202003a03130500c000e0402001207540c0c98075210384901c80e0f115180075107a545258198003007404401005182c00c0c0c000d00031403000680032a51589014460349840c9503010300b12001a95550b00c80c180c81030307402400031a4240e20f60400c02e501eaa5284010800184001c5400d038907200c6503e44425190350340e48510721078489810040c0401d0b58000744503003000358507103040048c0300c0300c020200b4101075204000a040e41107013020680c1c070120182c06035100c2c286198454400034081800c01c4181c0d0403a100c0a441c400080001c10b4102001d6002411002c545a50203d00c402180e404649030448100341100040d070707910010f00509078080254401001c2c01c0765000d00304190742e080b500290015110341c92080c081a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 173592401 1250 173591151 173591167
    0x51e0711060306032b02011b1b061503031d0103050702120a09050a031406070306120305092701052701060e1f03021801021609051306020c030735 64
    0x20040841c885003003040c500c2d520205080b17080260141d070707003c0c94050b508000c1e1480302d041c00d9101c4420080712559880c00e0303128940000e495a6404403000b0344030142c41d4051003014450314024100150300c669100580c4002e504040d20320b00700c050306003a04040c14030b424800b4581e030008a84030b289810081855581c400c0c1001550a21403c0e4000c03600710b50321820000a014003808003400b180200000d441007513a611008408654141c040c4d000c1085524101c000030a1150380034040c108001b4149400b408840c005030380c0385201e10034022401c61280c00050103142481e00c0506003c840e421202280c1c0540b007071401546c804d050050a041040246680c0600c3e0784440314200812068100c8465103005000000c0c080c0d0b0240800724109107045981394002c0d4030003c0c0c0702010a0382d0000602e800fa080c08020350140101400c0100103e03812045400440c0d5548000c0c90048507200040d5543c0c100c2d807800280c5401812030288039403103000c80380100c00342166684900da4240300b21039079640b060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 173593651 1250 173592401 173592403
    0xf010e0d061a280e04321f06060e060403080a0306030b07090602010c050c0d0e0102010b0a0609080606010e0310020c03070b0f0402130225140d051e071106030603 71
    0x40b4807280703a2203020b040e9440c0180103010304801119240c140d001400a460302a44100d40c0303c02ea4006184080304400030703e206200190040c001c61000c91a1400e6240a4026518000e0701d111066144a007203e00d647d00009280704040c002c01941c144068000109000140c10380500d10010340352140001d1841500384c42540040c015603031000e03440da4281041000102004c12a000c0c08025629014102d4000b070b01800603107415041d1304008000e15800548200d88c071182007198141590340324482c132891036552600d00e20141500e6955080e41e07519140f038541c03030104040c042c2d83c140203050944080549010a081811070124000940c1d036440410050f0715501c28540701801040001c0180903040c1501d0440700d02542c004c50f41115508a1500c00324102c0c1314820396040e0340d000e0078158000c450488c0c0f10440c50240180042100b40b4444040c0700e0421340700f82c03402c4001070000500c0c4034480b501e11034000011a00100000e0600301e41e9038440c43c028081c10715291140d103000c4001441a60 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 173594901 1250 173593651 173593691
    0x901112a010c1206060503130f03030b0a08150a02030907290d020c210d0b12151b07050706031a0d11012d0806030a08040803090f010e0d06 61
    0x585503000700400103200d41d00600100044a00d42c0045090240000d080c0e440f40f001d40b40148096030044083c1030b41643c4000e04c2e0780301c00100f201490b40305d05400c40d1940d030303922100009011f001d0103012607240e101d80317010f40d40d40014210b40f0b03150b10500a0100d151030005841041d86c105100c00100c180b40c0144403c0000039445012540400000b400c51200e419500a00000c2c40c01200700c469161100c0920303002c10804800104110b2818041401c0c1d240d800d4001d200c414902805d00403228425040ca1820000c0808680c5080540002404001080000d101c40100e018600d01404c0c000c441d6036007500c40c2c080384105030405846003407883c07001e0502010490178083c000c0680000548070302c0c22011a140c504003203800305414485240c260306140c100c000e000120107203030302030048200105480c20740000d801c1c1d607018030bd000d07540340c00254514000c00140101c03000868645021400b041102c4040110590401903000001c3c20a6190401030040b01680722402080000c158085124a03003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 173596151 1250 173594901 173594977
    0x509160305010b09070f081b0f03270303010b0703050a0e0301090609030305010515310306140604020c0d0e28090f02090907030b0a0306050f060108090111 68
    0x2225800000040010551001e40490800d032802c2110303580d0300c03100381c0341002003030700800214031500001540345001030102e9030344610030341440b81058111581c0c0f84035600100c2d131341410303006a040c00500e41c0f414507a0b141684058000154515814001e2608660090020050500070003284500d0803500404269101007400b40007081840081c0c00d1540180541000903800700307240400103e80c0e0309080b01628803a1101c1e21b0a103181040f2070305410b00d0b05403a003544403a0054001c40e40038804041c850384000030f40c028040803031640300c42d10080d40b0220000e017106118502c1000010000c0c0408141840c14000c80e040c03400031040c843d070201d0041122a502c0071904050b080391035a2541120000409880814104000c82c182c10074408040b1f20074101c42942c007402850020724400c0c440e4121100c0d0100281140c0c0026075a41c0d00c1c0d038251001925480b80c2120309004100b803650348105601c0e07004050700000d021140c2c1c2261140c029105002071524202408200c0c5d41c4207803150300350b030346500d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 173597401 1250 173596151 173596183
    0xf02010917060a0501050102030901140d02090603090f0f01090201120b0d1b0620030906031b0d0e010b040b1c020102120c010b0109090504020102150a0f1119180302040509 75
    0x30084035505030b290501100c451883c2e52038200003082ca54800801c8e554000c506848a81640b21280d00440d580e4204115030141103070200403611301d64030755601030360107070784248004c00c10207070101170044c20a00412488540d85e03160002c18000b503070b40700c00d201c018601070a00005488400d20301041e42400040e00103003892856103031001c06010b01c10b040104a03155aa43c031201d0b040c4018070107100e02e01d94110380c02164000d021481c003601e003180045400c00103c8500e5100c100c50404120519082880204941541c8014806d40e81030280901050040100c8081110300303018000a041d0009082c034400c0c00100c000381010440e4004c00081d40d0301000006005d40b96509049020b0203013628080060010b001c46900003130708103103401040e00440d41600a0080b40d1440400903080090040104101644a19504120540c944202c070008214024001c1d581c14105651810343d82c0d214001c0020401080000c0c41c084144a00c1d4806aa604071004a12515030018403860711005d4101c503a28 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 173598651 1250 173597401 173597429
    0x3c010c0204051e090609150c0414120f010b0901140d060c02031309150806070503070c03030b10120e0304030c05090403110d02030301060216060503070f0915050304140a08070f020109 80
    0x40800c001a010300c91b24050003101c0c1025203486550b01021000d9a80c003206140070b200603c503688603802690230050018042025650040c041d0b40d160927660101500706940d1428000c116040101847d4050140324201031000c10484000c944031003408030000e4155a41c410b00884030501c01e00450f42030711800c840304488141c0728844040101004181d2000b84c40c9481000110380402261403441a01c80d03031147c40c19a5a40302e030943e101000844202d04041d9200743c81c585a585642048000c41407a58664200030581c0d041030f021a651003600b00c18661090000300001441882c2ca0b800341c0d00180c641841c1a02d0720316003a90132115452001d8458040c20300d0f002180c2d1b9000004e10304031951355088803441520700c04030300000b180c50300030303100010410000105000d0040300e00c60400d1400e846c043c852030350346440c0000700d000d00056001c00200008148018003188030066220a40c01602800400b03495650700040352240020043c00e0b4545451040301350380c011001580242480224006 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 173599901 1250 173598651 173598661
    0x507150515061b0105090a03050403032a050606010801270b040e0106062a0f02010f090b1605012909100806041a0702010b0f0607060b3c010c0204051e 66
    0x40c10085804072580f10f50b00e4500083e05102002403141e14980c0c150329058906403c68030b00b103034800d00d119034103000040d24011000e0410215800303844400d000e81c0c0542540c1c04e214000400014060f40181480c2c40c0b6188103000c0c451003041c0d2500303c42480e031000910600c0100105000c0d12200050701d405510303210001408940264850224058401041300048000390785004010340045026001e08a11811880154064011140340f82801d042070140d843c0e4414494007150711141d03515510020320300412040100900170a258540503907109100c1c0c0904500c0c111449079001072003849010482c001c61008c400c1e210102c0d024106c4032065854a1a1038200480e5100c115041da001d822142000194001d1040c818500c80d424020030407031016041508002068100e02401d84020f581c0349179001031959040074070403181401c0d40103d4120a80300130500100003036140c3e090341d903400300042d50005a074410b0000c1d8160358110360001d12074071904035180d01030380390307440380302c040b46034482400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 173601151 1250 173599901 173599927
    0xc02030709331503020705060412020a0507032108010b030604020702130e060103031403060a170106050409050d09231c051603060b06040503100e011806060e07050715051506 76
    0x502943e4212402c4150401014011002c070302c90b0860240403504200301160020324091140c0e026201144111680c02815403201410714619500c2210f04500360514903089000c82414404400001d082041180d032400003000307aa440002c0c00d552280c5e50000d0103c00b150b41d012541159502805800c00800c40424a425641c080a010540200341100101885140700404582c840c0d140a4403101c25186800c400209500708810041043c0d5203818000c15035446900c030303032045030340610020101e058240f0000f40a4101c0c6411510040d1100203100c0030225410068020640c03041e2900350f485880c90401d01035049090900070080e01070794103d038210784a620100e009407402000d040012015010801540380301720b10600d40c040d08a600d401d030300c00400d0307401240e83c1420080040380614100c01d081c01c010451a00071181e45688880900c0b88071880c14145a01034514203040d45482e00399180e13070000303291038102200c00584450005014022518000350b0154006d40025180c0200000705 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 173602401 1250 173601151 173601251
    0x21b0d0b09030d0f020901050d052509031505061c0503040e010e04061a0d0f060207050d1e02120909040c09020a020309040e120909040309180b100c02030709 69
    0x1c1e03c00d4504029114001c2e10b454400c441541c001612000c0c82e00c1c851201ca80040c0038024801030425400e040d6a60003040744c0d811380a0812229541d20700030314258604008614004c420368490b8604e00070801c040741d264024841c0300042d8010b40324000e812949010751039481150080081c40035004000030f011540000c800d030065100303c80c1030120100c40948203210742510311200741c1c4034200c1c07446880422040c014000311a0702840c00075140c00002c1d2111841c010103298030000080003140c07101c035003413602c03c40030b000010103101509440404801080542c000d23101c0dd584140740f070a0100d4100142c40f40118000d12501b0815512808080c1003c2d4803500106640d90080e418202d0b1440c203070b00c01182c40c01902851250340340c10f060a02c1e090203245c80c0003c00490601007144030225581c42140510884c0d801c4810303020810754800403d000001040e141010244044002101c0c0140c0c0e0205503402a01c5c40030400140d00e402013581604440c403a039403a203034213985540c060358501b4401041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 173603651 1250 173602401 173602417
    0xf0414180c03010b0c010b060f070b0f070e01120e0a0311070f08060c0901050d05040f06180308241f02010509070303050a0c020d1a0f070f021b0d0b0903 67
    0x1040c505051044100303245408220307080c40d001c010400040c00900200380c00707001d200c0d444400020380c2c0c49580d00495090340c400d98081c900c1d1f07507000c140ba07001c214040740e110317501184103214041c0d0307420011005895a65411062414071024019185540c0402e600c581247d82c5140c08403843e940d490b0801404450f0012500314941c05125000b250b030500e82d91a230707400c4031064002810300d42d0300e01144c01f0898001d0301c0c034141008000c0007145088001400307050300a0f80201a4910340345030a16045080700d102160104140703486074050400f19070000f0500740d0041c1644208005144021110002d0160302c00d042a07110841800680040511603240450181d00e0740080003640c071102455070340c52841d44001000510f0401091200b071384a660b030144560703c05004c02c40141015581c40e10603229001c0c44800c429151410082000c00681e49030307030442ca95040085540300b60000094851146040241c00360303039122490582d54441140c00c120047c5c01141c01130072814510001303500e136800420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 173604901 1250 173603651 173603659
    0x607060f1802010e090c041d16090b070b06030c030a08210f010317040e0910060e01060e090c0c0a0b070207081912120c03020903011119080c0f0414 65
    0x40c000d5940c0114510076406030142c403603203494006902040100c003070040680f0f41c07403101032000003040b44440300f45100c941641540d060342c40c94148501000007541071172000070458500302c20400802131348100d494007a00180081029503130580801e1030250b6a140054161084600240030720480302c01404180c400100e4009040006004640c1c14190560705190420340841c010800035410422140c03c103a1400803c40c03c0c69581c640d001c40c000000c4501d10503940040540342c030039181501c5200301501030030003c0b81441d418118001c0004180240050003002c1d0b06000c100301b0070095060b20301072000c0c202210403903001c41ca000000103000f074a441d009849010300102d800840800c03410800414000440485051a00c0340340540183d01510410300c2084020642e00c4401400760349902006910b001d40d0f40c01c008000c0c5030868010f021015081c0c7d009200000904208502d8101158a6440d0074965a120481154414810480c11625150340010000380d200d048803480c0c2030009040b1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 173606151 1250 173604901 173604911
    0x18060a0f050c03010f0b030a1803090303020607020f0705060c0106090203070e10090302010e010302030703090c030b22050d0c0206040b031015020604021f0e030105190b01050a0c110105090607060f 86
    0x602c09007240c082030041035001009241c090044440c1900070310f61001c40460b0106a0700c20380c40d80c6804801040340d0544c00500d02031418824141c040041c55000000d6100400103981c4415405844038014001e0500c10b02c1c2c000749001494609421600281c009010119034a0501000c094048916030b00b6043c001c1058103c0702c942180209100300842c0e8060f1070317040070343e4414401140258402000310042c143e58126000104441e44010000766204001286d21402c0c0400e402420082c1d9240ea094181c10980300440040c0c40030442100080c01c6080000fa00b9400b880060740c80d001d10342008520403404000c0050034415081d20300c00b160100b5461880071512103404a8a442c3d049030069007000a4110000c82400d4060741102180030b18941160350b0446400040e0944800751003239010140b5490f659541c141c00340c0700303c09141c40700b420520703d01072a0a2001c2d04044a00c4006440034060040c8812240d0241c1d0407140b200308028145556941c81c1e25011000740306020301a0090f5243c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 173607401 1250 173606151 173606161
    0x30f0702031c02061b040e0f060a08010b06040b07060216060605011e051e0405030a030809010c020a020d08090301021c0203240d0b09010237090e0f18060a0f05 70
    0x12080400303282c40755002c0d088560310001d018061140960316121103410801c4001004e01c007c0103c28080c5410a24112003810703c4410048290469000421035925190094405070f070b84008440448803820758103900d44400d410513070003d000ea017106034440c200e03030341d00641000041e03489a0f082d01c0c401d1700d424a10269074120031100e45c411b83c0300310010500820041c00d401e8000c44804802d00d84070f03001c07203103015101c0000c40d04084001000710045560b240900c0181c02c401c0c000c2c2d81000e203507032000340f280201540020305c0601d580c0744040d001c000d00103480f04042c0c400790101d402401401544131541c2c1c10060100700254006c5a80c20005a02c04990070403030281c048400c1c4d0785c190014500880140c3c1b54640140200c0c0103400700c40b507990308010b14010244010944d00610340d07010010720400c074440c1409000c400723104105808101d0802014071614a14032030580d004601c90101d040194bc034282000c200707041c0301e014181d052190400300107101c0041d400c00044a003a140b130900058540b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 173608651 1250 173607401 173607433
    0x30a12020f09040b040f150305011a03120a090e040f0b0a09030203270d0c150e130c05070605180c0102071203082206023c0a0908030f070203 62
    0x303803000c105072503031041050410714605034000b1149540c00420000d010001107200800700c0704216a0f903410540c1080c41041401020b2043c00f00c0c1c94480481c5102c640b400b080000e883c5c2c40001302002e44000082103410302d2901c5030036210042c03c03908400d50101d00700703802e11050203000202c046801401e07800000c1c04402541c0148408076500d40c004600340316100740140c000c01148108540700c049003081081e61583c0d008407024002d4041e85107100b03000d0401100700a4840704443c900700380440d0407450381898448a4500d041c90185100014918045103000c0760030b441440006000e03217017402c0031b0120000ca03200e002e03508440101c0c01c0301d000054904c01623071600d250b4440c1294002100ca00e800c0441c2c022981c02d03a000424007403c403c10011910015422201800150f888641c0840d0446203c80720b82901c011041c40e42c062551031140401110284009515990043c01c10104500c40800d0013400901c1c050440002a80c0e102d040c0020303186040c0e081040180d210384660064140d003581 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 173609901 1250 173608651 173608657
    0xf01050d0c03060203071110090501150b0f070f06050702010c0e0a0e010e06060f0409090b01170a060f0b03070303030504020306060105070b01150e060c37031b05010c02030a1202 78
    0x7912940401c000d51560300c1d10030080d00020001800e2001000f003a08a01c0c0d401d1003036218141e8800e41c0010b5500705410a6130854040b445115541c103031848041c00b400c2c8038030003941d004042001b0b442e50348140030b1030314040840c2c21000040100342840c05100c1d800d901034202c410020301765541d40c041c0340e4001041100300c071001e12514002d807903c0001407103484022a04280e10407005270600e0714011045400c20203d41c8541e02c5a120269965404400c0203030760a00e03a401400a02c05000720f04002d00101e0fa10340a0003503000f406550380f44107484020016820807480464001d040d0346240f6581d0038094040e0400302c1e0103d109015241c0080c2040d80210183c91722907804c080e1070b200c035a0030649071010b47e0b21050015800c2c40b409241c5545e50307944040080c07180341f420b44044c00810b025510b00d4214410180d0342c92484607841c03d110480c1071090100310041942500d000701c64000c0d51103401c0803120414030052301550074400c0c040785840c0c0000080010010b103550311414444101d0301601240 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 173611151 1250 173609901 173609903
    0x190302030c07030c0c050603040f030f0201020406050d090302150a0c1b080405010c0c0317040611010605130b0a0b0304050a0210020304050a03020d0201031d0c1503010e010504020304170c060f01050d 87
    0x800c103004210220f40b01e00c52402c0301c0c45c803c94402c180740d511400040c0780d58104071011283c0c01e049600313580405074498280342e0801c4540c00254101420854094010f0240e5400308500990b164110000e042c401c002d8050300b40401c011402050034061050000b40c072140d05140042503420400e05a10307202e002201d03041d603801840a50416040000442e00075a65800070780d280303400c000d8080003152148103499900c0719945459030385c0d10320302040684841d89000f0040010707403600380100400d40341e1644410b801c02c0701e03500c001514802240003400c0c3c2500c41d0042d1107c0040401080100940000d003465041d0085884600c0c01080002c126620304c40c90040681064201c0030030401810300070560f40340c56105040114024030554034200c000d07418180da030310080e8040ea00340005410842c01904000141400c0741745198106041d05001810610803980107036400000901481007581080016441a4803610341c0c840400d072110781d99020a9440904010311103000146a250237500c440ba19 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 173612401 1250 173611151 173611171
    0x1404081905070f080c07090c050304020f0d0308010902090109120507080114092107050a0f020906180f0c040f080303010501080a0c1b02030c030d1206090b01050d0b220219030203 78
    0x544403540c4c83c00801e40040c01c0600c11445448000301d49069203005601c2c410b500c82d92019240c4c03074140104076070782c01c1c0c8044550189112122080129070b00c100c1c0d05054410408015a58181c804012a0b103420385900c00f0821160756107902c0200200031a180c0101c89086000344400b046800c410030071542c0c26070714080c01d940191082c05440085842c101410419004001d003824519200c00c0d080c075a5045044031110403210003901145000340003039401a81c10355408024804071441150407007005400e484092071400001500c450680c000c07038000c2e144144e9500340440c0d80307000300e9070380b41c1003801440d0100d410b5100240c8075811038400c444288250355a04c01c0c402c03141101c502401155400d040e6054050001c181a5585041102440da03040541e21685070303040000e6500201d802c1c0f1b802001c5414140144540d590313a2140564079079003080c00c4c0000d600051700c03000620008044100070281d03510001d8045a901c2ca0780d02400d0640031000c90b154902d0f1041008604030b100c00c035400045 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 173613651 1250 173612401 173612423
    0xa05010c0f020103091a0711030a02070302091f0b041406070309030615030803010f081218011202040e13120f020318031e061006110705040f140408190507 68
    0x11500c201c0041d02158018140060043d00b1526000042c1d01e4142c4d0303040307022080c2030520841c80c4d841494500307203c1c201c0c030195041078031207100252074180500c0080e105400000206003150412403581c0c005c00d84d0318503c41403e543d02c5aa0341e800307030098030980401d114003031400152400c1c0402255001360341a03036581300c501c1c02e56480c00e000b407507641d40c10200c0400d082c1e40031002030f032100c0c000c40c040c01c0d881c2c50030b4119516100040785020505040030910460500c1003085e40c81000c40150b403240000d003006000042d806840c08001d0081d94007031841d2280100600c80242d0841c184900300301e005101c100c182c0c1c1030668058134400c802299120060307000304010385010b25021450389004400070207554203442c41e107a880c503104109003910070064101c0002d004150791000c51a8004040030705002c2e00e9240710b03140711a1510070310710401d402581ca9103180301882d0520342c410348904003c0d107012002d900341400c0c44055600500782104815030520452030820b4002d4054a6185511100d4504 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 173614901 1250 173613651 173613653
    0x30818070603050a0914030c0106090b0901050402072d020a050603070909150305030301180b090921270109080f0703080c0f1506042304020405090c03030a1d0a05010c 73
    0x9200041401014954440c000305c002032411301b20281d401504070046403154600d00b141d0342151a158003802080d850035007220116280c00440c50704488003241c0050315080b103400c0c482100c81040882c104031400d40d0b04000d23624816030070f0280101d402500c3d5039082d01d40342c5003030158600c800d40c0c500740450101e00b0104a800f945410810521104c0101043c506580c8c8d512285146c0003a000f04001c0d110100ca01c0031203041d18800c03082100e500719030300300792420183c00250701e8180c00b5070800c1043c120b9100c8209146540401c8822003145280d4030f02c2c2144800c0031018036800599030003800200040070020703800e81d000030140c0d0b0300b51425010f044403903e16075440d103c0783d000007030380d01b03160142d0004007415100070310a0032620041101411030707501d0803104000c2101d8001c00d43c114200c1c2c4c1500383d0310305189002801c5a21950540c4d0015158698010007841d100c0c80942c01ca074103200c0040e1486c020b070ba00c2115441004901e614100004034030700104148419103010b0b890018500b107070b5000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 173616151 1250 173614901 173614907
    0xb030c040b01020c030d1211070b0f04020406050918100e121b1507020106051504050d05100c0509120a0308060607080909011203080f100b0a1103030f040308180706 72
    0x507020581401160b803005902e00c0482d007081c00480070300d0082034070600e0100301d8010f24080c42e01e90070150000e00b81b40c081d0315501c0c444c0049005e412207024005044c0000d0171500d80c0c0e4040d5000d0200140300e8030340341c5401070260b0040d05080c0c900c810076000e80341c0302c54081141405400390407900000030b007101c00103207001c200320354018042c01e82001c0010451704d4290403061009144050928281c1000752030b0008000c0c1c2502e80c03686c8400d00030b54048205c10f1480c0b1b801415201901c03006c6480f100c10501d41c0c20040e00d05038001703a01072055450700c0000d203100d68000b0010450950162a070501351140d800b4001e496110a05025011070382c034000041c01850014018500c4604c103a0000e42450509030219014900980100040300c2c00c03840e00100b4543c1040e486a1301800c4110403030040d01d004034110b0b40758802481400404840031810b002198001c60990003103031161411203460b4078182030001030510080d5802d1700030400e10400301e0b4004c054501c20090385410309008280a40ca0f2246c11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 173617401 1250 173616151 173616161
    0x180c0501050903160e0915150103020904020d0c08150d080307080405030c010c050703140313060b0d02090a15081b06130e0f0108160f150315080708100b030c04 70
    0x90340c94013441d091141c04022824418014000020101450b480d2480c1c41c0381c0ba01c145010071144400c022820441881d50082d000c0096103400c2c44d000d40c5960101c004030300640a054414038140f400d041c0b558050710740c040d641510400a000407510041003c6081c010100f41d25403000d4072183c42000090042401807030400d401900c203900b180d15181080c503405007125190405400050000641e10b0149684549080d014920031203c441c910b0900100701c4262041241d00203103c01e4454510001580e40c90040c0d18101e81c0150002020345090f100d0300b002855980c4001c148182d0000000c00e0081001074900030f880343e03030358040d0000b0f5414001c20050340c000448001406206860110300c07001c9200c0d49034000c0103d180781c0c070b6095040c050440d080c2410305841c214444c210050800510040810384012221403240305241049284e000303c0244c03400440a0305810b011100015000318005001400ca925060545150102001e800401d40d4030311140f20764940e200b000a5101c5240030707801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 173618651 1250 173617401 173617417
    0xf1006080114060f04091a0402182e03060306060803030c03010e04050c0a030503070b0a1b03090606080d0f090504020304110f031018051603020d080c01020f0d02070501180c050105 79
    0x241e03401e10504c81c0c2030402c168000e820101106072615400c0c00d04484c407038103102c0203882c201e03010350404009100d21628a402c500b10b042c0305500d40c400c80400048044500031b0920850941c41c50700c5244280060054801880308480d81460100c0000c1d20300c50200689004000c0401c507140745074600800d00401c40d50103402500e0381d000d41560980c0c0b56660328040c0009500c14006507490f240b407410802903001000f04281811801e01070f280118451715080c80c9801da44c142030014400e0070904000005001035007000c04544500400e2804840d00010490a403801c20b9440c0840f094031103007032109a000a840050211902c480100000e180c2084a0200364001904554601000c00c43b05001d8401403021480425100c07034026060010510101055000406a0060891459011645803641c03108090403080001c50000c090010070340441e1840c1c0d04010b0300781c2c1c540c40b07410716a1000358072160080300c041d03182100b684100741e0000305c000022600001d0601d911803a000040d1040e074400f0f80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 173619901 1250 173618651 173618659
    0x1306030b0f04030207050a06030506090a0e070902160b01140a0f060509060c0f0a14010f1802060304020d050708030406120b10080703020702040504050c0306090307080a18050310050f1006080114 85
    0x17102041d95180d9080100050500c0e82c3c0c0400c9038244241800200c1002800c011804d41c24070800038403084e80050780804540c0c940c100107a607071700c03104040300707000d01c080100500003a0ba01c1d000290903450010a0031144000301c1e4044a402e030389528a081000880c032440d408504280008402d510700040542920744500c0140c40c800084240f00b142000c00701c99044583c0c0d05620070744140c0c0d62091003000c3c0c0c080d01803141003241001440c460b81c40c511142800a2007640e0000000d0215103d203e22100942e5001003100d51741030310b4200c0c1d180c894005002d0031000bc0d03001d84100642c055235025007510020040c0101c203400141120466441c040102448103140d000c000c0c03030340142c5031823150a03c6607000300041c2c000300f00200101820580d010303241d165554018001080815000011120402e0490800305c413030000d41d4901c1d900000792540701d1903140c000e1500d07030301d612221504220b224088440a490441e901c18a5080803401d0794060f407000502201c3c018003e400085807540d9001900078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 173621151 1250 173619901 173619913
    0x60e06030a0f0c1211070201120905030708030a05070206060901050f120102090d050c18070512070903020909010504020301110f040b09040f020c070f12020f04050a15141306030b0f040302 82
    0x41109043c2ca01070f1040e0000103001e58a0300120082520502e440920b00000c0c1c0c038580a4a50002003191000c0134203e032506564036588004c0100800446441039807080c02207880307107011100e14004010440310700340580180300000c0e640e840c0c80301000d4180c40c001002003081a041d43e007400b03414041c00002c0c608540d0300b040110b07803943d1503003003d80301c1034411401008584c02210521000440d14a9081c2200030128144681d15401400742c903407403980c1c10f441c1041c580d0f0307009040318940481e91010350800080d4044c0030580344190071807480f4900030340007846004600390780042c941c483d8490500c00c14201f441305015400c2408014004241c0092020504000f69121542242d0103d8180b81140c1c1c40f441080080351a04e00b4032000400c20004100807894003500400c05884180e942c3c14481c030381c1c3d0f000042202c0016442220001104180f0803104d40d115a081d04550550903103040c4500c0c042203140881d030380a030107468190303903209460703100d00c1c0c6490305045072000001e00b040341940204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 173622401 1250 173621151 173621171
    0xf050304021315090f050f0426030c0301140904030e0d030c021804140a050a1509060509010f060504050c07060917030702010b0a080f0a03050a050403171902030301060e06030a 77
    0x140240e18901d80558203203d92640340c910090304560321680e052401d6402c120410101c004030b41d103400d80c8070317411a4008000301403403000800313030303c48090414100c03000120034022000780b42d002540c103075240c19010065242104c81002403130300703080b01e0060010301c41001c6201c03641022100034018138843d041030812600240e0014108100c803441c41c044054000d000c100c00d10000306e240c44003d038100030140c01c01c0c00b00d81c0c0740c25403202040e0780050031858951401c020040c1c25503000c5151142c0114013040301d81452400240030700382004030b00200c641808004110380c0707002e200e0f1070b00808030035641e24030f446001d640701d40190200450503211350004d2009010494600c200a600c42d80c0207500014040082d14200080300c074007904000c119a2190b00c0c41052031200041030340d6043e40605007162581c0380c00340e04031511321490308010250303120f1f001030b64645007100c406482d5503880518007104059080303c00700d07030b20f000034481c640000d01e42140d4030980741007000007160021003201c0b0104003c0380c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 173623651 1250 173622401 173622439
    0xc02100e03070e0c13050d030806011805030a0606090b01050a0507020f06040b030906060405010b040e04150b2806030212240406080a0c0b0a140c011805060103030e0301020306010f05030402 83
    0x100c0741d002e28000006104020341d0403080400c00500011a0300400101076508e00800e2000002c02045c14001d00d130308110042840b4240d134034001c2400400f100c409000c545008000b42c22140b05d030140c05824054546000c2d800355050f100c04040e6999602d0070404140c00300300c81c41c44160390541d04210f0411010459002e103030000c5200300307001401000c41e420408284411560140d021074860300081c4420301001003070403400ca8200f80c0040c22000047d40b01040c0c600245101c031041584012101c000e6500107407582c91800780404108107400000759210019001c0e0701c0740100359038040d0200760004000d014801180c03d040c1c0500340c401000c041c03d46000c40c2c1101c00383d0700000382c180c0c0440028820080001e04c00c8d8080c181d20313070b6002d06042070004080e0054200c12468506e1840c04101301e8850b44003544180c0c900c81c1c81407103140c402c106504066496a00a00082d40040c010382540c407a64181402122300030b07003040c0c2d544600504503160071509600701070800c80e441058410f025041ca50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 173624901 1250 173623651 173623679
    0xf0409061107141c0e0111010605090a09140303090c1e04050c07050c0d0b011401110102040605040807060201090c14060d0c050a02010c031a011124010302100c02100e0307 75
    0x8440e50f00e0319044045100481d00c1e00100d610030071140d400311100f188055a000580c070407072000a0904034100785c00d8440d03c5014000e039410181e003004c41c46081040780d0740c05810a1804501070308140040005c261003590300c070f120071200380206a0040e500381303516080031000a030039905d100300c0008060049400241c1612402d507051440804081114001d0120070310100300303400c8086032101e50a80c1d10b9174868941070414859007481801c0c003000145070380d0042046c0c52040900100840d0b03a1620740350b000d840c0350010300495040e407050b8500803070758a00500c0b58041280c0c00c8011034448500e00113134402420305500201e9084030050140341650700e028001d040301c10441f0b0316032035160100084000d0842c0c140084c1c0f4400c06003003001400480c1c0c01007201d079100b944c080c80d00c051143c07201481103180074881c5104c1840d80443c0c414814100e60004440e0741a83d00c21103d0b10820050315000f12121030010710f000e94459181860581014040d00d1400e1785c100700501555807140e039446924490718 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 173626151 1250 173624901 173624903
    0xb010e09030d0e0c0108060d240204050d0b041b0308042303030c0a0b0a060e04020d08090612040c0501050f03062b1b08060c0a0513050907020a03030e010b0f0409061107 74
    0x71303128013407200c4250b801407105580700b601504c401d02d55622548030300d203107800d19071180941a180110000300f110581d404503800340130090712501e0f18900a1900e03800c0c900c8103c40036107003071102e51141c5803051000350004049a030403440441c2420308000010300e112a04004000c0301c44548400075055850a0016003040248200502030880080c04c16081200c00188007075504e0b85001414880465603110300c0b50071170340585407506a4500b51410a1641c803800c07141646c001300103c0c5a00001c0c25400d207140c4224480d0181c1c2c0d0246648a0064905008038a0607110940c0c06200080041c20095000250018003408242d0750f50a001d18404d40001c0503141642c006180c9110038407078500c0c0c21612001040c07101c000341081c1c60000d0f00411107006541a1004126001850580f0001990060000b0f800c008041407002d082258001e5919810804101d0201c0d040800d4090856410310441c40ca40c40c01805030001d895442c0c04100041150342c0e801c1b6241d079910782b200501c200c2d080303024041c1f02d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 173627401 1250 173626151 173626153
    0x41407051c030e01180905130b010b030106090909031d0307032301050c07020a0e0c2b0e01050103020f0607031e0e13051b1614010f180b010e09030d0e 66
    0xc0d0701d420002d0100d41c1191910b4140100901d00e000700c0ea5641c680c0b88112001c0640c0020755031284001e00200c0300045c6401307004820400f0000c038014240100960403114103489100c440350b03032080644207640c1d80700c0024020501d001080380380d0428103040750071001c0e0000c00ba41e4080c7d80b6680c036101400c03450203042d03208900403590022001804d01c24250455100b1404c00e0a10019a00007084030b0701c98010981200c00d82d00100740c440c030071102900c064a0303c00420350f5a0307217061044a40441c9180c0b600c80c10150a0184617015004184a003505070f0350041c040507011181481403004d1079200f81e00440c10000032944601100322003a0421043c1141e9644024820700404100a850010781c02107510342803400c003d00c0703107811003c051446000f1140780e03c03903111003c03140b82ca140018000c1d0058244c0807002840048070704194400f12072611114803c00818400910340b0841a000100084c800710a90380140309500c59441880d034050f52810842e40f07080f80e0000201e050b10b2518440007ca = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 173628651 1250 173627401 173627449
    0x207140f010f0605091021050a0f03080f06030c0609120a0c0614130509070c050d030b090a06061b050f121c0203071b0305090d030905040509120304140705 68
    0xa0b000301402001e005180c00c4900b0052818807002905450016110303d030503120741c9184000c1036001c40f048000c0c40d25000010744400c80e060b8100650f0072031a05601b00d00083c20f0710001146441c458000d54010000a00141107034001a010f01c84d0b507a0104003100e5002807012000809003000300196000c451294206d241000c1c80c1c00c4010b8a204411078980c541020148948012034056050800c12504115140415a00d485605641d41c951000c40030701103000c0c4d401500309090f00350b00306140714003080e54200e01d20f54034400b5990448040c5e00815000500e80650150b55003940301c207008049005205640100b94002c080a2900d0404001101c0c0d0440110385005240c1c1e02103c02e040d20313008031034294a94a00810002d1201c000d000d02e081b4400d00780c0d48508141442903003500c000d001d001e400341902950307e04003c0e000c030406d4880c6521075824400062605840450002d4010411448080c00d61720382e030361034402502d155020101c29114041d40050a90303900032020110701c0d100e45120744 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 173629901 1250 173628651 173628671
    0x30f2a0527040c140a080709050402030903121501020a0b1e1e0901200a0c05010608031806070305090114190309050c030601030c0515090a0f0828060207140f01 70
    0xa995100410354140031302c2d0301030858803214000131540c0001e45460035011540d614070382583c0c002ca4640200e0b82241c80070013040810b8030000014180d000c207250094940390b4449004201422590a1460050700605e050400284210b18900d41000007266544a00d103200022421342c2081110301428080400d214442c0101013400300d5034114074070704024046002d200380d185d59459521000c1c041c4d0b8407000540c40c101d182c4030344606002c803075000009206d0681e80b4611651359802a0b000b0302c4087c1301c50001800c1626000d800c85044542c5a02c50a0901c4080d50043d00d41d02443c0000050801040094a601c8403590b1040003036a00315071400501f11007213003800751401c0c00441c0313250300a074400c170018004603804132904400c6440c11944d1b03000350042200c0e03003001d5002c5e1403041034200d048540c02007442c0483c5000072080da0010700813541072441c0042c0d516210395010071811500e51460100902080b0503400401e0000e01800011009140e22040b451405800b011800121f942d9000054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 173631151 1250 173629901 173629909
    0x616060504200604030b040203031209010c090f0305060105090601020a0b0c03040b13170904060e0f250906030218030d1731061107060c030f2a0527 65
    0x41c010484002e01c12207000d0b040340441e142c3d1041d4040074045130703441c200040840d45c00700300302d401c64500c0955040560401981440c080d091526620010070165074010466507000d213061011241c10100805080c0d28205c10700400c42c40c00740001e8110b00900c3c1c111000f0500701c04500f0b008144000d4201e6880c03070a03041100d80f502024144c0d1101003071300c0c0110701c00300e0005000d40e4594483c80259956078103003000001d00500e4980e01c1004111042c030200940d10784082185489550b214034200b034030408015500110803040c040c900b01040c51000c050148034401e80c05045a80800615850500201d03800a45000d04240341c03070300090710341400402e06039035051070310350400c00da41c11210f05010b400c20312a1018002c1ca401001040c0062104c070305215840d0040c60441c100e1131451a55035402c0c0c1081805005429502d0010900b42010003403e810070380700d00200401c14080710f1001c08403183c05035119070811060903080040034060454040c203913040c454040e00954480c000c1480c502c000348 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 173632401 1250 173631151 173631173
    0x120e0d0c180b06030f0a0e07080a0203060604200a03020d060e190e07030201030f0b04021b06060f0a0b03040510060f030c0b040b030c0a120c090305150907060e0616060504 75
    0x3400c11420020702d00c4183c0c03100010303079420054041c8000c1031035460003802c50080801c04800d4500307200315900052080c5000c90000e03006070007070342542c1d03403541c602041c8401c0d200044140e500340c1e141886200441d00d407602c040e024484c1075240c094940405414110b041e5040364102014405001c01400024940060400140030000d83c0505c0507030008401c50303482d8551480060305150301e0311103480d2007400550010409d0a0003c0085488000d01312442044004104000d50640702d10740c04100140740100c0e204d442120700500030506142414511649904041e00858082c0b00380c50341220b48508602400c4050407040400801c802e1460400c02000b0b001948884c0d8a4481000284000d440210403640d104145910417542c2d03903030240e4101c8078140580441030659241051800315a58048400c80c101c0f40104212540e8042013121011400c6090301c4201541d03000301d004001c890301038426888840002001036007000049031420301c035440503201c211a00c44d500e9041000704001c80c041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 173633651 1250 173632401 173632439
    0x11b0803070e03150c0904021804090b0615040807150c06050103032705060d020f04030c030605010510030b010c060f0603051504170a0e0420070b0601020d020c030a120e0d0c 76
    0x1031100e5040c200070305e0b00380d4400c4214240c05260000383c1d01e21001d06a403c46441c000b0040c1080140c0ca540d824a0300c3e00701c0c0180c400500c10380707050340c6000249003400141d4095038000c40151202c0ea1401c5c04003009403105403050014042d2101c400700c0401c2040c031499000794040e8450110110003c00904501c0e49146012001070317401e44000d208a8680c10266030025821050060352500e22000b88421802981d000074203000d13080170301000300305075904403d040380c4054884131800c845411055042d0741c074210a190000755081520004201c141e00002c94150002c90001080c1e6140d455140c2420345241030105022001801c2c80100105802100e045095031074041d810700e005442e005003000385094010780310342d4888210780b40f021102840312007804c14074480140d840401e8540100f01c4075048501c0740c050300401c10344405180c000700b00c8400349000103000e401080c41d182ea81e48500054041e082040110130014100542c071020000c0d25558051042076915520744803003243c181c0c0c00e140d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 173634901 1250 173633651 173633683
    0x60907020102070302061611100e0d0503061003110f1b071e27060303031b1b1e02040203090a110a0308030103060c0e061c050a1109011b0803070e03 65
    0x81243e002c664007180d00b603005500c090803000c0c504540c680440341050240d12201b41400703506a0031510114690043c1c011252a6042d2610f03103036401800e599034041180d146070816102880091014860340c48440103081520304142082d18060356900c0b290003881d1408900d1039108804111680100401e000600590000502030345044004142d03000041c40390700c0c2007600501700308030681e0160322a418450440c0c0001c0084c5a66410010007601c81980d10300e07a80220414801001441036084c81c55481059501c0c81d0840c1c45580e61307140c400c60380c4281004124080d6048030040e90350f800250301a9000c08010646c450080c1010410fa040c080001e600c0380c040c210040000a04d4401a641141d401080028040c52203103800c1d07811042c5c1d502120b034800c00001e0240c150700009120402c400c0b015410420040c3c0e24084460111104070790342069982051200182a61048610b41c0500e20741042d03103100035016a64106094000f69034001c0070a400c00d0f00818142810807450140704070080d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 173636151 1250 173634901 173634907
    0x160303120b0f130b151210050a180603050d17070e010c060b01021c121a0303090f0102120726070f020126010306060618030b010506090d0501020d05060907020102 71
    0x5002030b00c0c003104024240d019034190b910a607642c43c56940718405501c80074060b007100034060304980042d50301c18a0b0200040d51440041030081c50111100c01c00d42e48060803d013246810a030ad86a02d50a045000b044019103a80c40480094802c2c04070b915009425140c920b0000180d4074401d0030840010519000c106940c1c4e240c902c681c1c0c2c406007008080f500140005401c00c05000100d080c155040d8001d00340208000c5d404c3c4040741e10007191002d4605a5400300090400c20050702c40005a035680503078560320a000009c020701e019600c03140c0c0031005004032282c0c00d40709040700400b50048041584c940740410600d000752000d16080d04e0049100400440c54055903641e9034620314100300b0013a040000312201101030365800c150b2520340100c40c056680c078542c1c5d00c1c50003002400035402540d00040c40030103034440c1c4060aa001500392540402c040d61541c1c2000c05002e500e401c01140740e940f02074040400300200f00c2c00e02c005c0c00c0700022010040750611780b00c030038000301c500007400b80003c581c410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 173637401 1250 173636151 173636171
    0xa060602031602010e0a05030607020f0d0e031002030c1306022a091b04050d0804031103070305030d022203060b04201602041409070608010510050301060c02011116030312 75
    0x140d01d04a00e20b5090070002ea10720145ca010888049441e00107e406100c0c003004e0211040d0002041402c00100408440132200143d0301203c040350100d002c203405901c02009004400750079000756500c421803005140c140300961902004903da5a440000540c1107600641195491070000171400b00644c0c03401e030b00303440054021800807000242611109410f00f1101c540e0402000107d030010303c0001d203c003080d500715080c8000340e039010740303c01c9a89a401c5440c0080c40d04010840c8411207030008095410040c0b0b03005030a02035031162601c40c640711018540d202c000c1001d81c6403c80954091600058554042e80602048558040b40c0700d107640c251517002c00c0403515000c12213001c0c9284503a09070540f042d1303201140c0608526191110302c0d5190310304200e40310070b0000d04a400c4030060368a039030150742c0e03d4013400b2091100801080c0000c40c10401481030700d0080700090003140c410314141407003511070a0061300301003001a200740122403c80d410818541d02c1040e8818520640340c040150b9010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 173638651 1250 173637401 173637427
    0x10e060d020a0504060f0e01050301091a0907050a120302010f0506030309040f0b15030f010b0c0309040c110604080301080f070b090103112106180402030606240c01050a06060203 78
    0x411191140a080c0e01003011501c500081e907000308405813052140d1900c0300c0380118800224054140140042000040c1c00c0c0ba05002c1c14034101c2e000070001e8100154030b8034800c040f2400800c01c000611413010000782d552506c1c0c52220080508402403c0d03500c2d45882e0003820b5550802801d00c0702070801c1d05100f10b9940c04000c80c1c00c0700904540015140c9209846400517100703826007594080c0500076440c542c11030503402144941c504070701640007a03072243c1d003581e130b01e014114040305070303500600030b9140c40d0420750b012030b01c1c51002e400c0103800b111062110b285440030845003225111404030040103ca5410000303001078810000c0600031407410405248040d0044c44919070405840360b0740440003a03166030441e07075101e60300e10182c00c2c0300d1101e500e51140311406544032401650030380c004030035038105207841c14042c0360300901a148540701c000400108406044c002202110450821400040c0e004001c1850000f03000000c90f640c500074044004440c0281e00810035508100000c2d50380c07000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 173639901 1250 173638651 173638679
    0xa050603060f090c03010213030c050306100306021810180503070506030a020d0608030d05060f090f13110a06170c070c060309050c090405010207060b030f12030a09051f0f0501 77
    0x100d4606402d02c0d0b0b5507218482842c0410b0f8400c495015480000d440d121486500e06c1e01094070b000f0b030152400c013641c40d028190703100c00440b0102410740c0a40f40c10300000e4076507001898414180410340c0058035082000130030031406601000c02040d002051010844003000d81e5100410048000c2c0c18031914080202d4139511000f41088641a4005000504950181c1c0308401a02000017180e40310000203a00200034082980d255108120402d000010b40c600341004c5403144440c80512072864550381442d10000408080c1298180b00f040e600590507202c1c04c00040041606039034070104920000390b04030030f071800a0041d00d00c0c0c001c100060000f10300e412410204132616854009400981801c0c01802c0460800700700380e008221006100034010150080c2035200e02401081001228400805960b240540c01110240d009007100000060201e0003966010000c2040070582000c00c0d030300d40e4240843d000c5955075040310580b60524486040c0300b21544004012002c00865050078900d625840d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 173641151 1250 173639901 173639911
    0x27060316030509011103040c0911040501090512010609110d061a1e0705011104090b040b1003090c09020307050c060705070f0b040639020a0c03060213030c1d0a05060306 74
    0x151940040748100109511111384170b1840004141c490401303140584018406220340300c4000e081886000002c1683d0b0226012908141c485034482840c00c400d000030b41e0701c0b4541443e1555692800018484402c4c0a4042c0e00070341100203541c0c8002d44500002100c1c6c840d000100101c14800b0800f188405c56000c40f0044401c071001c0e50858180c0400d60050b6208000c80140076500f000300c1e054142d038094010f4000c0e160001014040c452400b014807085802240c03066900c00701c03c540d40b8511500951203107803142e01801152007055103c3c9800c80c1030342c0c410b56086000500010740500c06680074030049402005516025140821580f1042803403010745001416803282c440201d401c10480b503101079410a0508801c014501c4000d00d128143e010035264101520100400300000c030f0300c0468244d80c1d995010880020490440d200c0c2c000a4201e003221416682404401001145184d600e4100074520080690140760350001d170612084130281c02145158102000d02c0010fa801064032940f00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 173642401 1250 173641151 173641157
    0x1e020a020d0206090312070507030308011212030b040207050102120105010f0c0510020a110a05060702060a0e060f0a020708040905040c1d0601120213030503210709030f02040f0227060316 82
    0x4c3c410703542c0040d043c600e003884001c4802200103000c40401c1400704a5608980c041c7c2c40d6444643ea95030007640d00c0f980100001403d0111400e03403041014080e5001c880a00006040181445200c0e0b1310142264000001c62402c42c1c0e00308010000c540e401482d501c020301030751030861312142296035a69521010310b80e200c80b08503000305140c1c812510410f580183c01002e14120b80c109181ca052160b200c030b0081d10340303d00501420000403442a10350103070184034811540102072a031703100950710030015805442154800d408001c000086040e190280c40a4401c81c01e000415041c540352015542080c0d130b00c020170321154014828202031055002541c490740a0905d00004c0750b003034940c0ea0007440785040d401383d4845034a05c080305011002000d03042c40b0103216403002c1402000b035018101c8600480b01030300000c58811013400083d10521248040ad440a0b02c04500907102c0d1842100740d0f0000500c00031800034090401c0c1c81400242030f20300300c600c001c0d100340b8914205103002d00d0701d180444002100b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 173643651 1250 173642401 173642407
    0x40c02031603022404060e0c0d02040b0a080115061b0804030807020f030601060f0224130602070b0f04151401050f030709090803060901080c01170403050d0603031e020a020d0206 78
    0x50500901a40010714401011315150800100c20084402d4003650706a404a24000c9401c0325110001031a14103030400420840e140c0407150b08010240001d10b40082e0002c0107120f0004015400f40600003013521829180501c640c02c0c02c4004181c0800d40141d51210100100d00901140b1020210f50641e500801100d91750300450012400f988402441c03990944212800041c1c00e03070780030140500c500d0590b4203a541107101d81e40b29141c520404c81d800708144841002040313024401da1440d444040c8680000342c101040e98a038000c01507411604c1d0000210707040100001c120802c5003501080002910800c1840a1701076514000c0f501405043d009050b0300b2038200c0c0b20350301040110000c211610050021a42616040405400954205000f804c0f48000414101c42c049203d144100d41a03450410110034200c2000c07050001500030380910404011801d9240a075000300800355002c0d403a9044080d5015107441800c8520390081c00454009051040040e995041030154050b0100c0795651 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 173644901 1250 173643651 173643653
    0xa0201080f09160e150109050303030f070219050718022b060302062215020a020d080d0e0c0a0b0a0207090c05161a0c0301060206070f02071802030114040c020316 71
    0xc6070000041c012418200c44160000d000f0070030607011031260010921101105c080d03040150381003011070180300e40c160010b00015042c9003c40041c1503102d0700ca4411115040a09011200009485102951039410911080c000d00400284d0044040124002180741c40d00d03103070340441441c500350b101700c02c0c02820701d0300304c86090010f4007c1409950020f0a80d84da130386202a000098000d9109241c04140040400241c1e0ba046c450741c01d1511021030700078050341751b4141c0c00c000c40a09204003c030740208041c40313480e0110055118010001c44014014100c200701242000440d0205130300039001c2401c2001803200b52a03000c40d000301240c0303005001040c00c1e07030580d9064031140508a0400c154004810b140070a001d8000b4403802805000c9410060075240c4402c40e00e01c91100b4014240540c0c400004240114031810245051079050f03c1501d03001030f02d40640401007a45915001d400b00e80100061003030082c5080741d00003803803048a041002403001c01c3c01a48038041c0258516820400305a100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 173646151 1250 173644901 173644903
    0xc1b0f110a060306210b01060804061b05090108060901140f0d17030a0b181f050901080d020c10090608090316030302040801050907260114090c030d020a0201080f09 72
    0x1030141600622050189442e090010000e25082c800d451316031190340160b0f003d03c000e0b4800a108560805510783d090703802c00c00b080d00c3e80c04002c1c100f1075100c4d9803410504404010911140c82d02459903a13065512403415000500782000035003814820003d0345e0041144c4040421500401d03081550301c1c0a4880ca402c0000c0d0070807894050103002c200a200314262b103225a10010b51044900032400c120b0000140300f0b00001580c2c10a040da0146c182d40301203414003170000c01501000b01c1d80302e460182c143d118408200484000e912440b41e0380d21115200c0c041c0c2c1c1d014448900600710580341070840c1c0d000e040000740b14450340c3c4140024401c1c1c5002190304801c080c01241c601c00c400410800105280785002070080d03120b8400c0725215482c15000c5444124080340202c111001601c2c00d42c143c20202210686400b1041c11a03070b40d641d03880c0414001c1012005646100b234200300068000c411498041c0b40c00d210240c1c003e80304541010200000503070700180c6090304088101c100030790b107584030281e00f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 173647401 1250 173646151 173646173
    0xc170c090108032d04140a060c11042c031e030405030307081e10060306060e130c230c0c010203040b0d0f241502030a120213030807080403060c1b0f 65
    0xb8161340050040f03007111450020344c400d00019100c401000783c0e00daa0072200045691002070802031034581c00085440d05421000c2e0340c1c1c218050000e070b100054642c4103498402d100301c0c0161900082401c81e405104002d0fa080440400c050007490b629166031056100c0c0f000800513420711400c980030500091504161043c08034402c0140c00d40d90030040a920405c10581c403420001a081c2880401c0d0940300f48001070110102400f440d820fa46540c80917005484402d040038208404030b18071030001c108100601c0d07548100030301d01640d00e1310910a06428000301000c0c8038150740c81008100122040c040458840005401e00044c901c92810389503405001c0c620411030303110946c0d2452107503607610201032500729514220002d0800c11107040580c0c0b6402081e11060104161842c1801c0c1104c86800906000c4090f80000c1c45842d241c1e0794030090b035045000300b591344a4000c80d060042240c280706114441d030240c102520503c0200113612002001300100420000362011541c0404c0540415 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 173648651 1250 173647401 173647477
    0x9060a0311070605042904020d060f0f0509070504020a0801061101060f03030206070207140a050904060609240905060d08090a03021302070201170906071b0c170c09010803 75
    0x40782d039041d05007401409040f040d01d0556203074007112031004100f8106c0041440ca00303a50801c25419036203980820410076000362040d150191286804548440180705082c01c11010800015090521318031061404855405c524015807041040003011500301090300e04448141c9000d02010010746d6015004d0030a650143c0c03440a54418003004058020a000d4441c007002c1e400c452000382d846040c0011944091507503604098045014052420318111160740180550004603100303a8a2800404541c030414010301c0400803848040010891411020010180b0301d030b043c0481d050040000d49550b000c80c000920500c0700140002841d140c002810f0000c680040c80405c0b40317180480b02c0006984181c030124009407004204214004000c0e03149402454500000c164070340d1000b800382c40d44032003c0c0c0101011848410440300140c0b00d030b01c068002d0309139081815035031000c0310220352034145168803681c4204010130061012031000000d0350611150143c1440c1070b00c00c0d040c041c008050003592 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 173649901 1250 173648651 173648681
    0x703020603161805130207020402130b0301030c0806070e0d030e040c32160c031209030c170c190e040528110108041703070305090d050f09060a03 64
    0x108000102d21510038041c01804961a10b2071010b250081c015101040c500582d6400048603e40c2c0d50000d00660140140507c00b4000614022000d030150502510540c0580720002c0008014000c1244840407580104982c400a08071400c1582016004d4840f1908940c01a4100249403050602c9850521810b243c007410400100b0950000140441d03140e46c80703205000c456a43c041021108030b0344000c20030a4042e441030401c024540d4001c0f0314030b4901d200b621624540707000800070507250300c2e410400802545610812924526200c136080c180b40d48000c0c0700d4140003700b0603072014003040c2000034040486043c0d98041070070b510000c802c216500442240340d403003010001003110009800d4207031076075100c1c4445403482c4016406401e001d40c0344014500c21110201c40910f50141c1b4083c0d811901c10102500c201d541400188001d410468903c4006529502401280c02040c004040992031601e081031405120011030225840349400307850249100060441e005846503004032040500d0344 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 173651151 1250 173649901 173649907
    0x1506010507210207031709030a060509030705060a0504030305011d060d0312060b18031f0c140c03090f120706050903070302030304150f090f0e06031203010603140108210c07030206 79
    0x42c0c000b56034500b240421a000d01100080080400d4503c00341c449142e0000c000b410401525900c0030b0140c0340203040500c0500c001e0141c6000140c0070b2001500c5500d1004000036a031401e070600400b0f854041e40308983c840e004020860701101080480c03070380402c003520202e0004095207001c5601140c0d22900700c01d201c0c900400411401003090050406401d031210409001036414101906c8840000c200b007550101451103404500d9a60003c0d0352007000350402200d0035040d03d41c454030310341c48402001c2c0d060f02700007001243d034904007245100d10700d019201407200134004550f05684480f103015403030510030702043c0c61006075001c001560145038080c5c1580e407540d603180f010031326102240c000480420200e490b06000d0324407030080e103000ca5a8020400540503c0c040300c3c0180600003030410340d010f00483c0c000c000ca001d1001300440c0241203a0346c0005544911001c883d00e0114182c202c1000e607000402e07801c41d81c031022441c181c8ca10140203115640c44103070190103482c00c4000e07800250042804 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 173652401 1250 173651151 173651213
    0x90307031709042304030f02010204030c06200c0f040f090c080708100203060307050609031501030b0a0e0303090706080709090e16051c2406080615031506010507 71
    0x290041c00018909a4013802403007283c461208240040882403002c2d980c4060002d00031a03c03905d003084800f00d003030000514094403a2103808144810b85c1088001c00c60800303031510106004200481d40040500207828081540f43c0011149a6021800780c403c9464950b0400b0b42d203042c0d4002c0c9645503102d40c0000000340d54400154070380b4250f100308251405440300d000d584075401e0085a101e07420040207040e000703041104100141e001320164540600c22a1203090032200b0421702c180c0070314016466104c092401e2400c0505403040403403481c802c0e030418000e00c5a10340f000038248007a54054140b41d1820380e1984c50468401420341e2050b007545080031a130744d48098011032010440401500001c000f6500d4800f030011450032080b05020b001000c42414003c0b1321030140701c5004a044a00c40d0908411984006040e01c8180d08920415000381c005c0c4206580700c2c00400071034540640162925410300785800da48241c00604007418000700140c00d00c10003101d29650441c44224003004a80c00d001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 173653651 1250 173652401 173652443
    0x2090a0503030316080106020a08070b10050d032d051b01110f030f0705041203030507050d09050709051b0711041e140c0f091c0606082a01080a0209030703 68
    0x1a43d5541300c04035014000108086101159000740d07190010429490840b20303685181c115040208071410b401d00c1b0100100d0f8655401042003501d50180d034642802150210401f007170880100040200c805520003018000da40000c140d50f80500c00101010050850800143c05025104010585208001100c0c0a810080000f950042585039440c0001d5507503c0c1060300d040c03189016050340c4202c80d480800c0000e20a801c4144d01c0741c410314100382004084045001603404031441282c194120031420310104e009407103078960000d0034110025110035403a402c2d040501c95201c0c090942040900c400001d515181c102d1124282c041c07290f4001e80307107038031404c400801c0c142d107681c140e1110380c4d80894060740da250207480c0c1a5109060315071600f00d90a08101c14000844904424082144014808560f0038841c43c0300502d006070281148840da09084a1143e403c400075031910b5460300c08008440c0d0740b118031310b60300124800340180c1d5441000002441c0c000035910080100b0024040e0082c1c0144c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 173654901 1250 173653651 173653681
    0x51e0301060b0c010c09062c1c15021602060703021207110918071202030a050102040f0602120a0c06050606070b0907060e0a0e06060a05040b040b1306020f1002090a05030303 76
    0x1c0300f0340080004601030070302251a0803085c8a800009140c41121180100e100003040081018a0100301032654804020503040394801d440601103280c1c40d2240818000081d0b841006404500801c524000405c0c4204044401070803002c0d0003140c010881104260082014074942641c50090b151641520314002500d04d801000950107485980d003c1500503451508504800c501c1c580540f049600b01401c108112034507031401d80e03241c400e801d445e8010881c02e200900c050079203580500340321810f18070061f290074540039000c21512000c0000e98046980018400d070300e07990240000c50292500c1000071134078003802a01810322000307a021b000c2d4103400040d854080b20b8043d00d450000e4102c4130100440c2c003050384203d408846001c0c0c0043c032280340c114010b10b10b00d10b40d800c00301c4c00c082d21a41d0310b48068001d9003003922401000180c01c00c1c140201845540205003500c000c084071035850781c2450300c60000341d4601c0c0c031060300442c1d4228596684c801000140401030101e80e01ca1818000803c4610 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 173656151 1250 173654901 173654917
    0x2070e01180c0c02181b12090c0303120a0b0a08010f0c02060a0e10200315030c0604080c010c020a05030307030503180a0506161b12080702070609051e0301060b 70
    0x50b02d4050355115007801100a044290b40003000c00e000c01040c9901034204d810000c203004032008401028004004880024104109030a200c007190385c41c080c03d002d8548105104410310a40c4240700016201c103120b29400d503c586082f00101e10b991400d004110f00c283d450300044699420401c2030010300c9099071158240005542c2110003030303210008804120741210070181d03195080008030030f40c24071060308603040803403c101849410310b040d11030455140d0010364074103000300f0001e030350100c441c40c04210203802c1e82d60407030391a4580b602c0d00e0030482d91403940d20601342c180500f1105403800e640e946810304000b000c006c1d081e00d544034401d16009040307600488000041c500800000e00d425032000074208001e07a84240100180c0c0c40705040d1440c807940450054003000700c40c03c02c3d450310309510702ea0101c0c9207100f10f40e0090000d42c582c82c09400075038005c0042c8215806510104441d607481001d40c4121034040c0d0362000c1c90701d0311380090503090748810b81c8203030551300b0080000303010020030700246110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 173657401 1250 173656151 173656199
    0x607060c020c10020d080402180f10080102091807090b1b060c0703050901050310050604060309050c0d052d150402030f0102090a0b09210c0f01030e06010603020a02070e01 75
    0x1403461410459100e10030003c01005a1144000d00d607010300030f41900750020300007010000b030350f0010b83c03046600c0d100490380180101010003d00c01c14011400702840038041d00d80003941001c0d4184003048081e4448a4004540b00c0c404020540003801084204050030a00040030340d01c94124054560580c032040b84002d0f40d01c11440058159482d800c241c4484e598581c0d40e40b446c0c40350035001144d55400141000d0356442c501ca10005841d55804000c10081c4460303207010440f906513060180c20000b0201038180501566409980040c2011400c0980700d11280b0380c500490580803a4100c020051013007a5446115031f03407600d603541c0340003550b01344110310880803294886eaa12481034240d004102860350400c40941080c040d0301000b901800035808040e015240702c80520f02c2d8421500e01311682900310390000c2c450903605060100b41004e0340d00003802c0901c04612400b87e203655420051081e1402c060380806d0110142d842800301c01c3c02848024490300c01540c4884140d1800040d20442c0000c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 173658651 1250 173657401 173657413
    0x160b160201210e0d081b0a1103040e060a06180501030203090309060310080c030307050c09040f02190303030f020a09121a0708090607031109040903030b0616050c03070b0a0f020c0607060c02 83
    0x181174460155544601c461078041180700c035484812070260380000040e881031120501040b00764007020400f4000600c136081510f5081d040803030501000c030b650751300602e081015000749040d00c51300070401041215428a00103030303655a03500c0e074030f82103010340340c4407590042000082c0050031301508d07a02c03800c4d01d002200341d4059511800806543c3d201d142c00c020f166800071020004145880001554814010070144910803000d9001800c110b40000d00e0061007904c031a018428140e05124402c030707102418504518280c407540c00907000341900d11070b90500315601c0340d8031010040004513400c00c8003000f58001501c0d003002c01e0041d0810000325038082d4603101e20800620010300c64000c03594241c1340c0740541460322030303030109200107030000070820342c145500c41004030704a8403801c9c02418804880060b20b28212400e150440c2044454003100e0b00c203078452141840030070301c3d007421182c101160341002200c03030110800c20b03400d040100c00002e81c81540841e07040d05008007a0001e0000310840e0b425511 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 173659901 1250 173658651 173658673
    0x609060e0a020c0d0e18190b0103060506220306020307090314191b08070906050a0e071403041506120204050f07140a091205030c160b160201210e 64
    0xc9009502d140300ca07a6000d0300300080001d014114881034403001820144011006480d548003191b03054807a40c000c0c1200c485a48044400d5220f00210030009103030a01c051464080021121b01814080c044003090583c90b07140100c4440d603580c4003c40d88940c0664907450b0240e405450411244002c0d00c588407444000300340c0460105003084243c00f0040c407200a80900d46844c0c601040c1c00c010348100c8030a035680070904d624200b083c0d500815a034000072400a0505003404403804140c1d005107100d901c1c00c014007911540029071032100c48481c034201503c0355140e00701600d824202c8030403141041c1c94000003041d00303030b43e10010001060080e50309104a4869445540e035071501255440c0000717a0400306c20032114a001d00034a030591180ca0300c0809161950442c4002c0d80f010700007110b95600000b02085006018084020207d20f81c154140f0352902e4035800c40c1181c401c41c21660007a003840c199520840e0b000d10132000550b210074604d04284c3e01a01700d41c0300200000e01c2c18a0300d500c41c0d03c5002e1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 173661151 1250 173659901 173659921
    0x150207030b070503131103010b0901091b030608030a03020f04030807060f0501080303100306020a090306050c0a02010606050315011808010c1d0d02150901031103040312051006170709090609060e 85
    0xa4019605550941403140e519112003500c40c9000106c280d0554903031032445610783c4d400c2041ca0103400d204000086498092624010300c0c06242070407001d040c200f14003000307003140c0802030300c00040d800e003000742c2e80c0c85440c61940103d00c40c1e83c00c01807296001052034024065140d00c900b10a00c80c004042145903298004180d0b0390100300d42c0c284076480d1031801440081c01d5030b0058503401c6514100090f0036500c0c2d607540d5040d11400c444a40f0030a001240000b165a07090150302c1c002c08240c14000d1030360078520000f5a4056084200d07030306101001c50103054411090a40c98010941c03003000304101030300c6030390050442041e0340d0960034020041c01241c40c5480c0c079042040304141d00504071007501030007003003100b03060b001004014141540c1e0401c4944001c40d403c010b61003a8444d60b20000100e41c0300782401d01700c841c00303000703400c041c0741c1b003041401007a030001c0c0d0301940c40191408400550b520000100d0301c460103600603480301e5041220024082c1800d400c140180c40703810f40d04403030f5661038039480 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 173662401 1250 173661151 173661157
    0x3030305100f080c0d021504030303200a0c0b0c0d020d09120203040605120a0608030307080405100615050c010b13140610051b010b1915020601060225150207030b0705 73
    0x851500d400501d807203026171412840218034684041c204482a8010250482e46900a6881a80420386500614902d03e00058503402c0d00324004016a080076400302004004070b00340c1400400443c0c440c00498110301201064170908110301c80195502c0c24807040c01c0014010a400c02c41e11042c8140e0b1017440380780007009440030740e002956079a0420b04114100701da049009480d900e581982c56001080c0c040303040c07000f9442103210383c9950070f6600f414601940b500e5040491980800c0c0340401c00d1110511a00c588505241d43d454a542c03100ca501c1c013990300411640c81003580c404032001c03090040781250f800518141e02d43e00808605a0b5540f4148003481001d280d640780025800c20001d114031070302c81382401420030340c20000124600b901000c00c600b201c070200841074200180e0010000703240e180d032220380c042a8034409409154540b1310041c3d0350301030316090010b01d0342600b9050900000d0981d9944d0050880c4035001425403488040030b515000c13035020544020b550000060302040c064812 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 173663651 1250 173662401 173662409
    0xc031106040b0a020913060618170d0c0302030c0d020708010c0e06030103031803120801090515090c161a010f08071503050c1c1b030c080402090402030703020a03030305100f 76
    0x50300b039140d480040b420000e611031000107074060a07035900b21422403424400c82024100c00e859644aa4410a003044200c3c0316552102c01d4641c1e2400c03800300b1b64180418450f030240c207181420028106903140980c00d6028200b03409e80e0500c95007a40d5001280d001075541d08580b04078000700309600040c2012035104080c03002d102e40000c420401000064441c04c0540c104210b10345085040649940c0d41d0a1011007403403201001403801d80040c40045640c4c0f140c03d4006601c40c488941075810000031410b0680f00422072035001c0000f003011118410384c0c00450061641c08400c408200000c12401c02e40c291027030150100221168030b022522003800100039068680c280900560755852950850140c41c0090084510f080203200e00d20904c9400ca21011807482e061401081a12401010304401200d41d8064000c2500f4004042c80b81f640161801d60000d0f010b59610f00240c0d5075002080c90030010f80e01c001c2d082403c0c41400414558941e02160003141070f80a1a0b00d141d5075420018110320035409 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 173664901 1250 173663651 173663663
    0x30d15031e0311030c19050109080307090305070f080d1409040e01090c0503150a0c031e0f1407050913090b040323031b1305030d05040515040f03020607080702030d0c03110604 77
    0x2d4640c2d0303010340c44040c180d9070307c14400880c1c500e40503a40c500050700103891000104003000424800c001091043c0009041001c0c602d14542c0e2601e40110703914104030309154240009040e859615640305411107000c25405130090101050b60f03030742d16000300100c9500303032018408104042030b245800b084508810f0481c11002083c0d80b2074030703030003401052581012418940d6070030f00c80e181060121400d10300b0280b40d60002660031483c2940c001917600060400700c0c008024000c01401c1e50b085010740c1c0c0c120000350b400400610300ca0304907030010000c0d00c001030641645002000100360340124160310392a220003d100c0e0005131079210041d81d0000355a091160051854881c240c1d040d1400900f0b092003c010001c10a26034490129003003007281002000080c800080600841c20560409064000c80c03410702850310b883c103010704800908a00009204000001d04801400785c8001599903c0381c00500341c448014103031101804258400700304034003042c0b80e60809204003501140140c0300302d030011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 173666151 1250 173664901 173664913
    0x220605040e0f06090415090203070605030106122007050c0d0b0415110313030c140d0908070b16260405010f08041a0c0f040b09040b12030d15031e0311030c 68
    0x250f103d21b407001e182070000b4030f81d07582c403c140c03001342c0c0d010230500c8010905516900e541e075040410040080c9443c890813074420303041001d50310090054010012241004029150700d0358140e14081e42400d80d81c0710029803040c001000c4005001030a900680182c0c0320b000d4441c40c90303511603804815a2045000e8401c0d4070010f0000480c840c0125083c01e1403140310340b920130308002c85660750019a0815090b1860190b1110500310303002d0790071041040c098041000148611860b08201a0181c070445505411600d038112004d81005240c3e8611500305801d40001203030380c01130102041580d00b01d841070b0f50008040640403014980141c04a50055403c0020302c28046141c000b1703501801005445040c00f40340070000c0f41c901f68156000b41c8080d01070a00b0711a0395062071300c1000b003541c3c150a05240b083c071100c0c4270032901e00d00c00800c851606100c00b00118041c00740c405864074140059001402e1542c013202d025610007900c0c0702040d80c143c42500d8074000c460150142d41e949001d21140e40a1070340c041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 173667401 1250 173666151 173666153
    0x3090302150f0a0329090c0f090a030312060605040b030f0903160501020403060506011106151906210b0a092a180608070509010302220605040e0f060904 67
    0x15202000ca03800c03588000070b140c8002403224505651003481000b0003c0d956041d0340c40512840c2036000051582d10074041070003202c0f840020030800016201d41e070034000010b40c1060700004241a039070f020038000d00e1032035403d81d24240980003162080d4005411441e0490104040e40554103440c1070b510f00488650071680c65200e505100c02010784101e0b40c1e0f03c001e1004454607038003074902d0850140701e200003503111451442c0103020785e0406044181400b455281d96501510700062181c3e011041c4030402c558800f4070701c00b01c0c6200441521003951400114004a0074a801001142d0001c940c500c00c0504c0c40503e000100454140c0207040764052841e4104108018a581185090020b61204484550005250842c18a120500c1d410100c0c004a50492840c854014200010000c500f42400d07d803410310b50051084c4240c2c0341c1d1038181039002c542c203ca4803030145e504060510030f16428000d440c0d110100506580c0291103542e01c00304281c8001046880100107003400340802034416140c0f030b01d60f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 173668651 1250 173667401 173667409
    0x304030c0f170705120406020a1506050d0303240b160503040b03180601060807020303040b0916081b061903020f1608030402041b1d180a1d06010303090302 68
    0xc00c0c180d8400c00030203244000708100c14030880d40701c100c0b0300340696940c21a181c841d0415085240200390801e050100b000120340126281fa665030744a00030546011010003082c0007000a600a0754000c407040c2076501c109030b01544800303e44845c2c180400c24013409000c0d0500400703014068900c00060a110301000340b1082e40100b40d401d44500143c0b0704141e01d0703c0304000745810440744078800040c1a8010507001c01d040c031906001d80b40c98504000c0a1810301030207580d910000e04001c0c01c8180c0200061481d0905105807803203002c1f941350700300071260b40d4812250346400342d0a00c42e20b00caa00c0c14a0701202c0c50000111485042c1d01510078100c0000000c00758029045100f88001c00407007000b1019a0200c1d030000d1841407442840c0c1684c0302c0c1820f005010171640c0042d074660100303c4064011000c4c1c0d40100308640e05020b941e19401c3c0d4181c0c0c0d00b0104100f181c8150708c2c1d01d44403054400780b00d042c0840d03400c0070301d01190322116510340c0c064440c0e8080c4d6600c1d0a100c0a030204030b02c29005e1016040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 173669901 1250 173668651 173668667
    0x10207030201180e240604030803040f0305070209250e0d2607080a030609090b06090601031506021e0a2d02060a080403030e061506070c030203070b120903040b030403 73
    0x1241c0c10700d990307200d55a40d44d20021404d007100c0c2128a0b90448000b4105c9000b480380350702e000042a20f99034203007030541da00d0800340e10019002410a03104890321400309446142121000c69014100f0000e81c14105400c0312001210010000312200e40034030040c07010b01c92a40388142c0d00d03008081d079000400300d44484002080307685501d03145048100b0340c0344011840320b004100711885085003503078802400e40010112282a0003100c0d11a017050032581c007180c40c00c400d103900a001260b9441180d00d40e000160020400821141c04c822014140012125001b0440c00e100c070600009800e8180c4103c00500d4884552607030041010006901d81e110005c49600080c1ca06224a2160b0440c41800e80000d034a0f80c01c00c0e00920006039403001048109941800f807090b620070580d0051081d8202215060700e6042606003003402400c005c9030200034004501c1e48140116006001d541c003140e1a80d24006103039200c0d6000007812500748000c144401c100104030750403188103400c0c2ca425070300d0396581100e03500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 173671151 1250 173669901 173669927
    0x503090a02040203060a080d021005090307020f040506010309060f1a0303091c05030403020301111b16060e0105071208060312030114060c100501080309010224010e0613060902030403110c010207030201 88
    0xc045101280c0101e04018203401b5208c19002845040c074070190038030681e400100000c0c5190401d0256000603100c2e21241e03101e8080840b40404d15644a4004070000c08100402800c103500f0044007881c0039500f07510061400b11300350300c40e880313100b102401c0c15900c1c418000415040a80b90140204110190240c4c019291049003542d140031303030f2500042c0c02e507036400191145142c00080d1a82584005280d200d040d022100003600b14002c02011800105a15100d00b0061000e92140c100560b031246040380d501c0c6622101c603100e02130203058001d25660702210071301c1c0680b2400002d101c02c0170020090300d0407030303107030346107142962201005009664100d00c640d02c5140c07007041c098901c00300981c06114060a0800021510303581c031040020320345051040f251428000000c2e04428412400802605644410441e801c03e500c0701030100321048d140e01544004149810341c0810015018ac00071070155000780c1c0c6040b080413031014510b859240244030070340944e100540c20001035000b000007240348 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 173672401 1250 173671151 173671159
    0x813060b0d05010207080d05010e040308010303110708070e04051216021318050609100e071412070605040f090606170c09030a0c091a03070b1e041e060503090a0204020306 75
    0x1e102580c82600fa44c021403030031500b40201281c2080b411245215290042c00181d0100350641000d8034040c1205106010203001c12859030f5071154000d000b000100000c040003022641d54580c1ca1905090102e0155070495050103546500e200d5417191009545a002c6824400300e02c00005038200b0944c11942c00002d00b940e0b403a001008140c48500e01500041e60052000c0e100e5441c14046827801c00e44116002041765107400100301e4658000100a420b803241c403420562401e0702e4000007442c0d441280d1060589214058000c174071030f0360040c050710031942d0740a48000c0203901c4001c01011b6400398090280029400644031b030b0302c0816130f41c141c0e4100300c12440851400f05050003090800c94220010364040140340c00c10449108188204017000c07210560010188541100003612007800344600d2000c544082004003030102034614980d800c0c8581d80340c030340c0d80d00d80d18075820310900b00351410b9511b002180c001c00629180500212071240460704081d00c1d80009560030032000303410142c8aa908 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 173673651 1250 173672401 173672419
    0x90703080301080102070203060a1814160605180418020d14010c1106150120011b0c0201030c020c01090513020903061312020d090911090301060f050a060813060b 71
    0x1203850840214080d1456000240ea01c0c26280185442c000000e4104000700389400c04140b80d1810b4511100001d40d48802d40416200c030074108585401da14024960a0003034a450002d40d00380c000c4000e0081100e50741c01c1216464100c400c0000300c0f06a0404c04009900e0104030400510b402011484900d01c28040325448c4410689210308503081800700c1c0001c1000108503c3c030141d010401c45501ca0954203000480402c50400205002503402d442c4915002d81035484480300429003103e45d280754a81d0080013800c600000c010004104030b00283d010074035104001490702c1c8007154041c8040c0d010b8480c100224501390500c0b0091544620700030086034280001c460a035010301800b07000b41160480040032009509004001110f204900300540d800907008134a02d58001c02c41c5400c4171121f910000e001014074180400c14030030b10900ca035165180050124014607601d45460036503605640d4030074501c3d11044180d039034800550f120940c0c01034034004907000442c50b421510fa500b401400d4019 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 173674901 1250 173673651 173673653
    0x9010e01090b0105031e030405010f02190303090309080d140307200a1b0e06090408070f0f031e050405120312040c090b040b0609040510050d050a0605060d080f03090703 74
    0x801c591061400320741c46021503004100620701005100341d0038082081941c00d15071003841b42c0350351303101da8402c441c140718160f220b800d60a4000d111410340100c020041d05a90000362500500501e4080c80c03c1b0041000050041001000010b00d60482c050649a015030a04001030044d019000201030000f0403000c4000b020721140540c0c00b40d040c2d030b4561001000c2c0c8844a00c2c00030180c500d003503100031007480b9120301005800c0304a40181c2e0010000e5032542c0c000d45480c00e08010fa4810000044c20040c00758a0440400940035450f44a0a001b55208480300c55060303040392881c0202406000050400d11052100d440c0a01c240480540300e001103d24200d001d40c07200c2002c580889003958599140340080101c0d11603400b41c000c0483c401c440402290400703a00041e0540107518032240501d0b62880024411007041c10300d00b000e0030004000b50200207141c41d149688104175882182c8031400c000c045a01c0d0700b089200720280c2c50748400c0c01400c162401c0000c1503c0d400003804c854a500c0741e800004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 173676151 1250 173674901 173674903
    0x9070309050f070e0f0601020d0c08090a030f08280c03180e0c03010810090201050304030c020d02030f01021809090a0f06061e0905060f1c0305040312020703020a06020c030604060509010e 82
    0x41c04c511089080034601a580c803042c0c640010041c5055400001d224540c6a90000e03015102e907074031000042e00c6980d0071020425825060b08000d00303150358032142c1c1040c0107452001c4c2400c649018003000480e10701d80041c103a010a15411303580400c881d540c205002a0041d5140c244140a8081c8440c61030368500d00741c40c01043c1a1031300c0c0b0144c40000014480b0090600c28065014140d40c01405100745507030008006200040c005400c01904001420440d136590402146083d0020103c8400f0b00e44040454000e62080382042410000440c250103103082c10804540303d80d810784082c01c000c08550701c038134420394080c18040320b000c0d41c0c0391400b1610340903080c589400da100582c071210441d801e22040c43c003201d401600c000e00c01c5e080c40600e034440356038006404085e08954140701e411000c091500b03540070b025903000182044103200d41d0b8884654009804002c032030080312103c80c21503542c0416230300d55400740c0c001601034002d03a001801107100f0741c0099400020801c000100079103441a21 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 173677401 1250 173676151 173676163
    0x2130c030e0d050a0e0f03100905030318010501051f0c0f0f120503060a050111070504090b0a380a0e09011506050406050d09061e0902041a09070309050f 67
    0x2000032075520000c0003841c0c4010460115020342a051040c50b0084032600640407055441056104840c6060f49601c103490600034541c0800d00028140a0300500f0301d0065142c1c0c2003192011b032441c0c03030180301004400e41400307194100c403006818500200c54038408410a52a451403000501ca0750b9101100000c00d8841008035241c0100c000d42c00541051070b000f225031030252540c5080000610502c10240d0b200c20142044a13030900700781d00102c00f01c0503201d06007100d580c003403540145444454401c0c0554106030301c2c81141d00010802201601024400c0550030340303281e02040e07410000f4800e4204018806003e8285030040441c00410b540c2d00c4082c01000c0210341084290351030b10034150007404145601e44c00b420050030054105401e1840003011809074030038400105072154080c000f40965580800c1d0b41c010300c200034451000d4103003070340c402900301e600c000ca010340c0c40e051300881003240070450f6114a010040c04003406444044086004d400003602c1560f5500401d0305040303c038031040020b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 173678651 1250 173677401 173677421
    0x209030a0302150c09091611070b030114100504060302091c05011b0e01022a0a031a0c090108040b33030c06040e180709140109050a0905030a0302070213 67
    0x1800003416011032001c0f03528002e0456010f81d01300340001c00507692540791495022240e02e0103000304d81091901100c00304040d081c4030350139008205001c03550084003001107040c5d600444030074050300001c0701809002081c136450b00000071018803090016a00c240c00901480a0090440d0300300e1039690600ca48000c9030a00072100c1da9034900d640c100c0740342001d41c2d030ba8500c2c281e4203006064004030301c0003035142e9108000e02d06184c48440000c003e0000150030350358909601805040300a5241d1901141c0b070702401003980c24156081c000298400c070f800b002c4030041d54040c0d558034026211030f03480d0050400081c1200c0e1115203c070041c5103920100001c0c2c40c801a000000c520b03241d4030f0034024107042c111040601d84c003d41c8200000e0101040350080c4641004d090071112101c2d10b43c0d00145420865142c100804241c1094401ca24822010074924180d428040040003551201c0380382038100c43c1220780040a81d00144442d140b81170007075014003001400940407005002e41010f00b60200c4002c064 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 173679901 1250 173678651 173678653
    0x1305030d05060f12120a170103030503010509011a07030f0e130209040e0307122708071403030711040c0302040302041b08010b03091b0112020c010c0e060405090a0f0209030a0302 78
    0x800c2180d10f15180003e942410001d98440c0c0d00784481c041c0340b80d2100850429804070200c002502e4034013902c1840e610300c0403c207144030f0086a58481c9401803c0380c0c001e1142500c1000e034100046101c80762020180191401a00502c2c6410229a8190348920910003c51f050101d4000e04500030b44904a010300c400f560030740c00503030798075080c801c0000300c2c2e0702d1001003146917206000340c4002662250124001c00403a0802000e85014900d10401c0d05502ca1603140c0140309a2000040084000580009851980341c2c86400e078003451007450780d24024403c018004074a40602001e003414250f10443c07600a4924003d40350545907001f05064900d0360505200d540004100c0c494100e522180d61809040520f103024554201030b0303859540c5003058250340e14000ca516800400b10782c06903000400b030310520b0340c0540d01c51003001681c6000300603444180011514a2a814038030b4030788441140c040d9900100804c644c2e40301c0c1d003040f0000344142401c040c6015401c1000c0d4001d5901008400c40b16480b0794 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 173681151 1250 173679901 173679911
    0x2010c150e1f02040b0f030a1b020d030b011403040b0a060807060c0516120b070512070809010b010e010203040905060307031b090c05030f010e131e0b010b0a08010e1305030d 76
    0x2003074680030107450050310070b00c1e288107100510110703800381c04851090f50300a4413503407607890f4106050021b1022401c41c0d8042d80901d031400c80000d802165200d48003495480400602450200541b03010020714000d080700c800400004000500401d24290881055480010031585a40d6241d01e448500e07040100401c11104e003034002c0120403c07070702c80d800303410b00d81c0c140142e8540241083e03006200c0500600884460000581c8288514150f5201a83c0c2e080ba01c0600d040500b0050083d48082c0e03100c0c00c0c070b5401c0041c01c040b10b500803111441e030440103900640c60f2900e4050044002c04010708540c2d80f600a0040000101d859103201078005040d488520340c8051401044000700c41c0200c102d402408414420403020f60036020800341180d02d001159070300f42d920304415440600500308020480044210352884607030701c0c070740100081171180303d44010503601c42000c00c0150188080600000358070000520100c0320440000c2d411118442d40c2401c580e0f101d90360941180c00654880040c1030b078903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 173682401 1250 173681151 173681173
    0x6010f030209090d21021201030c14010c080d09060e03210108120406030c1704050106060e030a021e0105070b090c13090b040602160c0f0501030516080402010c150e 72
    0x10b0741d1054002d2101c0000705150300a950014020f03000c1452000025010354545090301400c0e40c0486010007904c5012045968503031504401405980c01442040c1c2c01e0640281059402642c0300012240c01610007410007110415800160040740401c0340c09a0b1070f5218560004030401c0178148055001e1000384800080c84040000000140d02148903079200d950a6442c6902c0c600032102070300c03080d2802242035820701c0000e99002c0c1c50340e20b100042d480c0b40c10407c02440130642c014819521070f82d4802c2503180d516402c042daa40c0b034081000c1e40c030004c140810400c0c01541441d80e882e0038070606040382480c2c00ca03160314a00803030469443d07102e03400120070010607241c0000d01d64450321020104001c0b41c3c40548800e40b0180c0010300c002e16407940080d52260890030154061310380d55000d040c2a240356158440040070039103611420740840e06100201c0c60b140780000051000252590741c000195036103800449030116a01020b41303841914a01c40d2486864a002d8542e0943d00100100f040d1044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 173683651 1250 173682401 173682409
    0x31302031005091501031703040c051003060303020c0303070c090207140f060702060f07080a0f0b150d0c1e03090204140901140702010608030a1101020c0607080a06090203010e0f07020f06010f0302 86
    0x3402e05502241131400041c00010f01e0318525001100391010055181d0f070300c1e468015101c040c0c0c1d81203a030f406402d164003030b981c20740d042c5c214400b6a0705c260300740c0304c0280410080c0342d41ca00414000600082d040907041c468480641c0c0a041e005000399520b400884031408030340d003030008000f205002600524208000a034040094603040202031907032450038504000010006c0300040c1010060940f61074001e070400034150085908000010100314944000401c10201613111101a1101c02d00b009141d0b0103d034003418100c40a81100180d408984c64000b100714010039000b00203d80c0590307035070954001080008040b41c0708503200800080d1051110002d40b0340c2880c010034140c1107a040490074007011401005a4507111190308140c651020482d203c7c034064001c2000303900361445800d0420455035886604035003c0c010002080203099100c003100350aa1209000e603090481100001c0341da8405801e4106620848510559440d50040c2c2e18450034817070203a20103601885801c0f000d0041d40b40c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 173684901 1250 173683651 173683663
    0xf0904090b1f180e0f0607020d030b09010503210708132306092b06060e0a06050f0904030c050d020606030111040e040f03110f1e0c0f0603130203100509 67
    0x142c589041c030900e00039680c8009441c001d504010203032100340f0401d80070300400206983c0b4007200140c8007540b034040c0b0025039512064411400107802c003008030300141004180c16050f15000742c05040005403101c401c040700c2f8281c80d601040b54504001240211311000040d040102e581100f6002c0d01d45001c0d08c081c21001c02d80510181000030b880030001d1aa617400489614020586103170355190102c03e0750081716880d08180c1c1910203030803a160b2082040701d80c0a001035030350b103040c07600c5143c698241081c201c2c1c1450240a4100d454060003019500c0e001152070f41c498400d280c4401d002a241d95501d08182061f102400968461000e02025280030b0086610440b9011030705424646007009440f045c20001c1c00c00b92614036010b11100602d8412101000c503011024100d4850866000b09695203c0340c20980105000c03a0034101c0b1000007010030040c000003401440e00304002c650100700003171a403015000c0402c00d21019801d0006807414051410303180c01c0031500054501d000321005041c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 173686151 1250 173684901 173684941
    0x309010906020c090a0c052712030a140d0207081605060105040b0303030105040506010c080a09030b100612050a02190504053c01031814070905100b0f0904090b 70
    0x141043c034500d616504d486001c00c1d071055480501040780d04c0050300035921441128502130903c428200d021044406011321801e1050b0143c0310102e00080a11038980c60780100b0080c0000507027030204103c810b1440d6401b070042c0402e03140b4018500807041c1e41d00102988a0781c106092884c015000d503044c40020300109006103815181070044102c0310300002e8030703072205010f841d10031955040424010b91181003442c0b00d05600440c200c0d56881100d8000c0c001c680648421103c86245a000442c0c0c51545400d8034101e6003561610100d00503030510070006400700400281803a5030910805c25501d0000d0b681000303909072600e400350303158205400d01141d01059403200404503040c409060019150300905c008a8460072044400a1190701c0101c01800307000a5400800d10b48824550030b204400705a102420a8070088078038080c1d132381407284196041107030b0600003506068010081d07045208000c10340c000b8a400302ea4035000322100060102d444490041e51040040c1c0200964290300d182460841 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 173687401 1250 173686151 173686153
    0x50d0212031017010609050103080304120c0c26011b02010e07060f0f05040803040312031b020d050d02040f080a02010f090f03140f010f05100504050c03040f080c01050405030901090602 81
    0x546070040c0d001501030410312a1070070303400a000002c10045020b42c0302c1409014000c6c800c0c01513596904003401d00303810944041e03d10001014500452a00444180132000d40c000c0c40d0804003450010b03c1c200100741c1e01c01880e04140040c0d46415041d000303100300d10b0708840840345206a960050700003800c44d9540819003a8503409030009200403500300c41d090444001510f8030070f0090f19074030b104550f103000343e5101411a10002c100802000b4240610760340c2031005580410030401030b00d040d41000d202d2032166401580101916072000752154009040744051144013500d45030780c80d04400b428208990000c0c0381741e007160207082d0031980d1000348413444180c2480e00140450070090f45048207100c6100042000405500405155109110042e08a00244001c2040507038400300e070405080212180c1da83d5291417000440c0a190510541d030050784469a000c1c19540c1e10b56407100001862134082c1c0b07100300240840c4804410900410b4800d91080018546481703c2100141040e00f158000c2c1b429 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 173688651 1250 173687401 173687407
    0x1050711060c030406020c0a05010e010615180302040b010c0b0f010303021203010f060c02040f02070308010302090907030c030b1320090a0c1215050301090b01140105040806040b09120304050d0212 86
    0x34040302c030401e4075006038101c5e200503507420020030b02515010720b0900c002d125500b80000e00c1244c60041d0f004400b2203014580c1142815042202101e030707040c001e207400c000307003403011000c1c80942807a500c12080000181441c82c14840551200641202c04a44401100300d84000500c00c042d0306000014200140a0f17110303045504080035000b02007081d000c0e00c401c20040c694080195640d42c0c200c01410b407031190f030071580d90580d420001c250b031000340800d90199a800c0081003207030030009604012039801c40c4031004903900356540d80040e00c0d006401425480014600c2d5004140070361205140d403c403008005c2c2c85503c01e4000c0c0410841c005201e880003a10b032100c100e43c920781000c82c0f050a102e61301000190528080d49000d880691a005a0341661034404140100326010110605a03030560b40203202d000c000d035004413418422400350b10004d41000c0c0c00b28000800365440b50342c01c8030000040d40c41c180100c000c21451a00208c1d01690710b540a400c4005405805008140c0340c1d150049030685 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 173689901 1250 173688651 173688661
    0x31e0803041403070f1101090609080c060f090307060c0b1e0c13030c06090306060506070f0b100302040203070507020f03120910120203010311030d21020f09030f0105071106 76
    0x415400000d101900a55031240c800c40120024070844a007135070b1188061030315107928201600c04014850181340401c2000c600464071600984007402191341c8880102110303081d4009200954000c8024004c605106220a9842d5039043c400c01000e8400c1e40d40300324400e1307510b00701850001c00103400380038007810381d040d41c4000140b0260b10507881f4400b41d203282d5035424800b0552132100c8590303002900d0510303204408140c443e0700007080e03011240240800d0024544507400c00056210381d0340d0040c260205811140006820803083c0c0c1d81c003c000145090209a5a0300801d05a0b4400c07900c1c1e500151001070100110b14085001c803545080a40c000c2030790784d881c2c0d0385014030ba2040c98102c51050203054039240155110b00001d10145074101029910303542d41e031901200c0400200391b0140f183c014503042460440c8140703034880420303102d101e01a40800000038400700962084000e0441c44204200100d0b4584081041d8039000d00c060f0000145454281001820b0f41c0c08150b42c600380d50000c0003402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 173691151 1250 173689901 173689913
    0x705061e1009020708091206060a0b1207270e0402130212152b0303110a12110d0c09030203060a06060e040509070e010f0608070801030f030e0102100f06031e 69
    0x810307a100b1860059541c0e0050421030041d015514a480d4405180c8401e00c81d540c1c0b003c6100c0e4080c00043d100c2c88400394807509015841d0290f18205100840c0340c0001403d410f20031001201110100445c5070b42c0030305030100e044802e40c46a00300800c0001e0b604140002c60a0035514801000049201181482200e000480c40088054100d20b211604003b1041d0203545103404444803041d055802c4400d41510340341000c000d42d04007001d4000c40d140480209003110004200c9564030050b664281c102054050072000405c510030084098043c240055a0b4204162050b02280308a03a02c03008005031039031041514101d4000c180d90b103094106002082440e420490b040c040d01c804490110b2075980c1e0600071490070a0562001e0102c0340138000029903400d0443e0f0040c00d5400c42c2d50350340c1da43e5898010a8542d00d02c00c0c88010411a80f103400709012074403c40740c502c20301e10140705845500d441510306e002a9206084031800184e0b550314104104900740122440c00c0b0701100086800f015030b03407142 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 173692401 1250 173691151 173691181
    0x1062f0a0b040204180b0901050c030105011e050d1d010e030c0304050607080c01060b030a0e0a1203020c1615030609090b042303120103031b0c09020c01060b0705061e 73
    0x14031080303030600480c00319078035500544078985c07900710000c0c0500014107140d20130800c15103241c0c0c459442c01011400d003007284001c8a05031481a1075903002203118401038080340c0c414410704400c004040c441e620601d40d60f40034400c40c8058140c081c12440980c80389440c06c4500400c0f0302602644104461210220040155011920112600b503261540fa090140c014031849111944a52070b001c4089074400c5242c004c0c3d07014004040003006205000064250b6810b800c03074014052281c80320808a03203921a03002800a158050f094030a0002003207440a0020019080362074076040d80d074500c0103447e60510a5100501d41d0380d8083c080150315803519403a02002510240c40110b900c864101b40141440400b103003541284200c0b580e40c4078070202e410740074000b0700084000821412486011040c102c00079611103800882c0012401c1c9007080716030081d401307101c1240565484103400110394100340050a512801000035007024074101c1205050807032058240c0b44c40b0740d4914103010582c5403a11079 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 173693651 1250 173692401 173692403
    0x5210c0607020a0305010606020d1706030307020f0f040c050d230105011b0503130e010603020a02120901090b030f0405190f0803041515030314070519030e060301062f0a 74
    0x811030351030105002080c200e03e030740e81002e007140d07013085000140698002041103c00c50a550b071002c491203401020346247c2010781d8010b5159206200c140007510f401410124207050040c08540701c0c1201c00c0100d4161181c0c00003000c007113800440c801c10008401c5c0035191040210795070b1901c80000c981c011160000040c00f0311810000c0d9400c8a00701014240001201c0c542c205d000c481d1100881c2e04603d40005041c01810001d07d0000000a10540a4000d03142100150f0300541100e407200c00c0c030030380c050b0003541c4028104201000e00080c03401309a00107500800c004003454926183c1810804e141444040d000311112480040ca43c0c0400d16010000300c1159001558940d0381d00c0364141840d1000c5461050642c06142040108500340400f4088003228800c0c0c0307542a00c00244c004040300c1e8010f081d4050201c0d000101a00c04040d03a401404081c14401d00746036140d154580c000c90f00c99002608500c0224203411140810808901d20355500089904200c4c8603400301c0e680d04079118403070300c0c41c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 173694901 1250 173693651 173693659
    0x608100e1b03070806090f070b120703240311030601060c03050714010609050c0c060c0906041a04080609070603060806010b0406120b0415050406050405010e06210a060605210c 77
    0x403204510707501405000e004085810454105080c145903c5440d04411880401f09105034030b0000b9403288560141c441c00703e1907402c1108260740ba142d00303074041c009644121051400120134140130254081d0846d0285009000181003007034040289860f014060300000c0520502c0749031f5000199105080780d50b01032348900e4085501b03640c10040c1d07000d0403081d040740a03018180300811a1030ba20000240c4016200301c8126141c580b1b4202401307885100d0500f0b25908600204420310400004008081100f1030017030b07410b80b50907a84c6200500b401c1007500c460300c1130b82022000b0480c107039040c081d0030090540d0101070070b15545003141021203841a88a0300c1c040c000000d403050b8801c11301e0313030101d03c0b4048060024090b650803800c00b19000b00003070081034420762034148040785504291113468140c614510240306182c0b03a0303030104006110705941c1080340310001d02004604d51018001000c61901c28a0007069042c18030041100b07403140e803d2a20020069180b40310302d00d04000405000e4000700351 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 173696151 1250 173694901 173694943
    0xe0f040b0d0f0503040801110c0d0807120b06090a14091e150f220e070f0603090804170a060b04151403100501030b0601030c0c24060305060a0608100e 66
    0x890f00030704600441e400106907518091103903101d80b900a00618441414a00350b91903800f030850190360180303090b900500001d0100c088481c036401d156000d8001c0f404006e0125042403100000101c5c20302c503d820114101c01801a420b5043c1170100701c49410203150f480d40b0741c12400c43e42c100d07014184018032240413501030f01d4240027151035440382c4078140500130b450104016603101a02454000240709240741d14541550300c80901c0002c40d4010a517652a003064003800e20b450070031000342ca4041e000b41e4020104100002e0b4500800410340e40140384e0001614404040e800c0c40003c999003407514500a42c01c000d0030380c07900d00034400110140d445074801c031614603015002180c503040440005100003481e00d800403084c84039000c10300c2c0c0710340001d0340d040c4030525141000b140d440103240070040c00d1320b407a2045842e60348030032106c04c22404050341001841555a40b00c0505d41002550100203d40c1d607a1020b000f41c0301d050000c071818405060045c01524242d503100c40d81d030b00750390a0000f420f0f5400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 173697401 1250 173696151 173696153
    0x3020706020f0c011407020d0806061b030c0f06070e1f050906120a051e0a180f030c03030c0503160503060402090603040b0106020c1f03050405010f0c0e0f040b0d0f 72
    0x41e50540d80400011940281c84181d20140d02e03008103104564240055503220000d2892440001e00003419000d5980b845080d4441200b403054941250f01c00d00c130002c1550902d01c8405100700040c010b680b03a458014030400306446051400c2c150058000020040341c1c42d012845519041c24500102800c3d843c020031150303403400100e404d03010f10001c0c5540300d0000921f505e6a040740c0b5016034090006e100c400c01c1b036505c860840c070220b8415856102092849440007c04402d03051b03221083c200b004070100118061145e485100785240c000044020500b0451542e06050703040c03040844198007401c10074a581042c40344006100c50224004040210010001e207142d1626019514191000b0b80607030740380c0c2406e06d801094030b002401030100510450512507102d00d007543c1c800c0820501000c4040040350416801c9001d460003c00650386907407104501d040d098013510603d4500c0500f662000d034018032034000c12036180c00e918031003480b0f81e08007c0da40e611903541c981c000700143d0713218158551800752 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 173698651 1250 173697401 173697413
    0x1701060501050a0e1201050705130f0302090402060c0703050a030801030b0f010501200a060207111206100302120f0d0201020912010b090604020a1403070201050105040e030c06180f030414030708060106050307030207 94
    0xc0c414898000e075080809200340250018003800fa0111441034074180c40d0340701c5d42f504400c061144006580305138400c000c60050700b404030082221211030001d540e8040e480c0c1d11500d02c0c11141803401ca0001e81c80500401c24000c05040301900420317052900c2c01554903002c0024581c42c000000801080e003081c598000c040820000e091308560300403000e41d2038041600700f8091a81000030010301035011880282150500414020b03c20704c405000348200d00e00390740a02105214035092108240303d81c994506604504000c104031000c00c50f0300140e034480071102441468200d0174261a820f81c10032040180c141c1d20103a01590001007610010703150000000c0031184c0c03445501c040102000c1c00010321181d03550640001e4140c0308152000d0000803158204d0355903a1243c0b50940903075420030f001117002c000990040d01d014007940801c842d101e4089013000c5056034480d91080c0844030891504121134102440845c00801006000d0401503141071000303446840f0007807242c0b04150707000402c0010814 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 173699901 1250 173698651 173698669
    0x60c0509040f06050a0b071e0809030102030f0402040e030438071b05091324020c0703050706020102070812060604090c0e1201020906090d1e05071701060501050a0e 72
    0x1500501c1849903001c100c903802c0041955000d494000e076103050001c51030395000c108442c0a103503c100d07c064500e00c0c7d40c522000360310070b4443c1192582d108000489041d54240051402015080c2d60006103040c0b520401c0120345003942c0e2050950001e010802c542035644104e98803584080020450300c100206100200c05980c03c1c0d4466460f102040b03142c00e11548850445c80b880d503419014039060f4a5808000e5a100102d50842400c3e0000c91610001000d41610032102840c40d40c41000c103040c4850440242d800001c0079250a40c0b10300420000e0110030082e01006000c41e0000b1840c0035945d40700c3d01e07e10b10602c00c100b601d0006a1001c110103407104001c44000706941841000324041c1c54400416031005598014400c440c20f100002d05a4411b100700c0b0840b40000b0720a510b40f006440c01e101400803805000e8800c80d80c0d6500c41c601c14080d4079008000a4407030406840c00300e00b02900401803000181e11151145c1c58400140000e0340c01a0440340d40d1382d071134100701a43c3e011403000181003038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 173701151 1250 173699901 173699917
    0x901060f11010902060a0c0c051509060d060302060412020906060a050403031d0415090c020c130f0b030a030804120503150d061e0209150906041e2301030b01020118060c05 75
    0xd400041020a2540c07011407101a581300d4610820f21279038074020841908895141c081041c2410007041c68185840340003405902000c11020410315034940004440d0341255011044529440c1000011803914140f000da00c01012200b41e82064040800100140038500004041c0320301000c4500c0400c3c2100c1d0001940c0b00010400c0c040c001e082520a01248071500c140c4030030909011051507070500115080c03c101e000544007115101140c01128080c02040b03000c402070075070710311040807a510b003480250350040c0691162000c074145072520203448400720380c101e000c008040c420321001c1c0301501a098002030f01100d03a11800e4200d820b15000524448802c40c4a6040c8118044c801d520150040c14003c0c100b10b98000f82c041144641d4143c0e4480c00b0703079003580b011003000180310f10350168100020003010714071034488040c3c4820143c000c100c140c1c00c843e20543c41c000714000456030b01d0700030041e076440280b0082c89684641c44600c04405018100242180d4450507104e030854032407000d4032495 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 173702401 1250 173701151 173701159
    0xa090203070314060d03020d0e040204170124120f020621040c06110316140a0501020405130b030615041b08040b0108010605010518011202040b13050901060f11010902 73
    0x3810150301c060028100700924802e40103d0900080240c904500024400c44e00350b00500380c03115132650101c0b82c0c641d020181e0780d4030950074480412003504040340300c400303001044000a1000049080d6241c60801540005000c001101d018810321840c40148015154009464a0402058400684540103500f11030842070760503c40342c0c42510000c00e070a4051401004480a0700d5103c84081741c000d03991280182d642d610070042415280c114220000c0098000c900780840407030101004d904003c498a0b00792681d80d00400c05008900d41400140a4081540c0007003003442001401b09842d207000605d207506451201510f011991119040340703080700d9607016008005500d80202424008080da800e450f001c08280004c0f4541905120b14019588140c581c0e17404c0140304d80f8900a0191f02004081c100300c816030488032075000500191000e0f014803698962504810703070005000302c426602ca6031054032417a004000b10341d004040c6c0a007080152074a090411840e450b29409840180030003504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 173703651 1250 173702401 173702407
    0x506160836090603010c1b020f0402030103030f020705030307021005070201090f0f08012405090406090506131e0b0a0209030f070803030708071707032307030b12060c090d020a0902 79
    0x40c0303000c003100100404000c568100c0183c54460626080302c2c0d0340d50120011500c0c3d41c010a1050388060344640384948000c10b1a601005c810300890242d820a03402100800c0855200040454040c055a001b40000360011401c100007500001c44070841012100c05010000400078196441100b03c0800350000e0452154460703521182101840c245104101c00365180040c440005240400380400601c0300c4444204c00c80d0030311042018082000c0c00494019a89071004000142c4c1400602e1080c1801512032040500c181401c11136006008011440e00482214000c0060165174415400402200005840303820100c040f034a0700a1000c0d00229900c9000b1001880d26400801944280325036a590040f94640500591710203003422801d2410004520001d80103611135070020540741c292403143e9000707560240e45818421001c0d140c7d58000ba072102004512414140d03501c0801e611128004c00c6589445000b00346a802000c2c00c5074461b0451110080956451402324409040c00441c1199 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 173704901 1250 173703651 173703727
    0xe1318020a0e0601030f061404020c030c0105010f0e060d0314030903131404150605090105070f0614090105070908071a071b05030105060a05030a321605061608 70
    0x180b044000c840d07681c0046e007841880040106180203102c1250494010200c805d51001c04001c040d420920b0b498607588000c0c01000102002401411f00900110440c16059401c21a0f40000008020512400b4008154840c6c1c000390307220f80d5001c070019402c840307036440b51220500c0c1c1d8110321400c00340c0c42c01c907847d400b400b1407107039103643c0161540c2001300e03010080c0b406065842c524103c0035118020200f00280143c0035130754000c000428066100320100181c1c00c03a9951001c0131540118140403038100c001041000e22042440f400360021220304061a581c0d01d0641d410b41d80b020107010b401030fa904188074041e038200101e000d0390f10455101e4400003604200b010700c1320070076400b840b40d80d101c1e6091402003109401e009910701c0a90b100500035001101c41500c07280c10420a9030400e032047c0c80081a4008041c000e075060800c2082f4002c00340407000d00c00341102800c04903075000940716160070801c00b0049588801c0300c80009500250007525283e2981010f00b5005500c0c3c0d030804010250a0300003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 173706151 1250 173704901 173704919
    0xc2b020a090606030e0d0e0616291603060f0b0d090b0906040c0e01030f0f020307030210020109061a030c0907021207140105070f0923030a05030702100e1318020a 71
    0x5014030b00451b04602c1c0e84c42e03c200c6c1d1040d000250300b41c203e4010410000500c2011901810080c01641900f4000d80d10141c2264480120000400103181715011b02107a0010381c07140328810340300c0b49428444d845c02c14083c40080d168611031341e400c0c101e000030360550454540d0415006103030032034550b810501d0070410b140e4454004840c100c8608a509001051458002188d54103aa41114122400e038249035074105820808680c181c2c0c0c14406d800001005a403895804003003000305600100d1511154540802516210400074414600c104040500e030344000442000c5088112101c0300c40c0d480b2414143e09250f01046a804410000180001800b06c1240d81030040602c01008001607641c02c1d0007101c0c111019110180055100c80042042151310700110b8850590180300d0440426440e00181c074103444d651044604d81c00205401080d07290040050b44049454280305111403d0500010410b607100892034602a584541c040a41030020400c01e0341d180e1b0107407030f20b0b0b44207490710121 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 173707401 1250 173706151 173706161
    0x915060f030c0816150e030f1006080307150b01170705030613021602040f02092205071e0503070e1002011509060501050d0203060103110412050c2b020a09060603 71
    0x2d4400036501040003400d11800a51100c5140e80c1d004070300520f50800c0348040d08018044d01034420081822a030f1090744c1e03414000706545000e02002032603000306078a241d03000e1700e40991121502e0b030002d005a41c040350034024440c04642d5040e0001402c98514070050b168101400b00591004864004100c3c41c03540140c02140108000c4603100300d50123100020800764491040136a02d1000c4982d140c1c001800e282e0005410f14551303c2016050096990110b500d80410804201084d003c40384100180f00851154a410440a02c1c00c03880c1103094180302c0701d41e41003c0d40c4a9041140020000303000ca4452900a58002401401ea01d07885007050340c001e010b04410903102e8444949244001050340c00e80c85120112001a11100d06010f03518240000a420050419043c16140d4801ca0f0441071880020005014040c0d10f041d00d14a01d4148986415101030303a850150701001081e103901422901d5000380c40c11000902551300c0400c0c40400d2025030154000042c071030400e40c001c11030b036425800c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 173708651 1250 173707401 173707403
    0x1e0310080303010312030b0d1a1b0a03090c170601060804050106090e0d0e1e06030a11040b0415020106050a0b1e0a05180603072a1a040201080a0615030915060f03 71
    0x400e1287c82101d0003000605480c4c200003d141c040d0984209450038240000e59600c032100012000c41d002ca00704194001d0b40c458201d800c0000d555110b032008014040c0daa0a01a1002542c0a41e2503031401e128143c0e42c43c03040c0614805d00c8000c00001d010001c0c2504450043c1030041400c1c06207001c00e40d9065a80d131a02c440300700215040e4000900302d400d0000c9285407050140d400c005104012105220350b0f0b0380040d0203000d1550312414203102008001d00140700800d1ba0b41d205554a918107034102c4030352950185030f40216414100200499620070020406403201c1da03081941e9400c0d80864000c07240354000004483e4013012030b201d00e010350424058003080c48800d9900c40401c0301035007000f1062008036160f602140400004038805403421000c144d0000201d10081400100d540320200e204400d1680011042c90510402046507440f1031480d801c400340d158184809400c1041c0c03029030450b9550710104242c0e90300d860000b448406c1081903100b4815038420080c05231140c44600020b032003804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 173709901 1250 173708651 173708657
    0x40b040303080a1103010b070f0203060106020304150e0f04020d15061d01110607260103050615190509070315030f0506010e0403050403060b0d02060a0206070f051e0310080303010312 80
    0x7000400c0030303103240604c004240340f4103211803541c1c0c20f0000c6082e03a40c1210b0350036606486298859001a20100803142c040c1405030021601c492501500345851829883c440003003001254030017900381c0300d100c0c03101e0040c0741c00c54000d030303c030340248050100030540d1100d00303207001d4285d28000500b160412052a80442e00e02140107840c0000340042d100000e04140c8405154412000200094411600305030328401e0081c4ea403080b0400402e0ad08594502070f0800d607020340103281480626031b030006079450600000e5480200e05410441d280310b06001a1040c0e602400d602c000040500d4400c4c0e0200191040c1e0114030f4030405d481c1c0c2044070042e2501c0c81c2c01c070b5580c41070900100e421a8140081446160b15682e4107203800e08503510400502011098142c12a090741408001070f0340c1d00b030151901208542c000c25441c40c12810090802c40714503021020f00c44c0c02c006803001d000c03506a1b50503400100441742a1380f41c603000c50743c20200409910404540c0404400441004500382c0c41e040b000429075 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 173711151 1250 173709901 173709917
    0x20103020c1507020c030a0f0b040c05060703020102210610111213050405091f090c0306050a090b0f07050f0306060f04080604050d08060a210209010603092603071112040b040303 78
    0x40525540d0071080202a1071404c801d129200040c0a0916158ac418814000301e02e01c950380e003010440c80e8005840403000341c0d401180c11b600c95440c00b0b107000c1d4464004000708909043c0031000c2000c5950f0041c0c41400c2004554414013807450030855041101e40c0c0190242d81c07445403103503142e1210345600034a80715030708100100715805000030b100f04207020071030360b4078010380c0c40e9588600040c421a181298040c050702d90000c0072419a10642c0d2041d10420000b1440108130302d401d089848000744003440340e5000c034041c0881e26522005548080d842e2a401998903210a00007441c24080c1d1000308a03131000009000c9044000800e8460241c2c0c8a20221007005042c0a07064401c3d00781101c029030848041c000402808101c01c1f0280c980c080d440d5210750301c0407080d402080b1114004d0f003090b00440d4540926804000d44600080c40b2442c074210030395080c1030204038100c150f201c06040907003003019020b400e6130745039014006000c20080008a05607180e80c0d40c3c1c000f003c1500284070582c0426464 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 173712401 1250 173711151 173711173
    0xb0c1b010c08190e0d1d0909190f080f0705070806010b122d070f080f04020f0307090204090c09060c021f0504030c0803030411031603030c020103020c150702 69
    0x50048185810640e10390554a07618030030001d0543c1000002c0325501521040b00d42c000180c140050500032074103640d00d0413007201c10b01175000c0d0048140701c5240100401d10410004481c003159031890903a00d40726091141c00e141c1403440078040c1d041000307820340800003016a04003045e030005002c0b00c1e11070801e0301c031025aa5107106450700001d20401c40124000c010030480c0b013459150059100049030b540c403804201405594000002d4100420b03040c20000041c03100e4a50081c2c84184549103030320b40480c4034a440b00b03a114102da030192000b03004062034400016590b800b0301405014080c8940119211540c0311054005080c2808404000c038800050110301507100c1c0c1500090346802801c0041211002407401480c502400198010890b05210110004040b401c0180007441c08900444d26402c0500701300c003000700c0c3c1ca503019200b640401a80003d070b0801c01181800c8036014140401b00fa0890700040e80a44a018a00ba0190280a500085c0f2494082030f0f94000c407090b90071180c0d08802 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 173713651 1250 173712401 173712403
    0x35090301050907030f02220f0c030b1005090409021c030804060c0903050a1401062711090a03121403090d08090f030904020d0609050702030301030b0606030402090a05060a030b0c1b 79
    0x1c213010140c000c0e0310034407000001d0b0038280c0400000c070107503203401d006806141c000c400c201c914540095aa0a0b1070314603510740d4940c035006441e100302e02114035281700e0f0316100000c0d0007440b8042e07020340980e03280c101390005c0d9a503005161007040e0305003001183d42c5580c0d10300144035040480b4115842e52070300060340511031080d800c075000c6d03961140080c8884a210386600000c2100d091450a6541d01e460700850701c9564078280010030f102007025580140014603100041d680c080e640000c1343c100c14000100e840d40d030240c00c8400c580d000034000111401d042c80c126051001451001102080003007400080c10001882910b28109a600d8141c20b03100e40d401c0b281c0b1004040030104040d4014040040d2928143c0c1c0101400c02040f440000c6ca50354030310315841540d0045a504c0b025800200041050100031001c9589c000e508403142459890180d0000e540100042c02404001d5550700000788592220310100c80510307000410b0903038a261030301c18089180c2c41003480da2144014454030403c0c1d044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 173714901 1250 173713651 173713663
    0x60518010e01050601080f0a1e0c020f030c0c10020109020a17010b03011401061103090a06170a02070803010605220b0417060108070e041b090c0e100903350903010509 73
    0x150594038001c140d10b0b481c06041d8903500207000401e0207039440c0c158039610303092000544400b61301c038000403614014846c0c001c7d0a1407a501904004c3d40c10801003b990796a000c1668003000c1c07001c0304c00b000f0601c20114102d00411080c1307002500600450b04c0444e41118171080f20128898800081c41445090024035090303455043c0e030020f807404110300501403a4040c40e1522004c40070b500449041c013224800090700d07601c5903803042020071040b00380007082c0504c032186903603c007092507410352070501d150340d80307560390300c414400d2804000c000318119031101c0308000c010002409400b00401c61a440e60300c00c0707549a1041c8103c4600740c1d5104c41004c40b00b400402c2950403030318903402070041c8500c0c1c845a0041990006c20403540061045005111501d41644500c054051a280084c9801040f000a42b401a801003014440e50807540c86000c1143d0201a40040c5c0b64810a035480340001c10900142c0c0e8044401c0103100301c0c2c0c000d1945510400f042d8081c000c0c0501c214000c0c041c03074503021307a2552145 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 173716151 1250 173714901 173714911
    0x303060f0501170c031e040803160206010305031c1803020c0307050117010b090409020d12020d050712271d060a03170a120501080a02040515060d090f060518010e0105 73
    0x80b55680000e20070344d503c40003540d80a050351740c2805200c018403040e840e60140848003140c0783d500100a01c50500300348d0a0003846059940020191941103440b590b0b501d00603170842d6800d46241700325211030021250072808402002022070b401081282c500079498126003400140244104a0000f460790300c6000d81d02070000306607040008990a05c480c44800d81e110503507268100d503d5200e45001a141c20b1200390040f030045001e0700801c09030038402428103501464040801206000c0540403e82e94410899400d0f89410141400d14004a205034001e038084a4124001ca842000190746046240c0800b000d0030b8000180c201c0d652a04100444014107000160a0f030100603050308449040c00c0051807020b40d1410904800881506400f050303036426000b41d10250801903503076086040c02d0103040d0b0020001a20091030450310000b040c05800340000420120341c80d0a9840c09008000c14506000c40c0c1010091001d440c160b0400f2841c0081c3c008401125172030301e070800c01410018800e142c040c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 173717401 1250 173716151 173716187
    0x20115050d0f020303090a0e0a0506060708160302120408100609021602210613110103050403021f020f030a05010f0b0a080a020c0316060515090919140102070303060f0501 75
    0x4500c4940b1804100d2455410490301480100201c200a549540070300c0d0041030140c2c4900481d10704104c00c130060b40d101a102c0f6001d440140049000500450243c40440e5035200c1b1510750345020b41412450030300401d035141d83c0e0203400640860301a00c0404d0801d070300140c080703050102d180d8034110741d8200e125001e008001156a2540c203001881c2c011051032560441203141a00511103881c201c1c144041500c42d24103000c0f010200b40208000441c040911031003d00b410450381c0781689000c2d407070b20141481d00c1003920308403c900c0b4602e031455050718101d01070803c400e9242d240c0b8100c44801003400b030043c4d02856050110000d01000f40340116444030b40d00765a0000d407500c9400b10440070390800503140340c40c0e00090010048990910684603540350103014003107514140b282105000c6504480c8150141c0488000c0007902e0300d001482000001800003408d900030040c2c180410000070107003a8021315400000c41e0003d00d58107070008001e454114821003092544e403001903416540f9a40d1540c46 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 173718651 1250 173717401 173717419
    0x190608070f14060c0706051c1e050a0905010f0e0c0a0f05040518010f0603020a1a070b06030a020a060804170c06060d08090d0606150801031e0623040302011505 70
    0x15441011080302c20150001e0000c80c1412800c182040c24200c05820071000202c0105a6014154110042c94000824040308000da0112104a09001c02c895040031500340c0d100c40c040b0b035190049130f000f05e001541100c0200079015403003da0070080d02105200303d5082c41440243d194524201c03452408440380301110145003840d000a000240c980103006000000c003440700103108400c01c0c001d006800c0b00e4490001512411841000100b498079040f903c0780d4001c2600311040d8070740c85022200e001d074120305d011103240d41d0080000e180003004480290801201d0b03000103413103500440340c540128829080e5440300c14039103605000502401040c0004c1d5400040801d14500300b12811003141402600380ca80780c5102c01000c201031900d1014112a804d68a10f400c10645480c99280c0d594162940340c110043d5145882d0440d00341040c00103681100400030f880010050f460f4081c10007650301560200c002a5034480f05120341504440c250091350030035000c40c00181d00c016440c0103650004100701c0d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 173719901 1250 173718651 173718659
    0x16030c0512091011030a05010906120b04020f060a050c010515011d0d0b070c060b041104031b05040513050c030c031f02160503130b030f0a02090105070209190608070f 73
    0x1c50201c01414902c070a0050264040c1040c06900408a204e040d450465a0341d05105401004441b01640103292240c60110148091141044141070341d582101c0d220242e51545d000045201d441c00c0c4100b82d20980c0020b1001b0095000400344c02c001c01c81d9070003000710341e890b507103071107980c0c10a09403460000b00c01e45002d840307600402070b00f21000300340589081044503090b512050b4184065403401c01142d1100c8080c01080124040c00c2501c0001317880c1407001460841c0031110300d02071400300400803014140d400e031203508944000401050001c001f40928100020401104c800620040c1c0c0d00e03008050340c003055420001144400c0c400040c0c0104041c11860715102441d217050355001c1070080d001c0141e82150111021061303c1c42d0300590103155210030500041d4a00320282d4406c6452003814001c01c4a005d030203202c101d07401940c03000b000da071300c501010040340c05100c4c00070300940c00a214002c0c1b00c44c00c01840b400302d11618220b0000c000b40d903251911180e8450161041016540d081c1c9400c5c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 173721151 1250 173719901 173719927
    0x80118050c07150b03060106080907170c090702150103030801031e02011d04060302040e0d0206090f280605040c050f0a140609030c090405030a08011a07060e121216030c05 75
    0xc1102403c201c0040c450302a4400a07091007030a034001c0300003442c40d00c14000100300610029008201c0101800d08541c00210070030f8039490483c1585124102180009501d0340c0280720355a92802c4e007000c03500b05582c40746070185c0301324402c0c0015514003401081c91300d003201070309031003640158058481d000079801c280c154a402d0307003a004102d0b401503122640040162110300445050b8504200030300400200c06038004d10b0640c2c020240c6040d13074442c40c00c0081060001c101c0315a40120034100500008084901f400030052840c0020030191806003000144510f844040068507800c4031703903019900d02e01c0100b060802ca5800b07205000c0c034401c0b603112030314a000002483c5940c40a4240c80038000d4203c0003030f41e9101c007200c082d9459000040c91031000e5501966090141800360840c0d1086a0841a03506160041c21002094140d45204a0310704100c10400100150345080c01f840d41e52071003010058101c0380950390910540e03005614050500d000f0f000d01c4840520755660781c3d080c06803d026034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 173722401 1250 173721151 173721173
    0x50702040b040b190302120a020915150f07060b060309100504050a0501020f07140a08030a091a07020c03060c09090c1315030501060f02060402030607030b0a050a06080118050c07 78
    0x200d03480380e69407051000f00d40b6501449265200e21040704000c207403450040c40041051b000039900650441441d2100603a2440d10140d08a4010490302e460030504c80e0200310306811410740452000004074001556014040051614500c200028002d6880c541c06000c200d01007a1160003880d00f004198142a0310180d01280e400781c02001150002940c9840700c90881c1e10907520158070010014004c030a0009d0f8038455503000c4510070003040030349425224a1090701001d1b01000c109074960701b545050044d0b42c04040d10300c1100380004401030811141c043c0d03139042030408041c040d0080780c0004268000c1c01d015100c110344d0140060646540c1c001100d8200c0e0b02260b1000c0c581e501c02500412023103c0242001d401c688140c0f00042d01d941001006000031120703903005411540003104200041e1408200b446d000525810041442c07110240000c05140e041e4100c40d410100d010b80c0003031019030003003206040743e03900c18100b81d800e0b00e11012882956400c80740002c50010030450840090ad42d0030034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 173723651 1250 173722401 173722421
    0x705060a0302071b0608010e070801091a090702160906150c150204091508010207030c0305031302090a021207080103030905090604060e18010f02120105100203040806250c020105070204 81
    0x5243c0802c80c0d0380c90181122070712103891803926100051221036044a000780c05010156610b10040c500380c07200400c0280140980b04480da103550107001e00b41c1c00c2501040600d10010b02184032490b21210007075407000c0078400303c00204024180042e0408091044006592424460a4116a40ca4429100742404035011a580c40524003515050f1440344068006031601c01d1000c140003144004c4000071420703941109005074410480c5c1000641c11581840074a81c9c1801c056440707139900c07040030300707600051b0304081d4100c10448200040b0500c0c9030700411081d440040e10001704d4550705002c44440c0c0c42400014040340400300e00703009030300d40115560b0b0f000000400214a254030345050090621050714882c80d002030307500c8810f00400e801e004e14207000210b09411800e01c019510225901801845642d0042801d005119101882401160051300d40c500c2180c4150800c115240325501441701c81041010042084282582c0f1030300196248a40595070340d4140243c90302003000508003449 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 173724901 1250 173723651 173723657
    0x601051306110c0603091f0b03010915140106021f0209060d021b0c060405060d06090c110c10090b0c0f1b131503080309031303060e0c01020f0705060a 66
    0x1542468032840114801411a5903035840c48540c1c4003100741e10309800881500e00c911000c5c070421454003c0081c103d51031882581518442a004410b94401420f075110529019401c00c0102c0050145034641e000c203600c500c1d14104094031034141000c09014083c001c01c0016041041a01040f2855800d24910211409801850034500c4000189203510102801182e41e4000c506450350b400c4103061213951032101d2028102c3c20800c0b5002501500c65402140d1250a0100340d00441d20280c2c2d000c2000303460312400800c960004602d026040390340180d01c01d1098803a40d0501e101c982445074440c290100c480d01e4000070181051002c0145401401d56440c1d46d1085444032988081d040207250710714040440085034080140702800900003c0c200c000406c07908207010010b03280c5d2141c1203113040340c0d040f032415904c03911500025400c0d8802c0d1180c10b0380740c604042d0b000c428401740e070340200001c0d90060100d0301c9030801c42005a8540c5480c10401610350400c0004100380d041410062203c3c517442c1c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 173726151 1250 173724901 173724907
    0x3070f080c040f0609032003030306040905030706061202100203070308061201201e0c0d0309020303040e0c1b0109050606100c0819020c0102070b07120c300c020315060105 75
    0x103c03500002e209030358854400228804803c000340704501c44074110140001341d455856201040c0030903030f05d20001d0001c41c015a03650182d40e040c40411b1041d07848403984000705001c0c140d900c64580715076a00c0701e0f4050384600011401c503048140000111608103901d5265070009503600070802c83c200003944400600d55489204010071030002140700801d4201000c121912260f507070410241700d0301c07a10000b01d09890104110000c1c1800003801891080d00c1e0714020490070307200c4c0301280c01c60156078441e00e0030366548414071044003c0303540a04000c24100c20f06005802880017200c0c01c0e01c04000c4040c0180c5c0200740800d82600301100c0001c0b01c1b170b5480c10308454107403c6a13600b0f00c2c2c0b54051101c4864401961003246440d40e0305000c10980c0300402d01c000c003071281c01d00d28600300074070440c180208070800b52100c03d854203008218585c02107070070414401e2005140e00305211203030032591a16003c0d901e001141d0843c070313000d141501e10b10394003c3e0051500b07140a2104c000704800142a40e41030101c14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 173727401 1250 173726151 173726159
    0x1080d03021804021903050a0b030303040213110a090e0601030c0c0605101a03010f0b0403021f12090b0910110a1d0405042109031509061103090a021503070f080c04 72
    0x5000512900c003005803000e20014200d040201114000362460008d1410248010500d54000066070380064040755103884c144022621b8400408400d260381410050219a03241c155801240107421201c0712512004180d1300c2d080110121080301d00f24170081501071544402051440d488541d11410070041402001e48404141009102c50540800341210010041c003c040e04401440c00030540d01071351604140c2958000382000c18080d07100380381690008000140d0314070580c80a84030308603110302040841c54a0800540344a000c0362002010b12a401c10181c0c410080e1080b00d00d502100c01c00e880c01c0052038441101d00d2210010700e8031098964040009007540d8500c0f84500032486199a4003506404030451500002001441002e0120314001000441c0b03501c0d0354403145440c0d00000160b0802e152800c074000380342410301c400081c1c60100800081400005d840f1680600845150030f5141c0585140d101910045900c1c5001583d1070076900b803d14090001a5081800c42c803c2c1d5042c107880d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 173728651 1250 173727401 173727409
    0x30f02040f0909020114030a090614070c02090405150a230603120a090e0c030106090b1303020405090307050d020706350601120e0304090b10020d0f0203040317030412020601080d030218 81
    0x10590701c0140c1107075101b04c40030801c592b5120f0382a0705403104044c03024500d4030798005040551842000784c01004403200180c10020141704040a848414110450a0800c154014010080521402404200a00000074203141c25440503c5220b006005080300303221009200c0701d0f500324501030028451426800718688403038181721445428102d13085c1d5105e614101e00180854095400601d4a1000b04040f201540c000e41c1d21a05a0340c042c3c03404102030f201c42969510314401c1c0782c406000341c000e82c00c2100c070031640810702c00f04541c3c0594461085002c03640d090044003002e0300c14480806503064441d8502112561443d81c800300c1414109040455526004180c52001007410078a4000090274403414086200d00c42a25074282c83d03900e440f8212610196442036100c0c0d000003800900038554114034402c004440c0619442904259188084041c0500580041d00c00302c0301d1403130030b240c07800c040c44c80050f684fc100c55102e00184952034010806030000d500a40e800c1003400c0102d1041415a25 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 173729901 1250 173728651 173728657
    0xd0f021014040816050603011404090804030b0f04060605010219120203040b0c010527100f02090402161403120f07020c04110702040b030f0307020609030a061506030f02040f0909020114 81
    0x21403c00382820100340412418952240d4205a10510040c8010300071445c10340451344c40240c040c0c40014440c242c90509241d28000c550000705201d914008004000c40c2c82d5071260b005600c21541440b03d81c1d1074200690310388050070041c3c40c0c901d82d68000f07980071450004080c07070490004d00590740342c551581d41d032588039400040045820780d100c02c24801c00503110100014041000f916855440c8d901400c4152543c0d02034540e850420780b00d400802c1c5198041c0c0c1151320b07012001348210350720402c03510b9211445115030f8007951129102e959142e60202d02000b00c810104104a100c034140d910031002807249840a011001117110399200c40c41c6984592091918a00401c825252034000b14030400082e540641c14050007600810b90f03404007160f0010554074600da04035507454403503003002d01080c41c01111030300141a650403c0b0001030054560800202a92080d0307a09121042c074a2078075000368844c07442540c1d102250380c0420081c94541c1d134000c0c075016105160003400e040180315143c040350 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 173731151 1250 173729901 173729909
    0x703030218030d0917060c0d09060f05010f03060f020705060f0c0c0102040e01051e0102030d090f0f03111203060918100507020d091e050613030b13110d0f02101404 72
    0x2442e094040c45941811245c3c10b00780102030000300040d16040e10f035484107004014606080b04d444a140c07104005c01d5400149000303d07511000c00c503070769443c2c0311000c44038003512042c0d80d03c03890444034001e501e1190080b5204190072400402c3c1c0e54690754895103140500810403c40b07030006004440740180280004c000500d8410000e101c59410a000c1011544e580d10112b001544082c0c8480e05998000c410340b50079484aa03800a0300c4100c81c10410080d01d5401002402a0ba027034131240101070300010317594001343d04a0101d0b0b100345010f00c41d002c120321050343d01d103510100d810001004584580f00442207500c1070001e1301d40300c0c0c2144904c0c03410303203400742c40c5800941c002c1403521030060360240903500201641c2803090075043d09d0103014201d400c124000e40303020f1800060b0540d214000802050010369001440c01d0092400d0381404107080070b0940d00319190044d2128000b158645000f20f84080c5030410b15054800c4826801c000940c4800401c04040c0403034030001c0704e2110030302c00c0508024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 173732401 1250 173731151 173731157
    0x20102070801020c07032102060c0306010e0607050609010506010513030206090d061503021507110f04060f0803091f080604050405101e05010e070c06020702010203090a120605010f0602030703030218030d 89
    0xd1070651501c0000c80240250601d47c1d01c243c0030764a80b0742c41d0300040b40307504160009401079982e19128012110403071001000b582059001030203208018000032400e102e1801c0c5d100800c6591600310045406100300c0040c000019001e410600c09860000c004080e42031000b0720b0005450141e544020a44100c2c1054840500b5105001c000307508004034211a078110050006103890055038030441c90b86c206840b124050504004880322580b1242c0c4080080d241c818003064440e6034881c60a0350300d0380900706c514090020408010840042c005000c44250800c0d20b4a00407941c07282c0500c8000c0400130411380d500d100f03400d90034441c0885c1d4481d20060303103000703000b00007844d01c4640141c0c143d50042e4040c070980ca840c6c40421030b10561000719162142c0e8001c10250b0b6800503400101d00e180210044594008544078000511460407086a06054404c1f903050140f680ea40191444c1c0814510500c0d015030810814240020702c00c3e8000d0804030180c101242e41e958014000c2440d04643e86205404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 173733651 1250 173732401 173732413
    0x16090507020d1b260f0d290d030905120a050c1c0201050d060b04091d01110a11010e240f01030201051605010e250806040c050904020102070801020c 65
    0x82076030602100000e10040d04060102c25030344802c00c845252025400741c43c01c3d01e42000050224500c2002d281c05001254461340c44a5134803070240c48070b070700a10807035040910389800c8007804c0151107004030300503030a4103040c5c501003102003d010380503000400460810048640205103a1340c0c04031102c0c4019031000081c100000c840c0360444c6000c44248645215240601c0304210f0046000104404668203182545c1c440c0e41c00c920b46000360060b50484408948c0224020854884540c0090344209859404e043c5600c107450310a8201c401c04d03032040021110801071216050300465124140c4040c58000145003203051341c0c01824501610341503d182201d025403104003110018915420162036000c1c000356500d1039002a040d0301c29002c0c020011402c0c902d5020074000294090000f40c5c6555050391040c00807591100a110400703200015122014000420318100c0021014400d9070300c140e5048000303041004001c007403840200100d04501c60b408001c154170400703001030f16018450f8001010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 173734901 1250 173733651 173733661
    0x507061a030d0306080a060b03100911090a1509110d0f0b010e0a120201030b1206150a15021002070c030c09060320090703091b030506010f0801020a0c14160905 70
    0xc1000d0b00040c8440805041882c1400041c0002c03c141101c10b40c0b100b40080d014101c01c021070b0402090020b412000e5141504480034031280c19001013100308120b55181c12a6500d0400f082100c9000f201c02c805032044000070320503504281d00200d42544503858440c100013039600c08205803a28007088020150712503050742140d5800c00401d861081c41200c4080340c95013040610000307250b2180c1d000c2d040580342d0b240740003d92034042c100d220310410581620507902d042d100030404106072044560154500030300000d80300c140a120080003510540c0070342511540c100c0103d000e900140b60595100c5030180e0000001410042c0c0d44000300b413103d81c0031484c1455403d0801c3e11034448882e0784501180d02400000305e584400100754000070301d0900140964107400e02020240010b100e050311510400c0006c01031000000702d8504a484403207d07460b416460701200d60a0303000e07a04400e80400d1041e5103040c00030f25100c03000c4448444140071164042c3d1000c2c00f45e0300c1007409030b03c84040142d491003884 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 173736151 1250 173734901 173734903
    0x3050402210f01060f050303180402040909081809010f0e1b2703150c160503030a090605130203031e090307030c0503010e06010f0b0a050c390603010905070507061a03 73
    0x3000414201c500210940c1c40c05c000b0a23101d118403080b80103000b00305030340c142050f681d550544000d071007070361002c02c0509110f1400b8001075020b00541c1001982c6010031040382d01d82220000e06032501e403c00090ba003841d01020740000d1101500654080c4107000d01c031030308140710001400e03000e41e03c41203601c403149500c005210007040840c4041e019030018400500c0900000d5080c40c2c200308820070303443c0d0324185811101c40c121142e890040a90000000b480390040c90394000c00c030454007030003040051303881d00c1030b0b612900c2211181c002e4040c0c006000602c83e012410756030703004003014191094649a081c000103810681c1c81c0d0007c42d1103440e50a0103100a0809105a420901d0003400401c91075040034004001500c0302d01c43d00300c075401c0000b0f141d42c64500c0b9106440b042013005049807503624418500c0c942100ba2501c0c403901066a071410480c503011114800c00e1003500140c4244d2450f42030070b05440252000a20f4001405800c000c2440060040d204414050014012889e05801140109 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 173737401 1250 173736151 173736161
    0x1050702061009090302030a0503130209011401270b03040c120c180e0c04020d0204080a15180f06021e07061a03280c05090c04080709020a080703050402210f01 70
    0x403d244525101d10007000a400100b1181005941e00b02503850361384510b5801c0d010221104000e401c800c0584c0001130500210b40c00080008098843d18003203c0c0644d40e4806003503000305421a50301010004100c104d0341c0704025600180610b0040200e15107403003c20740809014101152403100c064420050400003000900300301c0c000351418811283d10302c0a19075207a69a0b59202e01c07440d800180412841710550458000345284000ea85d030080e50760818200040e074034070440410a0400c4d04910007040e00e240b080802c0da9010901304036240f02916001300940160030b440c103401441e003604540001039100a4407030240b00d888003103054854141c008441d25140c0802d03502945c4038608a1346540110303280c541c980e422200d0001d400402a04080c0e4180d05258015500012840184030000d011b11008200f0307600d154085420300c56460350b006049214107020900042c82100200f000180310360056904140028000d0910084641c100c0000c07002c0240e180e0107682c80712480d4031482d10280a1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 173738651 1250 173737401 173737409
    0x5090d0f05100605011e0302040906080f16060804060209180c09010e0405060d060f0219090f1202010525150207030e0306010308120702030f04060c06050a060f051203070203010507020610 82
    0xb0501816182c9070019081004480c609900c0944440303d401c045486641a00c005200e503410902210741d031125255103504a010407048180102501600c8815036050300504464103a03995207001d0b501e0f030301c0d00e4009412156010764050007544074200b5400c0341000701030203008400400c580e5141010009050780707501200e0303540142d05010811803684c0c1c5800d4150b026030341100000c039030240c610303491b18005d10800000d407120008007205500d00c20b6000c1c0c04801a00c0590150b80c2680c0d0b120448041d14489407040280051810080400c110307254406a5039071490706091252a207000c2da444000010041071603692040d8089004800e00d41d1010a0300e858030020340c09011254155213030314a0318807980307a000001404400c042022030f4403c10803039108409031114652140c0c0c0303c400c000e00801001344155500341c28100407035080705d02403051400315481c4a107192086483c0c02e00384100c007003120f800382d03400d4041440200056182030087d02d1003012550301810b0329140100d1701c40041c1600d030304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 173739901 1250 173738651 173738683
    0xe0f0f150105040915030203010e06011a03150d03033812061302030715030c030b120703140111030a0504050f0d02031204020609030d020d030c0c0507030204090305090d0f05 76
    0x5059203141c1d82210841e0140c600e101004900b0301110240e040040c00ba5500080d003648c600b69400600a40200380603041c0c401c0b40016007000c0b00c0c8040081c1003804241c541c13500000001055404500c2d00e40040c21405109040209a4642c0404068a0454081d008002003a403400070703148004a601e40c40c0311003100407212a198010f031841e449a803070780c000b4803c800388076030000180b041d550b0400c50100101004001028031598006c802070186c2041010400880d0810507400820301d01400d584d90101d0214008290892179030300e601d80145018503610200795170300c0c003605a40e00761400041d4803030030321040d0200d0a400c02d45065841c2c902d45e40510240c85c0c110264480381c00380c0c04011260107050303206040c081c030b442d5800050038900c94003c440380d040c8282d6000c0d021950300031803191448900e9443c100102c481404060320304085000c0c2c0100540c000841c00d00051405900c141062030083c50290f0a002e4484041003030700c880d4040c00d4600d0701565210b1000c0241c00c20a109190b03007016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 173741007 1106 173739901 173739931
    0x130c080114070305090309300f0c0d020d060f06090c0c03031407091809050a030503010317040e0402011101110d090201080a02070302030405060a090e0f0f 68
    0x10050101d55111400000c02c141e00a126182c4131382510f502661403d00f07400308104241410742030b50342d214038004213400c0b850400043d400c121400d85400a10303003900700c4440d0701d20380300703904a40511402d0040e42d80740050b1240245103443d00c0d07100d440406c680d0616018000584284e4000100f0703d4a0710302d10403c026403010a10168500a403420401013080c251031681c0325038204c8120001c40d0300d246040084c005030030b2480366000c880c2c2c0c00015075180b1650300d540c104034107400c080e00010404001401071041080300d5012500210026a150902d89250062304000c020000390522295000c50f81000d9002c0d08099200000c42c0e01c42592a501005440001d00c6151320603400544800d000654600702842207565240d0590000c5090034502810080103074480e424240400c0b400b1100001c0d040c8101907018016200c03001a10418601b0314200880020010022225600031b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 173561151 173741007 := by
  have h0 := BRFrame.cov_init 173561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 173561151 ≤ n) (h2 : n < 173741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
