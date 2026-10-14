-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3784
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:39:45.714516+00:00
-- url     : https://prove2.me/submissions/30d48d52-2fbc-40f8-bf67-2850019740b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 680395683 ≤ n < 680575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 680396933 1250 680395683 680395699
    0x1d120c21040513021215030d0e190305060708101d070c0507060305090708120901080c0d09050c0f0d02090601030e0c0d080d0e0a210302042102030601080a02150306 72
    0x10143d54814030b10300302c00075060f005644c56081c00250814184024082c003d54224111106840c2d10001510a2030146030305104440b1b460940002c0c0b00c00c485109402d10398446500080b003000800715000d03000742050340b2400c0355901c40e41000411668140101c0414103c040c1440d0680031804001c99041801801c0800e42c064103038075894113080e0190040d0012a40301e106212120108020740300c01088003401400e00000c440c0004403841c410f10000504000302140802d444201c5002150b001c1010000300300000101131520588a0b061075080c00e21511080d4180500c81c2014002c0c20403403540100020b07640d50f01c81006400414203903c0c8189548507405841c1a02c0e15803803080301d0024000d80d2296100c3d1351289003003040c0c46803a030b0704214903000b020f0500c2c0001d62160100960074501e00c01c40244e414198000c50003400b070f50380b1002101007068500302040d0b0055107000100d900a405480040e070b250000166681c001e480000c1d0400c03144042242000c8000c00907540040c00240402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 680398183 1250 680396933 680396939
    0x2041e090b010510020d0206010b221514030105012712081309020f0d0b0105090907170604020c0a061505030d0f0210180303020901030902041d120c2104 67
    0x801120025081150450801e200500c500d2503d8228881401520301c020121820960002500d03600e040c81108100c20b0045102c9031000c111032028103000100c0040300c031045035101e01c40488041c15100c0403021800403941724200c0810242182d06954040c0c440341c0c00c01590440088400c00070810142c4181c0c1290808503208011003807031070381c4a004000840d01e03440802900c0c10007201640c82910418410410000c07286040303400c0c0c50032001c045000044c040d0303101005941c50b1199060190b8400c4d081010484a660425803003c5d070f4101e01150049141e440c0c07010f0208910031044a842c0c2640249000c1e400a59a50003141ca03110304084071242480c0d84d4004281360102103c240d8002c18203814a101c0320326410082c10311140c01c03001040c001c2b4004000f034204a107010000107000c1540006035100c550740a500280d8089030b014004016500030031011214280c003400090b440384c0100d0309030080620500d01a21400a8644043e02245240c41d0084e01a4080c003c2a5158903809000c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 680399433 1250 680398183 680398241
    0x8070210032004080c0301050f01030209040305070c060c0519151a040204090b010807080408120915010927113a061b12050a0b0d05030717070f0204 65
    0x1c205882c2508219500d40b03007401d52040c00d0a0720881124000c7e8945020131010b480780c242e5050440b40c06403540308c110b0300d80d0301b000c452600c2000d00207885090304503000511035600c5680ca5054500a2050322505030b071229a140c400001100e014241c0301c03584544c1450a413896014007180b5104075111007452101c3c80100f001d03608982d118484c0103071350705000405960050300310365100c0068609120079280507611100c1038040e00310104072080d01d5000040744101c08100c4c50741820044598041990303958044078019154159404a0b0b10000c0303100090141c0b4042000031405500c20308005000c200a8280489110074140c0712190040c80024500c0c1049070360a559068400c1c2188100d0b5002c003420820103482540c51020010350b0800d108964656021002151116013a10f01290549800144001504c1c1d15484541d01c401152480420000008010101c0c10702c99000000380210300d08180c40d183c040d0880107080d040072071548200610742a4040040034000c5a0301c01c411842c0c803112 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 680400683 1250 680399433 680399471
    0x120c05070510021b0d05040608220b040215160f020d0804030c09050c0f19030b15070c090e100507350c190804150c120c0c0807021003 59
    0x51840140d500181d902420344d403080c2040c85070f02d8141c000b0040da0500f5107000300300f07110702d1151900700004903000c030303402c0e03600111043d0803802c0c65a0130b1490500310f42404083d00c541910200d10400348842c500c07015911080507218860500c461000c5080c4043d200c45800700d19045049034030a0402e10101c3c009120b00e07000c2d1000c1c40c005c08802408508000b007400441d8809421300c107d4540c240182c3c04143e0202003100c41210302c0e2440082c000040000c00e4018145040c1c0d1682c0c84401d0007800e25079403543c81c0c06420501c0c0603021030030040d07642d076400b02c0071200c40a00c0d415080d000440c0c05401ca000a811030341d009a00d40c035040c48444208007060803207465035201910820421403503014000c0920f16215000004505603d150420b04195104104d81009104040c44040f10004041c04544c0d43d1080d0402074042080c0602404c00200510a80400b0b882402403440e154886070301600c0303030030090003980d44500740520f84009070f02000381e840040c1d10785004143d1548041d50100f85d404003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 680401933 1250 680400683 680400703
    0x207050307270c05130e0103021c0609020a0b09010e04090507060c05070806160e0315150f130b120a080304060f091209151106040816051b09010501020d120c050705 72
    0x524107031941c002a0b0820541170469105c0400c1d004004014800340e40c81d41c1d0304d18454800345d41d01510b11480e510b030020140c031200d1006540001062000180004014000d002881c000d070380e03025195503400704103c126030070074401401d0391344450014092140a5a41c0a584a014800b2522401c0d0b580104629060003240d00404000d07030200700664494100034a564100000c40c0909210f8551002480c44258011710702c1070b407004d05041c0c041c203076129121505054030028240035410400240342c1406017805184c1680205807024030b00b40200800300d02d038500103900004444c95501c86448410207401030143c29000149c3e10003820000a10394850200500c2c925140c10f0700319440c0c081c15008201002e02d620013445603400c00c101d41494040b42041d801544010300640340c0122404212150440b074000400324800c040c0345c006078120f0300c540a2010078040300c0c40100d580c0c8a00c01261501e1f01c0c1c49c140c40104600d10609600d000743c94004240004041c50850301780080ea413a17051030074203010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 680403183 1250 680401933 680401937
    0x311031312020a151e050c070e010e100b070326040501091b031a041a09010f270f11030109060e0c0a050d0602090a091103160207050307270c 62
    0x10501c03008508065090900038075082c0c1c0105550f208440003d80b000000d030340c8884242e110740d0a1015098040c10658135070581d020101d80c415603e500c4038010114007070051050200c030b40c1c40000d00d4240d083c100c440680b8000050315007803064a03030303040c0e0b52081c084070550860b0302914400d60301c016105c09241d00c198000e00021905100904000000c20380f145c0c80403640702c0004c0c03424030129000a100b02007815000717204907000d9446042c040703141078000c1300000d805890b130300500003032210540001c0300341d400b100420840d48031441d849110507a40140160b02c01d040d0400600046800320300e140e10094091792030300f03800c0d00610000900b114500c98040301d401c0d41e1030309200412a170030482e180440000740d401074203403400c1c100000d186084500d002405290001240a100e48840d030110004000d001d00c203000c0a42c500d0f8900400c0e4004132841c3d1080c80d951190b04404610018050040310009400303003044a0811913400007503400030000120300c2c0914140012030540610403805000000e03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 680404433 1250 680403183 680403209
    0x3060d1406070807020d170c0d020304031d1009050f0103110c010917040501091716141309020f040b0105070c080618060f070f020c040603150e01050f0403110313 71
    0x3240c014200c0c00c1d01030040c1c400c542c40841c00e40e1510380c0141d9214154030f0711f05002803081d56001e142d04054070a6100989100d40048284010507800c001c0c11310420010080800001c8900000d0207d00108101031034000b6048441c20045810310740324281d400c40062502281c0c401f41c150601ea038540c082c11984406a5503481d1090a00000f4140c0403002545610749900c1c0038a4000024441400340c0217000c0305404c51072003001800703810440f44203807030120f182d184425507991841055003a81e4414690140850502e49483c0410501c900060181e0040032200c1c101110030900c402024400e50b0039042c803508006d03840100d801c100340c00004214100c001c10309031a024544030030001ca0001040c606d540020288142e6003108001c29500141030b00e465100607040c01c2089240005d0a500075800920300380c000700034044015014450280003100c1030000f04101c00c1c80c40e08031002180c100c07142055009c003090000784100a16015002504103da00340003883c0000c82c0d180505510a518110384 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 680405683 1250 680404433 680404441
    0x10b09030c030307022107080a0803041103030c0a060e1603050c1002030a020303040201140405060a0207260327130e010c05071a07110d03230c0f03060d1406 69
    0x802607080180000d0b0b0145042038400e5021410010394042000b054134040d00c0400443c45041280b54028403203601200d04c15125418005030552013030b50203880d14180f041c56140c4505000045421844849009000a0045403500c0e002003101507600c0c01c050085075400d14030445c0868030100514003507400303850220b484504010661044200410643d0001d100f07a41c403050300401941c1d4015028204180d00c080924180c50b804d205030340001e94000e0000c00d0f584042e079800103901c0141e6205880f420889120307035010856024103d0001c200c241e1080000b04a4140d50301c0c4000a201403100840e18020022000103c1c0383c10640030301411030755110b181c0c2d00094000d001e0901c1441850400a1600c2072640350600f1040d2841160030307206140001045610b44115101041c0020a0058480748818040014007904204201c8a503c3d4180c00d5a142018520f15041d400368000d03107031070303490105d80c4c10a03003843da00003c01040e03100c4c2c00c0d14030b0a0042100858a1480284a40040c000ca468 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 680406933 1250 680405683 680405689
    0x8150409140c010207062c12011401140a14150c03030907090b15090f12010b03060604060b090904150c05030121050c061803070e09100e0c0f010512010b09 68
    0x140c050b40b031504660200c0020044641c11020016165102d41858010903114030420746803482c074208010b8001000c0f645100220300c06600402d41d4641009501c1d0241c1d0f0388402d4400d500c0050030310254401e101e8801000264030030102116003010103000c0034000400581a41040d0704201e80400e595080041001f01032101400244d014250301c550811081120101150300083c070320249841c04d80700000d004aa03a80c4200b0b404201d07400050800c0700002882d0107840c064000141c07228040d00c500804904541341c03a000304019a880e074000a800e02d9041c100300410008003074400c0d54003a016203e0040700360f490303010b1143d46180310386070203075654548044498001c101d80020006059010040000208003140c180ca18150449503640c907000c040d00c00003107a40f00d44140c903074148201c0c100050450954484071707202d003041109840424106140d08002e6450055242c4101d4000c54aa00102e01d000c000c0e18080c4141850958240401403030700c1d503010b0800303070400c0709640e40219016032646 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 680408183 1250 680406933 680406943
    0x1103090f060907180903033306080f040201080c1e03071b02030a0b18010f0608010c0f08280c0e0f03031305210d030e060a05090a030815040914 63
    0x40c000b41c0007000b5203450200d1844420941610103016140c940c0142d00906110f038201c6a50111984262150400c000080d00079a001d5074460505480317000a0003d402c034001ca1403248a007400518040e0b00b0b0341c49a00440e84a1030041195010790820300c0b800d2a9401c51034103041c1c48903903001c1c0c115903d0078003120180c400b10070036136825840c40d0403103829070050301d0226003840e4040d440522040c142d29900181c004804606405103029803802001d0700c10207803190000030460b000d14000708800c407400a4101c9042d00411824030100700c5c900042401c42c0c03c640c8956078407103646981500000c0c04040b80005540084441000042800c1c945100c9450300210803818060700f00d0085280801800103181101a035115051003841d444031001c01c403111007244000c5450320042922a000c0d80c000d8090003e0540004078980c5200c0e420026000c1243c0340300f090300401d542c800400810385241c1c0c00715000c100c000e01c4007030780b0180607641c4031083d120341c00342040c014490350304802165415040c0c14a01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 680409433 1250 680408183 680408191
    0x3200d02010b0d021f05040b07260702150a050d060602061008030319050a02120c0d0605030703030806040c0314011d0c0f090d0602160303020702030c01030506091302041103090f06 79
    0x442d840b8a07680016642d851500c1301000030307032068580400200300b0995045c007c07035201d04180c2c0400200c0030200803109815040c4007802440301d10240811100444550090100080d00301c0c91140c1c08400c00c00750754010f4031016066180161a04110703140043c02d4440d00d074001c0d809a8442824002121019250345001e0241c1000550951800c1440100e4201c81904000180355903031002c45c94105203901291210040c010204c841400c101c900c50006910071a0146040d51410130301199034a80420207500712905542d071401d9585503c41004020028a10b00006050751980e401e00300200c0c4004160081108100091340c9a135000840030032400000c1030707011604070400403540000440c030180c0b43c0e0364400b61040b1500d10a42d187c600020b01c104242c562400e524501e0090030180d05800600c0910701c03d405a5140b42115001501514010384200da48400007100283d003805880b000a07964500041000c901c541030303990000181e0f44142c800103156001100d9910f121403040114a0f04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 680410683 1250 680409433 680409439
    0xa0f0c0312020d050d0b0d0516080d0e3f0f0d0e1005090a080303090d09080c01090506180d05010203100f181d061005030106080c010903080703200d02010b 68
    0x2180c00003c018003c0c03141a4514a00310764030a10500d1035180c040b02648007079807080c1207030400700051041da00c0354805880f4650b4640b04401d20032100910030000303070400b0007002d0011103101507044050200401c11010043d410042007124180040504145a0042c0800e2340038008440160700a80d0400c04407807500c0382440a00020003001c0d8440c1101448441454a4441c0c0c40e61980400200c1f050925401842c440c0300101c18031588200206103807880c00d42c1340c0c0f6008200d50b0340d002041e0b126118103c030580842c440e05030401407818107000030311039221410072015030078010f10009040110030503016030f60303a9408801c0112550201c5051400341c04040080d02c850303071411845564290303903002d640c001152140c1c0440c1d910f0042010082c40484924203481140c502001403540b0400700344642d510035807c0100000b0520b6010503000d84025069481c12020790441c1c452109582c003640c000c50400045840852007441c907401c2a02001e194200940450210703d0390081c01e503040469920b01c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 680411933 1250 680410683 680410693
    0x222031b0518220606180509061f0b0c0a06060e04050d0c020a0909080304060c09080309010c02030c0415080705013915090501050a0b0109030f050a0f0c031202 70
    0x120a940700c0c120314001508000810b1030382d544a451005480302510106000301c08000306840402500340c22203403c2d1841d210f5482d890024507481d40c41511010f454072012600140e020a081000803403401c481c00e42600c44040405070f58070b44046090303101d4407441e003050f006074407940104201c81c000c038001400e11a88420243c1095202c6541320500d1003007620501c03a60b60500c00854851010b500010048404204014117003401d140040d640100c3c0d04940c128030708409540510300660140b02603441c004010350400301044015240b04031500400d0741c5c03600c600050541d0b02e907103502403120510032a4410002461a00d15214580506030f0030071410b00200b207540c101d58040844615002ca90f4441803444064111380e038580803f03030710041c0a45800d000c500d07660b0603c621a000041004c0c03252000b08401da903002d48001c1181d003203501d000e00042020000b01b0205241d00780c10309440c0c1c0150180c1e08003150603a264003070201e101e44202ca00c01321210302041400440c02851100c13840a0000d44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 680413183 1250 680411933 680411939
    0x604090c030e0f06070f1e030e0d08070801180204090f09030f02011a0d08070b0c09030709092112150e07031505121f200703050316030222031b 63
    0x1e840340c0005101d00700308485240c2031b4a00900c111401030740c654540f00c049400610032500100600a0b000110aa500c150001403c94620074070140307100301e805954101c010303424440f002180c105045400a422602804003040c0300101e84140e5000e03904035080083c05656034a005000d01003505030000540e403410302032070340c0d18042200718000c044007114031501d80c44561421141d50300903820050004c040d80300402c0818010800104120002102101c0d80e1503618040c01d800e42e107217039000402c0c07803040c4011101e15a0010728181038080700303408d00c00c1000d031030503072804116585100d80c20350030060088108407000709488400d07044299440e0500a20340030024000080c50213204142c05924400000d40202a00f0321081c0c01c544072805000c58070064001c88000030303010010f080043c80c03101095008010071500d04440007158140c4440b03085984001160740d43c1004010342c0c0052540810a49080d50341130505400c3c02c0d0055007059203894218104000590300c031010b10440c0c0005040f084c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 680414433 1250 680413183 680413213
    0x604060e0103020a09090f09021f0905120f1605130506030c13180308060a0b2106030115060302210126071205030304150c09060315050604090c030e 65
    0x180e00d400d4000c0c00d0240c0d6410f04140c0c03c64504206a014022980c41c1c03e0442c112841d942d04010880e9000b150009640c0710070301840e080304240304801d100400d00e0342c4810072031801d0070f0b450715510b000c101c4103803101060441c00300d50410f200b01d004900c2180c40380105000d18942110103a01100d20950708006914006000c04d6580460146061156000c2072026800030280d40011720000e0820f060443c030190a40b8010340500340a0718964822103e200020403c100038800b55106048005541c3c00231034103a02c000b00c8074400203408143c055484100360400c0c148502c0c4010010005a500103030741d65200c038842100c12101c00b6000d004840c041004001031000011b071141c990100c0d10042a0201034084442d00d44240d80c3d00045001d1505080070007841000320145103d64052101e2000da100ca02003004101c41240f4920404036465000c240b1102e842a80f003c801040488003155050b03455800040d50b6030403c1e0b11200c1e840f501d45100f0384040341d05000303200c00d282f81500181a184030303820032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 680415683 1250 680414433 680414447
    0x103140a0b06011206080f03340f05070b03011202190b220e041a01060503130b0a0b03012a02030f0a0305060a180606030c0e09040b060607050f060601020c060406 71
    0x42c10304000200700d5032031040d041503020030001c2c15080111069500d45001c0eaa840b40c00c24404141c03002246501c1450f1682110a4140b400158505403c03d9144d40c0d5544505140c160300250352500c5140c101042e42103800380258040c0440112900d01b5400c0340c41040796000e07542c0754103843c4051100080103043c141109031030720520110130300b40da088001150041007401542c004000c0703030400801d000c140b021f0500d0609064034526040c2c103203a038035840140e034684001c0e1140078002c6898124600480c400100b40c680010100d280440d0648007540003074203680d401c01800801b000b6200700b500d01c034101c5c001d03020000300d8140040c50030400c42c5407925900c0d01581035003205254031080042c00c55500c0d05a21805401901007001ca2020746504036001050170f8060b2401207440c0001c2c607450140030724008060704600900c000e45c1070751076690340e0041a201414154020740b0600c0440e00007070060112405441d191802407005d45171880c0028500344000b24102d0052030208020b116031980026 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 680416933 1250 680415683 680415691
    0x9050a110d06140a0507020d0e1c20040507030b0f041508060c0c0c090c0901030f02130803130501030c0807141606020d110c10151502060103140a0b 65
    0x210304a420000401065124403560380041c0703080c1c6070408180048101c912860302800c20740d0710410240d0340c0c1d45c10513a594140300c0f03007500100b84460280e41c420714000c1321444400d043c08084466015955460200b031404050481d00301c04515224110581014445c1a5020341c641c5001d201c240c0305903020405131691030a02900540c1c8902248000e410409a41ba0003440303000201c075103c0ca002d0740c92451903040403030081901d0003841c5020b00d191030540b10550044d40c440c1080d604d4070701d070100107600400c0310f03030880c02c3c2c1103809000a10a00d03080c2c10040c802090414041d50ba22a07030a03000a045141c41d8115034181890500080c5d01c3e150b2102c0c2d1240d01c401c4a09041e51503d1250a0191860043c040c00e0096448054031a108121007500600308e4481d01c0030302031014540c100d08400c820701540f558000940d200800d444511070560700000201c04144d800c0c1100341ea01c0d072040d41070b9105084209001769000b03d004008000e4114450101650312038003825200310165500c400c6000060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 680418183 1250 680416933 680416943
    0x24010c15020c031909091119140c01060810090c03230a0c0503010509060103080d150317070c0f03020a09020a111c0e011d010c1a0703050105090a09050a 67
    0x240c0103040c4185541101d0400d08000200c03912403c11000d4002c80301113008002e0002070440e18000b0b489046030161a000346054288282040c0f0341c3c48000c0035500c0c0302a142c030200040c0000c80c42c0b0b6205c5420040c2600d4001c0350001c164142845050b03171074907000710f84902e0b07024500f401103401b05030100300c03540659511095a0104091516070b218000d00741782d81c004403501900039400b0820400c1210041102c070203800074440c0d95145425561205424840503100e11410408105011150350080e48590a4005081b9103552607444a041c0c0000c0c03601148454480010300200384940700c00140c00801d042c11015034101c1c1140c0c049030500e68244101160b094000c60300907582400340e19451032000d900350881d40121141c9201d0614110010450404075501503031031a00c5500c84c41201144680c0d10310384840b104849001150032028400c1d040c3c4040c003003c89003000212507200480c2c0107500c650340200f129414170081185260003c0c10010301d0a2602450b180098800305825100701c2d040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 680419433 1250 680418183 680418203
    0x4150e0a0c090b040b030a050108030703020a020f12030304050709050c16080f04211716170c06090d0206060f01021504020a15030501090c1b0b04030909050c0324010c 73
    0x8000554854a6a030010b041031076000c41c01054511045c2d004d503103d040001400e10260342d0302c01e00305450f13104800029005030407039060180035050104040468500c050894440c4000e51141e13942550030598003110300790844103042100c6500ba000301a0022180001c640c54813401d8803c1041315169590000d000c50f802142c003d081100403400e81d0014904111402d604104000030300407081a2410221211608001500c610311001e00966440152030303074404461802030b4442c072280841000b44107201d41d070f040000018000041c06200d003e00b11000041004c4500c045029003401c1000386860f0140070041d2289009aa002400c0e00c5199003a054148094440e8004168030950a80081c1c0c0c6c14440180441c1140c1e505510090480c1d00e506020080108802d90072038540402c441c1c014a0303403030b24071000701c00b04510705a00d540051181c1810a40142d4500d00d42040c0e6108440c0300c651080040301f0442e8050702095461000c4040004641e440007100c00080d103600ca004501400810301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 680420683 1250 680419433 680419451
    0x19110406080405100e0f12091c0507031b06170f041b090c0e0310020c0303160c0606061d01110303010603090320071a0702030307030507082704150e0a 66
    0x180011201410340e14010700c10302500c40c002c1603a0b0791301200c4102e214490b8000d444841803400080d0b400050b0001c0c009c4849404204503100c44030b00360030059400f4064000000001100c2c17500e00c0100c4e801c110161000c2c0c624040003d845000c03a440c080c0c401650120822115103207509030380368040da200e801945250404a080c03298146113401c07040001e4900f03480354000981000c0c14900703800084080f41d8080030322541d01c4c1c0aa010b0024501c1c101d92092021030460030203490342c000741840d14035010528180039100c00c800d0710155803108012900341210403000706203041400403488000e0800358171103c80d01006643c1d0348070500c01c4404155a03024103204140c031584114084d0304d00110f01402880b100304141c1e4603418548900d402044500c0c81450000500f241960082c0e80c004000d10704140c0d241c3c43c10345e051340c441e00341162401d03c104410702ea00f107855100c0401c92120109100b01c042d16100601c411900300c0042d1342031000c059941000309441e155425944503880080210b40307850 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 680421933 1250 680420683 680420693
    0x70e3f06060f120c0307242307020303070f0c03060f02090a170703020303040e070801051806060901090e0f07030f141b040b0a0807022107020909070b0f03191104060804 74
    0x3030082007440d17040c01a441c001074641c005154194682c0619681c0701c00341c01d503480055a00c000d080092a080c0510480540344032100c50000e0300070140013800352464802c095031140820b0724080307011110410610824000d010b41071240b0701810019031011031800380350a001421a038518400c1403049950b410511001f02000d1040d28021540501266250303030320780380100c2c0c142c6001c544000014424500000300c030310701045440c008070221040c0d00005d0320fa480910540354003071240d0b42d05000e030381040051115488103440b0301c03880089c0001182414070704002415a0b107440d450702d1141e82410502441c00d224816419044444682d0501c100d002030f038007140c10390045a1241c079400d03c0c00701e0304a640540210300035120381c03229820b9400d5018686200c4480c0b040b1844803900c01030301800000c0c0107044c100340f680c0d0000d102400700e40c04190768480400c030541c0404500103041d40c0202c14003800003c03689091203d841d0000051001c0460140328039124011449040d003002604408501846 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 680423183 1250 680421933 680421943
    0xe1005040503010911090906071e022803020d03020f040e090a05030310030b0f012402010e0105010b0d061a070807030915170a050609070e3f06060f12 66
    0x40700180083c00240d069081074690810034200302800384002030300060001401140151103250b02c3c0c0c84101c001c85d8010580002101d084003070009600c6840c4041c00100106448503425512000d21407000310f52030301d4000d08000020f048101070500611400c0c80200e2082c06442c03d440d0700c07885000b01956400b400034a851350b070010180c030740c1c04000207210f246a119440349050320701584d040304c050f0302c83d070f112081444000d10601d035204894140c036444c9605182c001c000b41842900c00442c0010496507020700f15502a030040034625000550342111444500540c00200b500c0c007003038401403291925840d01071050100c021b001034400035600c820503014121020140c081100c2e8100801782169026241800d03458240d5141c40c50680080e440c030056000c1e8603c03500010703100f044d917038072410b101341c42381d12015414550007070041c404028903422204d550700e03403452491014007103c190306001c030004075509020820103402035410424203032038540c5580040001034403150200070135903080a00308 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 680424433 1250 680423183 680423189
    0x110a120f05120a0902030f06130609080c010608071e03080702150f0301030812090109020a0b0a020f0f0c241204151404020102070501020d020c10051303050a0b06100e100504 76
    0x180304280b0911207054110791101000078404d804036210546403901040d502d0310105d8546012200d030541c81000100580c001d0301c091481451030b541810300b010074203425500e95802402c4242e01405c020000c412603020001d14a051250034000c10b941507072100084d910501002a006202c0c103204440d19051400880d445080c00340030407620781d61240b4204200c1e9014080500b03010844034003140412106103d08680c481d4010030300c024003440d200c00d20007141c001c418100300350701030300b241654100800d100d19030500c6005409050020000d0082000d91402d402450a40f141078104884c0d45d041520201da0240f044000d81001650380c0b40303002802c030441d04100040746410440d1440f002000c40c20064010b038400d030240c408468444004a0303541c1c5401842c440103a2002d0501c2c940b50608003002c00340c403280c0f480c200d840d081a01c0c040400c4000d559004444552001c1d82d01c0e02882080c120090f0440c40c221200c41400d0307000c10004040810402c031003803003a6605a500c0103200e000e4400c40d801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 680425683 1250 680424433 680424457
    0x14030a021003060306061a12150a0806101502060a02090f04060305010902042906070206091002071d07090501030c0c05061005040e1c120612080307110a120f05 70
    0x415100c0c071800401410080c40111950740c2050300201c2c0c0781f485070906406860084070340e6400c04400401c021b55000c1c024000380b250400c0d600103401203860b04980f0f08080c1a01c40003c203941d0822030ba01c421106619400b0240100b041c01d0300c404296400314aa80d000340c00d00c0b002507101d0100c3d00003d92001000e14031141e000e440c0c600004101312064202646181c000c0b1401c000301942103030003070b1250300d502010390b400c54541448511585000406007280500142525041c4030070036010a0068004001c070001607840040108001144800f4000280d00329030500c012034240958050701c2030032503004644c189074070341c1d8103620928495428010516040012540c0900301504a42c8510041307000302402503060800c441d90000000a107600c0201e560001c9040d0003181d500112600d000305460049520b4550340002178044254108071001800742c59407941e241480440903140540051521036140c100d17550070400b080708111120030400080c280b0b030910000343e0030212641c1c4280900814 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 680426933 1250 680425683 680425699
    0x807170307050c10270602010e0c0f1507080309070e0c042102030307150203010f08030301050d0204091532090c0103021b0327010503011a280305100b1314030a02 71
    0x907003105c00050102c100c2d4603a03002000060080c04240d0740702e0090000e42504441d540140f501c15007080405614000201548181000919615160b440e8416120b0818079403202d4010701c80c054003062038580102c55108001c0c038103480c00d00130700855a00c98100c0c201c928102c3c0d50b54401e6417418000c0f5070100d0b078440c040ea0f440714148070403038000750000c1c041d101030300c0c0500501041c00140041180d05a44c0010400c2214040542c208409400500000c8424580348000410301c202030380102850720301c1d000e8000c4404000b408180b56201c0d070790045000152048014011000c0010404071a0940203190150382e0320300b0b000c0795542d0105900c3d14491140b1002420b0150107429503800741c1d50700311041c10081e104000d50011581d50000380111800071540d40300b20070340c1c182403200505030901c0c000d14034221803200b41d299400c00c1e00c0c00e41d0344501080d2a0740800c0b96643c00e8010060180000440706802c110b01841c1400244510340101d421803000755050f101e80342d07010050001c82e103900421200c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 680428183 1250 680426933 680426987
    0x504060c09050105070320120403061a0409080912010b1009180203160309210509030d091406030907030c15030c030504110f040908040807170307050c10 67
    0x54028010640c00800090801c030707000c18958403900485643c2e64141d510074440388079602407440da080d84c91220251520904a580041c02a130030058401503005080000c1c06803407e01ea260281d8a44c2d609061045280140400c00900d43d102620b104100c1905c100740151407022105005091044825030b1007803008641011f9940d02210f03010a4800a98603035035458280e02c040c00a03800155032400d00e095407810030740941032081e03004180540c00341c082c0080104020740840c1c1900480800f102c0041e000051503101ea00382040050316044c8681380c0107001d1403808240401c02074034560182d2054a0010101e10089010407816018603081091110300d6942c1d120b005600e03420480341386011a081c941c2c0e04501c14002c0c41503510482e00700034548004e050100c100050200204001940940d40b01a0314011500b00303000b61020385541d0303004142d91410a02c4409001c6103550b0090150307482000b0900000d40c010601408010054034a01c01c040416803042d0b40040003040140c00c0f01c03450001ca5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 680429433 1250 680428183 680428193
    0x304030c05030301180b030109050606280f0501020c030d120906150803070c140906040509030c100e010b060403150209030715081008061303050307020a1e110109030f061802040504 79
    0x2501d0070b540b41748800c0085040d00814507091300d10f01394019206030010400501d00d41410000c1c1400c000707071a4503450b04c0d036a40002042101e90380703070404884030300046002d101d296010080707124269811001409011800c0ca80102181000d0440480258032203500604000264110306181075282c0e0941c1c4605490341c02e1180e41790001030041e182d0340607903500028404140c20400c41401009015555039945610500025282c00b520028007440700700081107046500f031148448040030140080303a41c000d07540308542914480b242040c499042000104000f80b0560b10302d800140500e24050784585811000034144070050703001c004001115241c41801a0744082040d04c1948070000300c1710301c291034800842d600c0d0300448040c0e05a0440c1c195550109000b10302940c0d0203401d0744122071135140544d40d44141414002c8040800802c2c00d01c0400c02c002c03168030340d40d040c0c1c4020701c0d240c2c1d501451500c40e0514500c40d40c2014080d00e5071410000390b40f00012660040c5550050800c0c40581024942 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 680430683 1250 680429433 680429459
    0x30619021b075d06050723040e061306051909050c0a020c011206150206091023100308210f060a031e06091b060306060f050304030c05030301 62
    0xd003001e004000110003039050701d01a00709103d0184118007190405999400581c18070810f0419084a410043d21030020f010750060600c1801a55910304180c03071442001c07a0100740680c0f04603000601404140900e0465444640c0e000d0030031101200c00d412044503500c000c0c10b850700a00d410078451000340e8512140101d0203030442d440b2820420050341d90154503c1ca5004a005090068204000e842c50541c4030b0301c82c00d800c88180d013100050007030f038400144c225034081460580c0940c100108001d01b11909012100ca2410006001d202508608030f80404203007003011098421880c00004ca103440b89641007030000355074029605507581d0340340da28254100341048189060b002140340050164000c000e45940281e0b405425101007500310380d0b81d1401203c500d0381800004110003a9400414118000c0f07200e0700e0f02a2810b000300c0340180d02080c40f44200c0c2d8219409240c03c0c0101004806d50003400b00125034407919000342c13203446038070b4101c034600c1204c41e02400b144804400801c0903104d04074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 680431933 1250 680430683 680430719
    0xf12191202070302060d091a0a090b0912121008010c0504080c040902011b03030908132c010e0a02090312030603010c1107060f1407030e0f030619021b07 67
    0x2000c0400c412420089a6403050303400000c0d08a507080c07108041c408540d401294000d8415100d04903800c111800e0420040d1003264000070181c0c9510080c400d0081c001c1a064002500c00007a21030300c0c1c050940c0c031400b8481c501d102840242564002001d07807000c1140440540708010082c02002740f654001802038000703008581c0e8500031505856982d19151042000303e50741a164408001c4410f48901c4c00300c1d04190003075052507210380c104800544454014403085003c0d00c42c450f180d505100819902100b50103010601d1810510822034a00c00681038904540700408e80c81e0071a50344502d50350281c05031041d4182c240c445c1d40c40103000c005d50030000e1441000d054008228200801d02e00b01d6505040d00045801c0740c003c2a02400602e101c0d0042c074040d01c00b1400c01d03041c9440708046040e10380e407010717800754001800c0b101229a40d03d0320b0b032451401142c0c214000c4c286410903c01001c0c8100e8410039000803940d001800d4120b80400032000080c02c60404151a10741da5102059412008080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 680433183 1250 680431933 680431943
    0x10052503090b0a141e210106260601030b031911030102131403150c13151704020f03030706020903060604090c0909020d0606090b0103050610020a020f1219 68
    0x8440400e00e41100c6003038800c0d0f40000d907074091404291034a501c0280d40400300c0f0352115050035807440c0e46000064001d0a504200143c0f1b40b0000071500c5100c0c0a502068005d001001035400780da10490030714040305a501d01c07919180c001a5114070f80181c0c0186444503805400d400303540703444550026103074005040103010781003c882a0100a040500300e1241e8012281c118201e1031050110910003900e05101032009812a400100002801941c03200c4c00c03101c0504500000826107002c0c0543c000b4040140f98144542e00e0600d602030003d00602c031400d10400304034440000040c113564441c170980001b58005001d80c0e9403100c140c1440e402a5001c005060f01030300c14070010506ca400d092140c02c00542e04070b40e41c084500d081c51042c4025002d0100140c0e801031501d010a004a20148520002080d00c1c81000401e10398000026051703032001003074684a400140111815942c02180c6d440c4401d42c1181e86445003c0325000194549894980c07000c2c186c0b150000407074200325000c000800150142c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 680434433 1250 680433183 680433197
    0x41404140f0709080c010c060203150316080715141c0c050a141e18130b0f01180b070302010f050708010f0b030c160302030c100c0306080f070510052503 67
    0x244070140d9039144440100350020f0255001f800114201e40d01a54211400200441e000c9803408000782c54007000c41e1801c60f0b080500c800030080c1610030003481004218100303010040303801158020700010450108002522000581140e8880200ea86903c0307680d803410f0308101602080200402c43c0e000440120040f420f48603034540f15450501c2594490081c40c54070300c8440d0041c032100809600a045c100078401c0ca00800d092443e5242c0040c49202c001d414000680d40c2c0459041000203181840d4507030510000d14400c4d1000c03c03502c2c04102c01e03100081003c40d41c1d40a1444c2c22801001d45d156548481e618103014001115401804281243c0010a5048a0302d480310f808000c603100a45698080340f0003004500701d124001c295500015000740152810120031009031410140380301540c00078640c0d40c248800c0915003600c9144c01910720000140504680301d6203007030b5141d41c5030161521800304010044038041c4a50211407510f803003c650180f03010360096000300c0040c0c1c0c0c44170490100d0300c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 680435683 1250 680434433 680434439
    0x30414191b0801060e04030507050703050d02010507030c030c0f0806130501031a06100203041509361806051003080406030504110d231c12180206041404140f0709 71
    0x14000d0000b940c1c43c5e403400f03e14a84560303900b5580c0e9402098101c80d207004000340003001c21400d21401c182c0d5206031f0000b1480d847c01d150002c080703691440c601c40c181464000c2c000c03000c50380303d85502c4d00c00c0000d0400345003c0c0c455100240e8086201005800d400782043c00100c1000280c1c50b41201215044482e683c060703c4003001c0003036072203540d1030940050303000340810001d41d280c07003090010400860428451150312405a0301407040225a00e01c5001018201c2c9500300d4804840c80c429003044040401009075071030200303052000e00d080b0140c4040d0b181e8002c100405000703000f0800860340100450b98542d652b05001d000340200321420707a004a01411446917a00b01920360300700c4d241d07000c0740c2e001c4002c42c4061001c0111601045800661194040101d140c0b251020030120043d83e507192803003551941c40341d0800741c501d050803030307003011a5140c48a80180c0362001594269043d00c02300d8030107030200c031002c1401400c0000d106200c9140940c28002c13841e4108008a02400082c2c0c0c0d0700f001c16803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 680436933 1250 680435683 680435699
    0x60c150c04120b0403030204120828020d1812051605010804020a0b1e0d0b090a110405060c0309090c04060315030c060c031206080705120c06030414191b 67
    0x15510403614584101d03003a00001032203411011358882d12904005080c507440d588003001c00d88446a00304c410b808002108841c004030003101103941c210002104403541c1712250025111004c9100c204140511084410002d181601c601405082c82e160440b80740341407814015980c44040ca107009403000003401c081a2544104107691249401414000b6210326004820000d507202e5164803101400580c240089030707101c040102620f40700d281c00441d650070800308101c82c0c0130010740203010292509947c1d01c4030340b0241042d02c0840b403080714408d0301d4081030b030038507400d40c420410410791189480007040a400c04041c0a04140c3d00299800c00034a44403042c582e221140c580406440703803581403010010244030740c0e00c81b035000384240341c001c443d17080d01d480240c1515403a812030581500300801c1448642083c205415608114200070103800c1400c40104103603110141011b0140f05e03401e411004600420801e2482d0303482c001040020302da05600302040781c203422a0781110300540425000481d41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 680438183 1250 680436933 680436937
    0x30e1906291509010c23010b0613050d0c030602130f060f08011a09090f060f010804211709010b0a0909020a1419060815011b031805060c150c 62
    0x80054112169507008208860190b0402070b015130401913a9907445001078407140080190440311416080403611000d103250079500303c11311481c01040180540454180c0c6c407000e003000c4901c195680c10340140982000c48001d031094202030f2809000048031024030810b01900300860ba84205808403864983c07008642040d0182110000958060018058040c0d444844a00c0500a4210a00d040a0302c00032480240f0102d91a10441d5481d108000d21401c1c803001c0b65501150034030f4900744914150f03580c0710003610203240740c1100e8414404001130880c05220b882d0703243c0000c030741002400c1c80c04010b09806003005021160003000e40c0d80c3c00003956507160040d81010f60707000f094041464144142c144040c1040540c05074000f4882101112288804081001034a0139507140c245a28217621081501c11010941504018110780c6e0804186106400c4140055241c0303000030010ba441c3c03c1d5103548800c51307004a580040d00107454024800c00040d6440c0018034950380b441c0700c0d9541d509400c014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 680439433 1250 680438183 680438261
    0x70221033a0c021c02060103020a050904050d0509011b140c010201050c090f0604121a0603030403080405090604060e0108150117030f0a090e070521070f030e1906 71
    0x300c509101c8036050009504940b50b2030185204031110740c0d05003200300301c003410010602405600040c4c01481903041c40408100a080d003a501d0080604080e41e801d0365400d00d66540700c08000b408101c2400682c800d41e011211200705003601481c90703005003000720b09081e81c40002101e40c82000c410904035401801101c0c89486406119400d000c914424800c580c00c05910080c0d00010400000c0f60f00e04140d5440341100c0d014014208503204040401c0d01c5144010b01701074403990090004000213440741c0c0841d0207445040c1c80c1c030031140e20b07008041005070003c0d410030031807500349070004113522000182044003030f800321803000e901d641e070f403d140b034196181000c01d515944c00030004a40c5221181d0000c1c80f507028946098600180d44440340b500d6007a090b10f0303074000208001110310901d903e010210903000b455103403020b65810201009480c4500c0a8242014103441d890111080c5009204030001d41c3ca80d8031507018500070030314081001b01f0701c290703080e80d1030359041281500303011180e030080c1c81d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 680440683 1250 680439433 680439517
    0x60318020a090c05090306040303020910020a0206070f02060c070602010c0e0a080607081f0909060e010e060403210f020d0e06130201050f0f18010201290607022103 72
    0x841410310b004800075000b43c0703954030144001006800f0141d00c041160074820f07070007030b9001611104407404000c0c030400b64403600300441d48002c101c400036035240ca084a011640c84043c41c0d11401d014030204800d8091101c000029006a210000e0855010342240c8401100c641d035011000b506402080f800d441c0302e018101d002c0d80400001210a400b0f02141504400c0311107803241034080710b21444d007003030071740e0380105404948072000c100c100041400341c0d110078240c19009010a00c0024240c2c0d41c0c03a00d004101a04000f10540745244001e808454400e94401c050001d22080715011409000380d44090516004545009003840309540d0100781140100d801c56010301090b985500112001c2e000b10300000c081c40410007a06003012038180c014100c0000c0b001c26070458100c464006421030308110b84036401410768001070701c100640f8045080d02d4260880c0d410ba1640c0075400820174160086003581c0d8043d80041401000107800009042d07600b2900e280c03082c1c00c040c0641400c1c01880e0300200c1c819 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 680441933 1250 680440683 680440699
    0x3050309040203060402090a1e0b0421021f210b13020304020a0504051302032509020c030c1e06090c0d110d0803010909230307030c03020a1b06031802 66
    0x906858590010350300010001c0c400340c200195400098104807107039010f03411070044160014500c0109c1c8c0d0850000307003804011542082c0c941401d40709208009940355443c0d8140300c1541c8115510300b64681004d5101000d0500d819044000c01b400b4425010030019542001c203403140c504000320b0280c0c032504140a0f10081502a0300c58544020b500094401c0703030310815138000458181c81d14420a80314a2030000c80040d0443c250044c03605246211803e0407840d10000b000c8040a004d25190f00110b0780c96100040e5240711144840c1d040d409901c5281e1302c207000f11a038011150400e107072040b00c000e507900d042e0360b17403505d80482d00e070758400710341501075000f031744294002c0085802081e0303090821801404900c080009955030380d0f4650b1003604161001991849110240032242c2c1c0f0b034106902c501035490b5907102c41140300a80d00d00035003500030100491402c120341014070034004000300c5503105c6007007440c68862801c0348188003003601800000030f14248084080010501440030000c1d00607204075 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 680443183 1250 680441933 680441947
    0x50a0b040f120f020301022b1b050903030d0e0601051f08040f050a05010f02031f08100e070f080a060c0201140f0a0612050c030c0109180c1407030801091104030503 72
    0x9010308030b41038003030b94500d0985511030003584003800100301d00480f4025070346a881c1c00300b501f0518025900d040e0080603207000f02d00c0b0b09800f40381c8040500c121071800e225464140040c002850f43c815100404a03407410005807040d501400619241038860846949200c039000d0300540031400800801d80e4001400c00010602017441c480c030748030501d4000c005480c042c00154440f00d0940e0f50360300202e66010390002c01c020700b40020f0314400c1e40c101032840b04405140e14060138590f44013540003594040a0f5141c0351180304032410800031008009944222a91541d600c484607200e8940e0301095607401c1c20000c2e2006114418866684991104e40c0e9000080d00c2e05d80000340182002001814802d6480002040da80c200b89000250b1502c03e10060429045d03500071325080c6406040b0040c14018010310070700c18444000004c507a08040c0e05400914490268403c44640381006541803071100b00044007414160701a9105060b65003600050051030510580d00303109118511002e002c682060101d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 680444433 1250 680443183 680443199
    0x30e040902040204150216090902061c1b0f180e04140f010f02040f05100c060c140309010e1209030a02040509010b150714010908070605041a0709050a0b040f 69
    0x111800740050070040c107003500d40100c1010030402c104810701507400b500c003200c0e03492003924101000d060041404d01649500b41d001c1422400303502140340e50856446051030041e40d269200b14216929101005a0f15202c000094404811500e051001070b032400c001714400004a0604000c41e0f00c3c101c1e544885556686a039044001e100c01c03262440d0141411000c0080e209016103c6030050b03000d00103954510b0010309580c0202d00d540003d001c2d441c000165494980c1110707159081c03a070091008120760011850841d9410b01c07a03d9a202400320100c144110110151302c10b211038506041107071131820100240c1c201c28000c02007101e83c1940414858001810940c000c1034000384c02000211b90110a90000b851038069682060405078000c00c0326001d004160f4a50034550700048000c1000c00c20340d450b00c12041c86030000c00b4082c2510b44000c02c1c01c02c0000c600c080036954107191002145c0c140f40030003d088484a00c2030500c2424200c1d008034230445072004440c11902000c60b1151410b24100305 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 680445683 1250 680444433 680444441
    0x80f01051e011e091d01060203040627090507080907081f0b030106080a0c090c0507020f0d02040507050306121507031e0204080c0901061706010e030f0a20030307030e04 74
    0xd941048a901140c2c0030302000040012044405504c8a0b0221428070089100500704131500d901d109020314010400706030040103c4061b00d5041c90200028840b0722128641001c443d8840800e07046200c40003e44030049510040c09141701e59602881a1501c000d1250b41e00c0a500030002c5a03000f1301901d02442a030603901c0f1140300c800b0240490700100410003e03084130840d034003032111600400341d00d0f420842038040c5003000e020132030010403a042c41c02c81c0042041c0900da0000303000350241020485203548200b106058960300070000e120074a048840240305d0740098484d80d0188810300e440710207070240402c03020380c1d02c005915200202c0d52455001c402508040465502c001c1500751052500c601d280001c00c00741081000906508035140240715090728160701103c100400d40d0040340e1a004d41c2607480e508200f0074603041143c840141d00003401e106000514001074401c100150041190040050402207009007054840a242170f0905807248542034008001030701988d000000ba25150380 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 680446933 1250 680445683 680445739
    0xa0509030720030f0105041101020d090e01120206120406060920090f0d14010203040302150114040b03070518010302040b040c02070306230414100b0a0e2d0106080f0105 74
    0x10071280616013010000d803c58509071400d603090f0426a50b0180156010089821100400d1600c500c0b098904580d62414000600844640c840107021401c19551058191400900454030b01461424140390010090003148551452a803c02c1060440c1c071030f12030403d10302c07201400000c034034081003501041005c0c10200500380c1e0040c03c18410f03d0101d0518203005000d12032036400183d40341000d04019207010b1807090802e403040745c90302c0144110842d101688105403c185d80105007060f4000c00242810030541200b90440c101028922125649040791340c12a8000e850402c0f0b03501820701400151845a050103015922161041000510a03031050303200c803007180b0134692802c0450181c9000c1c403c0558055848034601d180c041d142d400301380502c84000103140d41c20002d2141031000700e0f00c086107034461041d0300c5d4003a80004051500c884802c0d401ca0304402c0e02200100d8404002c01880e10080c040d045c0010703070550000b4900100d07002014180d86000f01358100d0030480c940c07010180d1030300380 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 680448183 1250 680446933 680446939
    0xf03100605040b0d021c0608030d060e040c03060f1b03021e161506030b0c0408160e07030209030a050715090905010506070b1e01061d061e030c0c030a03050a0509030720 74
    0x186c0380154440b445400040d00512016581c0c4205055500d800d503006504000f59400002c2d00b8400081c9001c4030f80000c603548600b0200b03848003111004401031486d40128000006491700381045aa410b500401620324100d031100911121000d040115005408010325806a0a1449004601e59006070a0401441c506c086441034a80d543e1005498090703980340c3e003030341c2d02043c20b11034032405010f0200054101c2c00d040307254502e80340902402e410090003460a0541c0041c1003402c03078809203c40c42a042e0440215902e07144c0d6660356280032100c0e00c0f4030350002052224040b030204414003c05040380e200034a100e050070700039145c542c078551000e0000b103035486010155400f05046c004045008166130b03290522003013607003100c8005200c002142544600b00402c540f06201341d05500e50104103040c1c15801c0c0d182e0361610101442d0740324201e61060070f0311000c04e0a0011a516801c0148645801181448140c94810015a50340505000204101c0007280c4421140c1c0c600070300f18003062002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 680449433 1250 680448183 680448217
    0xd0809030a0609030825140a031103040b0f160c030302030c090904051501060c0308160903140309041a01020c0f0f0a060c14031e0d110f03100605040b0d02 68
    0x141d80c40400f120b00c06007040340404c50450411880402d003580156800684000e192042031100000810b4016446c030045045140841d20f030041510a51200800c00502c24915983c0e09081c2002030782190100d540e141140704510008100d12910580344036000c00070380741d40401c0300c0c00350b17001c0e0003a4200915180902e8014002c0e003495a6400003414001c0d8051350207007443c54604240103105000580101e0b0030b02010545410010b80c0c001c00326a8490110780102d0310b0840c2c0e00c54120385522203944041d02e1a41c5d901050328a80c1800720007032070400000c840030405400c008110f030401d20b01c2c5540d26030160b001071013100303824102840200b460401c004c0c041081a140280054002070442c0c02c000d0000320f001e0342090401c50402c5900214120312001181131941e40142540c0300400c840d94040c54503008920b81703041c0c103c07503008118072045400c800d41d2a00b845c40d12030001c903003048681c0c0c03464001e03c081c0014602d000d00304480c01c0e1404040d0191402c40000e2104000e5440f5016a110384954 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 680450683 1250 680449433 680449453
    0xa0b07170403050d021e12150f0d0c0b190e030d090b0306030f010c0905030111040e0601050a1206060c020315090303010504090305130f18020c07030201080a1b0e0a0609050d080903 79
    0x1a80305184440d41c0802c03400d130b4072046941d03081019800d0040440401780b070348400f081e940360342d00164405007480841780118081c8aca45400400740c1080d074008908191302084440b04030b11600d61000711601e840e600d280f0710182240c200b50b920051100c0c82004214000c01c04c2c000c003100c0c01c0c001c1d980b085010f0116000c048611003064211483c80e2407400c000307908030388148070707500c0d013800b843c12421222503d0604050410004048460000c3c140c42d06005000030902c82c864011080c1a40e41036120004208540d5282ca020f8001995942c0491090141c00181d200d40051040c14a020f45541401942140c1c06c0c0400d0100801000d2400e50a0000034454030300e17251244021000030b8002c15090940842c6088000c0c2080b00d41203000d000c1150062202e80c6001200003a0308046035024a0120010b484012101004265640b10341703c60b01d040074118a48641c004c0b1000d600c0407002d6607089041e07940c0711002c807002220350003642c1d44101411542004102510080c2451880041c199001002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 680451933 1250 680450683 680450707
    0x3070c140309010f2703051c0309080f0309071a040612050f1501020a2f011d01080c04050909010c0e010c0c05090901140106091508010b0a030e070f03050a0b07170403050d02 76
    0x1000d41c1c01162540d000c140100c0f448d002c1800b4802c40038940f400c06000440781c0740e591030300c18014080b900b6222440440001c0080c1c408000c08001010801400c0d0080e201448901c400b641c041d014000101d0014004812500c04a12809103d070349885031440c3c40783c80f0131091580b003600110541341184981418030000c034440b140c1213000c1902c6480c070034040d02d03004441146282201c4444c1414006014481191000300504021231000c0c00d282107040d9554260340301c001401180c11840c1c00400050800c0342c2070324150301000d4011000d40383c0040e2060070b1401140d1b485005400100300d07185284080040e070a10300100c68000c141100003295103000303400030b0002903500360302c90f90010701c01900400800050031000321002400d03261011342503051895901c40ea00c03c01403403008240c0c0e5454800b2545406100013005040424015400385075241080d40d030b030344400b95080c0c0c0c40e1610500454038a50041c0e91001c8189100d146034211640c40341c0381a40c40d038101c0040449025000c00414845038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 680453183 1250 680451933 680452007
    0x10e0f130c03050405011a0d080f04030c03121215060804020303090603040c0f1a030c07020d02131e02180d05010609060e0403080a0c02061311040203070c140309010f 73
    0x42102c1c1e0b400a41c41c98942051400d6035940541c0a4281814020300449601d96509007451103400c425920307541c100a01c81d11001e0300c2903a101500303a042c140400f00400007030007002c6590203034030390b90383c2030b02c0e2961040c0c40101d0304860172040d0441034520081103600e0044110035030040c0020252818004141d000c2032007584221012140d8074045002030202c50310340403403103018003010142801b140c1250485c1d1a580c1c403001e49002051180440c8040c1150385181a12210660207000e854500c0383c0f001860b0081c1c5004400030380c4551555030413400703800c0d541c4262400c006c5c800c540c50000d10b900d00240160030700040b100766101d5403640c1d00030440202d2400340784010b00d403c0120482c1413426040091465802a02c0b00c1e4105041980c4003030380741c0c2c7c0002c400740c00510340303803c104200702c55180c00c00071010355200d216005400403003000085038014089009290051b140b500380c5d1544601e0f9592a4407580203c1c82c0845e20407502241c8152103100021440e000c8200084255108917542000032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 680454433 1250 680453183 680453201
    0x70905031c05091f110606030604020409050c0316051525140105040807030e030d0215060d0c0b0903011104031239030e180103060908130311180105010e0f13 69
    0x144e03a09600d4140709580c04466041542500700107420300f4101840001e4640c040a000a4407854460f000340051050905c40d082c4824030050445400d001a042c4025400078103120360ba124100720880c4000210100c0102c0c0c001001d020070100c0483c10b60801200680e41c020030540d100f0070f0300b81c080e02a070392007440307043e000d14050307180030340c4810300c40c50018002e07078401100c0742c00b0340c100380c181268050b00040c10b101c1c8500303c40d52541c150f80d25000821044082c0d40c0340a01a6504034200041e42240034005084041090303000f8040340e426140c0c2c0001e1449a480018400325440b80c0005400f84105e0301c00c08001074400142e403040c0c0d10640060010f004003205d1030300854948000701c0800d60080d203800b108240c06c0d20050307218900803d014a0b1a0b60501c40a05290344951038801000301100803201408000c40d0a0920140c4a052880102c0d8445080354054540d1003004080c000c44510024100c6105039185070304220b5417400e0002c03040e01c00e98810703040000f0a61380c149086090043d8414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 680455683 1250 680454433 680454469
    0x5130b1306031103060409060e160f120b0c0304030c02180f0a060609030312060305120d05011a0901030c0201060305100e10020301080c0603100f090c08070905031c0509 74
    0x549101184034980c01196a219034107141c40c0c0440d0b01002c0030b8001c1500ea20a0040300c00280000e504c0c10b01001500080310002801e0003034a038507400c0035000540f4682518003025942d054070b5200c800c2e082034859487d5026148000c8100041c1e280c4044000640e401840782c5000d10003d125940441c582a2818855100d240c4c4040100000e09121780d94081c0e101500c80c00502c14246081d80203841c0c8481401b01800b001141c040a54031044075800242c011940041203034502da41d07a101e11411604000c118a20782802d02c00001860b0341d41850208028040b4145685018801d40054000303000c0141c41c5400d5540301c01d80000031400500c500080e085200750003083c0c055000080906200c001c00c000309000d0700c180f005101400c00020401c101d4007050351502e030f036074945040c0103840b030030107600c81d2019a2000e040812140c1182d00545e60105d0030380c5801c0e000b070b290707030605503036000c4140100da405910400000c0c00c0540c10000c198400c0d809402c2013450282c030b51012a100148404101c84 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 680456933 1250 680455683 680455687
    0x19050a03080a020624150f03040803071b03020c21010c020309030d020111030109051905090c0a060816050328140106080c04050d060b03010e010507140c030d02030705130b 75
    0x207015018000360f43c0c401c1030040d1761880203114001341c00b0340301181c4501602a21001400301d00b0350042800300d0351443c12043d42681c0368500341c03800c1522a441141c203000016a45100c0d01803418030281102592580354020f03000c0b5011a40c00d10155000c084a4181021203015665025000a10980d03001284039406165250350030b206051405807640300c0c403011a85810f9242060183c410701b0f0f40d0541e201c8507008500c507102e4640d020000c051441c44192681c1c981020f01400d042c0006483e000c240003610710141155680764182c544080032115240c0d4010b01030785c0309089610600081d94041801c206000752041e40c00c0e12211344900502e61070301455038070002c0180c40c50040308928010440da01e0019000e00d080840120b40e4000d034030600d401640849224410050035410402106001400800a06094041480c0600300c240e40910100351880051803000c003084c0d080b101100c804000540c507005e240c2d80200020750004149200b00f210034400280c810352503007403807401451807461050b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 680458183 1250 680456933 680456947
    0x11218030903050601050a0812070203070b040e0411040905100f02041e082b0e03010f1103040b0601020601060c03080915040804030b01080325020109260f03030705040519050a0308 79
    0x43ca00704e01a0021440b1300e00408082041120001c1c007100c120181d085060384480c601d10210b454031744141c000c402c0c561408100403c0c00031280f08454032840c0a8500340b40e148080c80c0600003201d040c44030142c07076a0012846180f8125040d00200d8001802c200c00515243d95460365550601508980c3c45800c910b441c1d0421140710100458100640c01e2540060714408001c01403d03c84184440c41050107a0107000f108a56801e5000c0705032418140400c3c003d00b00640e08029403035104507000c5a44070040760205000307520009080741628904d44596950103025201a0b5100400902c02036081c82048160f05070b820104a0080c002ca1003085029240c0341503141c4100b42210580010041d54000d1003402c0c031401e10b0301d4964011001c810f1041c507803103030075000480b86805181c1201e0600c05014a40d0309082c0d80d41c08804d801d092165040d00e40c1350f4240d010113612071105503411400901c051005101c10f00d408000a1010200c80703481141203603440012400d07415281d070041c0c5a240001c00c203d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 680459433 1250 680458183 680458193
    0x10219080603060106020a02150d05150103150605040b0f040302040204030b040c090e030703030c111b150f0f0c030c10020403030e01080402031c030609020c0c0f0618011218030903 79
    0x19801c0041180941095130400800954982c18241c000e449449141110741004c0c5800c4119942e5a8400400340194501040181d0003a01300e02c1c240760010b40340a80d03054200c03a44205120513503a0f2503890b2413074240703001c40c40b0505801201410220f40402c020000060741c0741d2000340300452183c6c04804862906080503581c16000790300410001d4184078020b05401c0f80801250b460603070500b8000b40c0214000c81c201c2d10300e041e88207141c40b0707032051607290700d003213410b4800440030000c0c1107030b02c0040782442c500c1c128520302820090050410f0180420300344402d00c400507000c012481e00441c0c1c102407882200f50314214050b80ba04a010b940090309100780340c8d0065a00e1078104080c01d081c107207400c1a501099403900c40000b0518440e04440e485a0301034460b40103031006000f00e10382913485400d04076201d40c50303500c004030482c8030300100154008107060050941c4c0c8004440100c800030000d03048015604c55052b0459142001d80d500c104010094140d01e44514082c007e40d40d215106043d4982 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 680460683 1250 680459433 680459447
    0xe0a0f0201031503030509060f12090a050d021603140a0c0611061003030f080619031a07031b0806150c030306090a1505120a0c06110106091a09070908010219 69
    0x183c580411482081440402d130044100d40d031400c0292481c547e00d800f0007940c4d909900980107860103a180b00d038248042e101c00040c6400c1000d0044017512485240c000f801c1e0380e200340c0b00e00c3e0f001140c90104020000701d0f8261725420107120403003042e143c5503920342c1e4800b0301c21000ba81010303020550002c0b000081c3c00c2c0401c800c0b1ba00c1140d20311003140060039038602620310341c01c04010004000c80c05000488d1030710b4002d00610000c3ca01111321105940320707e4405140041e8030030703426064085100180481c0e21a0040c49900c5001c040c1ea031688600240044135540e000610380e98100420f524402c40124080000380000c04580001d142c0741e04141d4200040404054001c400842c144800910000b09985800c1c04488040301c0c0845d488a5600e0b100c0d081c003942c1d440c00b03489004203000009040350401c080b640c00b03050100080280c00d48843d41e05044950000c441410400d000181c1410b40c1170400b091500030b5110300b44041c0c802d07598900b50f400c0e80c1c04000404c002003d07a940400c00c031a08055 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 680461933 1250 680460683 680460701
    0xa272303030c0a110a0b190b060f27010f11070e0411010f020a021c03090b0a0302070506011502100f0e011b020c0909150403050f070b0105120d0906050a030e0a0f020103 74
    0x1420441e13009482d268030082021f070204100940c08004110000443d6222402c0c601c00944410748441d1120780700c82e450303000500300302e00c04850004401007001004c0b0704068030410586440301d101d0450401114406541d080400c40b5100d040004910000c03507907030046c0f190b48500304004400383e42000051407141c510500ba0299807207403446000603030303c04120003101503c0e04421141002c050504940010b51640580c207003100001d03110001c2c0c1c5c0c0c550000d00c5003d000360111030390340c5d03680c540e400b1310518045800401a0011450582002e03600d0b0800030b08040340c0403011030703000350000c1d006007151082e00d44070310310f04e174110803403c203a030740510071818000350498011b403552074100c2215813660bc07000c404d41821080100050105800340c02900da0141c12844125200c8a092828000901d8280074840c850f410384a003099459000280010940141e66a03c840ca10b1074039034292003d030480c403020803d2507141d03041e030445054100a030b282c030300707014607100d4601c60340500000d02110002a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 680463183 1250 680461933 680461967
    0x10150f08010c08061c080403080310061b020f0438040b0a1502030f07050a0605130f060b030f2a061201061b0b0703050a272303030c0a 59
    0xb500c40d00815005100c0b00d13030100040d03a490011a8403401c0d064260442543d009000281c045004000d000507072025512425014088164103a1520400c1d6086038811082195610036030042c440103090070055080000406080440c1c5007400764016407100b5501c0c4421400740c44820b1990780245894448009481d8050350100060302a0401080ca0a0350500591043c012a00d0b85030030194400c07c11540d904200102c015100c0090f403502c140c440030b600c1002e03215181400c0200b00c542078483d050602080c2e22420b115210242a0b40d0040a803901d2418594103020300780480300710f07a0303040c4041d6204002e80040840250300075015415002040101c4600800c001d205010070483e00c3c981030307419100d0504203015044011030340108014849140140458400e209001116405400580c061a4500300501c101c1c0031203039800a100501c807240000300381c280f1405401240009410488052902c0d40e41030a4400500303049145034800e44845021070340c0010a20403240d80301c01138150f120080303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 680464433 1250 680463183 680463191
    0x405010f0c0f1d0604080d09090203070903020d0c080d0e15040e010614070804090f0f2f0c0706020715020f06150f12060a0b09040203030d0e10150f0801 67
    0x41e0007051410001c402105000c03946049030780c100c2200b004005403600c0140241c1d91152254812625040c02d61400c0000c2060010040f445d000c41c0d000b0b4074407a503000d966100f0701e94655000c110640a0b0010b0640c1e4000c218400410390b442c00340f0450350344911355140c070301ea01200b400900c020b0101d42e8000700c40ea901c0612051000099005600b41161103030329240104411181c0c0350041841070720402805910300190000c1c01c0311058100d4a00d9150700501084100a080401400d40d09a241c1c0680700c40c1e500b01e000a02080d5035003030751010700100b1640a0400840a80c01450000c0e240c100d28050b81c46004204044180b482a0070141c90302840a41040340c10300c07101c0d50b619400944020508c03040d1010106181d182d030708250406031801000102c000042d801d85036114201524503660032401c0c0b080b030f800b00c1c0c00c080c00c540e07000e00c0d0302900035807030444060210b00040954902c0d4203614003031070501c860130381058017844003001c6444003207141261501ca804100000943d000d03200603414 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 680465683 1250 680464433 680464451
    0x5010f051509041520120f01091506030c02070f08010218060c07030f080f0a0305060f010c02010c0602071403030708071206140906030708031b01060f08072c0702060405010f 76
    0x804c03518107801410194002c0340355007441e240141e4001008011081740ca001140200644864800a60151402c5030400700703583d88818603c020385415140c082c0d04410b02a41c10482e00b4840d6011104920091040c1d60700152540503070000034040354403004540c2e4000c01c46100642d4460b03141c402c100e40845441e4078082030344e446643c413007072a0312019042c2010b04200d0014084408100c44822904145580d0b841c2080e42000e00108425070700d40340103c11032680b80c00c6550051541007880c680507102d80ca01c0000c66651000654001d1310105c80f003000c050101030002d50200040c50192001c2d0311984007030314007000020212010070780290f89a40c207103a410459031740e00354200040034405889211840e81d680c404285006da565200d401d6078400001c0e050a0791803114144940014420300901c0219602c446200e040481d50003070b16a140c205a400300b2042d0031840d41c80016011241d01441c1e561030300c01902512107021503100c40580c00190401c070421000b8841c0760700c1d5005d00c00d010805044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 680466933 1250 680465683 680465693
    0x515070c0603051315020706020a02150702030301050303070b0a06170d02010b0616060218031605031507140d060302090c090f04110306040e1011040e0a0509060c070f05010f05150904 80
    0x20011000c1c0c00440000c5c035425001031181c04846075603400600541d560510079600950f25025000708008c120612800b160005101100b2241207a00040c011410030081da00c0f0100c11881c081c103500112a66a400016802c80d2444940d030514000340c05804013003801800071782500c0d03040c9950751280c0c40c104090310b0b4103440034040e00c1c84190025001616054030300a00365440d20400f030002e5052180c2c0e105a001d40e2200d03c0b03240c00b518426001d80d120024060b05080303e0510550710384000c15035903090050150f4a80000d003148040518000c91101da498000c54042c480c19900c0d50303142e40380003500710103a0030850740da020a01415201000000240740c160382c142c0c000901042d03c6183ca40f51b2002c0c2c040820090800c0741428200200b08031706101c10301ca0002d50091040c0e840c01c04210001400ca034485d8890f50784a080521302030710446e81e481c9011b548550100e44101e804000050295010440034415041003800486d4001402e0074214004091044284200ca119048581c10440010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 680468183 1250 680466933 680466961
    0x30225051002090613140a05031501050d030212070302030a0807020a0c091a090108030d0b190501050922091b231c2108090d0f02070515070c060305 65
    0x40c0501d001616140c94000203405849410b10004951407125008100b0400349000c18100d00301c1241d45902c000d99590506844030003039601d00c409110715130300400050a0400f000c48a840c030905c1502e031540d03103440010b1401c0d0402c00059005078008074558243e1900a8503250700300d105400205190461907407a040d241d00d0794000c1046050b107601c0c07040c0d81091580754000d0017840090400183d980c55003c030301d960f0b0300114140c02501d800c006080d04241410b41441151a00c454031700c1c41c401d800d040055130964042c4d1045a000300380c801c0700c0c07520b00040364940c1580350341d0011701241c0e400c12400c040a00c000c2288400540c81d0807003070300b00240d40b03030064035050300202e4000311307840e21a162001501b20f210440d0308203030350503030f074140744040002c84050380c00c41c4d800345e9149660003050707440e049841110469555011340c4c016072101c1107542c0121030820704814244100d407070443d1907202051224541040700c07101041c0c04100762081040c501c071004050807061a04002d145080c1514104078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 680469433 1250 680468183 680468203
    0xe100309050312070813050a200307091a0d080d0905030d1409101a09040602090316090e03040b162a09050109020f0910020a0204050c0909100311120c030d03022505 72
    0xe043c8040082034001122182c0d0b40327500c0390050503203c20035135402d2950044c01d841c84542c0d40743c1d07a00c800c050303c2c186031041400300703c00c2e00b0803503103424201503000010040028840958062005101890141400e40202c01c0600e0f5105203a81e100c0c10700c501501c0c030b003110542e500d0b02418106502c804040c41e2150409121000448d43c1c409541ca640c02c040740207104510f801d82e018004d05403031007803d950b034a5800cac0031100d8412041000e0a0004080c540b28044d034081e280c028841040044d5140208404102074a401000b44542c020700c204545465210340290940a0f00e48028003080707200014481d090041000b01400d500d41140028050002d108045040d80b20b007419845d0f21000d503108000340255240e000c4c208120b18181101e40e00341c0c07504000c102c148903281070000500300c10310012080d01100d038000354850300c800f0401c00700030307451f81280b40c0084c2d24443c901e80901a56010446844000c1a40c1c400603075910860078002e04103120030841d0b4004807440110f80001410005000c2c1107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 680470683 1250 680469433 680469443
    0xe06030a0b0a0504050103030302031b0f0304030c1a040308090d030213050603040f061e0605040b010215060d06050f0a0c090b04050618030f0d0206060a060e100309050312070813050a 80
    0x44500040c1c0082c080c07001a40140341c000345001c001008254150340154022000e80c800c40c2c06586848580b40d000740308160059540e42e609101143c0081e000d080c078184058070411801c601400e03800d94244201c03004844c2680020140d10030b0120140b402e11085a400e405841d05520b0180b02e10a90f0308801150300c5010301401001000405001c0c0742c9028041c400d0f40410240044200359544401d95102011100031540c80c1800c00111444e0510032181c4521040c0c015146500b5034043c001001c40005240d00d41141d43d811a5000041491040c5031040900300000c0e2581d040c0170b04c0e00400ca88584000c2c60510542c1c45043c0041e4203480300380d8003143c80840b02c69594020410401030380080070a0368940501c544080403e04010100340460301c4940303a422103070242d80b0002040045001485580c01003010a60016040e041c44220044500d0746400c0100e0100c00d943d0316603280d0341c80007132402c1941110000344007041d50b202c2c51668003c1013100c180d00c812100ca8903031940ba51060540240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 680471933 1250 680470683 680470691
    0x906030f0210021c0c03090b0307200f030a08040c0f1d04030306150f0f0f1d0f0d030507050118110d0c030c0602210705030a11030412140d0e06030a 65
    0x14490f032082110480300303228030125403c0c1c1c000200000d0014800c81c0001c901164101d82e01150a00710b04080ea48261520341c5c540e2444a4503011141500c2c801d202482c0315406280c500840304c05c8100018410719003180d940b41500d10b05800c205c1c240396425040307003032149070400c0108046403813054800c2043e4211105e043e80c0d9111450141d009048603401a102c501c5454210321420307410000302002210f0a4a904200501c040c1048415040701c0b01d5080100c1d140000d20103410b2042c410741001c042001d070001100c0c2c206403000646042c4d8100049000483c00a00da408100081c0155464000e0b400d01000260750a03a071a0b41030991080d020501403210420b648084c032044906210043d50850f12518000f030719060000e48403440503005045010720107084442c06142d00c006c48622b0307030700080a5810040c040304100c499101c40328403200b00c2d101c1400082144943e0481c40c241c468414445021038240103152142401c03156580741007404100500c0014a40354cc05c11243d1102060790005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 680473183 1250 680471933 680471959
    0x17010512210418051909031b0c030c150f0305060303030f04050307151505010c02090609041b060c021509011d121e060105150409050a02070f030c0209010906030f02 72
    0xa0150f5071004968070b01004084441c800d00b40d00840c0240386042852480052564514043d6481c443d40100011281c0140002602d580c10906034800d01c1014080ca40565a07150f8090108a90300100c184091407044403402d40e4003c0080d8106445034102807003985003a4001988038000280700d0424600141d00050400c070313003403084a104640c000180c100c9a48040c0c80314000b01a00c00e4049400288a040403c6541c014a210391100c0c0e4010140c011650b54001030001c03501e40500211005400030303101d940403842e98200b810142c49260f45041c0c0e00c2c03d403401080040109451514070030340c1c041003c0b07083c3da40e00240d000c004070100010241c00d02d2050340030500407103851200301c2e801d0203025440702e2115803201800b00fa04040408880850b601c4000300400c03120851a140803025007003200b0410011241c02140e032046501c04014241506500c13146007080d91910b0071000160341e10410021850030201441c00362845040c01c100c00c0d421a55031002d4407148410191080d60020200303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 680474433 1250 680473183 680473243
    0x70503070e0f06010c060e07050a0503160b07061409030319140601212a05120411010216091d06280f0914070902091020030a17010512 59
    0x1040178070341e00c200c040249544541d02181c55070194046d40344580e0b4440d5001840f441e00145a41100601c81c4c00d400780342d4a40804c10b80d80e54018602140c0301500e41132140003070b03c8281a078512510b1040701850340c900d03200780b40726840e400020140001e685088820380015607040b00c5164044428208000c141c58904c102411160a2400010101d41001d6a030412540300348030344505020428003140c2113130340843c021341d458011802009800129000010081041001e40d10317844c4078180140d40100b40100e409440c0c0c2010390f00080300407a1175000007070501c001085a204d501d103640002c0d0400c4c0c00d00e050358242d47c80b441c4007010700c1c0130241d2420300c4c91034003150f000030500d100506041048800078a4647e42036401c000030141e0701c3c05118000503001590f4001c4a07130b0350000031301389161070103400e005076000c505050b04201032a2004102401c2080104000c04000703142c2c1c1c540103c400840441451300fa00305800c074500030901c07590000b443c0c02c00000d14244152030046038440c800d841c82e0030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 680475683 1250 680474433 680474447
    0x30b0414030a0e0603040c21030207050a03050d1d0402041401180e0a0c0512150102060108010507142a061012172212060f0203040f060f1104090e070503070e0f0601 72
    0x1001c2500d103152340382d03078111001031094011964440c0d000d0340c06c010f90300c07010060003003014030010340b031508510303034036440a48203001a121150440603079640118801021604a8019400980d160f0001000404541da0056402c841e485800038a8451403410942ca0640488001c0c004403925901c13491003070495800784042c2ca2000070451854a01c2d8038106e01c1031030f105030300324510381c2c00345c01042c001089120060040700d10682d441e460303851b0004805414101c0c1c660000350741d100d50190394840101c141c40407543c0003040084920080c034250400f01c08940c50b0801c554404a0a081781c01d409000040302400d5480813160281c2e041e41c0c80307801031a01c018403081070a100344218103c0c2d10b0042140702c030449008540034040d050400c140a611040501240f000ba00c0240c0700d2004107603081c0c00182e154005101e84405184007203600c90032a60f030840640c0040d000501480d4484910092381039042007004c00a1804500900f0a203182403141c101e10b01c0080c240d2080a00d83e007000514503400340704 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 680476933 1250 680475683 680475689
    0x506030c0d1104030605090601060806010e0105040504140411010509130e07050307170705040b1f0302092d04020f071b1203030f0c030b06040e0a1401030b0414030a0e0603040c 77
    0x5000d008a8000c0c002c880c80c564428001220b4240c603260100d5616000052a641030b40d90071348902c00c11740c407040019103d00d50b030004803d04000c4104004121502c1d20300840c034000c21a01041041c6003003034944009000c0007510010304100c400c1c0140c200b10364880482e2260b03000e200c41e001807001e401d15042c078200310990304900e415210702030b8000b844240c0880410709092031107064030040790719501004156440030f01420751028004117400c401c40030407420170075440d406045c01460001d2200100b80c0405901c141a800e5100201502da00c2c0c450030320080910642c200e5086183c40900b0306e0624050203800400351042100c43c1403c020688400680c0d005086c0000d6200441c05e9907140046c040e195445108410f60305208039508410b0290254155228000b4902406c103800d00c1d0401d020003400601a000e056220036100c503a00900281e070301d010714010541c070070080c541400c0c681c12194070252000c0b12540704200e8203508030b621090a0310100c070101c2e80d059807030321681001b411200143d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 680478183 1250 680476933 680476957
    0xd0504090f06051011061b0f03090708120403031803031b0c1a0438091903351213212606060708040b031f080102130506030c 55
    0xd01c10810f916041201802101190021900180d403100340c101544103181c1c0c0e13014601f1505020000110146001940e808440e00007140c1e801940c0380d040c5880e16000d80501c111146001030103000341a801a402040c00d0a0000b1140e603891466030000c09100c1880040098805008009810440d018021800030202c2d200e50700303040820301c0d905925692040c46059000c10880a0703278006009031851000801107414000c2440d003a400080b0f180c0c1d80d200d90103990303002e0880303a00300c204041800340800c007850217160369100140741080340180b940343c1c03400e502012049440c080101c01890034101d03400303c509c2441080c07140d140c51002c0302d0096229000140300d01a0b6814103000003d90780184454a0480e942d403049010300c035003800d60702d16000390006904264160010ba4070f8100342c1c00824038140f140034114035260341d440384c1c03192a070403e03110521004692142a401c044407001c01e503000e8035a1400842c5031a80c4120f81d03988003a924482e85004950110004002c01e00e51402c0d038400031000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 680479433 1250 680478183 680478199
    0x3130603140703180201050d090209040c06020106060503390304051b2d030c060c010f050c1903050403030b04090807050d020a030c03051318020a020f0d0504090f0605 73
    0x1114050040d003280c800c4020307450001000906480d10a0050380380000792140d140c082a10750b50011036082e8010748407051b50340c1d00c6210a800503210745410138030440c080c0701503100441c2010b50080c250749140d401201080310070700034059800508000c00103103005854512000d668910051401030340d0312103551168034004010003052080c003140010b0b603940c00321040b5039030034400da0420250720640300d054108101416410007004c21283c0c191459513400400b2a900914280002075455202e54603907a11a51036650070340170070130640580c41d00320381103d10090a28100c080040a00720910b02c04404050b1640e001c20140350095105105550300900244000850743c01d00700c919030b2012100300c5240c42120002d60302d40c5c0c400b099421103154556142c070800b00550320201c5a03500544464203070f00d0f1522070b0015a10000750b212600ca10720b01600543c07100c88210000c0c2c148111402441c045030400b00c401103e0587c480c08880c01c1e02d03911400081c1992000c0d004200500b0140c2001c5c2d000454 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 680480683 1250 680479433 680479439
    0x90903031103090a0c06140f1305033007030c200a0b04031b0e010512030d0c031a040c02030a260c0909090106050307061d0916300e0313 60
    0x100c2d001d0004d5008505c503030880c9999070130459480c49144400d1010200034410b035540821243c0040011800d00c02e40d02d18007580300c0d40024107003400d580f043c0700420300e00300942110b0042014103004028811158a05001c02034901528039940144010030066003c9091040d598401d40c10381004100900080190b40d25000e000786168403d00050382c104011645002c1c2c60160410f0fa1010b07203007410310360f00c0e0070b0b480e10b01030124413240d115418440b40424000f011002d400c9100d00c03164132001380d0b0040f0314041c1d02140061401035405000e030242c6c1c1007034001186c0b180c00000b114007006c0f161030080b144031007000a4203580e41c424200300300c0b02c88404060042500428000d8090000308071002c189a8a030946924225241c81c810706415401c440020480d82e4020180b041007440041c1880740c58403118000203800110450300302040c0c4241c008038594943d445480428000444182c03502c001e8500b080c20400c09500c180c084591035140c9803040e04001d41481a900101c2c015075101d100070703403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 680481933 1250 680480683 680480701
    0x1011100c1224060521090c06092101050a0e01020a080718080730031b030c05030c070929120f1005010614090108060108150307080313060306050901090903031103 71
    0x4400c032000d1042c03c0c1d510b8a5850340c00e41150179903000e5054003004111140d01300080c00305a401c00e030106075100404180c80010590107180024510025000024003480c3c007241e0001200c0d0b4442e14256680c0c8103000e090042508054459001603040c02c04150401401543c400c050041e13070003501960044180c0002c4200b041c1e01d814245600d21a442d1040c1601c189503400040c20f80b0001800150309a80e04640c1e104c403000848500f43c3c041e00c3c0000b20301e042620341514650000307106c0d01140e80400303810468220103104122480300003900e08280c002d4a510b4140040c0403e8840324400c0006503010881c0350010404280031007401815114000d240e034801d500100424412140410130f00b242e40c001700c1010340212110a00305848401c0340f81c48410044400c450f005013225800c56240c0c84045076550100003010003020241c00640c3d03150849604503100380e000f0352041042c1030609030103024a640c1c0d03001c0749043d02d43c80a80051100041d040c00c40c0580580004000811800414080000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 680483183 1250 680481933 680481937
    0x41d0703060e0303131b0b070b1605031506030a091a041a04241d010c14030108060c0f120c07200108010b090f1011100c12240605 57
    0x1d0240404000040ca800d24240d22480110303000d190148507500d0750340c001072440f00300b610000240d004007000d494031461200c2241e4020001a1000c0000404014172034042c150b44001c0c00c061031170464210b040003003140013400c40c0750b22000d20500000c4002200c000710b0764400101107800c1504491000c071003c00607000a001070b20155003040c510320005c0444091688064020350303200c0207040220f20761102d0b0403c01c1c403032050034104071900c69a01d08005490b890722090340050540000071075060000010740040d2110b5000c2c52450380610040042c41c2000c41c010368000200034545036106c82022036030309a8400c41c2410f0340c05d005440300b070024030481c007409007164038030400c0c0e521000203442c1c80c028151028860341c0b6002502040c01840000301e04030140c0b81d0688090712919010704460000b80e824954940720000103a144083c68480341030400c0f000b4040c100d5000c0070424800b0340700c1c0c010101a400d030007070041c241c3c03924414124401441c040d51800b540d440740300a901a02c0f50001003442e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 680484433 1250 680483183 680483189
    0x4080304150207080915070b010b03150f0303030106051303060507051e27010201090b01150e011110180803190506010908031207022a130902130b041d07 67
    0x12148000d81d40384400328801c07a40216000080a8202001c4208025104074045c0d241ca051100c184444070000e000c2125581c043c058403441381d0303224900710244441c05600740494a10407140c401503854039071404400ca9041d5407151400320b98600000d1040782415100c2d80c40104400d180608000c0d6056000001e0030780000302d5004030354203d0070f10011440034061851103041c200c00a045001086605c1211030140003018000402c070b08816465102450b0000d07408109600c0e4140c024288660307100c400201002d0f02400d00c0110301c0a103c04142c4d0f524040700780c100b1069030710302c412405030754442c4010048036030045038190380345010301c1b000c1c4c460090300344406545401d000103e1055030207407040301d00790340030000110708007510f08845522307012002c1c100c1002c1d03002d0703075141c548640c3c02c21001c2100d200c12000071980105c411424044a494504440802c1c02d01d0420000c00503602c000550a1943d900300d008110751070b400c0c000600905107440d03c1881c0d01c14452585030280c2c0042900c0c021 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 680485683 1250 680484433 680484443
    0x5060915131722141918050919030305010e060103020a050a05070c03060c02030702041b0c0303150e010e01060206070e09070c1a011701060902030c0a0c050106050306041406160e0d02040b0904080304 87
    0x4511032412020f86011b000340c001146200d80e06822403c410f0344841d82c40304034141140d0a8014400d4021003101ca010019170010380c6a1006111041511030001e8000c0002e28085103032502d82240241103000724202d403410010f0010303905061054000c020f001441e0440300800030301c21111800f035901c1d0310502040703000d1400d0503000001c1c41d4107a50003601c0403207543c40381110100240c1d0101c006090740c2d01e05404150358900041111034a0303044090281c840b03040c065001c2d50600d10040d242c80c40041580d0100b14140e41c001e01240c40d1100816040001414442c24032806407508800e007242c1441c1412440030184000071b01d1000400454181e280004020015241c55940c84400c1c3d1000300c0740b00c16000030400080141038420300031044018003a000002e18503445000080c1000c101f600c00355500302c3c0802d08411600003c2c4006600b249000800e00007a0000c2240501043c0c0003001c0c00744076aa11a4001c2c0035074640d41c010002000004040080d20b2034107150400f4079810a480545d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 680486933 1250 680485683 680485699
    0xd0b030708100b0a031506080f070510141b0618030c0303010e13050102191d010c060221130c060c03090302040203040f0506091513172214 61
    0x102410041640400d6030388110141458900040c4102c029110382c00d85150048550b010000104050102c40000a24001c001040c81454581e82e40d243c880c20021205c0742e9089848200031560340d402400c103042c6024103002d01c8030b140182c0b403415503010304869001000d5594405030f203201c4011480030f12404804410030444401000307500d65034014071800316010390040006001d940c000c10200c6600c4201ca640c070440c00c04250f03a0706401d9800209020030200745101740040d042e508078450305440320a194454080d101a100000c000c42440400601050380c000348400520804032075a50322920035240000c802d040079001a000d0981400003900c200390905800300e21a8800e140b032801c402d80559524106034299005c01c0000d41c0302510031600320090f0303e07000700001d0f01401107034822604c04c400361004041c903a0008090450082c228858441c28020031000106980a18103603120404a4561a101025540381d40d040c40d003100503041603256900019030405800861000e00300544800c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 680488183 1250 680486933 680486951
    0x2091f0f05040608010b0d0e1002090a0b0315090a0213030309051018062a08120105031c051b060c0703031b0e040b01030f321005011d150d 61
    0x80303050189010f44000201110700403c03034600300c3c2c00600140307108040300180070031151480504e08030308080c06564154011590b1003c6180c940b020000801c8205c189501d10b107041d04107214611301034130480b84125456008240c9240255041da84a46092511014000e841e8140540504214072030b082c802d40103440c002141501c07495200c0482c4d012070700c204144030b05010050700d2070046106c018000340c660903500502c0031f24225543c401140107980140d500e01046d81d0314104240705802441c000c0d403050844803540d0740d002075040b250398401d141050f01e848a00c000c414680c040782c0c40410040c0b0683d4280a00c019040c8000e011251280d20f0030441d151114050390100c004030030804c808036410440c4184d07141000d40003c14411414907000907a6071845030500111080b0f5041c2c43c1c11503030000c8068100300d180002c03106c8103100c9030030310007114909000744021001160140c54100403945000b1003c00300202e4020145400050102d006d150a40c00c1024840e048905c00c001c1032801c001040c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 680489433 1250 680488183 680488187
    0xf120f051504270308071103040e0402010e150301050f03070503011d1c022a120d140f070809030f0604060b211b060d1103040b0c040e040605070302091f0f 68
    0x25000b070340106664852a400e0314117642c601e200500c00d01c14020703013034481101d40d802480240003400325014a220b41c2c2c00c190000414003d203004409009900d1220b817031160808140940e41120400c40b1030210f42642a8040ba041411039800301d0b42643c200328154080320702c1c000e070020003040c00c0ea040382c00786030500031a0741144101400c001c02507041800205850007150410400681c060242c3c2e0442c0c2a128010444010702011900140c0d044801650841036010000c0b10603006100b0910b82840c0306c500c8058228490090014010100020500240d072428403402441c01c0c0c0352003d48110385010305100001d0201c0203c0319126401010444031820401c0c0a40c040c554240d80040142d2810310443c3c01000d62101ea015601c5101809620aa81c601d8000e14540c228001c03119a00da00300342c9880304940c00050541c0e52201c1045c04140724594851444942c029084140400c650302d4655090b80284540842150031419140310401030100401d0907091520302580c4211041d0300410007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 680490683 1250 680489433 680489471
    0x80415021615060e062b02010309021008070906110c0d0c12080408010b01110a063308010f0203040305070b040312050f1905061e1309031106060d030f120f051504 71
    0x40341c04081c6c12200e054410000ea0100042051046c100060035260540009111a04a2000c400059010010852000d0f48101c0340e000504043c101601303809003240120361500c2815140501070000c401e070000034402c1c0f0020700d4005121800d0302c070140b036050341030800f100e9016004017213540d0309001c0030780c266503c50524200e801240c030010b0300007031a007a03480d00064048404a50b032580d042003810303090594ac1140e40c0c1100c0c984001290b5402e4581441d050940ba003d0010b08600c40c4113008101c0802e401c84c0031a48800e0f440181303400581c0c0d9525080d00e00e10010301d007c00c3d81e185001e08102a00e100100a24018803891842ca0a20304220202c4c1050f1074040300c6207500300600404461400a000c194410304c40ea0040c81d02c07600045410214085620540003600050205031180c411803100748103240d0042d000b5240040c8140c4079803400b40445804071020010001c441b0240740c80000142c4c02090038a035000014085420131079094000100c41901c00342c85140740103140900c0300e070301d900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 680491933 1250 680490683 680490709
    0xf05090f0c0f0612061302220f030f0b07091203030b01020606041a040f0b0907082203080c0c2518020705060c07170301080715080415021615060e06 65
    0x100f20b600d0502e5404518010300000780403103030004141c02d40110054204d001030406079502105043ca110503c0e2049042c1b0500c5900034214071155090078800310b9250585021207a4200d06640341e95110120126085842070780032001d010400d110042c100b584c16040403d940109900310b68a54503601d0800044800d01c104006440129405d00c4000b410a500440c503040d501c0800011384002c2c801c0440e940303840c1101c2e0580060030315000c201d8103828a005111100a925141f500e0417a00796401800d0360341c02038511071a441c0081041a030088040010340580464042d06021406003100414404516400303900044288516205119a082d00c00d94004542080c000c200030b460781002d40c0d1440d07000c1d031130686181d081d10f8043e502e1001c0080045008010040007000381502c0d09820003004035002000f1030420a8490900c070100d061601311020342c2070412401685c44c0040f40c100032248503018002400d0583c4059010825103240c0d1004089400014170030750b20fa40d0310020080040ba00784 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 680493183 1250 680491933 680491939
    0x2061b0c0a0201120f02040b0d060b12070302031003081b0106120f0807050c09040809101e030e1c02030c01060503070b0d050703110c031b0601080c0111010f05090f0c0f 74
    0x41e4006000d0340c85055203580e040c1604100280c80501c81c502001664016001100b41040008035030b04142414410341c001403103655519424103200d00c1001c88000e002405a600f0540c020020620403800064801c00030755000100d07581c0d9088000701c6110400801e10403407403a502c1c1c994001450103004801c58045030740000710a0070b440a6545010840c0c2104009640c00d10601c00000c14648480b0b03880c0e4050b40c02010340c5500e62104400b0402d061030180518020042c1103500840031180800708400256031710704020480500340c19905182080000c200c0460790181c0c06200000c03600030000341a10f1101e0002030002e15141c00c24150b40e450720344140200208104035000d87c0c000c0300d0340102c0d0440030514000ca00d5012141c0244001d030410a071140c950380000848412000d402d28140002054980141841d50f24007038080d40c031035409482540c144a82c84146215110080d41302808902940e48200046d042c03801030075940e00e20810780103842f803051144411840c90400d8100540d52401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 680494433 1250 680493183 680493193
    0xf05090d0c050603010609092d0e01090602220b09090718090204031101020c09091906020f12091002031009020a0516110a0b0702031b010203041502061b0c 68
    0x50000e000d810400c6000075070381c540707400101150303d03902c01009500030102c0ba40c030b6680080c10884400c1c112142e00d80c0361607419203219050a10025804007800c50820241d00004014900f031140a01601c10888020300c0241300140d01040201c00035101c0d016070005840e1400c10941310f4051803158803aa201ca88c0e0b01900900008005c0c921601d008140440002501c582c035a58138800c03142645c210390000c480100e0003080c2800c0c2940e040011078112881141d03150040c0c00e10070030702da03154080c0c003000091011040c040d40e0241310140e01112004108140d04a940d07280c2c0150420014078180ca0440d000d0040798a40c1828640c51300036207010309450901c50f5283c0c1d280038a00d20003544518004401d001051115248102c4200342c40b0f120a4021003840140079240340c02c0080c0c1076a281c0007142c064109210b0350015880019030241403004a081e03040c0c09605060060b8a540a55440500f81c4c11140d101d030100903601050841c000c80c10045047c0c4001503620b0021441d009540c4a0b40e40d036404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 680495683 1250 680494433 680494447
    0x90307090f140708011d060f060318070305071d062b082a0d1d0a0b030405060604050702010c0e0913050307050a1a04031e14121501020606010c0b1e01030b07030605010f05 75
    0x427401c02540c00c441c014640d49164107001d8a240e08006043e40b0694a0f80c000f8a01001000a5101c40d002920b05a1a01b072005281c000c002071022001100042e41041e0350300040c001c040c1d416864169029040382c407658035000c8a5120401070b1025905e450103622a0a130000c400030000289a8480805078a030007030745020784501401000d40c6d025000c4d03401040080005000d10700d20005500482c0203102800062800c003003408141c030000b030040b8045a240528000c0156840050040303e8541243c003031565865040b560b4030000c64200014115001c00100607003040b0001131040d2142e8800d421940407810150401c0c3c0b80607804490240c0810b01041d6402603010ba0b15080c1d0102006c0d6003440096855a98407583d5503400515031004c66000010500a20781c0d03410442c6104d260303091000342602c0c5801e60008040c030340400d4004041e100404c0110780c2000c400d40d002d00fa0401c603030340302c1e9159603500d0a006c40796000039190700c004245400c0b40450554400c1b17900030820042502e5003880c00341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 680496933 1250 680495683 680495689
    0x30705030c1f0905060d090201030507020309031b030307060204121b0f05090a09050f011a0303040b1e0403020306040b0f0a05040b13080d0908070c06020102090307090f140708011d060f 81
    0x40b41c2160410503040f6000c95180d075010003a02941803d0100001c010705548005001c031500944031105542c02880210f0351560005003400d5280e510f80c080e41c0c00720b00383c5000300b0f14500460f10010046400403801050149003005a00a1940200b00f03542c00310301e480c664042c048805002d00400e6040c030100502040c20401480780e080a01c0740c42c002280d000c5500c90b50b06020400044205a0b5150050300c270b44401000c01307084007084101d024506e0246440105040e91007082541d0502600408074034840c0340c960409d0350011078014069820f10300c0c152070140c0030b0900440e40c1c1280507481e40e0205400e035000c0d114a1380301f0b42d8820402c0c0c109450398030b4055204c0420010886805100f00a443d82c000001c2c060a06484d114030f8040e40c4904451800d040509541e030444800c42e0710505ca24000c41d030300004c5c1181105c004210006902d0281032a1001a1591005c01c400e0b140d400800d11900390350103c0c04d603048819042c10705445d021240144000e0742002c0d03d02503400020500c00d020145 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 680498183 1250 680496933 680496979
    0xf1703060f040e101113090e06130309030503030f0f010902340203010e0705010215040b060f0a080d090303091502030403060509160603050403030b0909190813090902030705030c 78
    0x8007500d040365080742c140d40c1c55205441c410800309040c03105c0070400070042040860100050040040140080202820a0341d03a80384001c116461131150b0a10941c01d26004209074005140c0040c140da550785005121003402c04425030740c00c070500c2c00220000901c0311941c426642d00000e02207800c0ca01002110192845003003c000c160001c0041031b5240005035000d1080041c07075080000503020035440d1400180c184030b0011040040305120104010004801400c41d5034408411205404441244400b0842c251150b400901c0140700d0b42c11004000d030b40082104040305d100b40e90f032442e229250403402407807440c0d4101d03200150340280400c5c0000f50b00e41d0040c66000100c5402c42c1c1c80000080560421000c0d1540810701203a50303101400103040c2d140c025000201d0f03095804240c00c0c14041d0510fa515180440807080c1c01c46611000e10802640034115000d068400d25100341040d00c88081e03200030007101c041244203118003900003403107040100ba07010003141c0007001d0a010300c0300c46069400c1d034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 680499433 1250 680498183 680498201
    0x210e091602070b040e150f032e020706051f0f060c050a0506100e1006090605030601023d050c070f08040510032405060d021b06040f1703060f04 63
    0x98042e10b1004950a034000c8080d1005104c18808092141810041c048075103e81c802240e00400500c2c0d0402d041e910000790080e00c1e8140d410321107202808282008981c0e4090310600c3c00d00c3d5000042c0380040c0225034000500a8202014020901090141c4500102c200d8800d09803d560005003c02c0458080c0d5580384290703010308180c4204100b10343d2800d04122048460400d0740000d45000d1007111151001c4503805420840000700b11810044040c051800d0b500c6980b0170480c0001c00101c040c2d2003030003504403900700d4842d09512102d00c18429003c164001030441040102940001c3d03c0e010180030341030140d801e0701c070182c0c43d10040c1e844101944540304020b544048003004001240d443e0319400c03640090030781c0c0e4006044400e900200b000040c0764000c441000b44400c0080c82659661400c407019514072020041e5141c0b00c4000d02c00d1481514200c095850090030208024010300b402d85c07940007442400c1503100c142008101e0211070200340d0703016400c050254821201410258402c00704 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 680500683 1250 680499433 680499437
    0x209060f030709110301060909090510020a0e0307091b090e06090c1b0102040611151807030609110a05010206010b0306090411040c0f0807030b0d150603020d210e0916 73
    0x4262122240c505480d60004580b00c4e00c0400001042031580c440f07045d40240c1828001406110000e4541950f81c4002c6d4150349280c1e6800610102c0c01030190340c84002c040405030070b072618180d842c00e082c0020210b2500d1142d98500c0200f2042c401e034030509040302070360380b040c2c0000520748504060213601700b0024030144808604102241c2c1420700c0d507074920300d15601d03d800540d50b01c2c180100181200600311408010f030784007004a500d0208601d002c20783c0f100514a42500b4a2010110946060321720750010f031045141801d003d041c03220404e441c00c007a040694421440b19034540c012a07907020b00344a00b0034281014804244039203450f007070117034219024240c0b6240000e002c000140449190320a5a4081000c03688140f443c583c1018040f81d2103510b9080800100129101207500c0134468840100701952415016809c000c140e4410300246070080c1080010341114504036142e01031f00128100e01541d210800c250780e62041c0d00681d03618034064582c03d41c44e120f91480b104040345c0ca01ca0142 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 680501933 1250 680500683 680500693
    0x12090619051204050a021011100c12290907080c2d030a1104050319050307081b070b0403150207030e0924030c101404030c09060e070c0209060f03 64
    0x200c0c110b4003950540540e020710b01070100898184100301d200e81c140c88200d010b22064400d0280001c102091102881a50800224183c031030301c24102c40c510300c642442040c851409295011250000b803100d1400b0401203000502a14860204023005404a500c80001402200010070f5a45441d01070208148161a11291540c1515480b00404a6400c9c01020b508010007008903010680c05182e10080c080304440303103003909100110b522003020444105038460020f8240301041801c008556035950003010071038807180d03102d12802c59a1140251450700e03115544000c280300c03000004890840f6801100c0006582000c14140040d41100500b1307800d119508902a681d5110204941c0c407039002112003034280c590480d03130302e5882c0d103c3d000c04034001e502070303c0e0049440e240e00850036882800c900340001c04103200c566801052255400060510340c03411b0000500d8042c44d0441d4059500c1c00b245040340d6581d0381c40032900008024800303540a040c00f000710700d10f0304144955410202c000f4003950 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 680503183 1250 680501933 680501947
    0x6070305160210030515180714070b0f0907060e010903030e0613030302340501080c0d020c030a0f020a2f0402161110020604120915020706021209061905 67
    0x11004118000c000012a854004200b0b00d126031400c10741d44001b0459101107003541980070352034411070003000641030015240c7d080c050b025402c016034038459440804245035181c904030f8188000c9080d100c0340072a121381c100100d26a4001c0d403038443c4400e0181c4d1040c0d401071442d2001c0390183c110012454010408001d844460b82054030304c100650b020790003c2289102015510b40e61180301852041802e8459040384200f0303d0304c03000d030783c221072003441d1000c1c0c1c5da10b441c651040e8512400c2d4008460a200040c201541980400902040c90b9140c032100400d070310a8005176210000304600400c3c00d89490b10002c1411000c40c0c0d010f1741015081c20041d81c4000c01000b00301241c2c0107540001c41040c0701c0801804100000d041601d00b40360558410141c11104074010b940c480011380024020301016880034042e030b20525203c00106114004c01040c038210240184d1204014082c240060084400175200300500c0012a20b070803402404c800d28100c4908500880f80e0030060076a010003404100308 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 680504433 1250 680503183 680503189
    0x111f05070c05061e09150a0903020c0d030f0807030203060f01030f11220f0320040b1807030f2304051e030309010608061e04020a0504061403010b040b060703051602 72
    0x41c44c8942010705107aa12070300d152600d490000c0d001000c0c181160301044801014420307881406070080010031020942c0c2401c0d140a90515260341c07501504030b08910006014142e00c80229012040a80c44032030b03c9859040d421400d0b88000c513030994021501011115981d4402d42c84404054200c05000510666100303810096910900c05c103060301403824150400304c0c107810070301c600815410090515140c5190b40c0c4000451482e68418592002d10700185200d80b42d0740c01010382402d000700745840390540d081e4160901441958402d00091500c0820302d068607113413040303000d4252062a581e03110010710502651180d00180121168000c0c2c03114200360400704480110203285080c0035607102d1030318100031402c46481d83c0c07110301650301103c00e020940360181c940c00f00001c02c00d5210641ca41c4c031400803d02182c0c95a201541251601d2800590320345880b10700103555200320024080c01e03040320300308010344112035100f41e80401e08000420001e40074200a0800d44e01030905101d03411019000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 680505683 1250 680504433 680504443
    0x10507020a1e180c020f0601030210200a03080a0b030606031c020f071517222109090c021c080712020705010605091305060403050a050904021801111f05070c05 70
    0x29202d01c10384c54504404000e81c0601580901c00100e0b00107018561441d000034400000c2403004009008500039464002828152205a1a580c25045404445070f928005011500441e80074054626000d12011070b0324010030020300400300103004002e60008858002492031144241c0020b501c180d45085207840e00920a25005154608150b41c009800e08005000b41a8203200940010506c0701003185c183c29101051500100e0000c0d0311034250303074601c1c00c2034108a4207824088454605507849114603404030f00c11007560035042040c81008a102021b03607682440e0030b89408548500c2802c445943d2245130325039803081c510300d4809203011071990304800300e03800b07a18160f480e81d44980040c131190824503445504043c1002200e0800039094468549550010340014100100080d480c0b05a038440c000755480801c000307004550320020312900c600400f00e1003d42c140410300142c50f0031b142c0100810004030080d0700040c48145079000d084440d00618005211500348460140145c0c041441040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 680506933 1250 680505683 680505719
    0x3300908030412050406091806030b0420040e10020903190308010609061407060e0717060103150e0d0e0312030c120a0225021824010507020a1e 63
    0x180c6a50390341802d0408400110359400d0640601c001004100a05a03002e5003040031a00030807080740c4000500500440500140d0380050300540381c540c14003041c00640c560b04402c101c0e1400c5803241804c134800c1440706841000807950030b107800600e044021030382d01e6002411100001003e59003801c040070001c090002141ca0f0540004038454018000150404d240c0401741841d4208200b511122101c03400039031280783c000510503915a684122081c6041040c50060448920b25621001d0203100256030ba4034244800c0d41c038402c0c0c14500300c6640303045100d60001c5010ba000a084030f040a80c0382030780e50300e00101c0c42d16014461304201070b801d03c00d600d0155004140c44100c0c559103403401d0600d65000240a080700d60000e204004500351404040003010304c45010085205480802c2c1c000a0000e40c04488415900030030901000340e5841d11300b814151440c0b811840719100000a401121607024020000f50030540c1803c090281500c112070004094101821596019880300e80960500002003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 680508183 1250 680506933 680506943
    0x4020c070314150610110c061c0b060306010e0d030c050d090510090f1e0b04140a0e0609010501110c130c091d130206040902040b0d0f09033009 63
    0x102060209010a03c14103210701036840b041001c5040003000107100407017280c0e021003402466a42e000031080144258002c1c80d6004001945400140c0e045191400045000c1c65020745408080c80c15481c244083c1c2c0d006030410394408448009180c20312201d240000d00c1542440f009008020000d030042080000c9814140d560300301d5a8a8041801132800110201101303200742c046080c08105200c44c40c4c082102d1440c4601c0b01c81000589100c4c3c980c01142c0c0100441040005000c640c411501400050a41091300c11602917070352000c40e850300d040255900c075488840e02004001643c41804001162900c0c50103940110500f103000401145000385005c40344e6885a0b0350070041034010504000a107012859802610b144200c01001690b00802d441c002c0c0b08400300c1d0b8015901d80d08151005000c1c040f408550755a154030700703040700c0d402040c0c0742d030076550800c90b07815900080da000f8041440c0d031640301c41c107209080e181154495000700904410342c07240301c5101098131900303000e507180880c022 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 680509433 1250 680508183 680508203
    0x20030304030c020f0621060d0b0108160b0f19050f03040c060305010605180d11030f101a01020303060f060c1603060c18170a1703060f03010b0a09050604020c0703 71
    0x34414810040d04141d10140301d22810f20442c6c410042c04e214650942c440c0c14201e00065480000040042010300c00140809101600115404000258041d00020316064107020fa5640380d0103840e6600c40d5640c40c80c4030250a104011810140c05c840300762007062403c2c1241041c290040207204c5400860701564990300d41c04e001c116250b00351260f85e003d003013245042c2d8609204600c2103141550794013090342c003a80c221086901802070b100f20a82451800074103841c0b0307103500840b00540d030721003600d200e0024520f41040240c14078460998000329940c1038010b5402e6940703200810a40a0010942d20b41100081110300b01140c401d0010a0504845e00a4801c0c001d0550600030100c0b00c03100400c2c0240840b900142000541c0340d020407003103030190300080592807403059500c1c0c1800d011900c0203000103a840700000b180c440c254080c602c210703011758040208140c540c0401d42070b50310f00e14509806c4840d4070340c10301c8103907000d0300407035032000001d0405031a0207051050175241524030340c0155180151 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 680510683 1250 680509433 680509457
    0x90112030f0f0e041e050a0606052a0d09031a01030c03060b030705100306030c0504060806270a060b011205160e0303040305240c031e06010309050a0809010201140114012003030403 79
    0x1030386c450680c00c2003480e01e0411aa40c20108054054814924112150248001641d4030314004504251806030403030151313030aaa00e541c0c0d01604000460000300c0b541010300d20b0300c002401c1c81e0b9000c24100c80d0898801920725207541c031068010142c5805158060003503d50100b41034450120104501403181d50004003686142003140b81c0100540109220f07a0601e001045441d00009800b03400100d843e1309881040003100c00110704802d4481d09180d14040c07150b03150103001c0c43d44e014142000c8203895102401e940d001040003241c204542e0306480c03520b480080001c0c5441002880d0b180c0e10050100c03807400751030b5104c245c84c0c051000b00801002014010390445141d12100141d0044a0146180c0c1103042c032010200000e45808a2440804242d20004407503030321070780104445540050035aa02c603510b50904482992140204501540c00c00f2100c1c41001c01c45100c050480d1a00103580d090203c840c0011101403084089090f4400449a400c2c0c078809010300083d07010380e20a40b1a00a5600 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 680511933 1250 680510683 680510741
    0x201b010c21021204350c25030210020a0b012402010c0f20030309070f06020f0a0f0303020405040c0305180a0f0f1a07032a08040b0a0f1109090112030f0f0e04 69
    0x34075501d1801c1c201001c0c0402e2003940200003034020a407035048403040380d01402440c0803481c2920310303300940940808400007900c2541c1e01c240135128031404515500c454a400d10682c240c3d100004081c001546601c1d0000105100303640303012500700c0556041e01b400303a00c1250310345950021b8406c02a290403000041141c2680c0305600700003490907001620f4500a007280300c0741c43e907840c52405840d1014220f03c82d000c02d44a41e0444028100041007000f51484018004000340303400c407101c2901541d001c1050720607010001d0110f00e510751040d0f09500e14102c5599111484610714000c44500c414074100c4800d030008052401e11800d441e550000e940494019044c40d00780c034002a040003205c6c44104540c40a51061070710303600c150480100115912a075401d407005260044180e08914948651400007518100050a107c1401c40d40100e481c0d1f01d811b0780000ca105011030003800301d1541d0a8109007603015a0966040708203a045c0003190050060215060b40d0440c215007521908111080c06012 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 680513183 1250 680511933 680511943
    0x1807120b220b0412021903050a0801061b1e0606030506070210090c0b03041b081005010b0f0901180e010b0702040e01201b010c21021204350c 62
    0x18850308900080c8841911400407010b8060405043c0301c0080c00a60786090081103044a02c1c00c81162a2660400c18100140103402c080004c45c0000e2064000149940c0704000c003642d1115460810001d010842d0740e003041503820507112244a03400091180702180302d600c61140154042c0020380041c0c9080c1702e000b404c021004d21034400080ca400c81c0d2101048258010f5815941030520b50342c0d1703c2d141c90401800d41c00b02c040003110101076860021a1905011801c1507413400458820321240c1d8a406600466000e00f014a24047d001442070340d01561045100305d0100c03600201c54a10130351a1650080582d400f40c000401e200b50001c0d0703400c114200b501c11039121040e0103000700052440501d00c1c0e107180651803541c3c0c0c40303210081030005010000c404507180786800c0e0b000801030841e8245002e4403c224a6180c000c00e4895940035500c108100e0003115241055400c0041040d540c503941c1d828621000800c4e0020345040b52031216480c62060100c9490307101c0b14255545444c51500da0324540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 680514433 1250 680513183 680513221
    0x106120c181d1e0105040b03030d09060c02010c05120606070f1704060806120a0213020f0310050f01090305060109020d110c160503010b03070b0304050114070e030c0a05091807120b 79
    0x20708541c074550040703d980c1101e42d81c195001103401141001a4400007031a600610959980b400d14080a1204021140c1d000c04c105842d144c00912044440c68401d540d140242901c0060300c0c2c0890000a03018038002000b040d085100c0d88280e41051070a885420790740b0b05c880c181e0101030500040038800b254004c000c566104000302c40103c0c1d003c0081d040e80391190b1410f94002d0245288210303405021503550140c1318a40440d513180b90312860082c00d980e01528440c454503010301c228050100d040e500c1103600700709803030300300008241c2646000400b038021b500c20142d00c40855514898400c140e070f003450080004000000c02862450000003162600f0b07103035a48001d11981c5407040c1d491380c40d1004070700102182c251036040c0352269102c1c106075001d040004402c20301c0100080030401000d401124610088000780c1c100c6152421400c1413144075502409038607880342030307000010b00c40c4d5008983c452842c0c02c07181c01d41c0c440e90350302d4181c49031004042508484044141040155125000c0030314080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 680515683 1250 680514433 680514451
    0x181b091406070f1403190207050f01020f0304061b060501090b0a050306060d1b03020a060206160f1b05070f141201020405010c0201050309070e0420090106120c181d 72
    0x1601486540307104500f20030000040c04071508198034041c0b401c0a1098803940c80b00900b2030440d054002c0c5000351a246030740035051143c00d54600c040300e19440003c440a0f14800080107610301420440192072502d44c034100c00204036006100500010424040c080c004d2076092000b04545050008020181c030840c0c01042c0294440e00c208800ca41d900d65070003100c01e0300a0380c8042c82d41450303001c003108000a5003020750030024600c40021410343c000384980c4140d00b48407500c40ea05262076021a080d4180c1d181060001d15104644078117000400059101c40744a041110070320341e9986607000e158401c0b58004403418010400009050070710400703403502e05400c01c0023145018148070010303180001c4035501904210b00407000508400b42084524058400c01c6082c140c54942407500008080b0041014140c81520014241103814807900e40c60603119540c9505150010342003082001f0100900704500f0440d410313409002c9442c22102c104094412581001540c041110304810000005051611 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 680516933 1250 680515683 680515687
    0x914010c0b06061b0f06090d1701030809031e0f0d0201090209010e040f05070b0703030b0d0b06130f021b070b0304080304150e0625020f07181b091406 66
    0x140007072a5203648204110b5540340c50b002c10700d40d14041001d100c00642c5042c0b00d02d0226009607400000d180744104c1e11142111201c402940d41200c5d0155202042080b080c2d1840c0180000388000000d0000c2071005000c036141c40d83d03640800c0d000c2040b03000c0c100619802c01d07810b100803084107001d442c801040c240024441d5103050350200324012b00501c914958516440b0101c1d04009003416609045500681100d00f0b0588556540304564400d00301100401d140100341d08050410b9101038a40c80d42110b446041c595075001440301e400b1890303403407909090345d60000c160f40200b10720141507101158040c42d105902c5055001d80751955542284c071542c0c4042c001c100010755082d04030f0380c1c0598051042003001c00c145510b030000d480d1040c60740c4c0c0c45000380f608000040300c5002d0705101d80480c40c0b4060b2204031454109070b8950400d61217413002c07900026001d020328a4040c80c05c1c032a0115070080050300c0b9a038054940b801100710440308000a80c03503507003001411400d002c152000321040314402c1c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 680518183 1250 680516933 680516957
    0x1215100f061704140d050301181413022d0301060905250e040f0222080a0b040c050d08070c05010e0d030e180c0a110a08040611030415091401 62
    0x30700903141c0c4050b2001c0280651000400b00100100c1065404840004441d40030300c900b08050555002405070540d9207a4540000101b40020b00665185100481c0c040c1c02076107607018045a000100d10080e0782004507900d07810100804003882140e103058143d040030124241100301342c02d482c8140c1c08499060b0070310b82400b60810780300d107003880d1804068090b840d030048030280a41c0c90540d80c10950740c0c0f040c60403c1880b61000b40790000c1c40300e0307058500844000c002c2b408080580108500641d1640d0f0700500c0101d0003c1c0c50501001e800902076405018903d56510000e5480d01103080104d580c5000490040c007008818101500034201c2402e002c4400880507001c160700d2260b64a0107402c0100001c0c62003180e440d90b10305409003503210394181440746003002030700c01c1952000388070100003410410300d002c0b0741d44003264078503047e607201902d140340500d003000071640c0080d0503044540d140820803000036114415000c03d1860300781c13034451201e924901881400551003440c00b49040c8003a0030018 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 680519433 1250 680518183 680518187
    0x406031404050618070e07050703030c0c03050306120a08070f020102071205060415200c07050a0b0f03100803030a0507080c0a0903120207030501090606141c03030504021215100f06 79
    0x410340c084c400c09403003840c084070007107038901d070441c56481001c00d00c00820500152a902000500790a0b010303840902c0070030145401103500003180744014000801c1407000c01e403d450400328101c51040c0940c201d038200c1c002520b030407a01d076208100c115030b0700021081c144211f58040c00a02e0040c007000811034040001904e0b07840d151b900c010001041d00740c0403901403001240562044000c11084da40c400d043c1600c009802c0304a500207201000c3e20f10a04070000351601c0d01c0e842d41c1080e5504210024248090b004424902c3c1d04090070210009400e0040424280001c00141d88140d580d4034003c00c3d14141034030050000e08000e002ca41c10f840b000c102c441d01d40b80d041546031007100e502c0080c10f8040c03910240b08074100360140c0c10060865003030110220a05c00e05070480800d80b10310041002590300b44204210314114180c2484010312014004500403a0196004661050000d0300070080003000c05404c5041043c00c100c859805a0340c64180201030b812201480060300d2409450300f15507080000c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 680520683 1250 680519433 680519443
    0x601080a0303020a090e191b09050f060712120f0c0c030c0303230906090a170304060902040f1b030509100911030f1015030b1f0503070902040603140405 67
    0x6418075400041d150780c4075104000c00c170b008001c2c00440c21030508001d00681140b08400d15816501400e200100400e103040118145c02015181c5960f04494602001d118030b29505841c0c5c0e650082040c892440460110841c450400d02c0556030074800c9801300d2012030844a43c44410300840f442c1903d0f042c0841e400c64100e14440d5010308000180c000742c3e2500b10040c0c010b110a02b062040b540041052035400495114000d100c000244c504135500c41e00910340e20900e560b40a440e4450b070341d010124216902005540290003103c1c0490319961075004030707090321521b08020500c0ca84d1220603031400410342e402d200061190b031805000742d0030310704000c0742e0780c6048000c0740c00103030b41e90415481089510f4102d6004c00ca0054252000e05e5003c034151521803010085050815040c00c2c00c0e810003030740180140302669403040240000380c544010786002c004c0c0201080501c48444880441c0e1603404200c10801003d2a10000d42e0b1241421780040a403012220140000844202400001080850b03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 680521933 1250 680520683 680520703
    0xd110d0903080a0e2b20010c30091e0608011401120f1409240c0c070e071202030610030207240c08060d110f0604031401060e09060108 59
    0x90708803006000311000410040c0860403400c03036208200700d40e01e02c0d900da032019511580d000d081d50b50301001602441d4200c0700200c00006c1d0004421110041c0050f13151a020301203c100c000c4070300c141310244050b0f08404030b40d105201001c1100000b0030801402510b00b80751080d40c2c1c1c1408100380c14541407015092a2060203a003119504101207012564451010f0710300a844d5004103002100480b80d40f00d0003030485071840c0d4200c440d03040c005404640e000035030070107040e40d650208690a070141000c020481c0d000e04000c0300440c1c1001682c0404130104000d00240990b0781001e50301d420f11001c06000601c4081c03400056500600400c010341d6207180040050721514140903941e500c41c1d14103880c0c000b2140001403030708500d2030709800030040d050384002030b946425265000c40ea160507081010324494000c0c01020758010850100c0700c1d0504081000185078003034241401d180e120355805105048038145899160b65400c0c0821240d440c2c20381c49500b2440341d0b0f02030030b899418481c07007580344d10100d8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 680523183 1250 680521933 680521937
    0x60e0f0606071511270102120a0e0405010308070b06060c0c010c14061e011509050909010b090406090b060117042409030201021e0c06070804030509060a08070e0f0a120606080d110d0903080a 83
    0xc07500309e942c0341c05103c8200005030000c2c0308000707a40c3c592500a0503a001500107031842610480001c01900781041160200f05090004282c884045401120f0041441d9000c650300a03142160344040030302080307114010031842030120340c440c0715003010b0300c01c00105a0002031049107036801030241c140c0000c190030980c0c1003918055120307500c40446502500140000d03a40041d84401004103002955110b0351030144111140c074450344500c4011500302a1601408030110440340220b400194004080350720b4483d01c40584810099030046101216040b00098001d44d400080020425042c0e0054412600c180242e1505103000c00c48a95602c441c0209074509009102000c03d0515001e00180c071120390f0018607143e41c4025585000b01b9186082c1d84481c003003204482e5840036490140c1c03040341d200c4030280140010794905007013034610103c03024054400c1683c1e62808245200c00f4401c031105000181c49850740928021012403528248090807020001002c8050000a0018045441441d164 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 680524433 1250 680523183 680523187
    0xe01050a03020c0f1c02070504060e190b041107020f1c03081503100b010201051b0306010c060b0409030c020a08030c12030c1c050a060e0f060607151127010212 70
    0xe46101d0700e13107089050782d0041c51040c20158510b949100500b030700b80410755400d85288039502c3c001d220940e4000d0080035125440c01380099401005208201241c8c20345001c0030500709443e0340490b00300e07801036881c4901ea050000f110000e40c106850401c020704000d80e402101118800e64640d440140220000d0411026402140c0307070120041703030b0401c2920001c0c10380d80c00c162425002c50090105116a9000d075017440001508035039484218443d02002d0402a07140d6078845004403452a000706044424540d40d4412111544881c8208084a80704e500d4400d9000064010000a00c2c2d2682c0070440e2548200820300300440c000c580103244600c5480d035a500c17910340c034414803880c0c003400110b0445800c0e14808003995000076044140507030205201080060741f204406500000210b0300111007180000204413182007090041c40080d0213010760b01c0c07070282c140360400c0503100e420320b114500e2980451441c031802c01c00c1400403419551200084e50181c0e2110000c2c2d12524004c4a0000c0b41d000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 680525683 1250 680524433 680524447
    0x4060e040b040b06220c08060d0302330c03010905010e0702101d030a020601140a030209151f020c131a0d1b08010516030c0804170412140105070e01050a0302 69
    0xa84440041c1e60500c486059170340407044400f0320003e011241404000404140c0814a03e0502d48602ea0303040d9010b81c003078500e800100544100030340b5074070405100e034108403240707150701c4903018000f6000d14141158076540e5403514568100b91901030300540c19508400d01400706040d000504201c1b0040940c03000300e403101c24410005d03410103088403c400140000140035680c66030215515040e524001d03040310300c48000c070381407148000141c08000d42081e00403000c282c030546000c07124038004200414210f01500760001041d94074103100703074900250740807419080c032506d01605040444050f00c20200400c0401458002e04040341c1c075112070080c20200030840500201c030ba42000f0594400d0140b03402d551b91580c101e8002c03d800c8841081041c004268a04624424000c440e007003072890790341d60304903101d544030350300c42e03802904117510840410000091611f90301003124072040d005401d600c80003080c00e050349007901c0004007090200002e110000c1680d0381c1160a44282048910b401600e50700303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 680526933 1250 680525683 680525689
    0xe04030309120c05010e1906110d060e0a0f0b0607080c011401081e0f2a03060c04060e2e0c050a0c030302070f080d030c0c0f0c0504060e040b040b06 65
    0x102101c00781c07148107000c07605000503801c0f030010140d041c0b09100030012a00b402112607216035411a05186d8102603901040110b215a00705c1542041d961104034500301038020104d0454107684c0c441d41ca030303620310000c1290701e0800c3c1c40b4500d00e500c10820188200030404002486078817a0f0000203062081c0810400e004010951080c903041c800c011140549513100c0f9403483c0c2cbc0300c520441150341004086203030042c2030700125450b05400c0300c0c1c5000300384403903519500305094030b50601d1070050030120408510030741d82c003001103a0180c0410741000341c0c1c0760308003100100340344500c1440754080c005904174904544d2201ca07140075a00e1149115a040c114855001c4032002c2c80314201400d14820500b409041c8101441302c5811244030b81c00303c94900350303030790300716034424070144a0250507401800102007000d0223a0001d010801c190704d40b4800f58000d42c4da840480c100001404c1e5a05e4100c200140300e5804c042c45884040c2440c83c0030a001450142e03111905003500400c0100528404008180303561 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 680528183 1250 680526933 680526941
    0xa200a1e0c0b03221b0801020c10050c0f070606140d1109060409060203190b010f0905360106120905060c0c12030f07030b010c020906100e040614280e040303 69
    0x13500f000714000f40c0d00c01030400c0408072034640d40183c0501d00a050006509205108036980112210041c201c1c003954900110018807004100c0030311f1402c10050750340c01000502c020105a0b100d00000248103080c0075820070202c180400b048d024400c82c80001001c00c01c1200c29403c0403800701e424002c00e40d01e00010501405810500a0003580040180503205a80500036041040011410001012004011100f00014011035404503094643c14002414520290044484684000d14045440001404540440701c449020179113600e40184469540800c1c00d1500c4a04100b007400b4510568544644803500500048030038040020084e589880c10303c4500358603182c10100d9600d80c9001c40c1c442401607021a4074800091400183c1015036004810200e145d07900a484048240d41700410301c01d0400340714101c00c3c00e004a0403105203942d0b64a00400c8051b0010b0b07034000c5607280545091001100f1054941c03100c031081034a101c500c1d41c064244070400c8800860a08006e5290760405a0040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 680529433 1250 680528183 680528221
    0x120c0311070309150e060301090c020c0a121112070b0c160e01030b06030303070c060c12050108072c040f0c03020301090606140409170a200a1e0c0b03 66
    0x44030007203180d4060540280e001c0049400c03d2400c03641c20b0034410404c841c0311001051955121b50184014001c84107191f010031a07540d8940101d500c05405040020b03144d075001d50101a010124134030032030805c02403400d115420035040d2882d04684181d01ba20303980303c141c1402792031000400440c80c069028000c101d83c008482080742c14280b11a04d03444055021102400143c2d115401c00020035001d01700002128414007031999191541d610f682e03101806009007200200030002003000c14030954100d4841d0034004c1001600034807100e86485031070312443c4803c01284040143c001d1200c0b05e400920003030164460340c4a58109407103051450440da0302d00b030503000650950b107002405c00410000b9800401a100a0b0b10f040785000c0005003007206440050200074031041041043c240301e81d9104015044021281c1840f01c003151100c0d40704495078010f5115000c0a90200d0300c1d40045c0000860f10b201e00c1842c8403038070200030f0040e84803000c003800513225000d4080340000020300c2c0c080b8500701e01101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 680530683 1250 680529433 680529461
    0x40c140f0d050d0f050c1023010b04091112060d0c0911030709090c0c0201230c0d030c0c0507261b03060c120105090c0c0a080a08010501050a120c03 65
    0x1508200d04206a99a003890010804201a00031300d006050146081d50004101700008107112a201c101c0307040030700311500c0c02c049080c089041c45021100d8818030741e8040c004048005846500c0e128a407403c0c0c0308076450540640a042101e1104034080c10700c8203a20a00507100040b201030103151a500d03464035948a20540c2d89000c0040d00e01245800c02103009008030354030302892944a40060302100d10f01104180410b074103950300030041d40590036900e44950b00d001c208001c0d182c0140941040d0744a0140d85120350000034101c08410f03010301c91100c0312201860806903102503507484503901c581c140030b0004012440c41558010190340001043c04031072040c00d5440f0449050501e0446404048000744240502c20008503d004440159a480701d101c510991582c2d20f49414081401009404040034280801c541804c3c000108441c920305885001c03d40da8030a4040c40c000e18003441a001581084000c02c44803020a5006030034030301d203040b0220002041561880305038020031a04100c000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 680531933 1250 680530683 680530699
    0xb0303070c060f08060108010b030f06060904020d0902091605030703150f1d1f030311030c010c090311040b090a0e010b120706031103010b190c02040609020c15040c140f 74
    0x502560180700005243c0003500c0301c0f03a150301c4010042d10412800d010325450f1102c00e01c00110800d80c40c054042d000b801c050301390361802d200e10f40440c00340d0b840b0a07081d061154036440c844003142080700030036074440140e2205100001c0c10f880c1c010a288005450392042603200c40c000c65400301810503202c01460103600400205075030300304101481d0803507028080c10010080015026051010070049140101c07104420102c0c00c581d010b44140820807469406440144640d0f001c019007449a070005400d1030300c07594030032840d501e41121024545070b6014055800c0c04019036440d2030381c040f400d8014030200004100100d40002180c01410040e501c1540706083e12074003c200440400d440d0152003003580c05005c44910440000310b5440300b8070030340083e80804c00c500c4500310107842c0c529242c2e00042c50b2000307800d00245c00007816075901d60006500f05a00240100c0201810084480010740d0302e8000e81131481e050303c8442800e280d0344501d030b00010b1105a040441d544c0c1e00994964000000c02200c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 680533183 1250 680531933 680531939
    0x150e15060a030c020f1c05220806010302030d03020a050a1b12120f0e1519050103080405101701090c05120c07060b03072d1805071b0804090b0303070c 66
    0x40c05030400f902c481c0c0141c000c1c0349000c4042d600100359a01c41404521241030800c201c03100403102c0c0c0e4030440701d1324600d0000c3c080c01c520078921010743c3d100078142c00000b000307a5410350041605100d1790f01140c0080c58410400c00b0350303084e00901a26484400c90508500303001c004145080910b4083c00002c04100d081441006420340000840d11400c2c181c0704200724103089404503104413207a03801140010b51258130800303071010030802143d40c418103104415044403607280401d0151082a041184c1c0c9140105007840b61b41000140303802e120360070340340210403000c1a0443c00d01c40c0406005200720140c58101daaa01c10780102c080754030b00d02045815280914101e400c1c40640d401c140c40481e1154101421000c0f0741c98001540380580340d2450a240031006180806049010345002d1036141582e1740700001040910b541c1c0758055110760060100d40b40ca401c0d8002812941807540e07091002c05105940b20100d804001940c0aa80040c400012303074080200000c0d04e907008044c801401c4500c070840c08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 680534433 1250 680533183 680533187
    0x91801020a0f031b17060f1008070f0905010e041d0307030c0501180b191515110303010b0405190308190e04050f04030318080d06050a050301150e15060a 67
    0x11078003107502c5070380c00c0143c00c09003000302c580c20250704048400a01d560300b000c80c1c0104041c09032504008010607030441420240c000c80e0040e6480c1c4c5600c0c01090344101040b003d2a00070b01007034a501540d00c0d02d20342e424207090010300492400003a00303014a41d90320301c00c4450f40c0d003511098044e818120803a0349540e030740c1c036008119a100c80c00480b86942050418104020b07403900c07803030505a2107160a0395a42c1c03a400800c030300b441c10015003140e02e0303282c204811a0140500046000d0454000784000c20140d203500900031140341e486149859000300010803100e0f11603c203443c00c0d61411502c1602c80d000c20707140d40c200201250809084071100060b48690700303000911204440e400358a622200b8491102003000b1250708403070b559010a504000900060303c2a4400c0c82c6041c1034044400c10481540c861003000e0304003840041c03516075150814803903071500751410002090110000e07c441207054100340c004a8491041010405c00b880200d2140100b07020303a015400b00c05441c0c80e80b107810142c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 680535683 1250 680534433 680534447
    0xc1f030e032a010c02070b2b091a0c030601030f0b210706020d0c02040f090b103b07050d0c0507020a060c0218070309050601080706020d020303090c091801020a 70
    0x81c4a00c490b51084402d61000010300440043e450690081c207800d134035250394002154803482c10f0b0f0041020141441403041080c10480003891003041001540050900c0c00160382204c078a9602c4903200801e04010201e0800011654012002c3c640810a0781c03080c4440f8000d4913090700d406621900c8501c0040302124444a2a403c5044001c11140d0941d6034000c180e80702d0141d403c0070400154694950f00c09030420741c00100b0911814030300042d843e88903844140800d5816070b800ca4290880310000c01001c04200441030203840c02c140545040050141d4000e108010703020030b5058411034078005040d89020b2000d55244010031102806403000380d01005229910918041f80b003140c1e180d001080580c8900d5049042c198041c004460888101b13006850000c40200035104040d256007040e000600103201d218000d222a00c000c1020604005e0081d040810700d414035000c56005000304250b140f0001140c2c00004019200108103894042c4c0007071091460141e143d001d036000251201080345c2c0021 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 680536933 1250 680535683 680535727
    0x90703110432010b03090a0627030e0901090b010516030201110c0601060207090c0e01030e0c18060907080408120c0409060308190509030709020f130f0303020606030c1f030e03 77
    0x102c224016030f01c82e84486800d00094400c1141d5503c410074404c0091042d030b12043c03111202c10039160061007103402e050070002c0c003d24101c00181400351500301c40d0404495850240c0800030007800790a40d604002081070003040c0070308040d800c8a036450400d150003076104038041d011071044e0599400045618503507410080c4100c030010b00c00d0510010f103e0506215000711030403555103190400502c900110051f11617800c138522513004c1c41c074030144e89584042c1200141c56410400440f50300c1d1490810100c104002c04040c140007000741003100040c0c03294200c03100c080390344031060020780710008112120300841c1c200c0e403035007480d10343c0200604c14910040c4c050350a91003007541e1801980c2100301c800c4d00078280c07060f805500c0b1400c14003801c1c4494020340805000b4454a40c1071040020101c803600790701c0d90001301e480c402c5c070105005040d810300c11580d0086056008284441000340400d070006081c0d01e03c94003c0c40c0003828981003910941190030500010412070b078550f105403400380c505465000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 680538183 1250 680536933 680537021
    0xd02030702031b070f0626070f0e0901032d0605070804140a02031e030c012f0c10090212061f080a0b0106030902010c1406041a0907031104 61
    0x40c8901c0d0390f660780001c10b030b000d440d0790003800542545007034001d990f20f200348030107041000800400e000384041c50075203882c4210132644d00c2e0010182560070180545400c0300101d8021a0250014004a06095a4008030301601c4914035440d1002d1a00021903000c1040001e001c541400284241c0e0350f400490305004a000381d094800104000d065250340e448100d038001d4040d009917241003c90300a4110100c6034203030b01c0054038900844040390f6821941024071190b0604907459030f514200310550200249200c41d07015031071500040502241d0344807180d41540d40300a468000c56000c41d1603502103002c1c2c05482108640345410801d90720b00c80b8589090b031078440746c454074000048101000034400d03002030b04000f60314002e9003400307000c8000d1320301c12005138144500e40f003001c000160b140054006192005c00034028500b081e2401800280c00c1c454056068900802407080000020401504407680688540240211a0085006000540f20400000c2710282e98842098041560f10340510548 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 680539433 1250 680538183 680538217
    0x7090902090a0504200a050a1707080f0a0206031915030b090d08040212030702090a05010f0f1d1807080c100801081e010219030905010b0a0501021b04020d0203070203 73
    0xe40d0a20003203403c2207401500040e01c140104003c01504022409000000740054404546607804100381010b17a500c49040043c03078140700c0074151014003088020b881040094244591a04d80103580d8414586010b8803451000000c20f6101d41e8512014440c2034044006006146600821480700a07091006490902d407207070014082c1c0d100418224510b0505440306000f58541e40c01748005040c01046a03075503448104408030150361000f4409105080071900844c49605140d00e240d05400d259005031801883c51205201404030241d10f1500e00701800d02020a40e51100d6400d074540c003207240032103c03c1c0218880800d290001081004002400380da88000e00394ae2140105c1e118002485280441d8000f42c43c2510074035507603401090320381c0c0910000b40c140054102d95a8004e070940c0b020b070001c0b81c0c1d1115010704100003800f490380002c00803100503e03600d19000020351640e030b618060710402031005003602465038941d81540c01428200804545134542680c1c003a68a03400795544407100f00203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 680540683 1250 680539433 680539441
    0x80d02070f0501090e040f060207080c0c0a03150c120c030f140f1603020c1902101e14071e0308090604050a0f0203150c04090e03090913080c0709090209 67
    0x8203001c1d0000c44006070346004225103000d0f40800341000c007410803104050001c09540210304140050020940100c81c1c0070b41c0c90b81c907403083da46086a00d003100d60140340c584408001050034108c1d031840340d0f080000085450500c51070300316070207104001344526880c40e00601710380441e41540b000d1800da401003001c0055103020005501e80321401c03191003400e40c1c4a40006420700800c00c55407501c204140c100941800c20f10000642001000d0510590740019000181c082d40b5080008269500944c285000f00c4622070361003441480055102c5810300600b00114802800c0c070381d0881d10100e400856078004082c0d0401070b003254a0ba055400d5000400410100d0320715400030a61502880e4080300030900105c4035a129401020015000d0740d06009460910065050762115648030f076005610030743e07550742003074584012152018a0f4001c0b5520905c41001180c888841c0d464021641903640e02201000b468603158900c07a440e0600202e000361180040e040407103401041c6101c1c070807a450365003507603 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 680541933 1250 680540683 680540699
    0xe0609010213050a03020d08070c030c0e060432060102101d0d0513120f0609062004300c0806060312180f040e031c141015120501080d0207 61
    0x5000c0c080a9486139200c4c0b0b04000060504002701b24443c464101203511a950b610391414072106540f2403d095440341e8200701c001d02c0d01d8070528021002000420216400710403001042480340e007a00c0d100c5640c64008074099a008101044410425900c14400f095419034864609210b5901c01441c1d0710410100c200801c1c040d0b020748081c02c02c200010000d072481c041c2c0010411050b0081030721303d03c12800c030f140f002c104180102c040240c010040030803002c500b2444018800900703155010354600601c401d0000c052112140c264103810240d4802400d8003134280603440c1c0340e0305030001300010480c0c074000444d408007150f0f2070310440c0d0441c141c4058010195070034910f48a07065481c1641c0d511555200181d181500021500c4a006030000031900700541409203583d20450080c21854040002c101e03189010703008403003025801c000c8810560500060381801440c1c64000c0174600f0f45103480d07240c50103110381c130031945070a64044180034071350b55411000c2e12030940c0113100e00140a041c401054000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 680543183 1250 680541933 680541949
    0x30c0a02030114071707052119181103190c030b010e0103120f091e180b0108040b090c0d0804081b0109090b01020102040b040906051906050901050c010e060901021305 73
    0x1214940f80d4030005041c40505c2800140014200c900f4044240300e00c034028280440300c4d029000246002000358100510408201e60b0225890050903003012a44c2042c1e0a0060308401041d52081c0038103145014440042d040c6003082c0608807204040701480c0381400400d41480f011240256001c403a6640c99204104002100740000780402c980900e07080c3d10140b0441e00701100901a1034842e1803541c80d60200e1301c1d080d40e03590001080c10020325090000d0b42190a103c143d245040b032003001450030440018000240c001c1018110701e20107800522050400d00440400b110020030001c141c82403480c01c10000d0300280a54400c034803420320031202020707521980c521103082c140c407004e4440345080310200c05024400d0016045540a00001074060103850290014080d40303000820944d040c0014070480903048000d1100350000340d10100301468008040320f0541c01d00b03292007130ba504403210441e40503140d0480178000300e104000c1004084103040d400340440d002d04400521040f903580f01003050003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 680544433 1250 680543183 680543191
    0x601052e0f020f010507031b0c020907030506120f0318030606030606060d060f080d0e060a0f030b0625020906040b03031c060e04060e06010603090f020d020303040503030c0a02030114 80
    0x82214020004142805150004010080e0b881142c0d80d50046040050a55900b0354003040401c1d119003201d1070519000c801c0040c208094646080303400251380000742c0500029050400b419628404200545c40b100c000c1210311080204803840103c00310100c83e80c03507001841c5204250003250455200f4500401c115006850040080100703850700c3c2c00300a15a4015810380c0203c90f030b54500000e0b25858640031600904030f601c017610031013400420241485d00c512124a01c1440300b04640501c04d034215513a650707400c81c40d1400107043d600600121b01d81c1d00c035081075820184800055810101056801d0151142c400e49501c42030307855280501c000c0d201c218071403940c9034005100f040030314500003422414039021301c040440c041e030362506005512281641d09451154440041010100041104600408503403074108155102034480305400c1c3c019400c000d206100a02d002d4040d541e0400960b000703044020190783c0d4406130161a141d50780b50702c83d4124003d500b007240440078a26541c1c400c52203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 680545683 1250 680544433 680544499
    0x13030f0507170a0b07030e0a0308090c01050a020d0c0c18021c0c05160f0c0308030906090601060503040206130b160c05030a081c11071515140d1112060105 68
    0x20080503903400c20004d10060451040503510040c511144a040041d200310710300070f0300c0740380881c00c0800c1d013141007000c1040340e01c0c140f001c03c0000b990784a50001703a05e00690030500e052a10400140742c01c0404c51013030380c4010024031026044118a6003a60300600d60301c5a01080f04030841d1148a0314415100c0c036002c3c01c400704400f842065030a24030303400022034035441407601920f40d40e916138030130280b5003450300181c4005502004210720007008008141c1c000c44690024481e561403d0300050031444001c5c03000b801038002040c6100c140a20000481c00307003030f40c450101d84400c00142e60740207941036450b0a450300140ea6400140505010500380ca0007504084e2452034080404003003001d04102031030500e5040d94500302c164174900d280000c0c2024500c2400e07003001442d1384d90054006d60b02e03c00449082d07520000401c0011071040360b01d8101d508030540b00300d40b205a06043c0041100c111500d00c40e0003040416590f50036000c0400c0300e60503070700c04840c03004100710b0121071903811003070300030070640 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 680546933 1250 680545683 680545693
    0x8010e1b100306080f010501170703020f10050705100e160f06050f041802030a0b010f090e09031c09031e08010e13060c031506050f03150613030f050717 67
    0x8a900300505112450207482c100843c00550300d800062812002100e20103071a55100b0060040c0e00c81011240c4502c2300100080070303000c1c1150002001c480030810341c41c0c030410a0411729080c0502603410303a0002d0307400a064501111012108801401c1c85602c51030b024020031078003007180d900303804001d010341d01c0011070901280e050400c00d9403281d1208410003071040c801c2c400080d02401c00c404508182408102c00340c0c032424000c445006442d0310310310041c18012000c1641400c954400d001c0c400b00d80c03040c07295074601d860340b60000381944275902d00035441001104221001c03e400c0d4004500340d0744281c1d10b41c1041170030b0911040c648a401a01500040c100100401c0000d0103d00d901d0303000540c200200804090560700c500403a101c5001c41c8001c03e8660054120010070065070a0042c4600d08080d841c001400da442d005510004110701c05499600c12372810350303140c0c5416aa460b441ca60107460306a030300d030300300040d65419641c411540781c410304d030b804110146000c1606d815030104200900d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 680548183 1250 680546933 680546983
    0x3190c081b0405061c0503070b01050603090c28260102040b07030e01031e09020a0b03010b090d0507030f0f0c050339130608010605030d0e010f02030f0a03020408010e 73
    0x110107040080c1c40c0941c0285400082c008403090058004d03000351042d1b0081d55140c4241c40c2c0b030f22a00005030b100c10b00c0341030705108011030400b020449900c6500115a94080d0980002403494860200380303a4840c188403003c00803034482160a0b0f21040b4403041c59603820480042140c2e907080c0d01c0b8501900b12221818005c900010340225425805100141000310b415480003068043c080680024644c0c0303030f51a52003203029814100200310103800341051491440d03050024603842841003206580c080e440000c0c030501400700c1440720318055a40000c40f03070f00b008614102030101450340e907415181c80c011224005000d1a0000d01a060741c00d4030b00010b1000e40002004991031000c040c03030400d0100c60b0005098940d07503942c140718460310000d0400104241002034850840d04107402c0f4134080d40c084d06518640d29085151a10545c0003440e00c50381c4040701c403400324118056601806d24512001c900c000c1c0300f542640241c81a5000b100081098400c2c030000340b85e0b81c1c880314080c52a103c020050107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 680549433 1250 680548183 680548189
    0x20a090c03021804022b23010510030606090b18030706031e0510032012030a031a0d02091008030c01020d0c0206040309030605130c030c0f12081c0b03190c081b 70
    0x4024408001b1000400103d2030200000c02c58500b00340e841c02ca51a035005000a14100c0c1c42c144800c505882e041101505000303015200c28018040d140c01c514010607040703041d408500300d1011640005c1c059a40d6560344600242c080c20080c0810080c01840480640550f851807141510542d107404012522034950380b20b000104c0704584050302404540341303003058241ca50b40e0003054114150001180e860320805401012610b44020200001c9405040b1034050343c0d855025051041d01161b003a0b10640b101803180b80c140310141c1c0590740501000c52140f050113010f40c050844000441e00902c25a03032041f0003243c54003801c0b2001008960b1410007400815030030b40c800c980c440d6405880060000d107548134a0100075007a80100d030b40110002c0305100c80d032103044c000030042a0501c80e0000c20141c0350f0f90b000b840e0141c880e21307801d008545001040d21900c03941101c0b984000160640741050501030380801c00140400b41585e15070701c3c1000000b2108400070b206e00740300070310104041d4241940810 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 680550683 1250 680549433 680549497
    0xb0c0a060209061210240518040b0a090e1507211503081e211003141b091009150e090d020607021204030f020a090c0302180402 56
    0x541d640108080c0301c816480c421480d03401340502074511490220500c1c00d044c041222000c582800000e500c0c3e009001206604501901c2300070814001a4403007120303880100d002044244000c0341d02c40042500010380340096440004d0b07003d0140c064601c00f03a60381c1c1d417100c1e0000b000c0d10618002915004112000c5030b1901d18603500b8000b40f00c0c04115400c2c150004a155859600195054940007070940c2c030049031300001d280b81d5a2280c14030b60600100d4000030200783c071a40310300c880e8262201d001451020805d104a4083c6900018510004402c260510380d118011046000030394400500e00d0002d1030070b81506032142c401c680300c80b01d0040c205a150400b50584c028072030700701405450b01040c01c41c40d40401070700c10301f10341004011003030742040000d00d0920f0241811081d03412000404107500880340c01c58003541d40150082005003028400324035a0091940403640035031070440c5480d10780e50b01d0740007485103010002e94840010740c0c000404c0102c0c861022184034810040b954278042d07211b5520 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 680551933 1250 680550683 680550697
    0x1e1707050d09140c0111010902101103090d0f0b06031f090309150201020c120c03041502030c1204180b1309030c081602270c090a08070801090c0b0c0a0602 68
    0x12561414a59500010041041205083e9086000f143c003881d40e2040144040039422002400494000d401058680300a8035818042116004440d440c4510030800c8454016028010031340d5400741c0d05060001080d0148100d840c0036140d8082241032400280380346042c1c071031568006c45008151810b500401404004509000389180e00041c40722584904101c8070b80580c00141c0e44889050b461030410030103041ca112001c80034400c14900e4000002035030240c44008012943c1c0031004513080c0d2035401151641d8603a841884820150448a0b0010f0011a140e00316184402c10544030313030106480003800407503000b6a81c084018440c03560790b000814464000d0a04c0044080f06c2d8440490310f40c407032040d40002c1d0141e810407100314146410200200200c0340b1407080030090016030b0301d52201d400340808820400219440f80169114002c0a00500703503d0119003089980318660f90103809100f40c1510405c465200011301642040c080311030a16050703024109496150382c03800001e4101d15 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 680553183 1250 680551933 680551957
    0x106030c0f30090f0c08070e070e01032a020c01030c0c110a0509040804030b150303030a1d0a0506160c05150411040504051b0402130b0904090b071e170705 68
    0x44400100c040300391107070402580c0240720080001c0c0070750804010b00b0160b94004030865011040030858103107131018449c0c0120552400c1010040183c004030301415003803d104001c44201405124680c600c600031032400403241c0c09a59456400034019800c4400040034000424800b401e9000007803101c5003d0404054020901403480b038491300840c90240301203804649003003000030706100303000404441d1a807041824904900c1441c080001c41c3c0c49000c090320b400142da80302d980d03121045200080e0080e48046440c1220031101140c00d000340d542c1e005549000c10410104201e03941075119680d05060303150000c005010700103005c41024042800100300382d07419a2640101e403026a900c2c0200d600850081f0009d0207101c1d020b13581d051000e0504c250a9104500c1004016041c258074920030044413860036115403210040381c0410090f01c01c0003801070441102000b0000346a800040e6104400782e2003100812259580d0400c0d1001c100d0351140c02d6a8203112400905003900c00d03030003041008007132 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 680554433 1250 680553183 680553257
    0xf010c120e0f0703050a06061e05042013051207082e020d060504140411060a1701120b0c0f031b22050f06120604020f120f0106030c0f 59
    0xc07030440c00d03ca02500304a50343d800004000d4140b1103c0c1c0070320400f401aa1185010100702c0080380328400b056442100d010700d0315220700195000455803c001d0f2103511a040b2952500c50070003603002c00c0540c3c021203121341200801108400400070f0314106031880840104080440b203402d5103112040a213a00c0f50304056207154906a02d0180094240028940e0700810001d060400b044103690344031011840324001401000042107000307000354848201901c0c816914901400c080b52000e440c14125440000d2080c00002d00c0a0783c84841e02040380134040d01c444648410410180c03e200b2181c0360304100d0750078408131304860107620103000035400c01a80c1c549040030150000a10103a068404402002960320401c65410030100b44951070340c088856500d00f40000d5048000303c140035000c140180c0e0b012440041ca816110304407a0b8504500e40208a145405004d140100d0803d01842c400079084c0a968054240500014480c03802651942c1e1042005001c031b40100c0006e0340c050b61468044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 680555683 1250 680554433 680554453
    0xd02030132090a30030f0b0409021f0215010b192607120e0d0e01020a0209040809060f040b030108190f0f02042004090e03040305031c0902060a030e0f010c120e 70
    0x4410440007501180e00c000c01d8002120f030440c6c080f06c01c00d10700300d4001c5040241500060390f0700c1842d0300c0318107000385c0c0c00e560031207600038100c0c54900305c24616080b0004000020405a40c070002030104a1601c0d007501c2e2a041c000042240e201030400410341100e0303031007230712501465903c003480c0b5800384503450103400b0311034220060b105907006482c0c0003000c0d03000100d1381c3d00202d62000494101a6003800200080102c07a400f09819000040014003007902c00720f00340b140c035501c60088526608000c0c0b0000d407640c0d294280341c070141d030083c03060500c01d01c10410300300d821900c041256039201c0d070844030426800c66151150312861154102c22648295194054900384101c44124102c2481c0303800700c141c8403820140640211006642d5100c081e07807003400100f0000b0800411122281e00c0d000c0c4005403804442ca042d0054054650025405400404c1010840350316900c82610801040121003050407010442402c8800c01103448000800303401503407040b0300b02a0410603100030142c0c00c51707046d800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 680556933 1250 680555683 680555753
    0x3080703051e07230a0b0604150605030906101212170a060602060109090506070f03021615051e0a0902060408010e0d090905010e070e0d02030132090a 66
    0x984040050840c900828540d043c400035400003030007888003411303d03503001c1000a071240c0d42d0346480c40014046424800084c0076901d41da00328140400c05511981540c5448043c05001e80d00207ca640000c0e226200000b00345600c02843c04089032681d1100340365101c91900d03159400003000d40c156050201e02c2c02c04207a4140c0c9251401d00c100980200000d205051410003820140c0c103074000415141000c0540020810205072103401c441a400c0800798411003010a501900445c2105440840b6450b001001e0000941640d00548010681040250350358481d12051225844121094160aa0001d184500b0035440500034074001061141840d959400b01400d5034060301c880019a0840e80d001e00da22038010540c18040d03d01440c05008547c102a8100300c004801003109040040c1603005050940341c0c1895404000e40240c02481400e581c0f4048082c00d40106522402414501c0c200303034410f0101078a41070066020030007510180110703864424011901070745000f40740d1118401d00740481 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 680558183 1250 680556933 680556967
    0x912080c16031815090e090303181c020d27030303020f0c070b0403031b0f08030c0415082e03080f0c07060e042a03050705090604060c02130c090308070305 68
    0x480c9295807400501000c13840100007020b40ea1050051b07540a03c14800355000201c161384e4003c2c401c40c89031149002c400d0072140703010307001c0c2601030030b103d000005031080b181d000c28100d1b28590f094070398200e1800085240140514010302c81d441c8140060000c0c030019110b03030000c2440b0242a242c49040c001c0025141e8202000d80c0d020303007401940041c0030010160420590443c0c0d101445c00100300070701a440d1748126012213200142911400800180c50020340000c0c1c40191080b81420022000c0c40d040240c12128159050400003c4007881c1d503641f15030908002ea91280c4649442e8106483c3d42d85034441504142c0003000c0c5084244444a2020b1003004245c006281541ea160500300c00e80040c04100c0c0c030000c0400210007052422461410108800c1d004100208d01d8000f41a689014080f190f5001d0f01d00d40a074003000009000852590144050200c40d000701c0d11020300f5212408030000721114448910041600c04d00200301190802014100d4280281896031801c11000602038540f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 680559433 1250 680558183 680558189
    0x12100f0803030f070513140409140c0111010c12090528030909050f060f120f0703200a1701020904060e1f050f100207030f05010912080c160318 63
    0x507500100070440c410440309125900000141482d41c0350803a8500710b6110320116014061082c03640c0c00c161580c0e92901e601007442907800600840152505c10a00303a150040042d14500254030f81c007103002d0000041c031611603d0020307602c80740c5031100700d18102d001801c070200d4156143e002d0901e294a02c0b20388803a80d407004119007103108001d079100f072601428050300381d00100c0d14685840c1c1001102040c13484880c0c1c10002c122007904a640c0d01070001499261404426405401015141015076000080b0340d015039125205951690f900c801101c43d4540302149040d034003000240c4100b2038000d65611402c01c00c0c410314000741c50104924003040c1a61400d600900f80088207400b0004001e01c141451f04030b26803a015481d0341c182c074010009504030521000b040c450100d186041d62514000c00054004581c0104040c03250540c60800701e0007410324034003d072010542381d00700a001d94400d8041500c600d004001c001d04103ca00107601042c0c2c0807001084080c450300c00c2d46013045140d402101801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 680560683 1250 680559433 680559449
    0x31505190501022a22110d0f020949030905030a230712060209090915130c0506030a0b1e01050706050a1410050907110312100f 56
    0xc46403410000915103c0220000c10390481030004003401c008888404084201e070803503041030342042c4c5809100c002c1c00e065041464840c0380c408120300c4400e01030043c003100001a0001c000c80034010f0140000e034403540180f44d50001032848a003440c42c00a20000e1040c2841a0504c60a400320100c4000c080f28140e0034080c400000d842090300b0140c2c4882480040d01c01a0041e00741040d0541e2460000d01200c440458102202e81810401c4030042121000078034000b40e81ca0381c0c1000c541810802580040340c00780c0501001d80004d98520300c0010040c0d4030080703848500144e0781da4034034100710b0840e202c201115000b1090300002071580e28600554081c200f15030b03002869035041d60400841d012501c1204080e180d401400d121681e80201c02e48145039000540440d890f5291a091401419401094400c0c211030805101907000300c100c01000f96142986c100800d900e400405a0700025104001c0c1619401003090140c8403085070205a003101c40f44001416654540d20440903240c415003007904 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 680561933 1250 680560683 680560729
    0x417030a060510050f090f0301182906010c060b03071d0f0a15140a05060703050301030501060b0301030f110a0b0a03020a021902010c0212190b0103050c0405070807031505 75
    0x10262401900403d401038040c10700034505109400241c0080c00341c04c40c4548180c2d103040124210b5202900b00f284c01040c1d04603418800025803500b20005007054981500d060000c0d1302c038425403801c00100310f00958050b11034410424159a03040c0281c44418401a01402211400915440b040313403000001021921186041d2811100c407c8c8004401840c07484014141f01044804244840030794082e140c00021030302094010704c000c03441c91000ca91006821038000948101859400f101541c140c82c444c90080c80b03803503522520600640001e000c0905002113860407400001d00e041c042030211040549040300f001c0d603a01d0f0b6182543c0000701502d02007a00025103e440550521408072500c21954051003801c0782c0c0d070002000c0ba05a001c000b0300030003022200a0702c641d0200010940d4400c5041c096581811a01d0100765039042880200d50900c0340c041e074240c517071906000300c500c106800c0d030b03800742650b490754001c40187c10201103820703000c070421602250a40701c00138149140714150171024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 680563183 1250 680561933 680561939
    0x5090a0605030105132903071505031f23040b0414061c0503040b030c04080304030c0e0603060f1902070b0406022d0307140d0e06090d1403010e0417030a06 68
    0x201c000305c0b030414040c0000b0700c2e1160000d04500780c084d4220901e4414914210b442c00800d012901d0300000360030000740245c018200d00318950744403008510500304d00302c0018a62007d00c4a10300d190329140245101c01c540c0441d8030301e00010814101505401c028000719001c244007000c2002c5032705204161001b03030641420449103040025501c10b80d19002240c09280f905151100d946030300580c0100c6000b2003000001c81c508110503015200074040305400d50750744a94914000e041d00d07285110310303a1a41c1b022400551903140102d4014455101c0f620b050030781d5518103060a0703920300c14024100c0200e40c00d00c1003030040750340045002e03c038074401c60005070ba8a82920000001202104141152003180da0341c2e47d01a0340c51100350307070708404103080c611440305603000c250a5074000d01c15100e000c2c502c0c042091010340c4002030f03180d00418040064521216000c07004030341f80d42140c3c03901c3c1e11484007007004001d5072100349949a03015010b81d02d800c0310f0f841000c5808071190710680d82014501d071548424 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 680564433 1250 680563183 680563189
    0x131502031f0b0f04121419020a1505070f1506060e03062d04170c030a03060501091d090a0b011e0510080403030c0c050609100f09080403020603040305090a0605030105 73
    0x40806400142c10840c10a07940c80300084840c4628022185403480c520224400c00c030b1070782400c1d0941c129000c26074621111100c0c200820200601040c2d05c1000c1400000a11003c1640d10380c1404040d03a070303250b02d0031105440ba07102500020780112121135500800c000c05001510682024100c950b985190a5461608141ca4108098442e940745000075220280c084059442c55100b40d05103210f4003880e0361242848400c0008003a840904100000342e801140f440100c0248411032032501c0c1000041d86400044800d030361640120040d100e00c6000d400e454965010b0741c603502158034400c5450650060360f8945c01034100381d01617a489910b1040f10324100c0e8102402002a00044d20003044c1c81c00000c5e401003115501a20280925035543c80c0d9481c054812080c90348440e420200320f0f649800c184403ca56911030381c0c505000424600b248211081c0000c1c0030703050501d500b000302c5500380303800d50f004c000712544041c0084040c0042040b1011080e2552191600207240c80c0e20f609840798940024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 680565683 1250 680564433 680564491
    0xc0504090e07060207170304030213020309101505150d1104060909140f15180603011404020904111c0b010501090504090f0303020f1b01150e0f13150203 67
    0x30003002c2d041070700203216082d400640c8200300c50060108903603060125102909501c156040a1341002c00d2040007101016203400a50085400314220740d01428001501400c503502000e07001d0020503041d104014030300c0e209075a07000315011010f56504d0036050701c42580c2100d0b51084042921000420100242030300701d000d42000304200902803200401c0007134440740c0c5a031300401c0050380a41b1040440c1c07640d107601200c0844aa0003402d450b00c80711003104000000f41049505500c04d40c284500d06180307841803268580620b0303000c1e20341c0b24035440301d81d18070506d40c000c440050741007490800050121203850040b08485400390204800c2541403d0005001ca40240c1089006506100900300090425400c00d023080d0b81601c0c005803039006d61504050700703104442902c80103c50b250074050b404803040d40100d44620352391800c3c06515035103c513010a80b01c42107506074140400c0300e00003101580c241c4a018200d600c60350700810303014a030290304c00032a0001d443d070303141a00d00f040c2d40166014102d60 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 680566933 1250 680565683 680565701
    0xb22050c0421030c0b040c0e01060207140915060d0f0f020301050303090d150222050f031e070b0c030a090b191d0d0f03140721020f010c050409 63
    0x400914040c02d00801c03900c1101c00c1c00103100204030320003800003070501c50002044030a80c8458000d030305060a0601d1116140a80520418940b001000149a82c0005465000c43c0d03a455441080103021904000b8181c10007420f40c2e441d540b48046000c440c2c1d541f00c005000001203140009410389070802c65a0464126222401c42e4910400c0113214075a400015154030060888201c00411510301c2c01c50640c070451154109110f002080000d014003220740722100d420801c4090302901c658503001c201c0031030302c0c4840094242c0c0107480e003034403000c0c214229028480145021955142e95440c1030381080e910145802c6c4654001090081310325500403c3e4100030481b00300c029003480301c401e5035501d104000c40400c600303020b2251608200201042e100401500d00100b11a150f58014100742c4000d41d2104000c0700010410102d071002c0701000340507a1003a68211a03040c4504810b803140e840360079502181002076111720a440e8411600902699410101617560251214601000c0d0425a25400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 680568183 1250 680566933 680566951
    0x9080a020714010e210709060e130305070807141b01080612100b01020f0f150a060b0706020d1b0207060f030218040506060706020c010c110a1a09010b2205 68
    0x41c64100710b41c2c0d11074510a413426080b80c54402d5820100e40c0819588801416070411b030003a004005031003001640300c5800c456800c441c03917000c0c4ea605154485608881d81004010490034080300d0007040e0301e034018060092143d080002c1d07201403c0d40da0b03890080c0c251808440001640070b54812540d10050250700150180c80c001c0000c600e0f00740964650340300540401516030f80318100c49481c2c0c4204029592140c085007920311808491841c607448003031305050900d41642440220301902054030501c0300b20b0707044109050501d0050b542d2032001c1e51224288080c41915030000d02c02e9442c0071340c0c0440d4640c01c0c9400400034645030040c06040400c5d008242c5043c1441403000c030408440f260680641d88c0710072207002410fa80c540f0b00081c220301500d04c014050620100e071040e0741d90380551142c40d00c812161902d1001c000170141507a034490030f1110082c192802c881032a5806c004514031641c100d0307410700000c80c880001c8004640d0204052214242000a81541480f40c0c100340c07050303c0c2c000b0101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 680569433 1250 680568183 680568209
    0x804050a0602130513020408060718290c010501050102010b040e0703061128082d07050415090509070e0a0b03060102070b040b07060b1905040e1009080a0207 69
    0x5884503900c44401180c0542510b03000110068072076581c1d03080301e0281c00020700b91a2050020207541d40250018003900701d084c8034031004156414012001200462140003030444600e082074000d1404040a0182007858003005581ba2040c0b071112010340485002c0c030000080c02c0d803401000a00792400120907a010f585012010f080505020503110180ca1704000c020402c4114020041c4951040d00d0740d5038291140c0d03880d06c0c1440c4110701da440c0c1e054440c60340c40d01507a0722200300141c080c00e08800220075024105403403c1210440da030540703502042074102241019560451440d007030440090401c00a054488140300a207418080b182d00700c1c0551404044403041d84001c524000d24030b005200d12108040300241c1c15a03c2000510060a03d00080a4440c1d5030b41c0f4040a480d0443c04044a421f0b00340301140c1c0180c14000010100e082c40405a0903030740740303401c4c02c0c0001002102405c0c82035000d018021106410b641c0100341016108410650b03448540100c02424a8500c0d0080180407040d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 680570683 1250 680569433 680569441
    0x40315060f06032412061104050d0b0a0c080c03040308060d061b17011202130b10030903020f01110301180906020a09031b0803040509070c230708070b0f220905061008 73
    0x22201e0281445d9402040001c2c4860451020000c0b4000d030303130102d0f502c203190404960420104c0a107190046038031920a0100741c810003810354203e80c080742c210342005030038030000340440d1041c0100703604038201415035201c648203a21502d0507100e100000e680324010759a030540c0380c00d60020418440c00d10f0f00c5a90465541404850420a486480f001c0c0c0304040408201d0645c5880e540b00510800000300259880c21030440e0240c041c00c59004103501601030418512a002c806000e1440104a400b031003038034580c01e105082d440c800c1091000b0f482159108070070000506148002c00c00c0030350b103840d0100320ba45545448114641c429a00d4031315801034110410906400000759030654400300e078020001c3d0354000c011100c050340140b010309600411008181010031401c1e01c65050301e0312030292107120f40c55480584c3d482e440c0c0d10920b11124010402640341800d040f000d002a500104d0322919180010403400031070400700e4019908090740c83c0140862494024540244517446080007415407070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 680571933 1250 680570683 680570699
    0x30601080d080c040f0f03290103120c0501020d05061504030305030402060708090d060b030c0a031e26090118060806040519060803030415060803040315060f060324 72
    0x80ca01c01d00340074000a040031690781a025019200601102000016030503501c0903507200002440c4001d0758212040740f003060065107458603090300c904d0001c2c41250309911f180e80d03410708158080100420000385245050000e0380a0004007140c101c01400401c003401c20740c0c10040c3c4008510b200c601504403c000800000c0d0300034040d82d40c0f01e40c045502d551203003440c0c2025411132285600c2158802080701e011820011194000c1c0e0083e0b2041d0100c1e130b13508103481c0038401e507010107010160400c00308042d98a0b00c075401814000315035110b00800e005072940d00800c1005002000d141d400342803030101700b00045581c465071100403d82005900070320716190800140003031202400c024012030f1281d000a04004d506c500d4290102d15049c01044982c0e83c03880380780e0f101d400c1502c0865034004040035508518038140244001e607001640518038240c41c1d50360f40402052003000c44401c1d0358440da000222071000d644680d005208646006c13503d030349140514043d10041002a0b22450b01c00d01003440600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 680573183 1250 680571933 680571943
    0xa0c0b07230a02190602120a110702120309090108061504090b07120b0909150a0504021807170c0901080a0e1009030903020a0603202107030b130606020c03060108 71
    0x3482480c1c20541da18881c10049041c0301294603d01c84242075020820100001580202890040910100c3c0c2c40d03100e1076900b1054645400003082c030480c040c000f2038050f00d400d40c41d801400400c501140d1400e861034000c41e403583c40076400110250050002c205c501d0760022088204d00004075030410404045035070f5803009204c0540740e00100b142c0748001000fa5101603003d80c000350402041d2400500c2c001464907501c526003403031149801042004a1052003030b600906000c1d03540101150750305103d904090780744c2c62005020740308001602078600030307031070b54600c2080c0240c440303040e865650a041000900013000144c591419140780030078100622001180d103042c4615006400708020780d95082c100d0301856603800203075008488840005185402d98400d540d0001e00002203100706940620f012024041c00112208440107400a4586201005104c07580612203040000714844440b02041440039843c00a41c1c440e643d44d00f0a005140e0100441c5540503021001002107605003400c00b0b07250 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 680574433 1250 680573183 680573237
    0x60f1204111039060501080d02160f060e0a0902030403031a060313030e010201110f1909120318080604050a0303061707030b1510260622020f0a0c0b07 66
    0x3030b0140b150120035a00d80e583d03c090354540000d0148059619814480d44a11100e181c000c058401c003000c030400c1090035100001201c982001c0091150f10b8444152542e00007000040d50120880b840405c81c1c1441d44059800b03039010f95000210340c40c4c910b03c00f0380c80011540040e03200718400d00401142c0cad020460940c055980c5490413170b086a10500060b405070481600c2900d060741c0120340c0300a104110000313841c00800480304ca1240700002241036681c07868600400850510300148100402e004202c0c0808090624446e420351540d0355004034101201a103007190700e5001422540c060540c580104d00c094040840034084001903411042e940d001e0f1440010b1040b85001e000600d190348a103039038a04113002a0a8402c20044100010800d401e44001d641e03004003204084907048c410303010541d21448010308034200d50701c0c205000d4041c001c500f03880d103901e02c0d40811003200300302042400340c100050389031242c101480032403a1030307450503200070100404c02041c0d904200c08481e00030550042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 680575539 1106 680574433 680574497
    0x405130203030a030c030f2a08070203041e050907030f051f1404090b010b03040c081b0d020307030210090305010b030d0c03050a020c1005030f0a0504020a05060f12041110 75
    0x1010f86c04ac1e802000580c01480148045c641290f020081580b5000f15080e615644e180065402c0104031a0039000903112071044d00801b01d1802900c1d004440742000814100b030640c000d500c101414440e21881d10041c50030101980c89a038030810505401c03810721501036841d0303600b00c103185e84103540071100d4001da480d0024100d00c001c0b580300c00f1749003880800c604070780a490400c460030240400581c0c2c940900d000010040c1d41e024140c0c4080c00b440e4a88030400d03469414131070700311070050000c40d010380c102001c3c00c180079a014120070301580e41410000e03283d11810034100d103014541d2960070f4104240301541114260040045c511400662005074815614a043d050070f84109440c020b40090404805108030302c1e0040180c802003100c014004c1c203140c000390b444030041c0e10540d002d40d5a02c41c88070840c1241d08140601481580140c200101020900c6641e29811041a00c2a0706 = true := by decide +kernel

theorem cover : BRFrame.Cov 680395683 680575539 := by
  have h0 := BRFrame.cov_init 680395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 680395683 ≤ n) (h2 : n < 680575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
