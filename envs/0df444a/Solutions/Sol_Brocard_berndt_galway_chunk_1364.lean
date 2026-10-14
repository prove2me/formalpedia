-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1364
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:35:30.674979+00:00
-- url     : https://prove2.me/submissions/caa799b6-e785-4c50-8b7d-c6bc04769414

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 245143884 ≤ n < 245323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 245145134 1250 245143884 245143891
    0x2040e0c13031e060e0606030706030c120908070204020417060c191d1908060a06030201020a08030702120406030225170717030405031c1a090a0f062c 66
    0x6440607110707107182c84050301480a0740c004118094032004040104a150003081032a00341070002e0581c030b040550400d86080382c42e620010501d414041c842001507002151003027140300301d0102003000c080c0d5280c030781b015101e02c82000758014408500401c14101c104142e18031000c0c2a03089030143e4035010a01c10160080d528200d845140000b8109140b901c1180303480070f1901103888e5100600b00e40c000040601e4054000c107031340700032055001c001c070410820406070004183c5208104031400c43c0c00003516210780c4403003d00307295800000f040d201e92080100c103d032520b0302e07003180d511152280720040c042d611100c004106117030201044c0500703584146107140c610342e0120000f003030102d031000d000d021500440c40684008600044080120400c400114402c51050015550f2142200031103000740c035200f00413411441c079240501440c00010004111107441c212041c08050742c40e00c9101c4094080d490380b0030805410040c00080441070b207241c0e41e840e66901c0314000c00e0459000300641c2c02c10001c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 245146384 1250 245145134 245145157
    0x11d04081b01020d0c03051603020c030a0c1a01030b0402150a2a0503070506040b0906040b040803040c080a03091a0c030301050d022815090602060f06030c0d050102040e0c 75
    0x822140e010700441d007060608001c0c4600c0094280f0351401001011502c410541c10301082d01e40302001604c40154080032507040ca142421030501c0801940e05030b1740e016640c140c2040c8003215040c5e50a201034900d48044540110014181940c2c513842c00c02044002500c04a00921015401103000004007050b44ca00e030f822030b40d45061000840c0a2401403190000c0031821b0701103d4040309010840610003461007500036401088541405d190107410104000c141d00c0440c4c01035414040002c80d0a44d510b40c1003a00000100d80742d460b0b0f400c00518030300f0030341d00c1100136200d0700c1c4008082680102810045680c100c0c00249d15000b43c3d81d41ca0128810a805024039410800045c0400c0c07414000b0005554000783c000000103680b0310194200c035030104802980d10b41807074002c10070180c01c5041400c0144880c41e10445c203900e4682e000c0e5440030050040c07a8008a000002040ca840401040d45030500003048507820f21030301c5c10807034000e42c003c6c0607410704802000c0c002400e1600000c100d03070101d000b2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 245147634 1250 245146384 245146387
    0x5060a0f030504080409092d021c0303020d0906090b0f060a26030301080a05010615050403060906110a0e120a050309011101020c0d030608010b01090b0301140a0b0a08011d0408 77
    0xc0c1401140103020061084602c01001c3c000483c40c0201407096402061044400340f10801c0d00720340030b01121107001035080d20801e00c5031503000180c44041c41141762740590700f11a41240540c0c074044d0040d00624684c88681842e0151840910040350841078074140108070520380c43c2c450b01000a00781c0c008581c4190460000502040a01c2c0c0b2580d020060f114107a18801191218112445c1580d1081e445a00c45901051220041c05428402c80f0000c0030600c542086c1c455140c440503100307008600c07000e040a560b500b1040144402500075090b030070b0340314000d80d503100340307142010304524031800300d450040111907101040d000c0002010002c4503000001142402c5410004450f614000360400d0080c0d5000d02030000042410030000030183c003a40c4000c50f485091200b440d0854119072001810410410010890008142d08030f03419102e026403c0325400f500305000c10784145c2c0d19800761400300c5001500c00360565220780035606070b98481c01c0070300030300122000c1980c1e088415600a007440380b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 245148884 1250 245147634 245147657
    0x40f05040b060d0f0602180907020318010503060105070f060c090807030807080f07060908030f0f0f150a0e10080114071b030903050607030e0f0a150203041a040c090605060a 76
    0x1c1c03403c20302c950b051190049080d540101d0b61280107907000010035604180340f941200f400362600011481d80000390b840114109040031282d820744000e5008403e0511000001194240c1d20880444900300c0c0c21001c017100d035551500d811402172144841e44400035001560101d00654003082d014101c0350440400e0341010116215980d5540c04507130000c449100c100203010019030f0500515021501404a0940b2842c00010702890010000c02c0d980785030201d00200405642c402e204950442c0c652680c25204200000104801c0c1d05203420121000c2c840b0410400c0a004000841c8241c4074084000d0129000075009824000300940b6401c000c58500710000000e000f44044006e4a030303000389000a00d441d941d8507504c6c02c201050f5903180000c6e0301c94a0004c401402000f40405406200300105800b403981d8666140c000344060660b8a2950000080790510040500411507a20232202042c00f6003410702d010407142c0e4261051203075181c2400e200141c28503040c000d82d0303110300e52600c4100a464 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 245150134 1250 245148884 245148889
    0x30e060712030e07060c0b070509030d02060f0f06010f0f0207091409010c030902010f0305090c0a0b030403080702160603020c010b060a050d0b0307061d010207090c0306030302070e01080a0b07120c0509040f05040b06 94
    0x60010614020040700741f06082c0307640d400308030f032421031941d4dc0c001d44018207100695400c0d00341c00402003036074030b11030070300340040f90f42c2c01290a0369504c800e107040c9003c66030701a012402c1c40c43d503901041010741020105407841c1440040103000b203904000800042c821840141c0903501e0891020b0b000c01d0340080030420702c602070741002e40c0c03251042c401d5a4428a00d0030000d000040c1613088103001590100070401055008216aa00042035000418101000868050002d800b0340501c0c0205a008144c3e2200100c09400503211810f0050901d070704c0b005074030340007411500300344820302c0c4103428501c8030f5000c0d060103c0c646040c0d50859071854255146100c00f03200b82d54000c2034080c110300ca28900011035076581d2003007421103a83d85d40c003ca90f2514504000b40380056a400c0ba0981400038401040040000920301c3c4041364051a0840e1540d90720b4010340310007219074414007900703080c45100c0031003e41c000010105584101c8080001d84024803240c000c49208030781c020b25913204000411601d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 245151384 1250 245150134 245150153
    0x31407080408102315060c0114011202101b060e0c0406032004020f0306010309031103040906030309061805191701060608010e040506060d030e060712030e07060c 71
    0x154000c00c6100c1c038255451445078a81500320700d40030519a0368241100f5406800e518454001d9071007241180141041d0204800c04140c50b445148244400102d0080240d420340002015000c2941c44517403540c1c0d07c007400002140c0c03840d812032050421107403580310b081c0182c2581a46081c01042803640b4003d0340e9a0400800e9141252802c80c851480c0c0030405649a0285001840c420041e5161a084031103051441c4604007400b00c0c403560051001d0500e807039405003944d40c400700904e401704101040c1d00341030343e8072030924503101141c1c000010085500760840e04214112031003999802c000581d94a81221709030250041e21105843c1040c0402a03880c24208074440d154805500d444800c2c0d4900184214881e210460441a515904c1c104112900003183d9030052011500039415483c096540c20b8450000500c61480b40780d10300d00c200c040c184a40669850700d1800f4200f50760722080350900c5c461045a8400041c0080c0c140307078205c2c80e50350000c2540411034050b41c5400d08a04160f942d0003418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 245152634 1250 245151384 245151397
    0x412050307050c011d0c10050d0510030b0115021c020604060c0504080f0a0b070305060a0b0a0c0602030a0f0c1404090b121609180b15031005091b030a0314 68
    0x20020b050100381ca41e02c0b07080c825054000b00004408204d54082c95520307080032071500030544109403000819100d55089401c841d01e800c5888800150f564800440c00020141c541011b820900b0711301c0049545845405446c0090340c1a40807951446c0d01e007191190032080c2082c04034010f8100740003140014096070000e00a46409003030142c240740d110501c0f41c2c41c110340c50000010319480700b010a000d020352140e14a401070580c0ca814003d43c40e01c00c1c00314181c0007003441800c4800e44001040203009209a01150083c1d0348200d06545d88d080c00302800d0050b281640045207001e183c89284030304140902c280c110318400310050700d0301b8603160020100003040c800070b500c0d030001c0b010482440140018014082c03e25071000d4940c0f0f107581803450030002c40f11681a102c203c00380e5901000040364100180c2c0c1d900a81407400c21110f9400140840c0c1450f843d9000030546a0400007808030302003000c02c0d010504014408410010a041c0040655403020030b10b005e80881d1140c1d040360004507040006002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 245153884 1250 245152634 245152637
    0x3030f100b0403150f18170307020601150e03030301031505130b06010e0118030605100603021c0c1709070812090907200a031d0607150f09050109050102040501030c080412050307 78
    0xb03003801e171000b6000903600e00d680d0142c40c0d43c0085aa0404000d10382c1d40e0350070611000405503081d0728018030041c0da0b400c81800340e07200c0034081e502d21504180c421140ba81b140403028040e681c40e0b5a507450220740c2c01564201243c0d4a03802d180010360383c4032209400902494215a2516243d103135100156204580203083c40e04001c80c244c0448141104072407403500451003030030002981d103041d406c460b1a9010981141003014010040d100b150500c12080039080807040400080c40c1455010660341404026601c03200c032441c20042151410000c5903171070444040505a480e161000700d011580b0b0b200300740b0156800fa850b4000700707007210301c2800d6041c05c01c9007a070300351119041e9800d1000e01d00016000100c00040302d00520010700d418401c0000164441607695031b04004281e6a14030280c4640131040c28001e036620b8080fa040c40264128400c4243c00100030412001c01e0709215010794810302400380401d00300501100d0301442112201e00c83c9070040741c00388c01341c08200012600780d40082d10900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 245155134 1250 245153884 245153891
    0xa03020306090a021801080604021314070f1103091f0e120c010e09041218170a0c0e060d080f09041404110a061704050a06050903030f100b040315 64
    0x1a10100081c50107041d44800610f0030b1001441048256007003140007810000700700c4010000c01c000020782d55001079040759030701c3d1070034041c0f0041401041c0300a004d1030340b1001e010900007e90382046103000284029507501408482407080b00d42e0328422110325940081103609500c8032104400541d001d400c040b840c110040c07888000014420b90180003002009030416845038102d0b6030400c42001003210700707407500c207002d107019203d0f20070020114840400780400d10017a40c080300c107500c22000103001c500344003048002014a841d0740e1443d00740811240100c19610116044865008081c8940401402c401307800180c8d03618500141c00c0040c101108860034810500c0b55652030003010703107401c0c00340d02101d0316182c1400d142c03142c540c407503214900601040388203201041d84003448200807145145007070b200340c88500c0d00510b04180700c00080c0c102440c1100748120131740003100660055200031002001038030781020f460040402881003110300c840030402000011803040c44136680c504900f4000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 245156384 1250 245155134 245155139
    0x702060403020301090b0a0e01090b0403110f0607090314011b051309050a0207050d0e090a0b03030c07030b0105010f020705010807030506010e0a0e1f050907050c070801020a091508060a030b060a 85
    0x607017035959908044a444049500300900241244100025010801d00a00c4050400e80b141034480c0d0002d04060100690404690010902040310300c1101c48504100c412501c1e0003600189000850701040f1098260450080f80c1d1210500a081d000030380c0c00e6941d200141c00c14002d58881d0301032240c0940c556051000055224041e2042a1081109a20140ea00c1100f4500182420818060780302070051071520210644c0f80d20400a50029840d1070024450107000d00003441c41c026001c2280c4940709240d8040b0070402ca43ca181e5048a800781c0307600f548110803c000340d8940e0401c2c0145800110300c040050030720381c441c2c0c0055800c02d2040c182492000865004100300d40741c5608000da00e42e00e840180007a410b41d24001180011447d4001e201c2c1904141c006201c2c5a00a4031540070004081034480d0f804c10144480d5000f05100320085665421a000203085402c46100d10404403c40d0b032603102c8400e00410501d8840c03040188000403860641d41d900b142408080c040c4e42d00a40003081c007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 245157634 1250 245156384 245156389
    0x1b0309380a0c030b01170c160611040602070b0a0507111f0801060905040207051f020c03070f150e03090d0303020f0d021201050a0303021011072411030c0a05070206040302 75
    0x100390184903a4140815050310040e0041c081d41e10b41c280890410641809480106100403595a000200c018402d5500c3d14641e0350080720010019010788105e14240b403e51800d20080001c0089442c5a029107201d40d681359440c1200303003d60464a03012650030400e100010f42e4445201060304c0c002010184542c204510f540340b10015484940301080ba00c5005010880e000054480100011101546801c009613642d640742c2c01c2c1c002000414048401105035030048640507120785203801d0007121b80340c42c601e060442c80c01c2064001541d583c88090007401d1114441d010704d0704450f000d0001140340541035414040d0410034a02c0a400b0140d0a100784c1c03190301001c0009043c0e07030901d1a009610740844030b80103059000c06900c0b0a100b0b01038200c0410011740c001c01c0c03410b0304914100001602c0e002104011a061003000e100401c40030320500550b6680b0054600e810841401030020490150094910300342444151082403160409001d00b50b00c2038442c00042c01540d2020300340d14281541d0707a01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 245158884 1250 245157634 245157743
    0x1b0d0f0203031815160809061509090a0218070801080303041a07120c020c0f04061410030906060b19032a050d060803091804032001020c0f011b0309 65
    0x45450070b0380a0485c040150590080d007454103d060031014101c0f500f8544a2441c2030748613190a60f00034810743c400940d4500050041e00c60b003507009800f19a2074414000411070019086030742e1000b044001c00080b40b4910000306407840b0315485441e04640460003003a036107421000404034001c12100d501c0c1d03030f07000c8400d5000c1c4c0413031101d95400505050150900f080742d00342c1c4410507a40140d10f010130400c441e160945910800c640c06070741103140078032903010072005009042c00180811b401c004c0000340780d44484d0000c3c1102620340c88a1312002c030311040101c09990315081c000e0400200302400600040d9244155461044c160034850701d041c00c502440340030f550a55000070169003010529045604011410850100941d0301503040c5107440d80c1d0207402040110641c0060010380c40c4840308540c400d604885540003100200c0d20326008154900b03010303100e60494250941596440300034024000d0148070b82e45036010000d0030030f202d07102d5000c18400c0c0c403000c1c1c00d042c4c0c00d0801d00c600900001000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 245160134 1250 245158884 245158891
    0x60e190507050f030c1005030c0412051c031e0209130501080a020f060a05030708130609110411040b030103142401060915050a0c06020903031b0d0f0203031815 70
    0x1e002000d00d0b1404116a0102a40d1600e01039000386611042607900d6081e500f5202d1098140981c0307039101c24403030581500032508003802c0c008416106038203210b8001750040400038400004051000c81180c1181a03840403200001500851309800c221003c403038010304140d41014240000d514008800c80c01510800c1c0d000e00302540020303d1640030740c1083c0c03d0084024a081c2c400902c0d11b01410402071040c0b000400160401001c0b0020405484414040040041e048002880184038909181101041c0c02e9a01c500c034901c0e105d0106141e9040500703a504940052144900b1a0310315120b0324503038014640c6101c04d50146100490140c00140305103107044020315840c402030340c100200034045402ca038005e0088001e140c00780d400ca00f680b05085503150300c00303032412000c484035625040c0c018dc0a82c0600603403500010480321603040524131445400010013084a588085c203071826116005419040c00040c1c000b0000590420040c140034a10320303900c40111100d4020740303040300c420f0b2802907 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 245161384 1250 245160134 245160143
    0x5010b04060b130b0a120e0c090708060415140105070204060b13180203060d080a031d010b0310020a0903200307090c1205010501091e21140c010804060e19 68
    0x21032214030f45000035004a002d420102c40b6145840c81092000c0c182e000c0d0f040c0200e005c00d4039159802004e0800380255a8000b0002d0301000c40e60800c0e20b405401c02408941a6010f03c0c034000420502c0b09500e04140201d41c641034211040f0780702d00b8011540b0707601054042e81c00948412002803002094802850b421021004098842d800c180c1c0078185520102440038100d40140140210341c3d6400006045850b030181d446a5940000802075019001d400807130030440da00480055039203070040d0071155941c030044041c2c4120980c41183d00b000c074010034005000140c0e00c071005200180410740318080182d024032a011303440f102600064036194940d041b0300c40f140c0e210303111074900540104030710443c5540a00140225814000001c0010702c082c41000070b01d450004072103003011004803482c0c004d0300b07003807640900e510101d48031a0410042c904003210301c0c070400c406c0289007000114880e0039050050b541c00c2801c0c5c40b00e0302c81c00090700c1301680d0b442190240100c9009000c81442c803941940380305 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 245162634 1250 245161384 245161387
    0x20720030604080d0f06210b0c0405150a170a0501060210060e070e010c0602070305070201110613020f0a03020d050c0a060504140118090c0e040c02070e04020618060c1501050604080d030905010b04060b 88
    0xb40d1501c01e60201c23001e000100000002d1009005c10390310303400ca1040c400c2c00402d0240d1580c0c05014200c40225031960350403c41c21146050003a00480382e04294181d0340349400702c1e69010028159502142d070540304d03840044a800000c188408d11901140103110014584102418501c2d12400d040ba0312000b02140883c000050440c1107503006030007134a03140340da030f009805a440c20301c18415407200340c2d0380c0080c42036007000702800355991181ca05801654024044000140043c5005503541c1038020419101c1c0314200c070300251640c415400c5409440e013000e4180100e15598005581000d078100c81c100040421b1640032550700034604c00c1e440760700c00560342c8120345107041703003440202d91003d100c90085400044052120341d0030308585940007681555419a03940d00c1c40321070071003582d00031501503100c04001080401800006090400712940c0114240319036640c100700143d17441035120300543c68009d544840b5029009900400c5902e000300700101d00c0240b07880c001070841301039801c102e041400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 245163884 1250 245162634 245162699
    0x30319051006120917040306060905150a1a04211203021603050f0d0c08070809061302040905151303020105011401052b020720030604080d0f06 63
    0x81900480360801144031400c450349042c000b004048424521240c1502501ca10a1008109100395844688115031065039100c1c0c0d00e0b860100003030480d0388906051342e810100400e40401c24150585444540202603801c41458090740290f400e049500c03907a1504002c0c000040c1d40b906440c1c4150940b07940c00c10403100411140743c00e690001d81c50101100f00b500c1440303a8440c2401e00103849641306d0f01800c2113905d902c9000340c00c10f1075109140b0305101c02170500f940115100d820502e032501a124584402d8290340e50849016038070101100e20250f200e00180da01000342c2080d0340031500d190b0050040ea400f19081d81c2000000c0c0006650300c1601c1801c0d055800181682807148602500014085101c6064844002022030082d240740405680502500090070300c1814000108145000c500355100c2d5441c0c180014400c11580444195101154100c0326618010a20a11544e80702d00200d0801c07940c00d8031000100214a0310b051070603622000130034400b812035000324230714107800c803592172803030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 245165134 1250 245163884 245163931
    0x3140c1b0a0209040f02011e0207061202040f080601030b0109020c100c021015080f07050a140303040f092c1e0c03031b011407020307060c03020909180105060d020a030f02060c0303 79
    0xa40d0b03021502e11f00c40000500d49c0400c440c4100c81c01440c004211864240c9400e000b03204a89c03100c00036071418080040c5640300490682d040300d024001c0032000343c0e43e07040d1034800da10a45011042d1f90300258040e000d040b03900c0d40074410118051046a184504a110140449402c400404140d20f070300c450802c211803041003181035030b5041e00b0190800c103240002103458070181e40036014541a034580c019101e40c80c200306440041030b02982c071040080c0d41c0c0705407030018554802d00014481e40100071200c940303044c2d1100000408141e009001f028141181d01007140c102c440e103080e45001c0d400c1844a9943d0800141c010450400300003140400270040041c2141c0c42d0100c107145401c41403041140158020050b10400c6802071004140100c00c6c030f41c2100203210341840d06520003012402d00c5008445032916011030b0030908003c03ca652a110308202a400802c0c0000f580708000340000d000054030f448d40d680d9201c2c4050034040c00c01c4100c6580364103640080300c43e40b0000040c0c641c1e03105041c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 245166384 1250 245165134 245165147
    0x42c0f01141c08030406022b150e041106090409030818010b01020a150b040507020c09060405011422020a020a0c0501140a030509070f0b090103140c1b0a0209040f0201 73
    0x800c42210380d442c4894185840050002840001410b280070120020b024446640c0495401d00b003110103940d03c8140c5030584200d02c0708020120a0f685141c25161008444a02031000c207694055001060303590740d03590303000c4000310f04284c1d05400200502c00800345845501410204a100f40c4902e002d902d0b1580c109002c420f03500e030b07110040368113100b50041d040e6004100b9003c2a070700400a94024494100088060300f801d54542d500180380c04100325581d81d011809100314801160708410130b454000c1000f060f00d10a006d100450b18601d821401d030307854811801629580c3c8184450502d03c2c416030000100d8120035100c00c00f60b00700f0304060080010401c850000350000342480d410b403000c0c68040c94018040c000c8007505142c2c0e904c01140402c0c104118140c010305000c107110b4210354451611405641200790360030b01003030801e4404803102003000d002c030348a070f40c4032400f19080064490544107124001c0140c20424020700c21038501688800ba4564031a90041c806400c0d465201e10004012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 245167634 1250 245166384 245166419
    0x1d040b033f0405150a022416021c0f110703080301170604081c09051e010b062d0d09061a01021506040e070509180c0d08042c0f01 57
    0x649a0402080c0705540d0780c40c860044080040c044c207a2140807a00042e4500f81c86200041c4020707070700e00030600d41f8400b551701c680e00c035408a004140c030ba0b0090030300aa03030783d14910340d200b1008001400440002880741310044903044062030094039106420071031a05103121a0801d0ba0441000801030041e103c0c8078000c4040a0406c600a0407d40b0706511101424014138407011081034000010039a03024590b000092070b030b90844d0507035844840c4455840c201303203e5403860f040903501f07290015881e490b04200755201728180e580710707010903190707249540081050520400008002840b01440c203003130714895007a030244100710004019080c410401e41452107000600c0c1154080b0340d0701800d030800781d040340b13411650680380801c01d0045102510b041003903d812240e04100d1440401070022202229403c00301082d00a0704c191100e01c03810301c95101c2c4168805000400f00304020001d45c091300c00c2c262803140303003032800c800d0313120300d1801d00303501041c040d0f03160400820f007000107000c4030b400b2002c602d41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 245168884 1250 245167634 245167753
    0x60e0105270d05030c06060405101206111e0d201603050f0d05060f06030105060301150306050a0305100515030d12391d040b03 56
    0x1401c610700c4410540c4644481c1d00d40010840c1c0e2850380c42900c03050b40d4040300795404002d80307449141d9004500d5840a04550203841103040402180e600a20910301000b0380d800d41c08031426034882c80c0c4807040680000050685400d10422000b0031544500710900c40c0e00301c01c03200d650780e42d004110011040d1840000300000506e0b004054940c401c0100d0121a59841400124141104541805d407a80d00074084000c0540c00001a180d24003405030740024030a800c211090203400d01428280312150000740101c070b800220420060003002400721041d00591442d01e00410060303141d0004c629002541e0b44200d0b12513015424042110080340540da501c614000f030070032000401c0c080004d035240d52503503400b000d000200b0019155018030b40c21400d00d0000e01031008904c00b034003220014100c480000c03060481e269036101004d903944034150b0300c4030900801405107120150042080010040440c1203a030600c103200c80b2100005e41e25603c002d0000507a00d03006036239400c1ca0008814240308030790142 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 245170134 1250 245168884 245168887
    0xd09150e070b04150306030b1f0e010828020a030b010321120b0307030606030b24030721060507020c0103060602190803040312050c0304030e010503040203120a0302040b1201060e0105 80
    0x8a5400c1d20181c41c22200185013954030104000c405070000c000940000c0e002d12090820015202003041c03000509a8036250b841c3d4216690390640400304c0743c00e00941034282c00071140307100c0381c8001c0d81011300001021179034501c5444080d400160b18600580c4100c0c3c1c84600c40004005000200c0481880801003014811900d010064010314000b000044000c2d81661200070a003140c030100004800303140c1c0450108007180d180e003400325000004407205c98805406820180000c106a07901110710314014005000544c28100020329410f8107e00b12030380c682403010040046426402010f009034940d80142c0b28401e86200018161131003a0002c0e029980103502c0040c040508902000e0407a8021000039201d4442e0b01d401c0780c04400720a50070406c2400c0bc014003c00b816504011b40c01284661204032100c82c442c3c1c010745803400115030103076040d08240d0000d03031038001c1f6800410018403a0300e001840c081d2105040c030340d00e81082035004622000f140041c0121030300140d01d034031421000d0a005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 245171384 1250 245170134 245170139
    0x503060402090402040e071a07050f12070221010207060b1009050d20030a0b0f0109050402180c0c0a0c1505041503090507050a080d0e0406080d03110d09150e07 70
    0x2c1c1c0c10120182009020b19034581e640e40c00c1c0902841ba4002401503615544154041035688000c544c0103104140c0b4140901058003085610018070401281c4490754220b0402d41c4035020031134030100c1c000314a00d901182c07e10701d5030100002e100518086106840c00039501420205001d08038424908080500204c1103040c880c0e6900e026009440980c046140d20044074100741c42c80d5135074441070716035805208151506040224109115110300c04d02d02102103641e1740c40d4510700646005680203074201211905224000700c0d0131110503800300700d16810520740848106000e1424500d50b5041d280342d84155000d02c50011300e99042d240240b164603003a030074103040a81d0460803203100c449480a040c1d50b8003422040100500c105002084002c18503080c42c0c0c1d903410303419124140c0c104403a000031003d189020042c0381034451202076803401d90080c1441900304c902034000388480185509034000a0003000c0c9030620b039010386a1028826101a2081d9203110b081d5400d44840c4504e0980e1900240c905 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 245172634 1250 245171384 245171389
    0xf0608090c0102240a0603080f180402030105010c03080601170a0c09150527090c0309010c030e030301060e061b01090308070c1109040317092112010e0408041206150503060402 77
    0x1e0130b140340107200d442c10881c1c035600c401d8001800c203980300400c074190118028800095150143c0036198620264207182403812080204a01c406d0048502085407039648901180c4140d4010394007000604003840312690351110641c0c0d000d001c031201100070f51141d0801021543c0810036400030981e511000d1641e200307030765000c1c0180c0039041c01086015000e01919034107010802e00c020b234240d0050b02201d071500740804460003503481121a40e03803540c2010018090144203105000e04454218061070469007012000c43e140b8070842c2e62298081d205105450005207840c00303000004110500000f0748808070700c1c000d092080000d0101c82030001030481140810000c000c0c0103111a400c940518059440b813070241c0301459841902174268004130304101c00d120ac009140b41c000c0350544125143c0b1894407024180c075200302d1000c05910b0498000400990804811054205100d8511079081544070142071684008044c070a94440361070b8510050000c101e01a1640513007801e034080e24051605402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 245173884 1250 245172634 245172673
    0x307020a0b03060307090903030b31020c0a050712050d0908060610140a02010e0c06040f0e06012102090114090108060d0516080a2d0f06060f0608090c0102 68
    0x540d510307244000005100c07a50140000c0e03020f4080000c041105c0a2035040c010010011000c210380a04000e0107a000c01e180725102d82a034040c3c0080582c500c0000f401d03a00c102039082044500241d2241e190504000f070800c0c000c15010b001072954001c021102d6003002344c988005104800140b12442506224000000c112107922203403d80303280312002d4010000312001031504000101c8844041104c01c68181c0c1074210592046245045901c040d4001081002d03500c02c034800d1411103602c50310104034501900250790707800312050501090010421918103900c0381d40140a00b601d543c005000c03000d660b00441041c901c200302d6188282070240700d00c00a0600000078000c04d101e0450001030804010080002c0c50b101c0342c00c0741601c0b242d03d46d0360000560700c41419400300c400f60444010071003204914100c60248040c0070070400811000d640395a41d548805007400c0da03843d9150400418201120203200d0000c11043e40ca0000701e2501002681c01c1c9003407210058115000001c1641c01200c0004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 245175134 1250 245173884 245173889
    0x1c1b03030b0a050a1203141908150907080f1005010c021908030a030603030e030c090610020111040605041806051315030f08120a0c021c0203090301050907090b030307020a 75
    0x40024000d81d800d40020a003281691000b50721244100d000f0800b1103c0711009000b9900c20380302ca0f000d5000d80d150322002030150260703549481c0401803056084601c078004851700031440c490b4035078a07807842c20003151015800725142e2010840c10400d22031042d050301c405503408940e541980201d68180710000740090f0120002a22030b91801d050004140701480480000b03100c040f044135918481c5110140182000344815008116100400c80d2641008606104140780050107090166508010040191008402001103650314103022280d107603803100a00203001c06448090301c907450075900c00c00404400140044540c1006001c0040b0740341c0c07180300c0640e5034ad9494082541d00403862001028000b50740007400d02c410b614040d00620403090000d0114082600001e4026603c4481c1503040d070702010f0701d04005070310080d100d10120408800303d032149007141c41680d2500403802c00203420744d2415a81a060f0b50003040341000340540c1442500f6601c40b00341d018508018540d00000c0b04c020061 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 245176384 1250 245175134 245175137
    0xa0912080c04090b1c1506121104090318030c050a09201c0923030f09060a090e090d1d010203031611060a020c060709030f0f03021603051c1b03 63
    0x701001d06869982c00c1d00800c1440c10000c0c5d10200c0c00c03c504240425401da03810101c850341c60a81c020400e0f203121208243c800c0d0300000003401c0c11240005100003010024010703401c1010310010062070000140c05007008600030040d0382c142606007420840001099406056050710f40354441545010141c9000c01c596003100c6130366140d0034a9600d44255900203443c01c0206881c00f8846400c025115107074503004000405050740b901d080401841d03681c42040304042e550f20003403151040700d15018000303180b51400303407821281d101e0741d400312001800821b40e02106560401085800c489911a969604401f20102081042c035000c0001079100d110280070b0b042e030b41181040070b6602c1c0c0e000c0c01040c00b1a180c2c0400315100e074500442d40000030340141980707909074010230001c03a066900c0342e9401400d0301e4210901d07280c49602c80e643e002240c40c65400440c154001d0f15156100c0705006407091000f0340c0035101801c1c6080011f501c00f0185150040030300d0603c9400e0000011840c0c03141d0180300d509515 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 245177634 1250 245176384 245176391
    0xd0e180f040503040510030509010c0908100906020706020304110f030d09030311120f03090d030504030e0603060d05010501120507090606091a0f040306060503010e010c082d0a0912080c0409 83
    0x71418800e055110307680003550000200c1da0310400ba960315500103441640c4450013085002101a0115054459449084d16940c044502600359000300d80c00360107611b218100040c600f800c9070b65510300366041190b0940c0c460380b01015003080340c10321440d02c40c00b05500b1805040b50b0070f0484405010040d007408060304200d070150412080010401c44040380501b19a40b03641c42d140c100c1004c12035030b030007120080800e0044481ea1400a0b01a00940c0e01a59040d11100c00146c004414401e640d00001c2500d540040ba2990f46000305201780325160107025021692040000746082043c80e0403400d03030000e211146080d03c1000207544c400450401c0e250303c50050020005e035005640e000d4000e80042d0040110001000420010240c4c000021503034254020b0012100c0c4074012801c8a0400034800046100180020003130803103581c080403405500c070000101e111418846422101003181c0d800c25103a941c91f00b00c0180b041010a210801c580340c90006034529004c4016807250003644200c0c51316945 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 245178884 1250 245177634 245177641
    0xc0a08030a11010b0307090603030906081b0f070c060f1d030a1101090317090109081902060c01230414030307020a0209061c0309141509090a09020a080d0e180f 70
    0xb02900714000d0080f0080481d05e20315102e404040061609100031400300d5031060000078014040d12501e407146601f0f188181c950078070001485100e90200d1650031406804005c0400010850400007025020036914084903140790030010304100d03c0300c05080c8803c0350314101604d00c0c1c0c0e400a00c06818961140d90790340442805801661022080d400c000c1c0242014283c140300151500060070000703000741d8500e86411307a1131810b1515810000b0414400c2c404940840025050400052000d41c0d04d03000009032600f10307181d0301701001c1205074040c10044510b8040c04107200d50001c10c41c244031000d1010794990308154101940e41c4400c0345d4003c1c021210314002441c1d0f03a0320003a501032000b444454148031217040d4a401098602e103030040038032a00d03640060b4591401d00000d40c40c0d08040300d500181c5440382100c1004200c8000410144400382c50307104140041c0c4400c000072009001560003014810320205000d80700c04540017444d03000c2c602444101c00910a04808143c12140d000b005014a0304c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 245180134 1250 245178884 245178917
    0x91501180b12030307020c04050f040f02060408010612050d02010e072702190f11030d050a060909050a1106030424060305010213030b0105030607051213061802030c0a08030a 76
    0x1905850294007082c9800188007200c0088015445020b03c1c3e82501e01c0c0c091500204000c41ea0260707509817010194400080003c1c000d55004600e05000038115130905544020707060035941107070014460110004060010071004108452111100c0d0000b8071004000c3c0540540d543d0b1fa51149040d003600101442100c0350440000345550158504159134415803803191142500810668000060202e411084d2482c0b090000c00c00d40d1004001031071502c0d11100301d500c050324010702071160082c1c0d40d0b04002988010b0b4441c0011661060001c1c0041104504280c140c6a000c60207040c0038072010000c000008001d05010482c4801c6503400c0c00003440460729800c02003031550030043c106d6100040300c01d0100916444070044910803404030a80303a817a8010700da26450300ba660400486d00070700c850f03e20030300420302c03141d4003a40501a80e0340200882c0c680501303903a8070151115a00780010401d00650506119400c2c4000c81580c49286051410b00d4080e9a803103801c08003020411205c0c40300b07a921 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 245181384 1250 245180134 245180141
    0x1722030302090312031f0e01051908060f27101e05041b050126180a08040f08010504110f03030d05040804080c011404090908040801020304140609150118 67
    0x2440c05000c071242e02d4a00503550701c041d1700544404110b044a01c1c046600101d00300d1040c400d0361040c0520b051940d00e071a05100090740e100760101c84070400c0040c085451001003102521840001d009412541000c1000d052060761400000c140e800601510203040400003078010180c0c0c8408000094402455440405034195240b15200341800e0000713000a03c0040c9207008111240c180c0c802c030450755241c005440c0c41c00780710040c041121408d606030720b0100141c4e542d03543c0f0090806109680345541109907051081c2010100c0b41312601040900212005c1d007445409001c0c5a0003c10690500c0d44499030b05403074400070710b8442d2810aa0107111a1010310940c0d131030300c082d014140082d003418901000303507400a000701b1519105465442c2101d6100d5404000c0d80011841258a05824a40030402a0465600c2134030403513010040018030314024801503105500482c098018040000b21b51420003401920425035640500c1c0118110003c40c00070301e04403041c5076030b151030180341e101d05680030b03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 245182634 1250 245181384 245181397
    0x14012d122a05040b0f0a03020d05070803030702010c0905090603030304060e0313080a02090a02071e0618060f060e0105010f0518040204061e1701050d050a0501020a020a031722030302 80
    0x140400e41c40c2400185005088903050720340454003488240c003194103101541d2602d42c0d4056000d060b4030420409400c3c83c401d1084c0c1940501c041d01c50041d16079075180e00c0c0da40103407203910050b95150703c42c09981d648580705034040c0c50115840c2ca841d0410b40006580d82c040500040c1400c0c2e9640348400b20b9960802c03c480030302641454414155070b031840c81644030503041c181a4020560790000440901d0b0a200f21880c481d444003100c01a4441001c0214003641217140c02c40d101c9546030300c0124a0a2092400000e00d48038440200d210b002c0c1481490503954181c2c0002201c40304c0b0310040c48260307005440700c603c0904170318002d40c403194141c10700303140b0a40500c02250054400640400d00992114401180f80362110503050000c6034640b084850020402a2154061007440107120b18500904040c18207030081e1300301d80c0407030b440e80c42d500d089030f0100e03907072001503480301c9030007010583c1100190517503805c1c080140301c640c6807014011047c46803c190f140142a4410703001e804050196040d10354 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 245183884 1250 245182634 245182673
    0xf030906060b0903120316050d110d05181b0d0201090510030507020d0f0e01051602040501080c0a0501050715050606070602030c0d0b060c070510050d14012d12 70
    0x5075507031280d040d2800e40c0240c0c0c06500034007030803050619030840701080380c0c00707022030861220003c0220b08080307505412000c001e80600d91220700010340b825a0b00c000d00081e5507965400038070b9007016108040002041c140c100f48903000011303004041c2007040e03d0f503101d001c41614440b0301d4032803034401200c07021a6a007001c3e41c8100c10100d81e02e491030b415404a441620b15030215000d1040001080d1001010070070301c10000360f280341c070090042d4032680c003401c0804c0001c00007406100644c0c0c0000c082c1d5400740c00a5106030300c800714054030362030024103880042800b8245185010301d40d171150395030300c81408101c503a03054690002c175174251111400c807400140c120501710349031304207411814050707400401c240c201c80b03043c04507008461a00004443ea01000c5100400e0800d1804040c001a40a8428803806100041c0481c01400e512802060f6404040307084900240d030500c500201d05043c0d160b486006072038210074124100120510503030a44403607202c901b0100019180203003d10620448108 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 245185134 1250 245183884 245183891
    0x1a0f040b0d0b04051006230103110d0912080c0a0512042303040501080609060d170405040618060f080607050309031b1f0c0e04020d020c030309060f01090c0e010f030906 74
    0x144030000c10081104c0c0c1480c0014003030b0541e0b9a07c9251400140441c048101010448400c0158025807040003100391860881e810a0b070035080c40c9049408a031001e80b01d69082400b407203d01d1307910551080d48024400041c908282c1088801821b90090403d000d42c241015400302e03050040b00c608048900300c8075907490b92a00790468400d80c4a80191007806e011500d6170010400030318100200303e00c612009010440343c0e128944890740401144500e807880910b04100205150700c0c1d50151a01804404090b514000201000d9000300c0e160f5131300c101102150791a0620203130310040380641e00700c0c210b403a01546035110750b080c1a041d40314414101e0800001c031100d0100c00c81c400310304a4000c0041c0055031070b50340310140203e02910007405a000010b60340843d10a6103140544c0034240b440d80e0003800508200850192910b0b5a00588100d8000d41c01281040754421040008902400c204203041c04141140c0700c01074180c40f01850300c503041c0910102ea201182d480799020354851a001401030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 245186384 1250 245185134 245185141
    0xa0e131e02150408010e0a15150b0d020c1225110a120b0610050a261015020f0d030c05070501050f011e120b060102070f06030506041a0f040b0d0b 64
    0x2d1203603000d44180d0740c095090441c413800d07128001c20000c243c2504421440581100508001c008000040341d09448030400080070880b6803040000c0c028140801c00300507951030880b582030b407900a40c00d8200b60a86801c01030380104003030640040a0b00a4018400c8008800514011120070848035a031a00700030019000922035000c1004031a100d40682d02d045101c1c0c41d141e003401b05e4020202c1d000c9010884c2000102c4440d8800c1115800703421000d102880d11030100402d024110340c00b9103040314910403859062220f088043c03054a00c0041c1c5d40002c181541c5c000c8a400e45a1003c0c41d4540300b41035407140c101d00318500030b100711042d15074428001c00880c54024018004034901313000d914801c150015291400b2121410f400c2c0646101c03050a5503184025522440b6400005191f80e04601402400044c1005128404c1c07000e00200d480214072813424205000454030440c81c0c4001c1070300c403d6405122611468041c90786010150340100d00d8107044004a4443d800c85540189402c2029082 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 245187634 1250 245186384 245186419
    0x1f021005090c0a05040b010e060a030603060e0c10050415080a06030203010c020f061513200304031d04050c1b0f0d0504030b0c0a120905010b15090a0e131e02 69
    0x7035042c4164116030101c0c00d0b5880e14180022510301e010007501064a40c9145101ba10f41711001c0d02d805002441c0203d111a02d07030340c2c2d11060700c0c001d250282090740f294100640398a491504c2c10100480f0349015810689051030302903040698818000a20a01714007150150826820071800766402800030701c004071100300002d64907100d84201d04418080c82c00410008214185ca1640803c0000d04040440e101c030b43c40a001850240c504c1d605040c841c0c0c4880f1002100728000d10310550007074032450002c0315284a01c82c010070b50490014401c030714001c2040014036080c070580391480007080b4142020103401c4800f62030300c0c0800200e16034038400c0c20360183d12503038402c00900c01d4a10a103c41503c548a0140c07000c034900407a08a04007141c081e680c25610b00b07429034404007040d40a000007064061003038020420426400351315503c2c0207000503242daa64284807101e44004c203800442c1070014917100c54084501170940030000d00702d80b41182d00f10030035045061602081d940003030400719505060b044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 245188884 1250 245187634 245187643
    0xf060804030807110c04021c0e03040617061305130c090204080f01060605040e0705040f0b030124092c0a050412020a03080f1e01140307141f02100509 66
    0x202100080c0d012030000c0c0b6584d1242c00d02001000c04400248400c40d1031074200806034120030000c81910440c2130641801c1e10b400d01480007070b46c4001004d0340e0340f1400c1080c0203008135032182905007805014400e200042d111b0447c6218102c011010008280e268141529010b804001d000303000b034102c9140200da1240c25500800841c0c4000c02280c0c000c840e581c4070603090341c0451188001041d4180303c01c01071255140000d950020b03584c03609914240d180c0d4091029809141c0010003031907004001070000108000e800401c0082034141107004504207440101400454060000300040b24031f680f0003070364035800e039030340351644040400d0140e46031400140c00288004c50342540d188402c00c42c0d8801d42c40c004034010224a070140d035003444550355480d5142c4c3e100b1000d406008000d40000d16602c1c44d5802d601d03624041d0030542e078541c150503c1081014544500381e04070191211210180004568600c1030b00740a40a00c2d0801844442c2d2a1000343d041c0a4a144604e06a0741401c040011007800440c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 245190134 1250 245188884 245188891
    0xc1b0507140108101403100204060c060f020702030a060f0209181b0415030203060607080c0109031d03070e1305070311041406010f031e0c030f14040305070803100f0608 74
    0x24506040958910011180f4050955181d480c001d10707400240002e464401040e0f1301020b014046176135842800b92400220382c0a54000f00000d0307a201c05043c10004c0d94003d440c940c1d480b00c1419810582c0d41e40010341c0f03480d514400113115650344c1941c0d040380e03006074042c3c034181c0000034224014039074100068004140c0440d10b13540c03440c00000714082d14980b900d090b0f40580b41005141e640340e881c2000c0903402903102601c290f604c05401c2c4400000154150b00070030103081400000f041d05040740c41c0280c0001c2d1502e03a501010389131144082025200080c5c1d00b0125488036010860300d44880000000300003080a01403e58041d6190200a01c03080300903004020b04255020000081920354902c20760303005841803400079452201c4d501c010381c425041040c5a000c030007a40040940380104030000c41d4445010040881d480304401c00c0e015255114411040e8034900096080b480c15a4004190b4881c3c880c2c010240d40c00840881ca0102ca0450400c006e08003c94030f010a03561a100302034000034085 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 245191384 1250 245190134 245190149
    0x409151d2d09060a1811011e0e09012c0a09050706020d1407020d032706031d030703051228020903010e010603020a05060a050c16060f020c0609040c1b0507 68
    0x200760800845d00c292100003100810f1041004010b0b40c070a41c09032079615440c0e040020140e40090118201a884064031155450380e01d4001c00f86024840c420805130b0000351802182408100b0b00f05640e9000c1c208095107403e450f110b03a0f6141c0e1000d00030151460050500c0c410741c14081102c0e03800141c628808201500c0b4141001600002580584202d40c0c0094015654840c250002401400040050b584000e81c0303100c618036000c4803800904840c0e104a0000740c5401d184900c43d1071000e4400e42194000000d0b5142060644000d0720038803030501002d407441c01c00c0000030405280198181c00c0c40615031603005c5c058112400c4034010750170102e2140e102c1d51901d51090001581441000101da501a200100707103840d00040002c10707005074901d5014004d042048207180201407029111076410350303c17110087c43c1843e06c01818420400034050640d4405200d00e00c840d65404240e408580c41182d0200d41182c21901c100c1700b1105020040034501c56401c00b0008101d004030381d030760955015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 245192634 1250 245191384 245191393
    0x9150108220c060e1c120c0809031615020f0d140c06040309032009070f091703130b03070206160c0f0c031b050f04020702030a08030406020409151d2d09 67
    0xc11403110440c60380085d004245281180c040c0000c14041c9642000050043c0c80341424036801102190600c04102c40d200c00340d039000a02800f91452990b40030601014500c014603135003e10710000caa585221050382030078001030a82c0c0b8030139002003c08880c1c0008001050314180c0c00d1502d000342c500080c030300080710b289110740700009102c06400081014214005e19288494840a03000d0711400820780304c17141004240031000c5424408200040c10342c066201c021a5940411030020300c2074095900010368140e001c1003844072080d0b0001d91950012501c1c1c0741400384081c000d609881861022200800702c0c148507410380103002c0074261036802c0300d0203400c000d2111900c0c603114042141c898007807154810b018040c85101d50a00380c4c05031000610160440e81030303201d075444427142034004450841d1582d400050500c0401e0b142c6c0610040c0004000c1000140780c1007078010000b19000f11640d0401031110f038001583c01184103002c0c05680e0704001c085036220f898540c00c03580c00104039210325141c0319 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 245193884 1250 245192634 245192659
    0xf02060c07150e030a1101090815010e0603030313080c010207060c02060703060611031803030d050f101a0405061809070203070b060a05010516030c120e09150108220c060e 75
    0x1070480407091140041c0606440740b41c46d0340b502584100801400d0410400c82c0000c50808401c0083c008442101e10005080c0d61401400c83c040300402084240a60020300901c2201904c4010412560f90b01c40c510ba0f07142d4820b041c005009015106000d41500d050029215106401041c4240640c020741c1c0c05014047d15000c0941e51289559181c4c0d0040e03200700052140c807a24114040401d0500500380e03442c00400c00000d405807001541d103030108064810602c80724031102480300004025010101c6410500b5040c018618040c92140a026200c00546040d00e0b07842c4141c1c1c10940b0100a200c07000ca4102010300035500c0d0402c2c00300310740304081310000c40e020740742113098101100c505079515883c1030481c40402140001d4a9012030a00120300382d4840090300160304200c01c19450b43e110690303a07403801c0800c1000800681500c0103490400d59400d130a0342e00414080d80100e280c440420559294100c015903010040c001520590003d0401f248065100100001440003180c0c5100681c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 245195134 1250 245193884 245193887
    0x60a080601081b1b070b0703020c120105010506120402120a03051c1109150c150a18020d080a020708060901020307030e0714040908220306060b0f03060d0f02060c0715 73
    0x51801642450b08001031080c20700100d0b41204c0d50a070004040150f0703a41607540d000740d41c03007908500412405a0040d9665100b1414968140148088518020301540d40343c0000720301184682d0049608a6060200003000d5464100d81c85003210b48540443d01004902e050007005600592001c8600c000c0e0942e00c9040703103415028403650703040e031300046603c0d2030300003410054801464409121120414064035804520a1213442c1070703001150740d802d03542e18181c0e503114111008801c50040a120700203103000507881e400400d44a040c2e201502540e5200310140a900d0720b14964891200c1c1d10449080100e4510117401660081c2d5003a18280407041e42c0351982d90302c40009006048080b680e11a07007030300e00e150540100103913502a0014a140c001891982840e2421901c801412501321860400402c68144140802801034103048c1e401c2403110f501c001e419100c082e248a11411044001a05014912010001060b4014280c90341c2c1c0c44203075291a00c4010b00d114103010120407000d008407a9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 245196384 1250 245195134 245195161
    0x60c0a060c020c0402121302031c0e1f2c060a020102120f04020913030e0d030e12030a0504050904052d0111041508090c04110913020f04030f080702060a08060108 71
    0x200700914280d44581d5050389110360002184001e2740d051142c101c5030424010780314045100300e2001d949158000c07148100707010311078080fa2008000e03002d0448030024800e61043c0090400da40600e8850183c9946074070311000040c9107031086030f01c4040000e500801940540c010200d2120541c070103240c2d60b540c8010715007410011100a5008030140b40000c2c01184059410b019040c86401c200240c0d0b00c3d10310214101e030141c104101c000c1a42c0101500c0586000700408860400000c0114900141c1c2c48005001307008921a890080c4525004102004400c0c001840910f004208072181665000f026035507000110014407425460151011007000159048606903600e40e070420395032000d40d201c1110000c100801d9a03049010781c000c08200744d561401060f04c4c000840303010b00c1d1240c1940040004074813a921141d00a640704120641c40f00c5001c005807811a6000103010070200303807a0403c030445d449074030b0009601c0207000414560381b0350801d00107401560281d0fa02d043d26540c150720007182 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 245197634 1250 245196384 245196397
    0x611040f050108091c091706010b0f0f09060d02071b05090c0703170903030106020106060c26120408070b0105180414070f0f05030c030319030506060c0a060c020c0402 73
    0x3415200388003403206500070b101c0c081e00300d18003501320f41032420455030590311414482ea248002801050301044128291402408803000b888081e14141d4500941e42c0d51600c5070907a2a0301e5400040b404821403240a4203868108034050101030381c5052400c0200000e510070310007201e500c000c0f90103044900f44003c01da24281c8a01402e000f00369250303048c00d507005811600044040007003c0c4c03142c2c00c117081d40d01a403602410031240116140e5040680203425180ca07030300b200e003c0040340c05482001c607403020181500c40c42e5010340040001404040d142e2180f0520740c0d0304401030940300c280402c02203131000600c03103180260160096a40c0310380401c03e40040e9620b066040044e100049400f0806d11038108400d110400216010155a0040903070213401c241c1c8045076a00182d0810002810180440c070000d01044000d9807a0040f440180c80c0100b03400030000f0101f40e911800140b00c0c2d03d41008841001109030125204020300d490140041c0084400c0c1400500508007680401e003001e00aa580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 245198884 1250 245197634 245197649
    0x40c08010803120402150a0c0b0105010c020609040221010b091306050d060b01031b0e1c0f03030507020a061d0115080a031101090b0103142104090f110a0309061104 72
    0x1408031103a1600f00d07800d0002d4000d0342d1052008003132440340d801120003000c10700095214148002e0305c6090403d40800142c6c000750601c140c140d100c01c016500c03242242c200003011980181c6502c2c01704010420b250a1559914802281d28008200da2a10b1009011024000c4070301505c2e40300922480800e132906441203642024060707400f0350004100c0d8224113200308040c5000a61b28880c2c05410050880c190066070102c3e641c04820241c0341000c950301c04054062820032301ea90415903641c00d0085007480c002904055990001c1034036a03101340000307224280c2020003841131020812900072441000000040e41d0b42c80d1500001404005d49428401c5030407034005400f5180e2191002d548000180d680d58115542c0c0c1c200349400114845c403114040c501680320011405104981d541c603001c0e00350144000070754480ea144040003100c030220782c00c1c2e445011010032940c074220307806009131100041c0080d003c000400d0340a0303c1c95055116034500340c0940c20a00c1a00c421580c075054900c0354bc01641c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 245200134 1250 245198884 245198887
    0x1501060e0102010b030d0c020406090506011e0e0303041503050a090c0902070602090d050a17090901120201180821090604031211030d021905160b190614040c08010803 73
    0x5038011115108010018000410b22880800001b420901c141c80d0800105110481c200305504080c450b5038050600124200024204080080d0034466100455040031400e062414801489081072800441024044030b0701c5540740c409007401c0210310888000041c0c940f40005080902500601e03600c207400900c4110700b0303820540020003944c0840707000d07180d0076001c11403032000780c80c4d400d2980c8540d4065400f8081c8240395203010304885841c00f43c039034295a414031580d90a95520304c247d50440d180c440c02c40d40004010300c016203008000381d24240302d01030403280c0062003c1020a0345600405a03489e862510900b4407811801360103005d003000d40100b000c0c0701c01d00022354a808000d50f000024200b00000742005400b481c6594072a1009455454020810b6800c009140a0060405e100c60400d00d041281c508102d24000802d1400a054120400c0c0498000d82050a412076055420341c001c1c4074068071120400e0b450281c00070310b54011840d014285c080b0503c94040b060580c0c140d40040c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 245201384 1250 245200134 245200139
    0x6010c03080f070509030303010902220e0a02130305030c0d0f110a1b03170702130b0609040b01030213091a0d0b0f0406060b12040c050301150b0309280b01081501 71
    0xc000c60007845a4141300007045212210345d4200080c6000340800701015903210310514444034840d03036504841c0000c6100704018480d0f000042010b503071042c1700c46070042c1c072403030036264880c8500b00766400605240000182d44524107004140c02664000e42d881e450102081c1507000c0381c07100700704100340c01960406880740000524042c00c8240c0c21154480480c09181c0342d88929a9107640c10042082601c0e0006041045040c100000c441e1a04d600f01c08010303090115000c00c070b0902c039401d061482181d444055000c00da0007030b815114048458501c1070100b1780c07500d640d40001d0148100402024480400030080751911031001103405610010849440d00c5040e03001c0344251000d40119145900d131000800d00c003c805005d1b00408100c014181d9550900d030170f20341051348154102e1402641051520583c1510104803041190100074a5907526078500d000c260a01c0510329800c0c0d0302e5a51817031000c0d64800d11940c0c848101c0d01601d201c5085981c1c07400c0300c03960b0300c102d098600c940c0300810004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 245202634 1250 245201384 245201401
    0x40501080d1b0c320901030812100e180105090d0e100c0f0303060608060102070b0f0a0306050603010303030509061f05010806010c0507090f0e0a02090c070203070801020403030c060506010c0308 85
    0x40310443d00c1289000d1403240c0341c910401310041802c228500004151a0114035400c0c0645403050007901030b203404d0465419074441c62018454032440340001c000a4002ca018043c28144600080a4200ad92405400c0a20030301002c08030050000ba01582031030085603580502080354000001c85d0344417a02000c048a0501450403801d204e4001804a81c0328501c1c00716000c000c04c2c24100b8440c0d94005400d84c10044060070f07107880130f0600d0781107500044040c4031442d82c6130708072070303c0c0040348100c20b440b080e040e207088024114a4016070303085200030000000305501600401d0003a8002820344015a0385d1070300c501c1d84202d0301c8183c0700c1e00003602c582c200b02075400358101641120040c504000181032035202e4a180c85140e038001c0d11a5541c52010302c040707140a00c42c481d1a60281c2001e09048401500025000c04000c0e02003109404000388000c11981e04228000091400100075521155a0704000d04035000c0300d041034501c0ca0811000a41da5032007010540074080d0305840b100d003541c607405035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 245203884 1250 245202634 245202677
    0xf09060a050904020619021522031b020a0807060f050705030d182a0f0b04050f060c06010303080402090c04080a03080a021e071401020a05030114040f0911040501080d 73
    0x1030717801403020000111040d104044a059040a98008182e6113160141542c410308004259540080001da203184070012440d011030101d90705468804056106407000400301c0c1c081c1799000750700c003503d16000a03000102044c0102110319a8540364400c14a20b0350580301d520a2001c001c000c2c2c0c20821002107254231507407102d854568080421041908580d07940005400b030801d641c0c9401143d00c00e0550030b4001c039440100940290702054207154600b2401000c030b8080e17406514440c081240c1420480d8569800f0380d0841086542111150350b5242406000a441514180d000b1811040021403c60568013114200da80c4140105114030707103034504440b60403004d09150f1649400b04405484c610441d044400d072121703680d0811344c0e80d201c14901081401d244440b0701044d80d0052041d2200039406c0340c181ca044405800030b24a02440520000740100900d165440ca0395103084500c1051084c1101c00020400c0c040d10b040249980f0b4581482ea11070f48072404031700103888003900f000c8264032540e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 245205134 1250 245203884 245203891
    0x3030c0a0c030c230d030209241207050301080d0504030c1809140304050102061003020904031103120109050105180103080421080f030403080a0c0e1002100c0306050f09060a0509 78
    0x107008108403603d41d0760680c00000e0749407426040350010b50029900ca80500201c4180c5c1464141113280850b0200880e142c0e442d000c04150a10000e4011411075004600859810b0380c003400c406030700b500d0030080180c0290420300490045200b0075181c03080d5140918110342c160b903007021500041d2071602d010440000006403030400d159486689540000c1ca1a01c80354038a520014081c51315241404002403400c600140501105003200c8400c20140e120203501c0303a0403581614001d83c1200000b00380d01c1c035610036102025090445400001030b9806c07103600950607104102d5070303aa0301358150024503003c0d1380280009000c009003040100224540319403000280740d1000030700400c2003165124091a50810000081c2d071500020030802010341c8080c03600c1c2e008101810030054000f0742d820007000e4000044490340101d09250f190200a8020815088034000c0d0450901030310b5020400103021b00068401d10303002d035103102c100c9503052405074801c900c5004050b00b03042a07185003a080042c0606d026 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 245206384 1250 245205134 245205137
    0x60d08030c090a0603320606030c07140601052817011508010504140304032d050109141b010e0d0201030615030203090d1403040b0601020712030201051803030c0a0c03 73
    0x100300d24906070322401c40c1c4800600700354400080d554a4040e08400820700c00e02024060b10940c114800008080103096803c80c00c207982c126241c0d41c0701c1c46c244036107110700cbc1c0000d41090440c8002038556000013600a040c1e40741a00c03070b0340700703840b9820745600c2e00b041e481440f11007103d44400500600c40701d146c0d005c8096a80c0307800441c03020f1403908034001d400d0361504401c0c100d945903400c200074004150071210301c0d1880c3e10021480e0501e152a480800007541c40d400030409429101c0680d40a005501400b40c1d54100380200404803192030f004015070451041e500781c0340100d003500207680001414000c0380c142c0684030301c08104254410001e12015030041241410360394600896480c1c0c6440740410f100b012502c0069032410036060355880c2070840703203d0100b04001c102c402c0011000e000e06a9401580c843e01e900c865813107450044c0d00f0108240c014004000003100d0b601c0500d0340c1500308502a000c56003051072027010101009032a4801162648500c0307104008001c07456114101120180e03000c1e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 245207634 1250 245206384 245206387
    0xf0d18020d060e1f020301140f0907080402061911010507030c0c0f1712010810020f090111010b060d0b120703020a030b04051f0204050924040c020c09040b07090b03060d08030c 77
    0x86840c04000340c070950180e184c0c440e42c0440103210311003c4c0c610651035143c1c00c0700d01070400e01482d4006501240020140400c210366600481d0854407010b050b2350303aa441440b4030071006500c0c04030080034400d407050101855070800011901e00e80c02480340d080c902880b603032110814000b9444101e0a0750050780f08803003800016080c03003d11400180500800403105503408a039500d000c0300107280480b038998150f0359034070400108a41f034403003070111514a2028205440700100c005800e50041030304007507541e04608001462403002e20340d41c0c043c9400384021200c100c80303200724404503550340f051404001e4101e0661542032010444090500d50322a12880448081101442c250540c1c03e0098004060301c5401041c00e114601d010345256a02800008000c0704007400300170301452911074014061b00850351100c10280d2140300341b2100c8401c10011704416080c0c00c0510782036100140331201500003c10010001c110071100000700c82c0226002056171503264401e48507004503602c0980394041e81c100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 245208884 1250 245207634 245207653
    0xa06020403030e150a0206060d05100c030203100f05030705060f13030b07110f30040e010302030f0601080a030f0e0d050105040308070509010c11060f0f0d18020d060e 73
    0x41600060019611a07500c2260403c1e001e02844160114668110305440e03060110000850340026019440f10341114115140160fa04046042c00e11503803410f040c03241003200070011140c254000394050071144182e40b010683e02c1a840344250301e40c2c09001d50503001080700b0005031a00740701500150725854507107483d111080c611050412190380c01200c0e00031380542000a159008071a88240038132a20140500780010f17180301d07482e806100c00d0504e85003211400da10740720010640d800300c0e1681e40d04c0c0490792552508560784101100b44000c80c032070301c00d21008107503060002ca0ba41d4100e032560300c02003055079074a560948411801103840d40c1008600021401241e50b40c01410a0f6907000c0c8000260f1403c2c0b60a00a100140041400f410302c84200700c00005030b41e01c0b0b40c400f8143c0340c026a2004882c8803103400200342c4d201c0c0f0040407251034030106204942d20342c1c101c0100007111020004100c0e55000f41071780b0210b500c1c0e840c4003950050005000c02d0100303806030400c0720812440b400ba42c41940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 245210134 1250 245208884 245208893
    0x1080a021810080106080606070b04020d03020f030408030d060b07030c300c12030b032a040603080406020d0215010306020912010c05070309290d060b0d0930030e0a 72
    0x602d1001680000b44101c0040168503000b26000350404000d07a4002c0c0703820f02e9a121801210f01c090300003400b61002c3d2010700e044c144203010458180c1d04035016269959503c4002d01d98a811504209203c1e81c90404000b402519405c00c42d03405d1640750b2034008405500d519803005112400c007200810b0840d1032039040070010040e001c904039040d59100d242c8041da0078180030141c072a1821040d82072620701101107503155030001d040388140381840510900d104901c4409602940c1c4042c0c0c42d600103060243c0442000101c1c4041c205441b6036500300c2c1c09004c0441003c076540c00340d8081c2603200b04800300040c00030940c140c005040d800c0c0050711404e81c10030f01c0d003072a41c21600d00303c040800180d00820000308165100c00444024110080a00400756110741c00c4075500f400309140100c0b030b0b0b00001e665030315207245420180040c80f130400460348a070129901c0340302400c100d58040f11811010900207800c06802007030441d60000940550036443c3c01d0110503402041d400505250a00c140843c079400507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 245211384 1250 245210134 245210149
    0x150504080d0c060f05280b120a0b070201050f060114090d08091503010b0313290714030403020c060307020304050904060603050d0809030d050402130e06010e060a0501080a0218 77
    0x30290359040750740020380c10710f00c0c12124210480420300e030401d0107024006908180031a1810410381030000a0f40080050000070300c0c406d42e40d650031980341824a0220313070000c00c10b4003015029402212169480e00d204074225541204c55020348825840418207a500c58120340b1084410000c2c031600d042086000110b46544804003110205400903e124481c00d10402c0010302002502c0d5180c21941045490f00a44c080240340c0d40c46501c00c06042024020b16aa40b501001c0201004501580801a0b411995802250280081054290304810110381c0108a9200b150540e0250101004c1c05040204a83c0007074101401c40c4014040420540d0794001101d0003240706207000610f2b6495840c080c0d0a081020074546e00b030041d8002002003c000110031202c02c49401e020024031542d8910000d603081c455010401c40452801c60403000480780040c80c181030ba4414451851a59500000c0041031500d9006c0c0318001a004c1020403081c44040d005012803621071295416514030032004624103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 245212634 1250 245211384 245211403
    0x6020a1104020f0c012c0705090c040e0406020d05010e0402030d1d032505090403080a020a200d0e030610090f0e0312220206070201081308030921070c15050408 70
    0x250f940d914044070140c6e070020b0f89006510340c40305898511114041d00030b51100002d02c41c15010ba82c03d6000a10300741c22030b104460140089410a0806041c1420b0140094002d409070380341041c40c0800109040c41c40d81807240c0305030350044c02001c440c2c8240748112102151140303007440d41b2034400404203081c3d40c14848540c000801d00c0c002c01c00d9083c404500100c40000741d001501823162503040c000400d601200c2140c2c0600c003240c000da6641d0100608841c84d401a083c40018111114400c0d0b040708404564080e000c01545d841048003825202015140d01c01601c0c5082e402528040810008042da0401c00c00a184c0301ca00060f50001050780505580c4107a03a1a58024000740c100200741c007410702d040d0081c0c1e18107843d0064405480e03000c40c003a44a4440040d0501c83c000000958428a404030390042a5000700010307180e00b0180383c040e507240e18220b100b9038118084001c1003085c4c074160050710600c1c0d41000044203101e05e04070a610103401012042000c1003001c1002044841042100fa0031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 245213884 1250 245212634 245212657
    0x1b010b100e031b030a230303070804060b0901050f0d020f0d06060e070206070e09060d0f11040f110417100504030905040b0f0f01030c120501030f03021606020a1104020f 74
    0x50403040704040505080b580300280210003001c1c03844490a072000140341d80190307405101d0304d41010300a9107000e080c021056410185105c0003041295442c0c2c801030b06170103144582020321840480d101080b20444003401071680111030903041c060a450003c8041100c1e40c0090001c0e0321048a0401040c840f92406006807080c58440d0420001030309084840c0381d200381684040c140b0b0703003003d46d401020302e00042c507140d10880000c40850b119a0324810300b80051f5034041d0200900f198a45001c40030b84035011040c40c4994a460828410142c160082480217249040c01c5464142000d088240780300c18030140c126580306401150901040e10b11485000d903010362920010a403a0030108012740b40c00c0039400c0c0c01900501c00c22402d5840381414070b4404002400c011a0003500000100c40030700d2003004000c02c940c1040c00020600105000d8030000c3d034041d500380c130600c80041c21107001954091080c0401039100d04c070080d0200d003004500c1032040b40010009454035014000e00d01003034008030081c81 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 245215134 1250 245213884 245213897
    0xa0207020306131407030503030a090c0b0c1b0102030703120f020705030a02010912050702031c020f07170d05120112030e0901090b090105011112130906030305030711070b1b010b10 79
    0x702801135400e00800c40b008100014001541555511a141e0002a203c0100301c0e8803000b680c420024031740d080901030b0981c140290744a14001d0a400c2d5100300100580918002105003408954408412200003d4040e2500c10600080c500c0080040c030000444000145d070a004240000c5c03401e00082042c025180d002040401050400d403810502d4607944a0031304c03d0800000380162408600512441031350070308003408051b01d5100340d007040010380e00d17038103940a050000310b00a099141001d042c80c0408040340e0716880c0900041e03500d441080d541030046802500104050302c0031319114030b44070348246441c4400b61140d0f804546060001e0b040b10803d50784415100b0706500b4241c014600400742444c2000d42c01c3d1601003160340316503060404250204001800003041510500d401006103034034007041240d5580da081c02041e5400680d14007000598a154280b9803000010382d0505961300110124601562001070071141c803041410041e0303a54a900382500a940ca91070b03600c5400d5010385400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 245216384 1250 245215134 245215171
    0x305070f0e010909020108070807020a0503030c0c01060f03020a05060706140406020903010c1d10090b0309061603090309091a03010905214b071703070f05030a0207020306 75
    0x811070603005821030010349182c102440003503a404016660081000d0074400e0700e40c0c40740310b4124101f03401004042c106110010500011181c1d0710b0080c00d003002920000c128141d02c421410310b0298442c4006940020480c00074420740c40d048000740031046c4201c4000421942c000b02500002004940135520303503a001c03c100700d55081c02c1c0111543c3c0a0b041c5859a01c4030080d4002800b100c1e10b4082240c000c00c121100b500780ca5005040d040040d1105a4041d40c0324038000c40c40c56615002242d05250030706650028a5489000c0e01030b46500b145d045c2c881204c0f50381098423003801040500c202103500103120300300c54103a031000c0c0300d81842640520068031020503200240c400c4d4a21101840c80d4281c0100148100c000a8203411520004802000301d080c00e12400c0104049036503441c240c096401846260f0780c0d4190b00f1005082152041540054600c0022001c0120340401c55501d07011074001c180b9070410078414001980c2c04941d03240c0c0141481d407103802003450850219500c00c10b03a20813074031a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 245217634 1250 245216384 245216399
    0x9030d18030e0108040201140a090b03040606060f020f120901050f070f0204230105120c03100c020d0825090909050304090e0606061209100e0c0a14030c01180305070f 73
    0x10030302c0410038284240b190070194002806030703880c050021088034000c2410f64059101c0c2c81041b00421028080a44a007070038204071009216510415004c906c40d10320480400b4004585a406800c4041c040d15604000c8400c0c0d005c158451142d29040000401c19001c0d00001e0030302901219000c0e480d04c0c0f00c9841540705100840322032030301c10142c00752250400011080401e806c00d041d036006440301e081d44140346101c1c2d03242a107400032407945401a40e20888074030446a100140000341a400c80b00851045c0324107441c03103d8280c0300000c29086420f108902e0001c0f0b000251224141d0b03150200f400c039901c555140807983d0280040341c107074200080070401c2d0441800380e00702000304a800390045092600010381d09110b00700d06c8008440503800001c898030b00c140b0103c10141d003c5401800200000f207815030b100d8844040040c41000f0310324010644550200759004014806001020381d40d04d900d0043d10801c504a9850f001d22800e044044002034060121100800c0c20500041a0a050901 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 245218884 1250 245217634 245217647
    0x1080d080105040b10030b030c0603040f0b0604090206030604150803030a0f06140307060c030507080d0204030b07031b0c0819020a020a09020c0601170c0d1b0e0c040b0309030d1803 79
    0x80b41c819800c01a40600c59510440c0c201005e121a090010388a140e04011070b0070424601001c580c01000030013040188070b002c0d0504011184148000741081c0d440100304030444d52100c4010303411075001d000003051030034950f11400201c815066095001640c440502e0310b160304c00c5801c40c0515441f003141c0901c500b00742c01a04d01a2002c8850f900c105421718000c295202e48500c40c03e010030400c12003183c141800b0f10100c1300c1c0c40d600f024186039070344003d040c844041d503c144001c07a0001480342c0003842c8580309124140059901007034290407603081c036000f150480d8680005859500c02080b4581041070309440000c0542d50756005880f41c51114010406001602c1d801128405e004010340441c80c200480d40390306590381602c042400740e079480c8406203821111440c2c1ea4004100700e81d400140300c14080e01800f42145000d081c1c0c240d0b0340700c1c100303020042b50940e080c0c0c1441e2009d02080c003051205e800515480340c400c83c03c680c14801080300b01001d40704003000708281c038240300c00c104042c181d01c8031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 245220134 1250 245218884 245218889
    0x9070609080712060b060d0c030b09131205090f03010608060105090c0a05030703181515080c01021207031b0b04030206010f0e04061a151801080402030d1b0b01080d0801 74
    0x207012800d10f07225086884484000000388910741d42d4402d042c4983d00d1000740c900399a0100c008001c1500400e001a00414142d40018451101c030b0000803c80c40441d080044460781c080c00080e41da040341401920903170489070800703911413100e101c0f1407c02d403024400d40005001250083c400d030f515280901107042e10103800030302d0400c010804080100e400800b201d0700300355a03141c0040c8609200414150300006004024425004108041a40754081e000242c402029600c080c012940e6410300070354485941601c1409a00101d01510005010101500c000e81c002c1c00d2801303081214504e14041c40e0b11213101119440e03004000e001c28998108046809420704450f800d41c0b16003000e8640b0602d0b1380c02400101000d8482030400644110701e040c03031014210103000b0380310014075400e0040150300030800b407208018000400d203805610800c440b600468014000e4003611060f880229507030301c1c0008801c4900b82902c2503c400050840c0000c134020000103003d4003050079040001030036010180e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 245221384 1250 245220134 245220149
    0x405120615030d0801060e0a051003150504020a170406061d090c06070c030f03020a05030307020318030703110d050f101b020601030b370230041e0b09070609 69
    0xf0103014403040d030003002040c19144e031400c0c920002e0140c0c0300000c107045165040789030044c0f0000d031030915070b903010b4000401030381148100c0c00c19581c6034800d0000700d000c1c3c0d407a01c400041007080c0d07044c07400c910841026042030203050b020415988900c4245070403416280d24164010003034007000f00383c01c4240005c42c500c800480304103107000c940c0d86803d40c0003074135404050032004490228804042c000c10806810541c080152a2a4a06083d01070349a410101c414020541180110502e07485c0110740b2005486c0d0003103903071614150300340900c20300e40500d020482e498450028468190001000220320a0079454004034400c0060251040551204903240c41903505c180c006200280385180c1440e44010100d400300054014150420300d5600c6009d24503155190007a110f0b41c849c44250003d1441060030340d01d19a50480300620340c5448043e4800c2d881308040000041000204030071300e400fa108407015881d081d00d85541e12501e211140070341c1c41005540c02030b0000c00005401041540090145 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 245222634 1250 245221384 245221393
    0x100b0f03070816090605090106030e190b0709050301060e0a0203040f060501080102031e091c0c02180414031303110f04020d0e010c02030705102d1410050321040512061503 75
    0x10013002c1f42c00760a06008040c10305446005018040f0001c01541d04182d000306509040303401c0c2c81c03c0500007190181c0b8800000b8050342c101190906050084604940c84c02c0e40f092202da03600f0750035400030b4101510845040f8032545101d8045101805000d000e0710103880016a642048810404c58a1480c00d0381140c1d82e01c60001c11564100121f203c2a9902000034503114a00017584125980006000300a6100b00048103040100c20880c4076036100340d04c540319030682003c1d64000c491307407802100080c049000101c40140000346220f01806040305000d000810380c610f0801c00501a03030428111031300c1442c2d40f14250301c0580c1090154420048490014501e002038035200c61391903032080e4811207074568654000940c1d0000b1406150b505480c07005540308440a84189900682001c40c10000030404040114800c190711103440021a0750040c014800702c14031818889031404440070028404405010004140d02c8a2005070007060208000c3c25071031a20229446c045021510a98001c1c1e10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 245223884 1250 245222634 245222639
    0xd0c020105030a090c0909050a140304121707140f07061110020903030d1404051c0503010513140a0c1106011a07050106080a080901021e100b0f030708160906 69
    0x810400b02e075004900c00f2400b055101242c00e080390404800c0d40024451172520302c020341030213004900c0022840c8108240d0010010b66444070f81e980c0500e01a820302515450f221100092441076001301c10314448003164180085512850105c84400c00302691a4208244140307208809101c8030016122074148407090003841d4440340c1d90340d14203080300325056a0004004007966020015a1800d0406400c240900e420215804210074410b40f8116070920400304803418501d41041e0071454015983c0c0d61600310f07880e080c1003002c07207890300002e01c00040c2c0d21411a00d441c160543c074684520100e480110b10907556200051030a444260480c17400e400680050291090300f101c0d05da052898100220f46500d01d81c1410b03401841d4035400300006114150414040240050240885150903001c0e640c0e048000900604440340c1d181d50010180c21241480f082485039501007182400060700d1500d001c500e03c0080b9140800c1600558403e40c000c6c0b01c038417102500d41038403901a0801e00c40a2012a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 245225134 1250 245223884 245223887
    0x90303021c140903191101080f040203100f14040321110f07021302070c23030d08070e0a09060311190b07020f0402070c0f051009031209120503030106020d0c0201 71
    0x10002c03014502c88100c0082e01c0707810740d031301008541001d010819540401841919100000026140016010404030400110480d201c80000b40c80750790050054042c20305207640c04401446e10b51890814182d5950400880300f400300201481b80d8031a849590317000b400e2840f088146441ea031050030000e82015110040c40c44500d0a80300036580303c0c0c00e0b0030b480e100035200144811103e280044481803020030200700380b080e140098001c4408a148412a174009402100d1440346c0351940700782c042d8080b82c0c518030021310908040394000071a02d0041c200303440800000b0f413054143e17403001c03646030303107405080c81484000d040c22101309400f21410303018a0781e81c0c01401d041c05c45502c110000103001092040c15500c40107001201d00100034001c554a402c146031203a8580309900822441156003400410300d400c105070a0b0031090407945458014500e199648c05424a007102140208005944001600103c001c0152102031140c0302a50301e03981440802440c040100d1400b204024041d405c91000d40d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 245226384 1250 245225134 245225147
    0x1080603010207021c0c03050d03020702100c050c01110c04091505010501020106060f1211030c120702070f05060912011b081003020109030b06030a081b0c0a0807060507030e030706090303021c 84
    0x400099175011481c0c0c0b0b0301b061400ca1080340d0001d4414020706000764003250341a401881980d1007190805002c0b01505021144124101030060040c1d01c40c8150394465070151703a503402d071018031701c4c1203859040403040444d040da240e00a08650200c0c040d004221108100e0088901501e401e2000700724841c03500d01c0c0141039810764070002c0140001095145d001d03120030341200e1469012182016500e042028189800b607000c41062000e50070a500400d5050f8400308071740049405802009542600b081c0030450960301104220b070b44003640d1041800700f0322080c01035400480421400e8042819080d801805041000344102e609203c081e40510040c2e80140400050700d070000d980c6465036485102091404544a00c0a0000a40407464500e01220840e1042d00344a00d0015145907141800070712090140700c1c001e08038141c1100006000c1030b0304ca02e025080300350003450054010508075000c40d04221894010000140040500b80180341d01080081d01d02000014960992102140c004011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 245227634 1250 245226384 245226409
    0x1020f030106080907030b011511010b0a050103020f0d0c080f0a090f0305092707021b030d0c0507090203340801031403091306050918030f07030c080c06060108060301020702 76
    0x5002c2d152000c9813140d1000c01803003001e550300503008203041d40c5035502c43e448498041d40040024100c141c1d104a8088103000701e421070076000d449003841c0f0782400c0042d0060740040001c00106081440740d005108814016240d40c2040303510380300c5980c00e004404a02442d4020000125542040c0d10000026480e000e0206603642610303201e6120580100040c41a203519140c0143d103020003806a003101d0400407286010705080e80882d82d40078040003045545840c0c0d0110390343d05400c0701d0b040307125150066035402c0c0d140380301d1382c25a10b5094642251904907041130303415103480d1802c442400c84031070707108412340c40d40f1200c0311102c40581000c030030060010405000007000e0b00d2402c4007603101a00204141c0e4603040c8024048518640c40b10a4440101858400c0a00c10100071020440106441400140038202c0b0000795203040002141e03d0765591100030107c04001c2d00312001808039241da0090001c062542004d00b542c0e00b40040014008603000c0e25440c440e900c1004018016038450368844803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 245228884 1250 245227634 245227637
    0x7020108040204020c0604034404081315080a27050709020d05060301110c07090b1f050c01060f080703020d080f0c150108060c030606091906030c03060801020f030106 73
    0x10360380d500e2001c18042c0c0501103454145101b20b8040c80105908400c01081d51a080c40c10080150007068400140d000315645410b141028651099085146e22140c550f00034041c1070050310b80040d480d006000078a1030350095444410882d004803695501c4031229421050000d03040c420801030303246500790350400c0001d0804401c5600054020040180080d0000b003004038801c6454103003107070411001d80021601c4511951a03e149100c41c241d43c070080d6607a080010b40204500e42c14581da0313000420040d0390030b551112056099a0384e150000054a07100b0a45581d01c9448081d642000c60940d4000d4026406202c0011024030034150b0015a680483c2d4040b18114120202400c0c0524503104009001d90040e0740001c007001508000201462044c2500012020036a030b101c2c0c1aa444035400d942c034110100c02000800c1840c980000500b40441c00200760b00c0910142840e807041070715495110740040b903114030401c0e0740300d44c16228102c01000054025403511164550903d590300c014001c000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 245230134 1250 245228884 245228897
    0xf061a130306051806060612130606030503040b220b091005070b0405060603061e0402040e0c0a0f0906241b0804121202010b01080403080901111824070201 68
    0x3214840442058000e40d0032000401850629003080c850011513083c4484040c031540f80070614604001c011905158029a82400c06880d000b8424220904070881038030003980300d25001c030210310180010401050401708441d99800c0b403404580c800829001014003002d82407404111900c404411181c003010100e0784014000c0002c081035500380190744001d0401c100d41c1003040f08005c0c3c0010070a000d04421000c448590b910005401c100300c12408401003000c0c6030f0004640142081d410520307841d04d8140680701d000c052540820740521340c0d940107201200d40c030801041440505e1080501505690344161240c005002140c00350803d004051410031824090715040403050310340091545a11144040da00c9990b040900000085180296130703135410100110074203030051059101007041038454000342c0d51980c034140c0d00d80c0c00041400582d03540340d071001d083c20140c0000510401030b68019a0042542071000c0c0b008100e507500001c000346485035940040400380c2d800b130382d00b0660b09180c1807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 245231384 1250 245230134 245230147
    0x90909011a010f1107120209130f2d0302070e130c030b270309010801060516060506041b030912090305071701110c010207060f0b0f0402070812010b030a0f061a 70
    0x84680e21003100083e04c403401030300c901145442c020380c8440341d500c2c000c46000c50980c8070300510140840320000d0040643c942e0750b00ca800060301c000c0401c15000c4507207107190120380ca000c081c07200d1042c100340e044006070411941400010b000d100001d8206083d0008040b08a1442d80e50703220420047c00702030154545440015514001004000c100043c503000c98401c104c003000031580c1c0da03003003000c04c14040342c14030b00003046e00c42c4140c0c25554041c3c03542d5802c401c445244d844940090401800840d0130a40710181040e22200f0301003200d5010085540000b4201d003a0304069400b000318020110070041c1c614020404070350009408015900c04e01d017002501060340d40154010540040140f03104c60b800300b14100c0107181076003e0040c95004580900c04194000c0005045801c003044180c0c0c0400c0c07250549000d07003419800b0341174003440340061078501071000041d210310382002d07481020400790000400a150030280519925090981001e004a5007040c3d481c00711030a03504413842e007160021804 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 245232634 1250 245231384 245231387
    0x180111030606091e0d05060907060e0a0306090c050a1511030a02250e160206160516060b040515031911010503041515090e0a020a0302040b150c03090909011a010f 71
    0x16500d44100c005c10021784d480c0140b501c50307242c84003282e0110b100c0c0513034080002c2d018080c44d02c3d0b00701b56000805000d80c1901b199900d100400740746c0400e88458031034400114554952510640240c00c4088440c914001072080003042030040039a4102681c005011502080303400090440e0380b551613800001c5a144800d8208071403065543c4040c1c402490802405800244203146e1218000c080d401d03100030741c0c0d4150003201c4401e841c000541c0010380c10403000354040b800540580000d40700304008644860b50307400040c107071030080d18601840501408560160b14040104403d448203452841c113000f80c007501d440c00400b0761328800c94180240000040c0070007414054051101309010003c200b8601c000c002d054122129010302d110003031030100c40d032128040c0082d50704c98103a801426100d0032410340d03090002421059180307540140ca1074201652a41c01070006d014020250390083d6181d001d0041009100350740038100b00340036490b200b040200d255580c01713100320b030902c282072800000c3c502400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 245233884 1250 245232634 245232679
    0x3020f01050c010203040c050406080616080907090905010b010e1804020405040201110a0308010305070519230306070806011412040605151519050f04031202100518011103060609 78
    0x1d0b1505035501c00010441000340521810003554419202001690f8407034408540e240001e54a0542540031081c0082010303114903c2240c0c414664000d40f1140ca5891401c00b0541b5160344044490340d440c1c00d04000d89590280036010035000441c2c91008880b004540c0540d0000e01500c084d000d2900c0301d00150569002d084000c140c150440201e4120356114180104100e00a01040f00c150052250004071490f04d80c01c01c1040343d401c090402e9226250003500e8254100c2c00c01504c032000e61040c4c0300c08643e90b0900490f0711801403500e17041554500000010008003c1d100120035200c010721240c04900d2403203c46582c0181d01917800103030b50300e6035449150030f03043c122a880d502c14030258220360381c68290b03c090254041c620a0001c2d1000894a068034a0b0003030318100c500504080c042040407424500c40f0b07054104060050340d15039108449139100b911011145003d1b81038038031301c0c4400106024480c810120988810150a5040c41c400040301d03841104c82062080c0517200f4018903c4010b440c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 245235134 1250 245233884 245233897
    0xb21032106241605060906090606210c0607030504060806010512070804021306090603060e03040e06010c0c031e1b0503030913020d02030f06090a05010b0a030911040f020903070b040b0403020f0105 86
    0x941d40c07402e0b10a407421395035910b070803140307034009000d1580420500440012214001c41d0000c1c078280000c00c105402c0c4100c4054241184014415210f51081039152100200070f440d0181e030f90141d41740e040c4a0094800032000e00500e042050800c2901d01c05010704400340d80241c039601d0b202030142c8450000940b107403014140c29030164500400000c1201550740502c08880c8070b84414000c050706c01c80748540b40c0c003a07071007880703000030052000511541c030a41528100c2d6203e03171002c055441d120b844010401c4948070502180d42d119041201c04c0c0109102c035600719146d02c0200710312a81c01c12000c41d40b64010145824041c8802c3c96015803c0c01060301a20030481040c44210740f680303400d401030301030b4640035030341c031030143c1590004528413141d87e0041c2e078140c036020200103180042d81d040480040987e440e040c1c80010400600c80459500c80c041d600c04800140c0000da150040d904c101803d040c1540c0c04004161801c02c020412086004155412640c044070303004034010449005a656100300f1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 245236384 1250 245235134 245235157
    0x51b0103021309061505090904060e0a0f26030405120c01023018070605030a060305192d151503060203011406070201050d0b2103210624 60
    0x82c0b004100c03403505512610498050f07402911010034540002d64031442244c0346a508800400001400308143da0000710700403811500300c944403043c60321010841810418129040d80038600105216183c0c0640403800c506103d00d5a480c41c2032580d581551100170340c00c01d052813035001c541c40c08014000c0d41900c800e10b101c21841c058180322502c83c0000e200d42c031380e426586810306801107595007010f0510b548600303210b00020510141441415a51070300004c105072461a10b407200800066010b10419203000144441034031600310f41c1ca01280c074090140c412801070f0f48c00f1848103245001089103030400503040581d1410400545007410060304950315071720000f00c0c080d20300004000d02e680c0218101d510701512001c16209030410004244180b00010380054418020503001004030390012440400042c07107001c40c01e1700d141c8160380501c29900c007100c06030804a4088841c9a4003483d40300c3c9440000042005480c1800019500620001d04071959407603550403c5811141602100c1c90500e64 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 245237634 1250 245236384 245236417
    0x30702090c04080102040f081605010206040605041e03110d0f020a082802030a02010e0c09061917010903030f050603150c0c0703110111010b1e0301090609050706090b07051b010302 79
    0xc07085c400c1240c1d016032264101500c20044440c52940c1036503409c01c10380c0d01c164090002500c5540b200d001400c8044c009680f02e40141448000440582c0e40c95100d02e80700b601e48040442d40d40680c00d080c0b11401500c1428005082a00181c0550101e0750304225688010680d4540c000104000400313840401c0740c01813400e00c0c01180c101c003030300000542014040c0344c1c0240184010036214036101c0740c1c0803000582100c7c02c0c81c04607103680f0300580c10160004214003c121110365400c0c100e14040900d080070402a550b81d07000d10107041c3d140c042d4802410341c02c8420300207810300e840032a540300203041212501103070302c1c80426010320003142103ca891003004101c07000242c1324106510004d40c20102c03280840c150f06810150b683d01030046028540c030041c20114441d0003050101c00c6020b840c981651f16550b00c0d44528001115840b60440c118051001031031000c0c2014409400740109410148041c0000d0060304005000000d4090f9450700400317060148000140058010380940320300100b030003c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 245238884 1250 245237634 245237639
    0x5102d020912011401081c0c05150c040504060909080a0507141203010e0a05190e03090406091407230706060b030f090606100504150219060203010f05040b03030702090c0408010204 79
    0xb015000140802c0040ca004081c82c1d03626400740d6a2003a915400107102c1c44401200e04003030303010b5124601e01a0050382520203040104034104408070040b07c6800c00d1000c0070600b8480c80c04c20784105000340800402c200001c00d002c2d00d98a41c5400b4800b049410840d0000340780082200f140d04500e40e48618404890f2445408500303581903800034060503010340c1c04100010b90300d0040340a5103000701d1a822110011003010001c034009055030186070b072100e1104020701f1009460b103210fa400140390140c80001c038040e8a50520400e0000600000c4c00c02c4041c1035888200c003048072070787c1240103080c4030700c56581585141143c040c00d00e540c003401700745001008101c44202e480d10524464110001a038071143d882104100d84881031042c403d0005d0014031040c06005001141803428101900403035070920790101c40401d00300420300080791440c0d000301c01002812441c483c9000038110440781841400c24000200381da038012004081e10903054903020030000e034032650031030700074221a0001f9507880380c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 245240134 1250 245238884 245238919
    0x706090809090a2003071b02060c07080715030506010503011e120803060301060f0b040e04150204082109060f03060a0312021e060708010b0c0f0a0c0305102d0209 71
    0xb6080c205142144d0704407107241555074080c1c08492040005450701c03c036001c540602010b442944440c01c07608600304000a22042904108442c0208000401807140d0750912040c6069503220308210b0f41410300b40b0b810b108072613030070006480c1594828215100e04480107114078854100759844140980f100070503400a1240e56401148189015130003070100594481e0609003140451243c880c080409000605c65048401a8960001e01807118020110460078050b01282e100b5800301000c5c1c0e000014400b990a00380710140c003c0b110729042d0303600701895000415018030529405100300900000015240e64035000e0074000307950440c0e19050110705010020303646100341000c000c0c4401d284070000401200010344540304112580e10310040381d1800346403e645401107111440903000c0c40207500c072012420018044050300800d1048951480c0d800d1090070600b0307600c84624401c0c1002a402001d00c42d1040084c20071804074980140c91003000d100e0002401500741d03260b4040700d146a01000741 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 245241384 1250 245240134 245240141
    0x2040e040614060a03120f050c190c1401020706050d1b03020d060b07050a08030603211306020d0c0b0709090207050d0201060b0304111e030a031101150602030706090809090a 76
    0x1508050000d0b8925101e4204100c1c100e03440e4070005003c05400d94245202c40d02c40c440301e80e81d0a00341d044c800e0505115110b014241038100360700c82031500341c2180500a00a01c103000354000d16904000c144116035600c0000e403244418014442030000c0000c035004d524046501480444901000000c001d10900d00020081c2d0701c0280c1048001e8205200820941e44034000c84420350703030106c000c03c140515503031040c015410040c40ca80d8140034010382203160b000c1954002d03d00310340c01819180e552000749251880d00700c03950000400c43d4030018503407142c1900440541013a6070400d0208a4a0340d908208a036a1100d40c2c0001d41c201d400450a0810403400142c00142e2031015002404001d8580402c80a00d0001301d802800c209210190802d03a41400c0c41406280c4051420041000120341c02117460208648001c81c001081d00c940780c86884028883e06041c3c00a103111034601920745040259070b4003070003101a0480381d8500540c0100002d03d4126410410060987c41c0140781041c02d1500a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 245242634 1250 245241384 245241401
    0xf0d050d0f0908010c0c0609050705060706090b07110a030309060e030a0c020406120201080a09030306050411071416060e060c0d120b01030207080a051e03280e07060f020102040e0406 80
    0x21822542c0040f42c40f5606005030b805010a50751180d40e508071940b10840078000000f07003911310340200003010407651542c00090110601400340841c04a01c6403074503410981c4010b10200400520031081212500d021444400b804e4051402084460407070a011009010341500c0710319900c000201380341803940000c40001c1c80b0b8001c441c108086540c6181c1e81e020000070343c01c020f000035200000503d407604503a000d41c0181d4000d15001408030348403000305040300e620101112644102017000401c01c00440005c907200c4882c4006004410741c0107440c0e00e800c2c100713802008180000d9100009160301c0c0c14050f100c60402d0071040700c2e0740c1010b100000e40000d285211402c1c0d4039007882c07100640d95011f4001c42c0c921582c002c0480d440e011502c04201c4440e004008110b05c00b0060940300145a66003c018500403e00100301c00c200445010314004018100255100d10a01b4011a03440e14840414203500306e43c198142002900c004030812030080c8070b03d030003100c0f042100c0018481449040e82c401ea0340f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 245243884 1250 245242634 245242637
    0xf061303110f030f0a050c03070609060e0706020606060a0c02030613150b010509040506011b050c01030b18130c080303090114071e03110903100b04050f0907050f0d050d0f 75
    0x10307552102019141c481034090203400c80769104202e68500681c8100042000340301502e4110300b040c41c070404042c115401000281e881310b444543c10303402e0141c0c500c1541905811407004095103840c041c806511480e0040400748035107400b16000300743c1c0303014001010710581e00405541180c0b4111800031040d00e00c050080c0c071211030100545038541c10502c5a1380d100b0005071074980c04d00100d2020000644401801c0e9410040c070028030000c043c211200540781d00b44514041c0005040800004045490340201a803082645418120f22081601c01c0c25400640f2241070754000c2e1100c3c100801c0404d035a0780400071a2000204000314002c041d4424041c01c403800300050116291202c080364921411048a80000c050030845c0c003c1301c0c000c6c0e00550007418101c04107401c00c4004400030742070409140b040801a902c0e14210300b030302d150074421290b01c81158020a0910b0034807244159440380c060084601921609101002565036128505400f40e0f0000c01c03035080c8580307003000402e2490b84140310360 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 245245134 1250 245243884 245243897
    0xc0308060609120f0c0a0803222c132312070503130b1c05190c08011a0327010f020a0c05060601093204050709031104141303020f061303 60
    0x111728684501048211000000114204220901190101000c1000c003080b40c0f101c0d500002002c01201d4807070b0085102402040c1e10900d4080c800041d0400000d250048a0ba9007c940200040e84800317980529046003d0085516060031181e038500303040410309880c1e03480c01086040400c000040140340381081c0050301100d0313954512240d003082c06103000808062030224101400000300f41d000302e80c8005500d0489000b607804207a00e004480041555000007040400180300750f5041014100846000710140c616602d40241c4d4282e90308843c802000d1469224424010944c3c0c0c250001403000d0f52400c8119602c0c5004640075111020280c0100c7c3e0f00c3c0550350009107598050401541218030443c4030303602006d00740424441101e110000c6884801c25461948401c0c0c0300d03840b40510030080d58890724030407030950401300b6110354101480c0d4407960405100f91700a1919070030103500030804000340320101d05185000e0f8140020b00c00415054424039040003204000e0000c8038443e89c0c000d40301d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 245246384 1250 245245134 245245153
    0x3070e0a0b27060f13021b0606030a080a020c0910031a07092105150609090102090607110f032a040603260c010606050414030303070c0308060609120f 66
    0x40a8031030a940b072200c041405404200d9403602c10b0803a582d0290380105989480198000003e0000c1c002001c1c2d0000642e012134900109036007504404071404aa00040c1307102d260120000343d8400701301390b00038006d80e000714010484038020820f00025000c000c101c40c00504d4010012030704001ea03440151a580784881c51420b480d605240d559008a001d50b840ca0296810060f4201d00d01c210007082c460300c0705004028001103041801520100b20300c2080c07069150034143d04001c80c9900c00350041c00c850b4410090f18810703551722000c690309641d120510f003105100c09070024107240304140015406015481d40a01d060044000d040b002e00300000311403100c6c03280a010322040300e105000040c402c03609a01c01c81da40342145003a2481408821020902e05071545003600c0c25030707046512010108001090074804402d40c5c02540c0c1000805800441c114a0417023001040c5841600c0e0150903c1b004402141d07941e05c4010454201117000303884d2000d1410902d02c10360342d40490031480100c2e8028041ea4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 245247634 1250 245246384 245246389
    0x10906200304031e260603060105060a230702030f1c09030818220911060f09150d110d0501120f030e0f090421081b071103070e0a0b 58
    0x1902d00071034042d6190304c08003d00150420b05803044d01104802e0001e03080441001c0614140400d8201854000480700c0c0c0c2041e005041c50040107801c0a4803807101031140751040c5500090f40d65075580c400c20b002568040d1028510342070b104400c2c2c040e406004490004011210018140007a01c089900889049056007011203254149000003402c035a0200070080c1600783c50201c84505030b400500e202003118002226424024510081006044d191103041c001d200e030428042c8401e11040e28120f2030a005901c0300903892007103240c101e109914021740c54441c0d210b0708003510f00c200c003040e1040141c0c03c111071201c0120703085107203e0078200341018004a40c00002c0c012081189a028148014080b15550141c92801d030103502e407a044a40039549107a6641d802c50100d0196000f0020750000c80c0c0c00d040d50b14014040d490300001485030790001d00005801c174026049001d030380e600e0f18584440040c43c08100c00c0341c5154610b0351500c5050310206543d402c1404d07840c0a915000400c2001202c0c0400703 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 245248884 1250 245247634 245247637
    0xc1205031c05060a05040506060412050a03030605030c0f041d010f0b0a120302070b0313020303041d060109050a060c031701060906120e0327030d030c02010606140f0f0c01090620 78
    0x40751900300c4003409040200c0c1c101b030341065400c0170000313140b642802d0300ca0340e01700c55244500d80266070030b501504503001895014032984001d8072040e0013900825030403c01050750b5002c040d1341d041c080c90f40d0b8199021a00103c0c0b01409000491400034007413490b103c18508094a1500036051240d41201d00020341564001c03640b503a00c540c150044d2026520308410740250703802c024440340074009442500001a60144005c0006d0305000c0c0c041c441d00d0001c005405120b400c02032a040c103025080d8000d10031a5a101c1941c2c0484002c0d01e0b21403250844e602c0c0480d0118104088030314645500000841c03c0d5410014243c2501e1040d5a10900758804104038070aa41c0002103014250300104110001803011041e0b01c0400e4401100321807901c2c82d1140420700d0024407451880010780ea41e6100d8031425828080c403402003002c1d10740005400312a42d50503840e07204400900c0740004001403010701454128040d1181d8040c1000204540903490500901802044002c90000ce50903506040d1400d0000d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 245250134 1250 245248884 245248891
    0xe0f01230a0c0504030804090501030606060c0507300f1103030a0e060d110c060604052a03150d0302030726030a0b0301020c030a0315050102010c0f0305040c1205031c05 74
    0x101410658440000a0000b0110700d490002080740410002c404a10b12800500003400b403200001495850742c20160111503a80d048402041900c0d566140440d05c00030382c520a503244804070003943d004003101424000f0008040d803107100c20f0f4210103402d020903012a07400c000d000c0c201e5290448004410103880e07102c1c00000d00049140150034958074180203000d400060b00054000a8400d210b00e0000069004074071452807640c4020200111420326005440c0c20031030060305140450801e0400348100400406480482c4001100041840c40c02e1a48040216809001c0d400c4102032420000d440c0c1c0d0203540142d5007000c0041200c050048602810012400051585811900c5003038101c0c000d4019010041e50544d001d00c4440d0f0007600c03d000400300040e05440000703003101907002c0a03108800650006041d64582102040c4035a00486640c644403070f80c1c540007a85650382d1400e84202034003030f000000d03040e00340783c60030307007007010000040080745180c50811036a04518440e0314280c84084 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 245251384 1250 245250134 245250191
    0xb010203040911090904050c03010e0c060a030216020a030b0411010206131e060204080a0204150b040303120e06071214010305030412050309030d03150807030c12150e0f01 75
    0x801003003000303000561058985140d0400741c645444c3c1c0aa000890101040d142500c041e005058200d0691070240f007074100311500c0c40090300701c8556940c00036040313006000c00c10007030640000f5250070010504044128681e4018030392240c40c0c1c7c41e400e0103112200700300c0f41100d807012015514000d642c000544c0c40c0c4280d4141a080c1c1464801e607550305001d404011a01c0522300340410380c1400648140090006010b03c44c0c01081d204816004100954003400740c0e01c0d60801810400348801d84d511800c8a058942606142034004d5072a001000140300b1440c1402d5a40688410301c0341c2550b010039200d9051000941c02d00ca81c00b1099403642c11050284001405131380100b0042050a040c0a4146803450082090304d0030044490040b03410400080c1c14140000c0da1001c100341007007030220110011b4500301004005c0c0c941581c2e981d00400005005c5d082c3c40000d800581c208020301c140c059144040000410300015141c842820b1307035007801040e180c0180d420421800c14801100200c054104e214 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 245252634 1250 245251384 245251387
    0xe150609010e09120a0203132403060f0b070f120905010305010b0c07061b050105041b0f0e01030204090809030a03080402090c0c0309060d090803041b090c2007170c03060a0b010203 79
    0xe2408034130a83d001340410015408140300c103800e480311416489000b45643c058070340c00100050f88600080d03520502ca042854503113401800013002010100051707440c0407590558420450900ca0f64100076060003c0c03500403080116500182e2202900c81114004e8070280010f90301c0d54010100c0d03001e80131100b4100c0c2d100d40d0342000358500ca0285010744090b4008649020300b0340d600d6590075698111020355070a0800202003101d1114801c03c1c02c018600101002d20315410802d205500b450107120281c89551242c00350014062800308841c03c040000302103900800040ca00070f404003c2c1103030300742d04c244140c10014100c020040b0483d0b540076032a2000c0c3d40b800807000c0800005800c4054480506c6076902132110010304044000c50184c5e018031581c81805ca86c02d404002c0704a20740e08401000741c00c211a0801041d0042607029030388200181c1c003008541684441c030300d0b1922550114208501c1c242d080111400003250807001c00c501641594500c0d03946408503410355074200e00250040e0b10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 245253884 1250 245252634 245252653
    0x2060d150b0f03070c022202041409270111030a05060112020310050d152a0c02010f030207060b0307060e010e0a0e061c0614090c0f01091401030e150609010e09 70
    0x17240c084404024401081d0403a000500711001540010700d90029841540c001400d0250f4150401a142800d0085502c04c5c0c0d50301c4d00741c0c03141100c8110301c280c5c540d00940004405929036402c0d00050101d0f0000c80d4042e071280f40449000b0080c1078281c4005001c00c0c0c0032a00724850700300c24000c5a00c103052207010a101d82c1d1418042c800281c880c40801e46820300000102d5050107024020340105c0c546003d891020040074005040e03250b16522410000d008141e610900141d8000703140d04580c184504006032250481e05001e400b0b090b8040446078540500c1c600070850503004550f140040d102a82c071001400d10003002c1c032004440601961001c0c002d1000050001d1819903100312180c02c1048143c14400d40507903952007035402d0760b864100b0451600c000c001105400300310680007211300311000303201c0da02c650707002a0158605008440362040c0700c0080c0328150b4001e4004000b4000c1e0807003111600c59098011090240099134007904c07481e0a0800000d8440c400d80b4120b00406844010709403026 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 245255134 1250 245253884 245253887
    0x170411010e040603050318011103070b010902090f030d0f0f110325080304030503010e0901090b0703050702010e0601120b060a1809020a170703060f111902030702060d150b0f0307 78
    0x4044071165016440d11800b0001410900c05421007821810303900c084450f0354400502860b13400b5082c500745e503006004900215285564045c1103411040e0300680d07954904010a60f00d8140c2c0c03c103541c06205080d58404115401300c1c0500701d41c0d0643c1e680300081c15060200300c424000030038813813255038420301c00410349144080e900081614055408283c8840076555071125400444040d03021980c04001000303040b01c101c8007a0ba0107440c1000812808085d5902c80352480d0014010600700760740c03280041c09050003540002c800d0745284045074030560756600e441040e03502c903403004ca03045640301022030840e0400b034134050f080d03503a0b10301c0300454016821482002400310510a0380d06c1200100d0000d03401c040c8080c10714100351045c018040715030550600005588165140c04422131400c10403203510600902547c8030701c07001401000b440321a09200700d146005070140a5402880010800d15030100e691018100c2c07000602180c100960300c100ca01600e0168444180254000300005028203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 245256384 1250 245255134 245255147
    0x1e0c011d010207080706030204050a090504120e0f1c050f060105030601032409030c0b24040203130b0c03070f0c02060d020a180f030c050d05072303060f0717041101 72
    0x1a0600c103d40b26190781e80c1019180048541c090b2000c01d50003d818086410202500340203400d04120512290405903204000d4071032481c8a141003181ca02038009030b075039500030800807411000306a81d028020b0b094101e482210401011079591040303c840103002a00422407504a4000501030030707581c6e1a5031218142c1d90042c2c00b29440824140000e8001c3e50002c1c0b05040c00c4500a0795001c070742c000c152900d241b107214040c2200b0007a1014013031030014214000509034418030b007502c0142c0c80380c50388504807003042c40751030000301510f4052080103040300d40000503501c140455600c20300a0032203400c00f0f940740c0d00c5c43c00001e900311200b0408801c5881407030b002010070f00800e10308030b04210720031321a0881613506034000c58000c3d990391404005201a400c140000741204544000c00c2c0700b420307550b10b51380d0380e45480b500407070310100000f55541d201d03040109800c407200507043d540c291030400d8500f4008075003114040007181038265030a08606148050610843c0e0000c00710341107528240055520 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 245257634 1250 245256384 245256437
    0xe15010906080c0c06150118080303060103090f1529030d03090212070602061506131203210219080405070614210105010207080d0e06030604020903010e1e0c01 70
    0x3c2c2400f04140006070400304402c9114011101c1c02d2212010044001055801c01a10900d0813200034001402488000b02c12681c02240c242800103140c11140b03000c00181804407030140c0000c035240b01b9020f24610540000154040302c240031080c080800c103545112203100c0b191940c06500c40150201d0060081d402844030700d00081094051030600440c881c80e01e03107903810480040e0003880501c81c440c1c045a101c0d202c1804111881f0782030880c452812034810b800c0e40301e40501d1500d5103c40c0d106050041400b03800c84230080000701c40c2400542d90890180d48080009080e40b8130314009440d080b442205114050755100300503181061400000301c2c1c900c03020007041c0001c0c0c0810403010000104024070356a5104a66101002c1c941c580b4001900b08030150340b1042580d0040138104210030350009503084010000c441c5a03440303441d000b010600a01138600c0903a003561801078101c804c0c21001032110b9284000140f43c14402090b60499621000300c0f016940c04181c0300260b015088035001940d010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 245258884 1250 245257634 245257651
    0x150a080a0b0a0b0306090d1d0102062d09010b0f0108070c260c0f010c08042d020604080c36040602091f08090105160e0a0305060901060e1501090608 65
    0x4248200380b001a045c920252420f240e0b581c020000015800d40120000141c1801550340c140080c800c540041d4a83d02c0080c8030300041c468001034580018542602d211490302c8070380f803410081c0f404007280d034003d00401c6038540c46451010b220407032a610442c02c10b442244c0b44d644011109079603943d00c8410180100b15501c100b28005414030180b40540c3c00340c880178080b0002000001030106009084840017241d0901304803859080002042c0c41c11002003445034014554000219580e4049140e080030b00c0f07009601050000d00080d803801c002880445d00c01c406c0707031407000c0c3c03d40c0756141c2030240d040080c000307521a9000c0032003005054904000c55002e070080402610340031102c00001c01240c1103030506429940c10441d02c002c013507071000c800b907401440c80c0c0003001507042444c0049400100c1c00446800c01541d40501c4907252220f03405c91004691003001c079030b4503040030380a20340a001ca900030401c5450440002805502011000310000e6406031280f2040506040b002c9842200c020a180c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 245260134 1250 245258884 245258891
    0x1171908090312030a140603030405010f0c17040e040b0603010c0f0f05040f0e071209031209080706050c1e040b030f0705040e010306020a081608060919060905150a080a0b0a 76
    0x3c408210b000194070400e04c2c610006210b002510b1000da606034050310030790107070744227110501481e600081c03514906402c90030314450750002464144514000388e0391f401c6250030b0100d800070300002007042c410300540c8106d00e0400d065440c00e090508940c206220140091103980030342000900a896034101101c543c9081483c0903120b1042e5200040f0032781c001416400c404d02009016903010390807004c6420745001c240030f0405191001440d54158580b420310607580c0d40302410402424a040301d07003586d400030b801d01c000e180c00c180c1451160020706a50b2441301000440c1030030040f10b10211420307903c8080005081d41c46441400396010801022141480010800401c0344803070b03454264000c600c0360703201694902c5505d100503c0c11001a140f250160000001c00c0010b82c1c02161a641c4000c05070341c109006d40c0d4480140e4072099191080510503441e1560100380c007109a04118418840d041600c112401c104d4284920000c05101d5904142c0016940000007400b0849407a0801803000011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 245261384 1250 245260134 245260153
    0x1914010608120d11030f01180b030f070602010b0a0f09020a03060506190f0809061503011d240403080c030402060403080f03060108060405010807050906040e1203011719080903 77
    0xc900d012a0300708410090300c404103240d01031080324010300751103405004c000790644c1400381d98a100c9103418040d00c40b0307446491688200803441903000944942e801400c0342c2170301c11082c40240e2510000c2c0911300055082031041c40441c1041440d040842d111040c00b088035501e40300c076010094100710340080405413100d4000a06a65010251184440c6100c5554520251300c50140001a00e09401c1050108a80c1006904400851120b62041d1500c40c0e4040408040c0c000038010007680c0344894100c0c0402041d8a202c51000a006041100c0304c0e82501d42c3c08020742102181c030404541c0100011614000910b1654801020b190414030207007400c2e0a1544983d40c00c407582d0008690083d41000201c10048503607845400d40d0340004041d5010410b950421052584512070b50185d603014120100100340d4a894230780c08110064041c2c2d0a545c0c0649140d02240010340c020722030250358881b10540003054002c04240a2440c814601c4807042d03080307142c0e40d12030722504501800c95060040315000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 245262634 1250 245261384 245261399
    0x60908030106080f011e050d0606180f050a0212040f031101050a0506130603020105090d0f0b090a05120301081f02120c04080d0507020f0f0307090204140f0319140106 73
    0x140d80607014070303250102a403401d294411001c01c4140d002026800d4103200c03060036880810041c509030f60040d5456820104141030030000380091ba88402001c1540001e03822350700907694044d16580002e0407050040d03440e8038004d030059000700b540410380300161501044c0040c0b131030000781040034880e01340140702c000c04000c9907003100e02c212804d051b41621582045028070b0701403544900443c1030301c41045134a0454000030f00c5030050040c09805019000d55003020310a07428240184203a00c80003413119032414602c0d1341d0f1519014141100c0c0c0d4803949001e5a170f10040442924140d8101d507004045130100740b17040240540c01c2d00c0762030640c10780c20002609100540c88a0a12800071020540e0740c4620f0400e4040c5858044400308040040500081005a0750b06007600c0104100304c0d01d80115405980009003000300c181d100000301440000c0c0021051100d440b003c0d00c04408032043d0030320800c0102890b40315000304200100c000c40c50f00340034002a4001c4001b1440c0c8404200001d10f4984855a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 245263884 1250 245262634 245262637
    0x313090b011b06091a0405060114010e04020c0f1203040f0201030915020720010201061a1b060901050a15050603041709192c0a0f090c0603020714070501020c0d060908 73
    0x405840d215124003480e0300740312454032007459501548402c485e81e0b241c1034a84035214030040c083c0e44a00c040c0c6c40c40301110340e8450318075401000c1c4020002c40d0307240c0c4400c55255030359404d140d41c490076000d0345007840078200c01c480503684110b030003100d101585000fa600440040c5240e0000300d07122444440a06041d039402d1005c0c1031454420b18a0700701442c0c440302c144c01142c1c841c091640c1160305000d02408180d1041c058107141203903d000c09900ca45c03000300b40e00303085030500f2498200d6208917010081d00183c1508a03d0082e95804001c1200300d9a0481051415a150003120340081e400c20210700002e000a41601004000c070b43c0d000d0800c0d40640000302c900c0f00c50324002c5440c0c1917100c1305124000001c4800049800b5086a0180c1600544034607150440002e00d9070540982e00c107520201c3d00519000030036540d030300001180c0e22036120740c4090025000300d80d007a10305003e11800d04c40011000100c41082d01c40c140c0051601c03003a42400c108082c07003c12012a8525143c0044000040c0d0900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 245265134 1250 245263884 245263937
    0x1407030c0609140a031101050601050702040e071e090b06040303050306010c06060e18060f010e04080304050f0d09081005070210090204090b0703090b130b070302030c1201140a05030313090b01 84
    0x20041c0c0702c40d4105085c020b00790381c481c0c40403518a0345411300344000d507078101003250300d81c0d80c1c141d801052040180c3e40c0745081c40e40d03581c045484a10b886010214000400e50501e00780e4007500e200304002c903140c0007400810700903400300801140c000c00228050750f004084005690b486503902040164175920105820002035803003508099100804003050310302032025580c4040ca00c032142840f50700d02080e60020040140015050b00d90002c0460b05010041c03001300e0f5202d4020045411103605020001c05404a030302c00e0011900904ca101540c01c120f42c01002d018086039801442c007060101500d0000b011042000c070b80c0596500d924100040209002612441e180d0720000b900580a0901c00300c0c45030020700c01c06041060110313401c00584c004005a801c9006441d0060f1a50384298101e4014410a040d6080410303002000003081d040b07001d0138128003c0c00307440042c4450345e90401e140e6680116150f400800e2110f240a00011180e03602405600324149410341800c81c400852040d143c0988 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 245266384 1250 245265134 245265173
    0x140d0822060201270f0305030702030c01020301060228030f0f050403140c0910060504060c0f0b151216031709090a0605031209060307030906060b0f04080705011407030c0609 76
    0x1208007061402c1c002420000f21360020321200e04202d69130b179406142c0204641e000b0248a0040041061144204240e0324007400c0d00c030086660703584400e8040d54031000f4550114100803c13408010441e160351404807001945074032581502005000242c80800f400c5a00208100007480000041040505000d04019100700984a4150300600f070001c42d00c0d00400903445d4211880c1c0402c04294058203c1d000c8403171720f00d04184403200900e42841d001e01d841c00d001c0c20041039034046c442070382e1f44044113240011007250b0282d41141e0308001d82c0d48520006179042d0b00c00c00b0f903c00400100f003180c1c8150010518009025103000038070400a000e415040d60b48464041d50b50788103010341c0c1030810006403001004103080b400c042400001075168400184540708258031404d1490403c010381d0400005020501ca03140c4d1551691410110745810512904480f0312941c0c0001500c1d5029006004614070200040d515001168405927207600d00b40104540e490f64480c0601e012400c11404208642d841 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 245267634 1250 245266384 245266391
    0xf0513090f050a061a030c0f03010e182103040807230f070506041403010b0406121e0c03030513050405010b0903010c0801180e030d0203071701140d0822060201 70
    0x2401c468800b1180010101d40d030403494180103101c841c8801c103200c414170741110940c913540da41c1c3c081c07003d8031401090101640d164000c4000f2407940c4100d00000c0c1b2462400c003243c411070508c15000c3d41d44441d82c4100d0541d010703900c3c80101c1c0c010a801d0095a10501a18000c0e1070911181c0d01c982403892a005141d2078451400050a5400003e002010700c044038207000b0000c080c2004002039075846548940031888040d00d0807801144c4081d040441e1200c001401006003903501c0d80380d2092031450241c100c8101e1a00502255401021245443c1c1990460348500b21036055540994480d44610a00d0b8510b06c1032480001c0c00c0c0d500c41c01682e0183c0882c40c416a12000580181070079641440842070030f019491005000d620350310420200c00882e50207021840c4521051031605511407421500c000c1400001044200c5401554030f09906005d1901a581607a85070b401408440920708100d60141d40d058140c3c0118900c600980f24500e020600110f203540044104a50281c4503070001000d80d44 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 245268884 1250 245267634 245267651
    0xa170c031c2c04020a02241008030408070302040e0a062f09130c0903020310060e010506030108060a02090a080609071e060507060f02090603150301110c0d0f051309 72
    0xb444007500c140350300c000081960704550140c035803522890368a0b4841c01543c0c00311360904294130802054902e5050340500c7d21a0f49a00e401a00150400711500c15030407104500001e10540700004850803a02d907a000303040c1417030440e804c11024118105d00c16041d44201c840c2c03a80030420b1803080c002c01ca000455880c648101003010b221502e0261525451031800c00e001d4503040d500c0d084141403008091240c00038207440c11240598000c41030b038001039010b115105642c00702e25100d034456019030322040d1201a8903030742c44040142d079200034000c05d0b0300c61300942c01241c0a11115000f415800200400c2c3c0c0d080261902c12a0749412000c55610850741c0c4040c43c00c00044484081078002080e08603681d040681c20220041c00f18800c0c070800505455407200051104000f95041e2503140070014aa80e581e4244400c1d460301c3c91003005402b40c40b030752070300314070180320842003044949500b0381700003400303a520700c0040c2603464880c1860401c040c0901003040f0a141034005048002501320110001003444 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 245270134 1250 245268884 245268887
    0x608040b060a031109250201050916080d0c060b090a02120601030501050d0b09072414040f0326030a0f0b06040501020303011802040902070609030314060a170c031c 72
    0x5034081e10080c001d260740030041c07000c118070b9902c0051105007070b1418001c1c0d403605010f0f40c54900c2c00e14007025a00940b40720104000f58190030860280c0042000c032900c900301d010804541b0101c1c1e214114241e4011021151402d002d410301d00b802d240203100000303000720080040380b0309850840380903000507030000700c0801c00c00c0d030300c200c0d580c0011082c41c04202541c140000720304130103da09409402e0115034400a40e8a990420904e0b001d006442c5d00c0000b200100315507908018044d001d680c000c22180c0750b9600d903200f295001c1c2c0c4c00b01c400d2480f805810a1543d2241c407201507014082c200007100c0003180082c40e205a800860240c014120001303515202582c01c00d0480300c2c0f2801c81c5210303501c104001c000d140c2e8000203403410f540d09800b82d24910201c4503a004000d1041d548076135401ca0020074200e0a12030240e02a03940d26000703440070b000c071241400c15000b00d07801c11030b905070b44040807190a0203c0071105100205a410300000c803843c000000f00068505602c4103407944414a007003200c2042d15 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 245271384 1250 245270134 245270153
    0xe010303030e0a120309080904110a080a052401020c0301060303081008060103020d0206161e1505100e07121107030f020d02030403030c2a05040b2d06070c060804 71
    0x450b0100503107181c520564448070383c80c4d40d00050343c1c1003540310780300441400b0542048400c1020002c00401c96140c0c1044401b000d40c000544c880c9c00300d004000064049142801840e1155070b007001c5914154525a0741043c001310126071302da045120f00c40c0c0744101c6071024461b940c0618020785078840e442c50115200b1811035029005000183c000341d00410058489645859a09604132074075902c0b400c0380342c0c07008070f60780009401400134680900e004c0c00c47c0c0400d2030385100075802100030701c9030520028400c4040d86c2d0300742c861081c0c24000510810513104818460748c1c00c155245440d5105040030f22107081a200b02d08904000b5100011b48a401c058021000c0801e0380e6290000e480c0d0700c00342c1c00300039440307000c0c910000c2c05115003200403004003c04202c81c4a5103900c4100d00640e80f4049103a10442c1c0e80c0c01d806140e0240e45808102c034894580303409008050680e03c21000d0701c0c0d041d00d00807100703020483c1c1d5801d904072000f03122410011312124060700c050950303540c03503e04078a0310341468585c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 245272634 1250 245271384 245271401
    0x9020c060103120309020f21030714010510061e030b130204090501050306010b030c0c030403021003021201050303090607030e27070f05070c03021c150902120303010f18150e01030303 80
    0x4d0500e4a1028001a05c0350303520712030803803011960754044c403010f41c01070075200c00380c0d41400056000c0080c01c2020441541581c5c10794003160b1000f0040380e91010012003440059008900c08141c050b00d8816446481248884c603000043c900030441110020110790701c0e1056060800c8100d0300405c00b444440704521400d40100800c400a000a52406103944018407000e00300c00080840020310601820041040301c00455010b01031400c04000751000400a401c00c50b40740a070401807200024540c5000420768116081c001d02907031a150312a941940c10703500d440e901d20b80240c010302034201d01c0075003450007581c20801e43c0181c8409107800c2c80d0040021044a0409045c03240602c60f40c1c021541c03420580003034a0b4155502c0300030942041d003c01c132003424000300906901d06d00c0958400101640c10024080344240c54042040c0c0d8040d00f22600ca0200b40120200d901031240100603610031900903c50107240c03403e00240c5e1801c2e901e0818100d140e01e4000d00e0148008500410401d40d25105003c038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 245273884 1250 245272634 245272637
    0x3020f03041202010c050a0c0f0302100c03050f090a030503070f0311060c1813060906090b0607021804030c0501090503041a430609030e1905090403030609020c06010312 74
    0x3405042c00c141c0300c0484910305000e4100000000c4680c1004420080c0b4a0141d401850b10962150398008100d2aa0301c80c0c00f040f4003408080c4060f030381d4507000e6180345942070f0303068031441e0401c8c61000c0110b94a40018090a922502d0400000041081840241000d80c041c0c445d6800c0244241005085840a20780240303c0b50f1000040100c055410002d071000e520f102c140c10058114210000360480d6020b00c0030100c0341d0701c1c1800000b03489900b503011a00315840c035603091181404400c100b003203901076200003a4005500d50024850b032a034001ca89940a40300f400d10342c07200006a00c2d00380c2120a10402117955500026061140c10401320000401c029000401454990803092091500703004401215849203c405020007107880d401e0b2148201d507a152200c801038007035041940c05003024003015401719016008058507418445402440d4501005030800c420b403900081c010020030040c401d50415031386141c0032039100443d0000707009844a0100034080c3c0c1d4114200121080d0001a480e130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 245275134 1250 245273884 245273887
    0x308180102120708030a0605060d092001080f180d030c140c0d1110020c030415090f17030906030106080415481214130b070c1b0303020f03 61
    0x1c01c95000b0380c01c4500003139000400310744035103a1755203410180c40d40c0c0d04210b0340190040751b01600c4120551080400d50300501d40030301e02100a03a00845820803821000f0300040751040080ca1262101c4030140d0000724a06100401d90940500319040c02421945c010000e40ca601c40100100e81c80b040c81c60350a910600748501d07000c0c0100e43e50380c0d1001d00a00310b100740039010740c80444426051100d5000b1100c1644290341d10810480300c50303160b1b0720900a100e140c250340030f203166071540704210000a88409200305128141842907038600b155404101c240349100030082c03c01a0b0719504041c41c0248002e4070b410f00a800e1601d42151620031a00d0541003080c90617403c843c042c04001204c10303480a27009250b001c426007a042805000d000b40b405050400d02a007000206c8070361164030620700c0203a0602c1080b841a810b1104109200e050b160340802400605800700403d10707101ca11508a44203050070500b200c3c003940da018107c60560f60006000e04450010001d041c3c05100d03854945213000040d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 245276384 1250 245275134 245275153
    0x30518010207120b04020f0907090911030624070602040b0901021903020616090e040507170a050c040b060705100606030c08060901272c03090f0609030109020405010308180102 77
    0x20b81d8100101c1d00150040d610980411709644408021420301e901c007408400d418640844080c2403402c4070310079010340700d00d0030040174002c90a1905680c004c40005040150803035080c941c2900000401c035400030700e2003082001c40c00013403852008000038040d070b9070340d1070311086a14006070400c684418a23503400d6030305201c1e00300025030200c0c0c200e502100300105000b82c0c0800c11001c981d004002d8210506114104c000d11060200005445044a014140c2c0a10036103149103010f480c1c1004050082041e4407079013400d607042c81c25400c0b41c26005000313071280c0c1c10074805454281c503080e6607080590b040d0380d9983c0140055540750082e04e0340c8401c1c2c1d09110b102c40c1020000710302030180c1449055501c10f5440148000441d83d014101300070036140205001010307a11703803812070702c1d044000d070303046200060a0030347c1003400080160307918104020701d1b01104002110600583b94800301d00d8650555980ca048001a90b0398411940610702840c03002e07843e1000710259980078030101400c0c0e410744d03000c203402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 245277634 1250 245276384 245276399
    0x4080115060305040c0e151806120d020d051c1b030c050702030304050f15070507080c0a15030509102d0509070902071a090c010201060b03060d0f050a020409030518010207 75
    0x841c002c6070040044040035035a07d2808811481d030344002240e0000f00710248002000350042000e00030541290000104a84051013603910059081044056081440d844134654000c01c09081c040070664221024150302c4044c01d02201c00300300c3d112004a540d000031809643d1306108803009101e042c10039928009164000a130380340124030610384100e40075000c035015600c0b9540a6803640b26031545907601d8101e1351612540300c501c80d02038400f10344141b01310b824042c0b8100d4103800480e20601d00500c0780840c2031808901800c001018800140704510b6103840c0420307503110343e0032803410b10010080d024406c0513804508910088600c50020b040c0b0b014071000207404201a421904c21204c0107990310b895142c0b5408518013508000c02210b810010003031403040c0403641e0456420241c1c0200215030700d8043d2800c682c00701340c0380203030415118511080050f1100700115091030088040f140c00c1481e0340d00160946450000480c001007010484101107107612106818201090000e00103540c02c0408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 245278884 1250 245277634 245277653
    0x80601030501080c1c0606030f030e1008040f050c0a291207230a0806030c030f0c0f1201050705091207062c0a0603151e050105031009020408011506030504 68
    0x444074880c201c5c00c0380400c5a641381c400c00385103151780184248880b039928140712101c0210b002d001c0c0d02040c00d0407072000c501d103400081200404850346036028140c45540300c005400c24101c008031010710032500c03010056034502e580c88000b482c1100342ea0001c4c8c0e01741184080d0002841c500080c46810a0014a100e80d002401c099809203c03407520f550160030014080800c070420a095041d0308500003114464107621400c004e100da0401d4044a00c2010000103260381d035031142c9268025500b092010661a1070300300b264403a004002400000e14005826040342142d80c2501c40502107000000e40c1d0303d403404c00d01541031036080e00e000505501071402001800c1003911514000440c40000314003051480d005001241c1c0560103800d4011441c1c0740c280140c002c0107544140d0069500c0000000b40165981807036400035104e01100401c868034181c01991241c01c0a480040c646421070790200c0e20348028070103031008115030f0b8000324a410384040070003e020a45c0c1c02c1039040600300010040401d01e103c1d0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 245280134 1250 245278884 245278903
    0x5010503070b0f07030e0a15020d030b0f032d010509070807080609031c021909030204050c070305090405040503120c0a0807030626030408070e09010605060703080403030905070b0a020105040308060103050108 91
    0x5184000c000d41070700096811f403464000d402d80799500340d0031066695000881e0fa10000064a04000240d51801000044100d505040b035240c1d0088544600210007401005000f20000544840a003140c68002d400e481044600c20327281d61004030104005002001b280d002002c2c030401814250810182454aa03ca26600500c41c0150400c83d0790300d40000e94116140440114240c1c00e04400841c0004d08602d42840700b684900c0c100740129000f0030300d41003241d0351240c1c140c4400d4581400c4100740406441c0081c41078925010510070443c140f81d103840040e1040d40340b80a00c560f160311111014082000c0680a64201440d2640c140b00d9216104030710801c924801040d43c03c4000300008051451259801001460290307502c0040c8201d0441c1ea224012003000001348820b90f140c000b4840316008510001c0c0c00a6a801d02207004a0300070f522044000e80031305d050701c0312207480b82d40c45600c9a00c07410028005079529001c110506922544c2c0640194092905101c503514062000781c0d94040d18 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 245281384 1250 245280134 245280137
    0x21803060a0203101401020c060703080a27060914011517011b050313121805040b0102071a040806010b070b0601020c0901051009050a06030212070807080103080306030a1505010503070b0f0703 84
    0xa085145d0070740c1c001c002440301c2560080000b41d40f540b20b4039000f481c1840545c2d0748040d81e23051003014102d448000c074130082228121030100c0310303085481d1920809231441e00420354504084a103400d06440c02030080c2602035401c000b24949407450001c02c0b01150040790944905a49007000c02000c0300c5014100050004052030300a4980d216500e000c02003029811000b041c0710f42d8112510152500000b807803000402c8030308480c1f01a80c0c0d800070701c0140c0720801f016a00503040003409000c816400c000316644006000301c201e0915480e83c02071031500000b0307041580c2d0804080f0300c100800140711500c0380d000e0002e1010300180245140440c0100106004242c410040c200c040582d071071183c100c12000f40700c000c00404080d6500d8002400941c0018074210000400302d001408082c0038030f100364014003c0d44d6405074240c1c60754a81030302d6a04060308003580742c0100700b004000709055411039081081600c2c000505035262108061818240794402c14107000e0500820400419003016a200c95405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 245282634 1250 245281384 245281409
    0x110304060b1804030306170102030408160c030c12110f0a0905151e09011a180604030812010504050703060b07110f030a050601090c0804151e021803060a020310 70
    0x5001610005a061402c4004540a8104014154590031107412a4a8400880c032031841803800a8281d02c821034000d80009800c2081c8444501d00005060015000b070103a800b40381d40780da4500c151180c05070b0111380119481c20600051044066144601c40811104200f21507000008601d104a081c17140c0d00710b956552000905c5840f0341616060b02d078600401d001e0346c40c5818001c851780481941032241c014601d480011800764198031078030715940710b035081050800c1c01c0d50542c2c2e00e00042c081c01c0503800941c2400000001800c800c0600310044a00c145940d9540c14201800115007004100c0e900301410940c00b008000d42d00401c44260907084048642012031210204100507510300d2010b400d4452800400140700000c901c00c0c0c140c8100d0441480b0011840d0000c4911200c00d50b4090040c2c0100203a20030543c2442e80407030000ba09810114008561030446070701280c12400348101c0c0c4400c018000301310780c681801010707800420403400310700f141032036410b4151040e80e40c0038000d203000e81c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 245283884 1250 245282634 245282651
    0x70b070e0105090a0801020c01182001090b030708160302040b09130e07030b090115050105030105010c06060f12030305011505090d05070b0d0603140607021209040e100204150311030406 81
    0x204100700c5588410140800c404503680c1c0c0c0c170050007940100c0742c1c20f201c0c0d4070b0f00c00056545101c0c0c401d03c104103a00701c000410103400b2502407400c80000e07500e0300350602890141c0042c0c9132214101440c49070819448590103032030080c40b1110700745c40310081c440030107104000c1480540078000985d010310000751a20303902b94011151440c0242414508400721381f140a0001082002c00314150384681e420038024000c04200d14281a1061403601466010032020310051017a0751180020511460280301d0218183d0790760f0b00b441c40c0904140d0400c4941c103000da0001030a05800d8007543c0e005100d40031030322040f40301c0760030010414010040d0062049a0303ca0803802404010031044014001040c1029a11407122803c01c0041220b44800c86d180e660001103914071200c081907441c403d00c11500941201c554041800089a01003800a030380300f9910070f915074414034100000c609585a8034001a07446040c81c0000006101c1c0c400050101400c00c110301e000315544034244d0760001d5001c07402285651 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 245285134 1250 245283884 245283887
    0xd0c14010203091c170405010e0609030a0215090a17030412050a121e02030a0806190f030b0a0612030c030e061210060905010c0807290405060f0606070b070e01 70
    0x42025402c0342e11901c54a01480102c070940e002402d02441794090350021602030003910780500803071003841e021072420b01c100c00c420f041460042c044070380014103403005403003a5030000e8002400148410007042c000b01e203813042814003141c24406003c00420250b280c0c04481e0395241d50b80709900400f00c4012144600004010042220fa49020380c072804ca40c1c41c5048640c40104020801881d40c0a000e0b2003610f040744850010086410400c22641e924403d90380e00d0050285041000600f44c020480600f8001242010740700313100f0186114042907080382c109400f005041e510700c1c0d0407002d007a500b035010100000c0e80002c1c54404055050030038030416a0f0202c0001d21900460481940241c1d10b1410000c9146042e280402601c07180e845088031035440703400440307650030766280007440d120040007910b0110f101d140410f039441070703603003408185450f10368034102c221a0140e808407010340c01481400161094541210b51180090b02c4003802c140721900e44034215440900b48a05011260200c9007859 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 245286384 1250 245285134 245285137
    0x108310f0b0703020a0e150d0902030c030d020a02040f110a1103040b0a050904060e010b070b04020301090f050a060b06070201140903011b090602010b0a05031c03020c070f030506060d0c14010203 85
    0x5a003000300701032146000c50015004e913020704856000215005002c503198074000907085e04002500c0006418508904820740007070005000c01d1703901d03200707a00303140745103680400c0341d801c01600c264050200d80990344148070a81301e8031000d1940541c00d020042290728000003c4c1c4103510600c0c6083c100c044e0036200c83e030741188115001105441030000c0c1c007030302c2c403230700f040040c0603641c0b09030780c100702c800c2d0f541d0715592412500380925140c0120810401001c1803110b40300940041c00200005120401c51b035500c00b5140c4140c0f01143c5642010742d40200307000062003035800401055660600d00890303540001c20034180303900b1119615001140070a501d031025841080c4110705c1c0e1000100e1100c03000000b400080071482400c0056080a00c0000e80c0e007031003c15034048400180080101400004004040100f241341c22010140e00303015002c5018020416000100783c84039902002d0b03411810036608052004004ca4012500000590002101c0250b60b208a842c075007900070301c1141440041f8250b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 245287634 1250 245286384 245286413
    0xd080711060f01030209100f0b0a09090204090b0a090e0c060d1d010e1207020a030204020f120a05072601050111030c06090312010f061d012a02010831 66
    0x540300708400c20464403021440141a0782c000c4403441120f03a200f0f0030440c45009140142c1050440d50740082280524600281000c4541ca052482e00151680040b500b260056401505a583c80b455545081e0822045c0c060252405510500815062848a9640d481240031490160383c1c001201030f06400c2a0f440f030580510320144690070b10107240312041c00b034102c21040b66868083d14410030301141c85881103400c44c41d40900300c1c184070b03071564080100a410560742140c03664420480100003030010143d0314490030842e6000110f50900740001002e100c50f9140d083c180040544180c3c3c1d2170903203866243d044441c00d1070102d1001c04c000d00b00da41140140040d203005441090188040740c040030019100c00f0b5005003200f40b00f6070713852500e0b91040c001480b480c00424403201d19000348001540f072017404080706040900c0341d05c07540aa808903e030280e80110300200e011a188500310369003c070942c0c3e00302040c41c44040b0202d0000c004120402c3d902e0b511200c661512030200e8041000203840d20340e5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 245288884 1250 245287634 245287667
    0x302091b030901050402041514060f0f0301030f0515010308120c0c011e0b010503010608010902090616080309010f020306030709020327150108012013080f0304030309050906030d0807 80
    0x84904046240d0b038064001079508038465810480c015481800050030601203560341e412012a410101d424403041d0761028007808000c1b0820020f40b001d11500c0c100460085124840c01060103841d13040c100d00302807440803e01c140180040042022490b8030081c1e60003490920726018058441241c114034520400384482d4a5500300f24001900ca0613061542d0a00301e90624140700000202004441d140301c2405104003150000c07005115219456000e050382e03007000b9046d42e14000c41d00040104001940c0c1c000c4820a0000041224064003802401c3d41d07403d42030011360450500c40006521400b032806a5800c40368040002258421800148907010b41c04180381402c051002920a40390000803045070381c00c1944400024214a0511850180f107515030500c0000302d00c05100107001c1d0384501d4480070306100ac00b03c041012141480041c01141070325004590301c5243d440c001c0c00b0100b09070b205038441d09094040115945010409407030415042c9002a450fa650f0601036070010314000c100349 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 245290134 1250 245288884 245288887
    0x31302011b0c0f0f080a030c1416090204031406070207060c020a090509062e090e1c0e010f110d270312080903070f11060f030f01030210180302091b 65
    0x20303016600d83c05101602c40211001d01000d4a492015984405412000340000c800c9441503012506000000c40300008000940e211a4040115606025181c1e0442c0d03400582c0017404100f00094000e170700c018421818050301a80c9040c000194440303191380700c0c03602840702c0d0180c590119911101003001070a1031540400031401c100712441d40e41e050490340310090035100c010f1610a00100220700c0307a0305c0c4031419038031582c50410007400050482c80404002a205002c002c110b6260b8034500211404100d40c4c8a001418a170000100001144010b010500c51030b00070364540c2c2d440200f0610f8141c4040e00300100f640300131603a041c4408070070041c02031910307d0001011081010800d03264000181303903030f1080c0071a1a201410383d2a4424008001d013000b20b0030414800080c0c00c0c0304044c0021300c00a21180c18041c0514030000381c1d80c000c841034912207030200300600440c680342c516212011175514204e0f41c040c1241940c40c005003080d0201a120300c0981340040c0c000e18085804115144034021600e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 245291384 1250 245290134 245290139
    0x9092a02120c030901091d010b0a0c050a05010b09071b060203070504051005030108070e1522020703020a0b010b070b1909080f130b03061c0501140c07060e0102031302011b0c 76
    0x4544a8114280f09400a0035050000811104421603500700c5211211fa80905901e8020303906141e60103420020240700034100201d002c00d10a1092a204d94020000425000309a004001e00704170000c040d03030240688001244102114110b280d2100340c0e106a006a40361548803064032a40501d07400680d00000036440244215840700285040760380d0f070b4084414940c2c43c1c0d50003000300881250103d050744d1403120461514034104417586405c500c80c041c1e00940341d0401c00d084d41070303900444054000d684108202c2c0e080128481c42d503401004005c1502e0b0900d412582e8010503039030007411600c80b01c08100d4503c01844902d5210b4a01647d02400d0190b9072500801182e406401c03007035000c40d600d080c1640001f0303211907042c100c0b4400c035001080c000003031038803003080c501c003030498401070311259a034203c0050540c120398026802651016100350311a0705038030300b0700e0035140150502c2440740d0051042c40803038062128000c00840d0b09017000d011112000180e10481c5950303120250600b182d02d41c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 245292634 1250 245291384 245291407
    0x90c08030f13050108011a0a090b040f14030606090f150406090c02100902280b070b04050f0d020613020612150112140c07020a0306020a0302090109092a0212 69
    0x70071050403090000c8180c00d65543c0151041300c024071030303048550407036160000d03c220240d00400c060310302070600d000c442e602c50030302441503003281d00700a1a00344881414072841c044000e14848011044000308441e142030404140e04c180c02410316200352814001103140a011a0000b03441c09401502c10400e059a0710070441c054082c05c14000050f0040302c0038a45109494014140d0340f41e00504802c50002414011141c000c41203140388a0040b80400c021031101c001e840103100560140030700142c2804d00741419800d00083c10710700e290b2075002c0034820304143c0c0c0124840d076000310613454800f507403201070000c150139220303410280344106468020060749018504041c2e480c104280c1e01d0111000f5480c40c0201240c40107410814401c10402c0000d41e52174441000b4050144050709800c401990b0f03540d100c2c03d03a0004004003010903000b090840171075a102a41c0c1d801082c1e1400c082c0400d94100d110404070f80701407040380c198070031200a51089030780200300780b82c0e1081082e501644d99000d600c03034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 245293884 1250 245292634 245292637
    0xf090c04091503030905030a170f21161803080a050904050f090c060414040c170a0c031107110d05030c0a0807020a08030c0303010b07020103090b0f09010605090c0706090c08030f 78
    0x114085521140e0106d81810009140c0c480140e014103454440c11140b83c2c2100c03160800c40400c0c040c0003040101c00d4021117410710f071954a04041d52079012a0030710340103044040c2000c402480802c000c50b280250307018092491001101e4002104640d1101480d1040b40d86104044149400c0390602c014862118182510707a1720544c40300b020303600714041032010801184214030034030b4003040d0003030060a0179143c030b13511024030300c8040e0801095500c0400803054aa420459a80c0f0301c0e26135540c24140b861381c040c002c07005d07001808814145450380d2a60f601c0395100703102c0c0030039001d402400401010004204121407103490740e1802c8691100f000e160581c0346500040c2c08030b00170004001e0000e03249400100b9a41d29a500102541c00c41e030038448603101641007200d00b42c1c10162180121070103c0c188103c0c04d80a81d005005124a92800c444540c3c00d403041d540c00140944101c404009410b503d4000342c80c2e403d07901042c0442c00c15810f003044e81c5048610741100311f15010020f4520382c41c005a40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 245295134 1250 245293884 245293889
    0xf0f0b060307050402130501031e15140301150b03041103010f0618050402090402010f020307062a08010510051e030a0507080f060904080d020c010f0204230f090c040915 74
    0xc1c1211003280d103c0061005900500281000b100c4000005004540c040e8010200d5112015a4500310411460300e070750aa90765080c01a5007416016000d000000d041010340d016410181c0081c80990302070805ca8295039000d02c030740c0114000100101d0304010318808140240100100240603140740211103000800691042842001e441c09100d0100c803624010f00c2d03c29900180000010340e1281c005640051044000c0411804100700101c00a005446140e0003685104586507250420105e03451a80d4100b15144040c0050300004110640d142020a1905045880c00c0398541d4800c03815034040952241c0301e0003072036502000300413044005500c4944503507290307130700c00a07203807503100e000004c0c5842510816040b260150029011505020051180e85114000180f40100340042d5908440189084111250700020300300414103000781555244003850303001103036005290300094018030040020718014100e44000580800c06903040d5401044000c070305009901208008008488560 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 245296384 1250 245295134 245295139
    0x923031e0609010b040b0a120f0f1b05011e0e0307050306040503030615070c03060c1b11090a0b09160315060c0c0605031512070f03050106170d090b070f0f0b06 70
    0x181c4c040c81d461815000b68101103001034840014941000d4030107207111600c01c010b8503202007240c880000281c6881da88500c05000d9100c0455401011441800000700c5600060402c041c80741c01040f600c074031201000c82c0700c0381c81c1400c2e80c03540340c3c0e02c01090a00c501a40441e905001f88820031060040210003580301d03040c11211180162030100380011f15024400014040c038050b46000e10004040745e101001407201d60428001204101215041c2810942c1c005c0f03540c503440d6203105e00f99003003007120240c0042d02040305020601d018008100740300c500070f20641e0301c5002e05905e26101406030303108290189403000030600c81e80d00c80c1d0004c1c0480c0f402c2c0d10308031480582d454000490502c5201501d014003400c0550400c11a08202000b15120011182c07000c64003a8041c00562091112803500003581300c4c50000c540c25281000b140800d001200070030344d05030000c00c080c04010380d01410004c00c0d140e91039035181d140c10035030a00030203d11912200900f1203640280010078031000022803481207008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 245297634 1250 245296384 245296391
    0xc0e190b18040e0d050d110f0a0215061f052a030a0e19031b210302011a0108010314100207030306030521030a0c0311180a060923031e060901 62
    0x201c0b030f90140c1d10700c4409030450004030207004c0f941c182240d075004004a541001d04103800c14546022094281d400320305001d0159100140e20307140f11810001090f4007190440d107c602000c0c02c652541c80d072540c0202403104010b0001600b000c02025102502e12601d01105200000f807155010b2503525807088100c0800700310300d0201e544d000d140c20903040c0d0f181035038042d54801c020b00e1036645082c0700f124010710001c001c10640000c181701d544a83e8140c82500d000d84154000c920508002e800c60308503643d250403c50800d810b120050b60090070050440754407000e041c03054003840021070700704071911401d000583c1c0001801d0080c550300d500881d007500d0080041d99451b41c2c0108250310500c0e45880d440d28207031400d0000132210a1580e00441c98a045d0307080216010f018840c1407001a8400380e0300c0c00340381106031084c2c01c003401c0c140704a101031700207810300f80d025a0406039034041801005240034540c4041c1c8801d01c85544040c01590190311541c140754012601e0440c40586582c1e084400480b02e40c603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 245298884 1250 245297634 245297651
    0x6180b01050c0a0f1b0b09040b030c10030605040f02040302030a120c050f060103030f030c02060a0e01200409110304200d0819080901110f0c0a1e060f0c0e190b1804 72
    0xc840300b0070100e034446c101c42e034030b0030140d082400050003c0b0300303980344e1601034410003084c00d454106510302011180d581c0019000c5c180b03030400040b284000c42c5090141c0c4180801d00041e180003a404000603000340010034401000e035021101c0c141a0180142980aa202c0a440d04a00040d2040c180d0b0302ca6160750340f5860020138114100e0b00992440001623100c2404206000c010380e016507140c1c07035001c002244800b2003908428400c0e21403c80038014801c0040c007000400030900c661107106000a8802e4518100f03920340303c4519851061088451903004007100f940c4e0f0b105104200c54903802803880d40c80704d50b01841200f20f500c0030351000c004500420300003015400c040c480c1c08207100301e440103907042c01844100d449503034201829003892849042c0004010030044210500b04000900401840c942c8506e4038401384c0c3e40305a4007d10355810035450390145500802140070f1035400391403170158032011444000b6241c1c5107038003000b0100340001c0c201075441141943c100c1d0320101501c05001105 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 245300134 1250 245298884 245298923
    0xd0804060206180d0804031e1d030a080406030222140a140303070305070c0909080705010e0604020904060c030b060c0c120307170c0a230c010306180b01050c0a0f 71
    0x50743c2034480c8442e030004410080f0881c00307040c41c550028020301e8a80c400ca6000900c481c1d42d100450302140c0441c01350350380920208a0250440c0c02d110b0250050f01340d050320b6903250f00180c01a801800145500032492121550301c0544100e041c03080b030351100d2b070030f10382d1180540f01109103d09407500944041b040402c1c11500d01c041d6400410019004524280d000d88041f2955040003100700c49481d810b50000810440c54020140154000d884c810368507002071030140c2c2159046014000260814010030001d6603844400350340c4642c00c8000418140138405045009188000005500650205540c110110009040186e580d0242c0e4400644c01c50700f01503e42e2402594801800b400d180b40c58415000c40b0500a03199a00201041b140c01402c580d0b03c030344070402c90344100700000020301030f00d07590000e00304a804800038080c02c0402260b0b081018400e0002c1105814103165515191445440c4c0d11036070407182c5028488095510348903240c641001120101407094480d211020020503107407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 245301384 1250 245300134 245300161
    0x1c05030703030506120f03030105060a03090c081e070f1203030b041e0c020102090904020f210d120c0e4b030f060115110312070201060801380d0804060206 68
    0x406c1454015825a86070208002c030a500040a4108041d1152070140004040700b0402010307001030405800700d10b01804110402600ca00030040255100e40070030000100c64902040a4641092003c90680494181030f405030444030445904546000d114260003046640074403100320402e40c0c280060341c100701c0e00703d080c0d01548407215400460080400c00502c2e12005254809201610042c42d002d144a0542c21961881107440540d400c00e102050280783e100052054a0081d01c0301006400101c1e1401490520b4007070540f1f0040711021449040140c050380043d175402c4005240b907a10740c000302039442c1e440c85007900c0c80c0041c02928142c0000c0d880d000c80d074195001c0d2520010b02150380380240701250007442130200002d021079000c000440230802e100138480c112000b888000039061101009017110080c0d881410f0780c0e450304806040c4a3302c40c1c03400b80740e4403041101204503010944c5a0a40307290600046542c058410781c001d804104505000d00104c1e40903400760b035029070f00d81c500309416 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 245302634 1250 245301384 245301403
    0x10081b030d09031e0212060405061f0b070209090c0a06050702100c0206030a020a050d1a090f06030a0b1504060e0406050a0204030b0705030702010e070f170106080304051c0503070303050612 83
    0xc04c030212050311144954501440c4800c1d000400c844181041c0420a604096081e0340688a80d040710781004081c0c18842c50202c2c0340b964641200012030b203044110421070042800084c802c0b018100031803800641000f00c460001e80040807114115910700c800b4000d507005d00c40c203c0c05149590b0b078410403240988aa4801d0750380103000d0314519607135140b141d4004c0d840380d2902c40a010707060000f444050164801c1000f0118000c0302400d64410b14810400c1800c0018014110501c0c11b00c10840d281d1408138180d201103074042446461610303200b40844040c0c600303c00e402d0b0801e140610020b8a2501d407541e140c00340b400ba0b9800c10a41d1280d0388041c003079105038000035003451401400b060791a44124015070340094613100000740700c130a00d5001e0b804e094079640643e100300c5e82c075a024818030070040104110414000001c11455190002e2152207001e1485403e21942ca000c0d1608402e004000700f0f10b4440707911805480c0d590350641380107001000159042d034001e0701c0049050401c9400025850310 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 245303884 1250 245302634 245302643
    0x10801050f06130204080111093a02010306030f03020120090307150507060504060e011a130c110616030c0c0201140d0e01151703031005010810081b030d0903 69
    0x716552107a0501c0f050310301c0e50301d80d60001507080000041285080c070a902d0b5410850302c0b031580e140c00e80710421000e068121200344815800501090300c112405081e50342c40002411060030750011400107a009201c268401303031060703140780c0c3c2001c00c05038103510610244410740d1f28941f20035240580ca0110740179010941e030b0564880c2e02c0c140422039040f4507240202d035003450890306d07001c110b9032250291030081d03400311401d079180c81c01003c22603400c0c050f511201021507150854443c40000090501035501c0c1a0b80b07801d41d40e24030310080184111184005054403404a5261303041926041071041d03000ca010324000380c5085000f01e44d46100b06c6064406075016502d19440718041c0b0140001644610010103082d0b80d224401c0304c4c001b0083c0590f0413104001c90001991a160403078058a6913249082407a40c0c0d00b04008005100301c1d110090070a0320020b18000850b50380300340c81c21000007410b07005030426115040414500c003014010100f4850b10130f40540340340301608401a12060000d010081 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 245305134 1250 245303884 245303911
    0x207030f030507110d03030c0e041a04051008030f03040606050a030b161206141008010503150402010338060a02210405060307170114181015020d0801080105 69
    0x31902c82e0001e07000280c000e060640b07002c06440d00240041ca0a8031044011a44800c240390718290401044000550255418480c50300203081035100c0da44601011413186903501d002c1070311400c400c038904000d002d0301c07400c895031a80c6c402c01c499099007049408590031800c00350007007914106684400c045a910041008640d100e40780b9200c49050740e4200c41042165100002c101001c05010b06402000305092681003201440b050110102c0c5403c1070344103004a50004000f640c4000851440c49448e507808413240f501d032480128003803c0703042002c03d42c1800b5100720180116210900c0849004500c0c400300e030303d9210000f03102070ba020300300d0b400e00942c200c4044c030310b4584a411031003001c00383d40040203440c080c0c80c0d100041003a00140c400c01d0000740346800004646c114031100300e01410301610800c010b030003450000788140907000c6902c1501d0700000041081c014000b40d50341e01038440b035081c3c5801d04100d0030000f0365444a500381040054280302c000a2101010310500340901c0803541c0b070b0ba = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 245306384 1250 245305134 245305163
    0x1206050d0f0308130510020a090806130210020c130e010b010c020f0f0f0619110a0b042a090515010306151b0506070801031101030e0a1b080f01050a0c020703 69
    0x2642d1070f4030010414050300c0c083c81c84502c001207003403003440f40304550600016103500360003070010301c0b007200d54024003000d038486424005400c1a0850301c0d403c150f8125090090016140f50490801381010304081e00701801041c00d20000e08a500034000640d5054020080ca04460004407070b40041c100d000394001c00041460f900d1800c000040d001c5419015112a090907a4440429542c1e8480c20030030709440207068500d8030755540400115150b45c20440203200000c01502c4400c05160040c00c001c21a2a514005503a6614034803148880c800701418601c4e002d55071074101e0400f1f82401c4500c00d0719064544100320041d030280c07003231109540d10290303050400c0c0d0707030194240c1d08407040e502031001031021525250001002000340e244218443d03591000c8551541c58001e082268107040c0038185400c201f0604604030b0700003800111103401c0035130b00d0400155038041d141811815049124507000ba5200603607a6001504a14028120040108030b15504800c0481c2c4500c0035000050a0b5020088607 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 245307634 1250 245306384 245306387
    0x1050a0e04050a0e030f03010303090611030d0506040908070c080c0a1d040807050d112a090402120703062408120c032a060c040f030204090f0507061206050d0f03 71
    0x141d48080c001c1c3c0f0026541810101061440d0400350f030242d0100c2d8004014400c00d50701040c1ea030010021800c24a1420700e0003201c0030789030f02a219021401555171000184540d40e00c0e0040c19495030032000055403208107003031081c01e0210340d004060052007220303c0c5d50142d082510003c004c880c40803e00e045c500a10107074140c1e401c140648180c4462200b070003040c0208405101d910340d2400d45440380c02d410080c400c59242031880b01909001100b0b800340a4040040c2180c40d000880e41c01200c00b10880da072144009045003502d0b0949194a01c43c41c0c0010042014503400040c031003105441c1000b018411011410241e075a6002d000459081074460080000441000d4503044d12401e05980c1449480c20700440c8140828504184049405410f500c1100e014411310750840c03442d461700d42c035090510050245041d89840024010b41d650200c943c01d003c004500f04550a81c820282c9000c1c9070385000007030030700708507130441180146040e9000403140b42c809800d25189031311225407007802140d07880 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 245308884 1250 245307634 245307641
    0x304061121090c0414010806010b07201504080c04060906050102250b27030601031113020408061006110a02090c03271b030c0d06021308100c0e01050a0e04 68
    0x1c25090703841103c5164900703070344034000c1030204011030300c40c4050b40d8504180d1354540201130b4081c0d4910f41c810003038140880d1f002c00810100e00007184464000180341400b1800480801078400c00c1400081000b2402000100e907017550307000d049501303014058131b6000c01e0302141c20a00c25a400f69003c1d4800701d40b00e96220a035008240c0202030b00e04001596070f1028000b681c84004816455484451621900d8034030724101e042d100c40c16401800b02d58115699200d085200508480c414001000400340300f400039011540a000348205440076414026030f01d4031104004d02521004c550402c0e60a140700f1000503281020030380082c843c068540b110644050f5640c07002c0c200200c8424440040411b404c00c60322045000b25000e8010b04085a00c1c8441c243c29491400240b032103a00f105c1c03107202d080d0f900e0800e0341381115040000140c1e01c0d0040c0307020f010386900e5a440305609015111452031a0100c0d984488d92440981c3c0301d00340c1c484101d100441c0c80303100e0604c000004c58010603150955081990 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 245310134 1250 245308884 245308891
    0x5010e07050906031b01111b0a0e060907031e0e0f06060d0b01060c030c0209040c031713090b03011506020a0b0a1815020f0f0403110904080703110a0b0406020304061121 74
    0x40503101c4454a1212a00345180d08c44521007410400d66540c1003418a030364040010542456194072504010b0001182c2c48405000704e000c2507203c8040724103c590690791180003120350f0000b0820580380b1180780c4e45030444a40038680034080c40e80000c55508010b140501003d42c0400c4c0101640e0802d00144c400320700d454000e03001c0240c0071014000584400080ca4051401101d8110740207146180c81e010440008191400701c60040c42940c850380403183c000c41c01d4403210240402c40f4088600840d0040c842c6403e000102c242040f00012000d4001c140c41071014010305044002d035486404072426945610b680f43c4540440558000204c1c0050504514003008044058649208101030204680108040c0c074000740000800b0010000c624451400d1307031505403001d0f4030914054481e102180504100502402190307015110f5045003805540071080c0d1090700100142040c0c10082e000750811581181d02d103281c8030794410b421000c2001c0d82c013495051503d226103002286044e40e251100503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 245311384 1250 245310134 245310137
    0x21009050717100b040e030406120906050f04051207020a03030810090218010e090108032d180f0405060603061017070302070b0a271e05010e07050906031b01 69
    0x1c4001051003a07500c085201c1d1218900300410f072054041c000c400031a0124201e9034412441e00ca001d01e01601c0102c280d4003107440604103a41e03d01c4d0724882480250a0258000b8000b80c58581004000d144260710179000c0c501400440e846840c0024010f9264410f125010758803018070101080060700c2100c1d150b034803603100303600c01102c0759440204100303a030000c021031220500340320740070001ea5070722942450040c0320494501c7ca0551500032125220700c200001002c0301e44d140034840c40c440b460760742020420000800d14580d5000300d07864620400406a02682c450100c14100e6491454180074880c001c8400802042c0f951715100c0411200800f40740070002849039041c9440030610000b25800e1040300713a603d015139206500e282c44500c6410003804100c07000e28107401d680005440902c20312142c2c10003800c14440e103480d8107014515080240b544002c85400084420070000103401100c2218102001c0340c4255481e03030100000d880003180c410f50944c3c842c540d650500d09013600ca040b00c0e000d06 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 245312634 1250 245311384 245311393
    0xe0a020714060910051015050f04060305061f08010611010f110702040c050f19091e0302190b0f0703170403081b031303030515060705010501030212010b0102100905 72
    0x55480316030380d10301040c807101c840e0022010480c400c5018800c818111202a40130820792502a0f00c0000d08807041c02440c04600d0341c83c02503540540038408840041c01001941502d8603900c800040c0076000856043c0c0c00b4020441e80b60b448200102103585000c283c5480c0e051582e03003408400c0340c8000e03654542449641d21000c22908408084c4940180c2001d2003000ba03079200c030351380140000c0d6000e0001003020030404000c415070071603220050b01c90701c00840c1d030b0810000500c80c0c000c94096200741c001385580340ca0401005407254600c17071002c0407688261002d0806641d0304425154010f058820301000c1c00040040044480381078004000c0c0c180700342000501c0c40d407a501d0740551414100d17800c402085454050104030340c00d080306003841c40c0a030b481803860362400d65900040c2c0f84001d00c008040c0742d10784011845018000040080020f00900070303035104c41e41820214060f00302032000b41e018102c070544001110506018101c0c8d11001a002426144417402c484401401c40c504141d03240e015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 245313884 1250 245312634 245312647
    0x24081510120302010905120403030206150d060e01050a0e03090f01050c0a0618050118030f030507110d050d150e04020d0f120c02030c101d01030f0e030705100608070e0a02 75
    0x51101e40184a009a00018100030f007885c0c1117290022001500c08024024802000025400550351b0703400f034840714108002040c00d00102d41c42c10714020008050700d0508111180d41501540141e02c40c075102d6005104652b6400b0031300d500d920441140c1c3d0342003a1035050b00a0154050001007840036804400c40300100340d0754403010308941f02d03980c41c4024044c5c080b1b194000e1100074000c6400041c41e52070607552024869601501041d0074030b10f0301050544401c00903038110f0041c04803400d0910340d182a9010700c1c02c2e00380300808036881107485640b1940f819920544802c5184040b1003036172220007241100c0e407100d070208220486610403c885008607100101c0000d003406038080c03420402500c50f103e420240b48101414841c00311202c40c0107000d2400e000500550020340728618095803120310300103040d8000100c01801c1c0700e080c1ca89016080c001c00342d070403039070000080180c0380c00b82007500d0038409141d03510020340d90399100700306103503110210921014002241c4150408443c0e040180b0b0502c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 245315134 1250 245313884 245313899
    0xf0609090c070b0a02090a03020f0d0c0b040f0e090c0d05030c0109030306030209061c030f1803120f050a0c15060314070f08010216061505031024081510 67
    0x100c04403103001c10340a002c642482041404403099402140e104829420300c030500b40400d40c003540a200c06841100c408400c0c0d445d81c0c94084520140f16048606030b2041c075100c02002c3e1807903000c0d10030b02d1000d03c508240041d010000c2c0200740c1c0694009405031001c405a4070804c11506002c410070f40340350000300012180c13101d0912410305036500c6502c001c40c0311440c5004000403100e0042c000c5024000703801c0311030020b01400c07020007100c81d858201010b18005500c011914070102e0001c291f4030112040e400b2040c042080401c00e4884000e903900a00e80401d01c5040b1034a008240c10340c00070494084000002135102014950842801e017000940c0503500d46a95420320358403140b402c3d05420120050080d4115410030902800640c00203500d8290000a0701c2e020a044070009000950f0340c1032140c2000b5886681903008100040444041041054004000304035040000c1c074041003520750811000d00351820f0208071400c40010309104540c0c41c440103528400203080100e9544c0200b000318030700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 245316384 1250 245315134 245315149
    0xb031527010e1903020a150e030f0310090e0304062a1104050901021e0d06091e06080a080711010309140708010f09170f0f040e06030c010311090f0609 66
    0x3a00e00d0001c24000748101c052401e0400021080351070211000168000c42d03000030b141060654030194101c814546040322200805824011005900002602c403503800141c80c061801942041854000c440c0c0c0d8020240484d00a24180c4425400c14402003110034050305c2e503180081002e140a140c02010340f50108281201c1000031240c0100c0f12503800300500305845456881024003008519044a0000b41146c00d140c0e00080d05402c900042c0c10051040c441e00f001004084001c0c081c03000000c09001c00c0d0624044a140313000355840e0050020340100b000528410050b0000b00d21490700c1d00300d45403110042044555a4145074807006160000303003000b6a018544035818002e000e00d00c0c141480e039800d65810030b840300e05007420802d1001c04118004100445c07000295100743d922547c1c12008145401202c2140e00e503c2001f0500007205880c0000940c802c40d001c074280d8684020890040d0220ba130146201c5013111024401c208490030000700107080f154004007a1030828010700c0005104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 245317634 1250 245316384 245316451
    0x60d0213121a070917010b0604063507050d1d01050a0b06040302100302070c0915030210021902040b120a0809090705160809130504031706040b0315 65
    0x440a80341c68003414090b01e440c01003100080d203002c0d0401400c04002c0180310f00703040d000c0c2c8006190329205244500ea000d62000500d40303805041c880d1215605c80019284402a815183c64a5804c20302c5a8400314298400516480a04a8820162a001c10443e030540010006161482e680c40c0b00c2031031403482d014104c0a1290120005c10f136460891640d00544407901080750007003a06000500040e982c50310090a8614107207001a2603000038100382142c140e443d84114042031400c01c0e5907181d92400c101000c2034a00079159015000303d812001c1780d4408074414002284542c080c00301c00103103841c0d004032503002d90040c42d40700e006090b44500b50404d461240e048448420005404da00ca0412440950780184c3c1b60034003d007040d4013444458484c8920788002401e1540010b90b40440c0d69590440300c2064a2000d01003110b843c151a000d00b200700c80580c00340c1c200e01041c000030020b01d410301070403805110150280c600d81c000401c1a4030b201401419940c212507084c0910080f18024001d0000d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 245318884 1250 245317634 245317649
    0x240b031b0307060e01050d02130f0305070302010806090408070f030203300106110a060c020102070f05030c010b0405011a0d02090301150f05090f0c0724060f090911060d0213 76
    0x11600400e020140340c0348403607102605000640c800c900316070380c2210548203040c511150140c2e6031601201c0d901d903100c210b03410070b1804007105840481880000100e51042e0b80c07003a280c240c2c0c5910f400040150508084030010700c003034420000d19000450280f44001006c0c402e00481e03082948078500d00301e266248202152140340f0302c145803441400e003203440038014000750800351402c010300c10905031144140700029100e241c03a210211081d41c804d5049804050f0001a2403ca4140e43d2030556140d5000c000480510b43c2011008413052401d80b01d810b0407643e0b42038480e000c441c100c03e40085c294000f501c0007240d1560070b01002205440a008417100c032206100703085070841c03c0c220333650b0164415400c29401074176150104030350b07020310364400c0f500316007203031007054940302d581c0740c6581180c0300b82c1d452804011104003d0b00400e40d00b50401020340da000c0000c21f8100e9120f0840800301c0d0034131100030b00000b5904545c9001ba09248000f80003000b00014054034207000240e000100394802e600002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 245320134 1250 245318884 245318923
    0xa02090a060e041b03090b01120203060f0907080304060906020c031b1207090e0a0b13080d090206090301060306021306170c030402180c18330705010e010207020a0503030403240b03 79
    0x1f00007200d0019805812a102160900e000d82d4001c6561000010302d40f50850a6010105940f0a0100206ca000b031128008895403607445030401095641180324a20141c414641c001c1c07064030700460030b07070130ba8001440c14690541c52041040a0880030742c214103001e0050002c08a03030091280251020110500d00510a11081c4d241c400c00b5900003c14162000000480c00b400082c1480c08454801b0301c140000700308158a40000b5200f40b040f080055819844d0010000030400641c0242800710081d520b203038856030351550103840d0005c2e05240101e0b110500700c000b40d101c0d098031b00070319000f6001404a0380f4401e04030711108246201500c406060403004216410300c010300c80800000002c06482c1f4580350241280350708503003400180c0180140d09076041444814040c1800c0d40d82c0340c0d800800a00c410100451040d000350b00c14141640500103a1201088a0030000200d03411a58000c1c02c1c00d00c00c060410800b1040050340100075078903622140961615942081051035a00d802d80075070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 245321384 1250 245320134 245320151
    0xb070c030215070c05090c0d02161407030812090c0604030507080c0a0815061c03091e06080118090807052407050d0e0c031606080a02090a060e041b03 66
    0x8901c0072002d50b1200c1d541c550400548001655113043c680031034005641c005084d03204c1015910460151082e13140f8900d10105401c210300e101c1900510b1207601a01610a40e5142c102c2c0c803030b45800c4a8003000c1d0656804108501c0c285c00d000141039030010b4903806658501c0b01030000116144c1c02544141d0320307540082d03000c2c0006501031040c0700c03070301201702c503850703c91494040d040d500c1d4581c64410040a100381c0000601a0702d80311b01c0030541d108002c600300b250350864600948042e50a026140d00d07925406191902c2d07455450541c01511019120381c0c1a0303a10f008000c1c10701c01c20110080c04425298503a0000240322840070b0000c0e180b0480c0580b24100802101038110030411214031540c2c420b48051099680e005021500c0400750414086290100e240d203071444d02031407200030342e00b622440309410195404590523006031502030303461200540ba01c0e48120268002c0254171640b200740324a007082254041d140d101c070301c204040c102143c2075001003414002c0c0a41102c00e400469100c6104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 245322634 1250 245321384 245321389
    0x91707060e06010612180813170d02030306090403050408030301030c0608150609010c0204060506030702070810050702190221100c03050f040215040e0a021b1f11040b070c0302 77
    0x898111008000003848070f50703d0040024035145103865410f82c0c0c5595544880c00b0745d445002e6401107190442c40c240d564014980603003004001c1d0744102010904454031303078402240301041e0750410343e40f1603009604685411003004410303000034208038140078003003000140611050018500840c080c0113600c0c5610b2620601400340440104070076503c0030541203122566441000f40c0c0c000752001c0c41c0000c2410f1301ea00c0490300030301c155041603601c0080030040040c000c3c0d00203500d0040d107825a0681b00504101f01400c0282c450030786000d030160f08070b1700904d0b0482804900f0f5588050009101d41d0b107525035038102000840e80858004505e821481c55640d8254441c011401008a40c1c50208560b00d002c2445d10004c010180c802889890f8800e4213071a50b0504000391805024070b08118081c80c144040c0740002948040d9010038060741130000c51040d941e0105032080310001c203c1462941520740c0c22648000c00c9207410303002c40350b42c040c40003291460340100034010030f500c50140c048406045004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 245323741 1107 245322634 245322641
    0xc0c0a200402070602040302031e0303010501030c1b050c0a060903080d0e1203010801050a2306090403020f0a110933010207090f09200d020f0409170706 67
    0x49000500004d0707030007032003200d201b10211183c2c0e840729811520390a030503000072050790b0401d1004000c0ba5000b5000042110f1061420f0085000072087d14682e02c10300100541d00c5030701c090f40440d02400c01c00f10321005050301c2d0070f0980d6070515550f1290311707503c00c04405100540d241d2200e100110780c10084510040b00240358180c0703d40c1c5652000c1d0090104480c4116024107008844917041c0000441038600f0504000d01c0140d40c0c2d504e8144000391070301500450847c4641c6841500d420024800700c06031074410200130b59948501c00c100060080060f011b074070303641d003d070040d003c42041c1c1c0b1500035940c5181c0f01c505405002c0000060382000c10310b50200d1030103410046900501502644980c010714031602c8810160220380c20321100040e0045070321500300c0d007048840c5000d803404101441ca42c00c0024004128503030f03d6651690550f10b082050b03000791002144200c1088014003 = true := by decide +kernel

theorem cover : BRFrame.Cov 245143884 245323741 := by
  have h0 := BRFrame.cov_init 245143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 245143884 ≤ n) (h2 : n < 245323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
