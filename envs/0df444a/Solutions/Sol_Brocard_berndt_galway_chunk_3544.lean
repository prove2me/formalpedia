-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3544
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:58:19.276306+00:00
-- url     : https://prove2.me/submissions/4aec45a1-9f67-4a64-9558-e33b15749da5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 637230215 ≤ n < 637410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 637231465 1250 637230215 637230257
    0x3050415110a02062109011b052704090206160201180617060d1406010f0e01080309040b0a0b04030c180b03030a180b0c010c020106090b030307020d0623090f0607 71
    0x401800300c07100c0c0c00010307a40000c101d4188212150140c0365903a007924180b1a54614411528402303614045041c29022024456100c01c8000c0411080340c41445002c4642c030303030360001286142c009010603110303400e050b4040c00c000d141803800c90008000c525081210125107094100707541c841d03615541c030110a00382c8005108400f800042d840126105c0100005036281c9004520f810080048c020741c0d45000f0000e1380c46002608101240c2c00344000500c418080041519180d40b81164003140c6480405c010821441d0140c11060f001d140c005004400d004013400400d0445204d42001840c02b1000004102100d03000c0850907810782040100c91030180c0319003503210148810284186400303030f88007400c1865174051030480210341d4541103000b841e690280315040c02410740340020f00c40840001c001940724440c204000384079200403c151400e010f081d5014280003d4203040c036a032207540380c040070500700e00100c0e02e40080d803003101071644111902040d003d02545043d140c081588041e04404005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 637232715 1250 637231465 637231477
    0x1808031909050a050f01020301120b1003050601090605120f0c1509040c0c0b07080108030f0c0c030a1109012117120c090102070e0610141603050415110a0206 69
    0x1100300403203a02000380c8480c424208160300c200300030040b8000e5441c01074105820055148020b0f441400100a5003050704183d0041503030040141981d982c4050740000408090b800c05032281c4150000421503c00c00e038024019200100d4400b0180c1030710401a035500c0000c040b80503001c1c1c1000000710342c24240070188141c0c0300c80c0404042d0500d02c9090200b0112030030510036000040203d6203c5050080c0303c0c18542d041070785450071600560421a23595541e10525901400209002840140000302400740c101000e80c010290740b25001141450003000072009800c61007060a0000090b10501c1d00e22041102e10702880d17018040b261030740340d100300410984854003048404000110a00c0d40703010f241d9118081c82c1d0040c548030240c1381c000a15048880c0c00140b070f00c1c0e19000600c02d19954500b58001d5142680c41e11044003130250490b01014008d102c899032148100c65032000c10990004058825070344441c0b51509801801ca400301d03501c41c8800b448490640000b42c000d005030400c40d0040c44 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 637233965 1250 637232715 637232731
    0x90509190c0b0a08070809030304051b0d02281d0604021e0a080a050702010b03120307110609060a0f0b0d32010615050903060a0c0c0609120801050301180803 69
    0x1410703640e00842c141c2d80e1001c501e50000800c020100400305030401d1401e5001500c0000660442c58607a03525680c9040010300c50205404020582c9031a5490500c40701c41a50b0181511003811201c0801e5186003164143d80400003880403c00308054010f80812001100c01c0341c884003541e201c0c54207000080d4451684403001510448400c20303940c0440d0001c1039806015900c01490b40740000307091080b0f550240858045906206901101c0d0f0740000e80610b075070b0b100c2e40010f980c03034460b00c0c015140704030309800b01b004500621007000029440450f00610a802d004809d00c5001d0036001c0d6101194001811244c0c041d00151182c0081850a0b40e4480c03804415400900c1c0c07c608907207840c0c0120b0403c01038009582d120a4244081c188014003000020311908100707081280300c1c40004d0311801c0c000d03c214611582c4107541050540b0681900c04d905d80c0054080080e00201d082c80c0441d4001d610365440031403844c00000407981014400d8645a09038030380d0402007110582d8800d00c05a00141c5103c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 637235215 1250 637233965 637233983
    0x10e041d010506131b2318030f0708070b160203010c110609070e2811070c05041103041b1d04030e0d030906030b04060f060206060a06030212010308070201030e010e1609050919 77
    0x980328003120010011542d200740321f498500c10101c105850101c802d2200d11254000318010004618009862015942c480c241a5215041030380c94502070040c1d924007035859801c00a008a505400c1070000602800c40c0c001d440c5a940e40095850b0f541c0e10b14440c0683c504403520025044182c1403020b03030850f036107410001d840d64900e4400340080e52040010a1514030000541004106a03503585034000d140c01d85080c00340d0b032005000340c2c010f400010005800b82081e004421720b4041c2000c20b26000d0100c0741030403124032043c0300350021513090858040300859112080883c452030103414882900385d140d540e0101c441e040c00412005000b041651f0754005450320340c08a51460001306040181005a004100c1ca00d0904104048a40f030f80c0c1c00001403502c10052412185030880110381900d0b005a1700c143e6030070407440100c3c001c065104203072146500c0d02c21442e540110110f034040c0101001c400354001c56490701c0c0d49004481c0c00b43c4401c01d20360b000c103041c000c000c0d490704002c6036032a000705014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 637236465 1250 637235215 637235267
    0x103f020609030115051008060609150d090f060f140a0c1b0b04170c1002030c0706022206261f03060b04050c0703020c010e041d010506131b 61
    0x803d0035900f0800360b030303200c0d40500d800c20b101c2c0f81415401500f030020a841c00c401181010800301c0e04a20a201c4424000d01000007200522022881140c010148070304c010402034a0501303010084940d0032208840ca5030030301c1c02c0c41041e0081070246070400004220048219115180280c009108425044040c440310f90004868600341001d0300c11500c1c004c168201e010300c2c0c03600e002000e4406050000010340c20134408158000000106a40300c2c00348041c00613580c0c6c9410303142c50441c2c0505000102024000543c0010120036171241d980031450b01ea480040b590b45800b030075074604c050b8103c900e461a81c1e041507402d0300c02c502400c40b40c01040018a82e101d65035102e1003191030f04059007050383c0140e16050300740302d00d007824858a83d120300c2078500d4908119095034003c3d1070f100f141c600181044028600012581d480f0781c030405c02a000d036044a08841d2903002c03254003130301d07080b40d11038422105180e4100005c0c2c03031406040280d40d008459400d00c0401e40c2001c0d55404000c02800402000345800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 637237715 1250 637236465 637236469
    0x150f16050726060108010c1e0201110307031505031f1503080307050c1903050406030c111f0b060c0d0503070210090b041209030b0c0c010f05103f020609 67
    0x28a4104070000c600586590b140c281c509482d0010603400807416a15140101c803e807503111105111591a41c520404000543c9500300c0c0507100c503a00d40003070000d0000c244a11143c160b03101e01147c288440c540b40200d03070f481e42010b44424601c210200c5201ca01001031544901c0c40c0c1c041410301450011202c1101c0e200d88540a480d00300315a0f19000c60f0300002c11000e500c204000c0c0c0d011390005070718042d180d54110740d0004c00d80e010b0f500c5103c0070715031540b98950180e07000342e00450b9a814072400316107082d4000340c04d003101440c481001c3e41c802480c200c0018490b00300803040351a052442d90084c0868032460000701d4140c0c1c4010b0103541107006458407080e540201d4014104a54003807144541642818100401d030700b958030030880d00b404404003040000819525020f40c0c451103110296032252007040405000d030014080c482c01203450b20f400c100079090660142e034244e90b4542d4101440890800d003180307903680b20390301514640705031210030b002034288004681e110320300c00760080e403e00303030f440300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 637238965 1250 637237715 637237739
    0x1d0607210c0c0804030303060f080a030516032601060908070b040b0306210607030b010302071a1b220f0f0302060a03020403080a1d01030b0901030f06021903020702150f160507 77
    0xc06c82c002500ca440400104058881d003202401e8103201800c21034119590140061150182105c22895161010024140101d482c0145031140300861355980c1c203032039840419034100b402054081210380d0310128240c80d000070a8003da9290181280c545070400201e0300349604010242035021503a0301c459000306010b14450b01d2250f0f00300740146040d0501c07080241c250b8500c86442d5040520500600300420403582004020801500410781c140c1c860344149104204541480c61411100207680c42c205618010285003c2c52141032080c501e40d02c900000070450b00d140b003440b200440c988002e20141c603108000b001041c03501d0400601c0c19540ea0380f103592a0704a6010030000c18030429070001131881c900001c00207035500342b8081025408140c001009141c040c000030b0f10180300030014034100405c5a04440082001c40f1000d844484c105400030003950040301c08130301886070407240d8107a58040c401910101d1181c450100c3c00c1008908000c009100108026215032140040024007008004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 637240215 1250 637238965 637238969
    0x60f0b030f0109152a0905030307140c01140708030702160b0d0b010e150708130e040c090c080610021f15050f01020a02010807050d1d0607210c0c0804 66
    0x10000c1070107909030510f440540c0c540704181a241d4206200e030f10141300c404141505c01100203800b22441210100100e400410035045190140700c0020428140941c0c40c1c8076854400343c0808860508070b50200445a0202c4200d4010a5400520544000603540c4010310341c441c901d84102c2c2e40d4524480b250303001401540c1d201015503400011140b440c40703100c0c0200c01d1809800e08201d0301c40740c1a040443c4041d103651a0407103840b10042815800c2110000c12141541c82031888a10400c6d103418421844440907981240d034055400c1000494100d9402080c2c03055059442e110820350350309052055000708ac001000450040c1041c0c100480c150284e50401105035410024455100c1c45850f80d8804a94001611130348130032428216a80e070008100e841998280f9103000c40b6156980281e5840c001c9442c00f010306400c1c4024078190201415840e4071041c442c0b400c0380c07215264042c00f40e4034005d0f507141c00c04803201307405840320511500b5003000c1085134003450701c804c4006058860b000190000d07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 637241465 1250 637240215 637240243
    0x120030d0603050618030d0906090804090501080f0c030303060f030a060501031101030b0105090a090b061b0a060b0607210903080c06060a0f080d080402060408060a0c1d030a060f0b03 80
    0x70303281c107205218040003d070340d00c44800b5100a80c04442001055564001c00c882c5803252511503091100f00465608401c002e00d030700901305612140c0794810300b000390409026041051141580d40e5040b04800106400743c2032014000e5072450321000305005034031420b882e00542500c078140003a40011100d100d0b0a000f14021448804040346101c001001d552a40060604101c0203111501d020b5450280c01d000310764030b00c41d00044242e00240814442e015040f6484071115003c0c41c3c8103080c01d00481d0203001103105087c1040b0303420b0300c8400c02400740545200508a0004074414580407010b04030560051084c3e81410038443ea605d41c0c4601242d840310821410540044050041906003400710702c015010307020414940c40e0803c05503950301d0b0701c0080307000308206030700d0007181c00d544486048034041d0040c90180c80e6a4a090403010010b000300302001400a040e2512307140300b174610481c1d041d1189200074081c0c5401850350716010301803e0403103800c001c1150b880030301031150350701040321741c2030702c052 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 637242715 1250 637241465 637241471
    0x10501030309140a090c1b060203040b0f15150d090c050307060c08270d08030601110712030305040c260708070510111005010f05030c0a0b090120030d 66
    0x11441c00401c6690300e50f01805455054809010b116510204040140c6020000024481c01040800c84032060700d1060012a0407035032011005100c06500110f2040780142201e0440340c454080c0c8617641d06d0102e621116220505c100e003400ca29110041d05c21201c001d0702c0c03840c00c3c403100400000c00c031410f4010440300d51507404c50800c19410306004d6140101305c50709150f0882c100c5a15501800d02c58600c6000f140255182d00c23410644000c00308094004004c0c003c2c9000640900d03100c40c8540c405c0e280240452041003150481040003d00081604c1c001c010106440e40165400d0b8040c003c09041120f0180c4c002c0e5001c03e01e40c5800b944101c245068080c400034440105044a0600b41c041d0800501c5070007070381d8140019154400401040c00c0389291000c80706c0b44210419041200d1160300c2807186050200004100490a400009450f0103c058a54604a61040107101c00540c4286510b44a052010ba01c994dc0200c495408120204d4912031080808c4a412407c540c030007907807424406d070703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 637243965 1250 637242715 637242719
    0x260a02040f0504090203070519030602031017120a030f06031a1905040c140117070e0a0b03010f09020c120307080403081f15030b030a0f03030506100507080304060e06040302010501 79
    0x156001d100c000781000d5a04001400e45900402c0d1203d45a00869000b20310109600101c100c0b09a0800d00964025408646a08010003a8009010b6a12a078130800e0340e100101c0403d1040414088002032524400914010036a03805402606085010400e21540c0d07103000004100c0e00400c2c0ea184000300c50760903a0b01d10344150001036038221441d078149010303d48030401001400d91103440c0c05652200c2030b440000c5040e40c004072021144880b03500440480101400340a5400103007a000b105801c560180c0c042d6110350401c070683c0400d101e04070603080f10107010003440342d6960040404c90305140c02da9403198000c00100090f40d1013a03038448000b4200c0c00820061580c44281c654100c010818108115070340d56400d10f001c0901c6c0c0c000c1c500c0070340f003842981038454001d82c03000405880260940d00891071030308010b40b5030800d2010076400f29040000140b12803618150040003560b46403905420800c09885840450f0402442164000c2d42c641460001c60410400c441c402c42c1300340d0005ca0658 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 637245215 1250 637243965 637243979
    0xa03032109110a060c0f02060f0f07140d050c070e0c120103080a08010b0412022209030503040b0705042d030b040f110405191a060a05130b0712260a0204 67
    0x94120742c000c0c000c02c03035405c541d03000080d01c800b40380500940446019840791007003010f00c42c40d03103d9000c3c14009844009019420441d14680881384000050b060b03038051046000240d03040e206200c0988110381200c201448071200d80720101c1d40045c0111103842c1080030071010340b01c0e991000e03041030720101c50103d8603000c05544900c039540544a0301070218240351600c03a00504404502e40000c4c0305005554080018030803102c0040785112904c10144400c250504001d0429481640c05131104003669001a24035070040d030031241100e1000504011010202074069401c1112202200f403c0707030000c2e8000b0101d007401031100e020318000c440348031001d40300745030610050080c0502213000701d00b0442000031785801c3d8241c0140b00700310214041103201d4408035200f101c11075070905e83d910003004a180c032800d0390311602170507820303c40d0b4003c6034141e82c481c0b0114100e8024000002e040b0385030091618251481420036880d003552807070705003e4046140100c1c080400c0d00305c5901d18484d43c0032070100894 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 637246465 1250 637245215 637245229
    0x80307080a0c0906120c1103191b02010c0b1306060923071d0a1a21010f1203051215010e18010302061c1107030305150a0303210911 58
    0x503000d43c18100c440524210014045204030768046031160390f9103060264641c020340c12900400b5004043da40e60301031464406079003040c2544680b0000c2e11220641400a00303000c0e00d00380854058403281003198296565402d840401468521480500640100000c0395405224042c0c49000004988030303c01d044042d000f94555240e8001c2d010b40c2400303022005400440120180b005c0103002c0d2460201c4102007489145a68070402c41c40f81c10b00290700004240301c0113000d00d07500950b8903455920403081203134240308081c010003c0722000340300104440100b02030380d20701c61442410000d0400740091603400d2400b80031188010034aa804540c4009903070310004622050707204130750505002c154518010340322030050200a014030f000003511985003034480210141080c80d004280641c3c5920200310340030b50802c20088011904180114203140007c084121000034041c1c06005a030b442d584084607c1c0441c1960b011021041200d0040c643c140c83c01000240342c0501c0042e40605191006d10041e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 637247715 1250 637246465 637246481
    0x2070302281101080f0c0a020a0209010f0512120901051809090a060615050913090b070c061a3f0a0506071103070b0c09061602011205061318080307080a 67
    0x4012913541000b4101c4682407003280c0000125030520b49811480000380e00d0700a26110107940108514000182c0d0103010441c00d00340d0b8000d40d1503252102c0031039906551480c0c0b8410680001d8024440c0e248954820030142030300e004c02c01c1da901a144404c238049602020b080c0c89100e521f402203000f14080c0b011a00031480108488050303060304069800d0014468001c1c407a0052040025240300390f0b480450b50404032803140c0041400c0d0300d0f4100b221008d842010061401c031807580c240780c24140400080a0214082d0901905501c03c00d1000341d0311250110901810080c07030f1868001060050109000d078400c0414100010301c0b400c0d4482c1030103850102c0040c8600101b00ca00000700e03000400100545072059800385162496490b03034401c00303009008204640d40c100801180e030030304007031208200b911194002c0c1c03101c8400302c1d00c4440100c2920304c1118041d0700310300719542e040d48582541c0d03c0140002040304000d031003c81d103a61034400960060b0355841c001401c2500340001d01d035040c405c41e15 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 637248965 1250 637247715 637247717
    0x4080d030c09141306171c02120a0c0507030804080a0b0604090c0506030a290909010b1c0302011e0504020111030901080a050a18030201020307030606090305030d02070302281101 78
    0x1030081e10700464070392001d0b104651203010311070309404103006802d60703000344004d0006c03202001d14081c841e580e03007030303680b40e083d00d2800c0c1c207050080081c03500d01e0000c6142e00305010103203402458203007540400c1c2c5406d07080690449042c411482d000003c10b0282c4040c06c003a05801010f09076500c281d080442d581d010140001d486031b842c000151002512580080d011244103682c40340d00d96880403000b000400089000c900d01224094588502d5940c1d92500c60300420112541c0907270f521821815801c8403815003030940c10646103003c03580141040c014203011075102c0c1c4001b04414401206070102e00c05502140f8000d02c0d00c5400707000c11581c109840000c07040045008504181c50400003c010000103040208415540c20100c0c0c4020855044a1a44070242c0f03009481c42c2e0440c90028001d50044515034000ba02d403c1000c0760040c4500c1c40c5c4030859800c200218102054040000700035071007460105e040d482942281c0101d141c40c00c14052020065807924101c454890030031010101c140d03c0c60b58 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 637250215 1250 637248965 637248977
    0x2304111201150e0934081f1d0709020d050c03400c1e0609140105090a0e010612020c060703051005030f01061a041d1b04080d030c 57
    0x504450284030802280c11100203601144c0340e02d451141445007045850390741e50421142c02c1d11700100300901034020600e00d04003a80e01303580c030980d460300e90140c1e00062500c8095040004502c5809810007440c201d00c03500c0f40d00c0d4000d640c070941c500c0d104066200c0101150080380c4c84141c43d40a20803140e1148a502c0c81610b075242424403900f01072401450014030440d00c90400e031a14203000308840011109181710b21804016042c6098100030030b11580e0101d010310070070859601c006803aa0b81c2220101d0300c80e0003c840c204040d50b0b02200045c001141003202c00e1055070296038480303290030002d00c81740e03080180650604800810140418025480c0c2d01c0c010880703101c200e8000907c9031360241080c5400151601c40450f82c0c4a10001c81e40111360512416002c00520141035110604655840a2816007e040c510b0b02100d540124070a0913140824401481c00d04454100850f5010300c03101e10350f00e03000380301d038400144541058000400342c0e40800f0040701d0083c0c01d07120350891a220307410f00c0c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 637251465 1250 637250215 637250231
    0x216050607030503070c05010b040608030c06100b0901050f0c030403121101050402090c090307080f1005010e070903170403020d0602091e2b0501020c0a0b0109140a2304111201 77
    0x24009110142c035581c20800c00200e843e05211f000e5100c2511004010024461a669a000d9a9494124486041c407500903100072461046044046c41c08840d1000c03105810a881d24006480316046a580904034840c104000c04402101384018070145119500c4e1a03c2c0c80e4110400804100500d04c0c29100d583c905020311003d65502c2c041c07180c0c4181c40345505955040c41d000070074100400c0d0350046a00d40f107082004c0410100118400501184030403040066a90780d0000c00e80b5007800740ca031080401c107041020700200d640d102140b28016040781d1091301c2d091b0340e030b804200c60341c2500200343c411176404528a415841c1c41c50030702880514489205c030540c8001400a45001c06009010601c010104400c40c404c42c44080600882078100c00215160391602100d151541c4100108030740d8041e1420020601800c40d20a40f0204c40081c01507071201d98070380184a0007408481c1a04900d41d54008107815660b01c9580520312072841a0030180f44d41200130f09001c100840003e0b514040d904080035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 637252715 1250 637251465 637251467
    0x30b19050c27090703021c02040509060f0d0803040302010218040516120b040203010801060e010b03160c1707050f060a02040803030c1305120c030d0806011b03030f020406021605060703 81
    0x9541c0e41e1003000c240c6002d0380c070548401c1110300c0b008650180c1c0159100c41081034681d05030f409021400b00507182c0c2201c490442585404900c81c40c050700350301480b03100106403070b42052030001d064514041d1034100c10b41c2407512000d8445d0000c441c00c500503900001c41a4415425201c66101500203490901c080c1c2442c080c4201c0b0b41a0703403d01d580400495111904041040303410070350000300040c104540d6541c5803500c4d60302a1180d03000d51003058141500010302c0340b840da411244918074102e000440e0440e01d50045803c0c001541c820742d00c0b2001e40307088403441d1900c00700400700c40348500010008015001c400c035080110003003c0c2e031724051042c402001968804412264001d5144000c00ea4034040130030103541d0010190041c80e0400200c904050300c010700003611121141c0c0450442d800001c1002088440351401c5031524006881c0d4035000e0699440402403450b0180f084c02d010880702e120035843d4040381c00c00d500000041e4040c480250415115051030b5003d0003068560f94a0400355440c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 637253965 1250 637252715 637252717
    0x80105100804060612060b030c03151b040506030a021809090a0303020d0e03040b0c011812080403210c080906310510090209090a03020715090906030b19050c 69
    0x248401e0200680001d03003044000c0d030048014000841c080c1c9140c0005040180082ca18010b40c2406480349203480007040c0740c0000c2051503665071081e19001a510803c0c00902c59045900308039070a28244800b141a588100146101d120a98001a00c8000400100a000340e60300c40c514090f046103010300207184000308203c0100b5825040150350346120718034180040c2203c01d85010756010104000c03038030518060042c0401d007840c4000b4004061020480c00410002a0000f010300c00b201c2c41d000e54013409094034a60190103801c0217005030810680c1120840c6504c4001c090459035030100154507500b00da241608044440000e180c545404500300703602c0c5c03480e062507006804035222000c4611540c00d142c40c68965020059540245808058401802a158040703101c1d072180000035841c280d000030042095500f43d8020300c1b209140207103c1081000001042007080858040402d000a00c0d0040e030000750320480080902c2e1030b01022081800fa2495545501d140c1080b040c000d00c1200d02c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 637255215 1250 637253965 637253989
    0x90201121d03120711010507051b0a021513080309030a0b04080d0204030506100602011803030c14160506100602060f180d0c050d0207120609050316080d0b01080105 72
    0x6000904080d5506009a459801001006141c4000101000f01c1da948402a6004121030703116803801d01d03004a03109090704c0d400c903400400034034140302c08400500d200100400c00e105003001c0d00e581a040d41c01245421038180c0f0f0030324110100203445490b0708250b42c0c014000300030140145080803080c4001a45980300f5450103071243c44580e01207428002400c0407107140101a59046644541c0c1c3e05c2c2c41500c820049905000b2041c81e00c000140d07403801030140b0200c4032450301043c0e02c2100d455606500912a290301c0b0003c00610900054031507402c20300030712502e45035604591044c0c1c59031500904d000c0000f004a401c0001d02c0303c0400039290006003460300500300135800d0740244d0710705004c9a4010b1804580a01a11484403113403445031304003240101240c007a0307083e41d000e00c1149200f0b907070340d869074407600c40103110901201004c504146d01c100072040c410410303030345480c0c002020644101c0c0c4444098526550005103070000d030a4a11801c0c0c5c59407001c2c00c04001c3c1d58545070000f54268049 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 637256465 1250 637255215 637255247
    0x1012020f060c0f0c010f09030b0a200406120c0306081e0102070b0103121106190e030c03040e010e0109090312020c071730030118060b070b090c0103090201 68
    0x4040140d503654511040e41d00070004001211901803030440792561300c20380002200c2c00b0554040f2040c0303600c4d11030040c1800b0b0300c1d0058101343c06500c58501c00001440116200814201c5c609200c1c6e9941c04004002c00050460340e1312502560a186005002c03282e071403606c001450325045007040750210101d01503010441c0e80c000300e00f207030004503042406403040e1600100810b5809002204001c40d4a001364001e50082ea0f60511440010403900c3d41c2d524150741281d02081d90811154040c242c54102107015800f030740940b03040a0f20880c5891668009410440c0c94910840040c4500f100603049030b40113120008003407012030a287c6000d01019210b00760000001d80016004141840420014005098040ca05400300700c088100546408005810080820b1180c0e148095952080350840044882c2d5015924507480c0c075520800d150900c03041c051045882c0c8100064644091000e04580c2c1e016980314070302c5240c1200d420b4100302600c0c00190500d4507090651300540d0340314121301504048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 637257715 1250 637256465 637256479
    0x606060403051c09410a14010215011d1b03011a0702090c0405011821022b11102a061811030d1e031d07030b101202 51
    0x1c00541266024256046150301c5103c03031a00600ca206901503220000401028600c041000390741d4045c500442140a03d41c4001040c0d0240302548050007880c1c003041050045503d600c20407041e504a0079400d034068132032620016405454008200d5599038001506082100e010400a000c44140e00060094145d0451100c0011040b000300100b1034654640044c0300070100c2c6840c000c48441940700d0700985002480e00d05000038801800a100c0c0e06a4101941400d2001c21403032140c02144070080c030a076405840c2c0700181800d603001c034a00f003030340070483d01c002c41c21800d1030b003000307454a042e5070903880c041c008596909540c90361002d07410076000f8041d0700c40d4810307001264a1002d81030f4480d01c0941200d2500c0709141c0c2c486200411034064503c110b807840300e80d2030307104209a12210700182c0745010076240340305885096441038500305013134042d0400050a41400c40f40c801d032058480222201540401424400e00c141c4404141e4450f02c0007001f06485410020702031051410b0440c02805240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 637258965 1250 637257715 637257763
    0xc0803071b050604031d03100c1404090608070509010602030a110c030d08061305190c02030d05040b040b1b04030233030a05010f14010804170a05070302060606040305 73
    0x1209104240d004800c900088410281038200203840750703400e070303022404290030949011001c1246c2410110006001300640440c01410019030094400d0341151f1041001d0460740628072094000600040c00720780b24002051800c110302c2c40d1405203176400c03c82c4180c0007200108002035000040351880344091424100b517891400c44580f40034441e41d034040c0c4c1030003418055903515a000d00001c0c49074604503016040c00c0c2102010000301d82007a2041c0310501420112020750882c1500440c03484001441200c2c50908640d540d03038200c40c029a0111904100d042c2403105205620880c1c54004c4510034040250424a444000091103203200c020f002e45007001000c3c0302c6042104a40448180c440301c400640101c2c0f401a4400c1e80c011500440c10910f0200003141c0a0003d030100815240c4041d11f051200c200b0b4401541c012030000d0044a0f1a1406460030345541c1c101c2010b80b07060042c030384445440390450300e006414484d000341164003809041c04104040762000600401011502481d018010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 637260215 1250 637258965 637258967
    0x908030a09110406090c140703080103030810030512030a05310813080601210317091e0d02150c030105060304051501120618030c020f0a050d0501050601020105160c080307 75
    0x40c01c40003100d0f801071130f10000080c039420039001032803840e4550303a50006988070101680034500403280080e00065840f070043c0000385c05118256046010704102191013079695031800c1c5801c40d408140401817001105120112102c0d020389500400900c4407101d10402c190070410302180c4552041101003070542d83e80041c48400f80c1101d86102581c001946c1c03481d103070612aa5908420703c220600310000c807004000301e00d80841a0b02c1c003035038141d03100d107000c000034042000405c4025043e525140103401d081161161746041c1c1181e41d1800f5009003504071503004019081601e00261800c000c140355040206616000c01200e056a00031254503460b9140c500b81145840b401c00c030070302000d0a6243c00131803803074194600702c05094858041400914544001c200709806c858000a001c038002060754001440e0220080c00582c4000e45407803229035481d40020160003920038242c9160350349109210b06540e080c01819030082e1500c0c1c1400c29501e200d20700416640706c80c030025020f002c010000c5007030070b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 637261465 1250 637260215 637260233
    0x621023402030604061a0d0b04121e0e01051b070504050108030c100c0903020d35090f03010e0d0305040515010b0703081b1909080d091205150c0a0908010908030a09 72
    0x490000d401f28041c650316183c110101e2005075030075100f49460301804800305219510a0600403e55044841c1c4504840d074250341220140e8407003814494148204200b2000203444403403104401c034010280c16250074240401ca80c1c043e0002ca01d2500204410703442520001210b0003420814400083d5011428008481026181d000298001d9044030041d0611030745904261104440c0c500d40e0310040d0010305402542d0039010380e10b900c03840c4103110b030915501d0606490782902070081c002040a180c0e01c0840744c245041d6a00b10808296a0028402401810001c0b442100040840030003107504140000c510340c069820002c0400586400081e50705241246400c010703072803903c6060b00d80b15400d000f40e10448035201e403880005c4100b5000200408001400d80c1d47e281c268441001031400d2606a8444240310f0b403060328984641d400c0f81007d00c00e90801544141c40b2000c005031200424900107041504903401007174140c0c1031100040100c0c50030411680c100d9031180d00040c07824071500d802024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 637262715 1250 637261465 637261511
    0xd0b1005070201050d0f0608030c01141003020d050f0d020109060b190e1909200301090201050415091e06020f030306090a09030c0501090b010501141201062102340203060406 76
    0x1b54030f06050740080c029400001816811282100a000d00011100300c454203030307000c540b41d800c05841e94401304054140440040c003100e02032010b440c61816072028403807521108080303000050f99201c8207802441201d201c0ca40c0300340380c01c40380e0180720503000082c60712600c0d190044980313489100002c92070148102000364001c075032182040c407940902d0304285410194450040c41d41408044545031a40703010300c104100668142c42c1e407410705040980648440d0a0180c2c1a0140b04113443c01190544c00d40554880c65045a8043c144080c100306c0000c0c107021350324000c1d140d594000d00c148101c41c0c1d1640700b41035001443c2e0200080301900e03400d04031444100745501400c55480c0c90040d4040c07007220f069180c143e41c400e0701c9016083c2051000120703548111480003107216440001402250b108807440810710000300014048080c40080120403030b0700030300222040c040440d010a409201411100001d9200f042d0480c2c003040c95600825165040140300804d4650b5070403468000044540c03003140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 637263965 1250 637262715 637262741
    0x141008160e130b070c022704060b06090414090106080f0a0807030c1a0108010e0a03020c09041b061e030903020a11011808152d041a04080d0b1005070201050d 69
    0x30305084c803141c0039101c065400d0041c1c2c001d40300601e0280c1000b9501ba000b243c0c0700c8082c03444070030659841d2200d8004142010007075038850410001981e00744d4a9010349001001010560700050a128070301e1400c446050b40001d003190000e600038503d418000c240da098036500032010341d549160394038007254004844600200f045c1401e0760b0a02c005049070b208181607a10300c40c000c002040448410654641800c0002001a801480b0b800080d09140d07050a030001d1084a50481800094030190000800da8000200040e007070203049a030111030800b41d80c003041c15030504001d80701e001e8034000c0d1550600030001d80707a580d522000400070b0b445100403010340031008807110b100540360400b942c0c550030f81501c24440800d1080c041881c05038402c0c0e120790505d0f00e10113007c0581510900482800000a0041c1e9981402d91003001c01c82489911461141e8031a001d600c0d0b542c5e480182601c121206101030a001d03907101d0000c500345079009411115400d40908019844c2d24140203410f0140a03400a140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 637265215 1250 637263965 637263983
    0x7060c0c030c0e100b04151b02090925030c092d0b0103050a180f080c03070c290a030e0f0d030605030706030b031b0102030d141008160e13 61
    0x840e031424030f0f100d03070083c26205284a10b007662000c001e1420b0040b4010841c1900808100d4078040e40034041000404d150904408549500c680008190841c116100780c055040101e14268448240b11714000c1d00104819040f001e07411926228401c074440c0c05000c0d606591145039059910000a5482c05e0410401440103210804c50380c541c050000440e00902103401c3c000400c0800440f03006410680c54040c3c03020064204c00d03207403102c03a03119a0070b042c0c46000c010858540892800c1c0000c003c010b0003056540301540c94180203400c4814114407000c40543e403407600c01d000c4440c410848031001064500031401c1081c0d0310f2520f0a005803000c4e816000d01c6a203030314562040d0190495822104100c00361143c10799a107005a040d149524019940354100aa503130001c1000b0702540c45030200188101c0c0e042480c104821411141610600c0c510080103034108440c00a24000c00005840480050100f039121030401010260442c000c0015030350340f600001706960078404d407500c22560454011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 637266465 1250 637265215 637265219
    0xf050c040509030913050f04060b0a08070b0316030203040209160207080f060f10060e10050405040203040606030c06031112150a0e06090a18020d030e0607110f100207060c0c030c 78
    0x90ba070f6030752141041c00c1c0179a071030728000e03254024a4400c40d489021003401d98006c641c1c0e036548400060035910840d5502c5414001c02007501081000208041d00c0c02d450703000e9580c1445485c0c0c0f1400201000040c003054010010000180c680c03108607900500d10140300d0714403002c00c16050f410f1011a4011107481d10551100c00807040b0f0000d40c26020340710300c0300f1175645903c41d2010215414072074003401d804549542940803050504e80184040061b65180040c1020b4031440003600360381c001e40b0241d44080e00d0340c00c2441800001e07180707038000b0141d90408000460030300c40d091209000d001e00c1115942c0814002850402400d44002c2d4121401031a82c1c04030b540714000d20651540c00d44071240140e0380d01d8005410259a84140c9440c840300402d441402c50055080040c0340a4005048040020f845c0c00892540c03680d40c05405201d1191035220300c905007035000c1c031202c901d0343c1c84100d10514544c5600402140c0100714001510107a28201e01e860a02e414484541a00da910040c0122811080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 637267715 1250 637266465 637266481
    0x904020a050702040b0d0201080c0307120504030201091103160e090f0f060108060c031e060a0302030d0906080c1204140115240c03050f091201020f070c0e07020a0f050c0405 76
    0xc00c00d4a100704c4040019101c400c003406a28810380e400240818401f07004103910f40029001f65030721810500e4038114440711201c1e40c0b03007a61415601140540e444040006c104054410400d0040d04294002e00f00388807070041910754111240306e509004d66040c2e010a00303459050150000005084003200c4105040564455031000240700c3d003416030042c1000b02e00090242000c0b00d02540800070b0548003540d0702c0455030b80310440a400c607a4080c61111000005032014820a0601c119549403c3c0d00b091038820080c0c50762800911001000c01e0800a00d900880c0010f2140c0d00242c102c50110b1071a07080130041401045032054008841c400d2290006065940701c2c00c10044089a058041640501060035a29000e00400041c0411000d02260780e040d08240c024040300c002c01407082c00a0b4a83d44001400caa115800d02003081d04002048000d0040030090b83c4014084801084414642058020740300e408071800140428510681c542c1070160402080244000040c001c10890602e402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 637268965 1250 637267715 637267717
    0x804030c15020706050d0209010c05060708090c010e1008041e060506100206040c0614070807060b010908120d050a0209130603060b040207050c060f040e010909051603110f04020904020a05 82
    0x420710403040062049680d02900c0450000225815a26180d040041c0d11790410041d42181507036034100040340d500300002c40d608004580c01050f5507243c560702410303c94841810001d031074001c603050198030850b076601602d800c01700d40c90003141403230019407544852a001d1207050310000c1c90186c601d581e80420003845015031089019400844001d24a07001c0e41005a0b1103200440d40038200c1c050001c0c04000c0140140d119442d4004c0e080c400919113407460741c1d210241c2c0c0002c0803d4a01d6a51840700420315600708007040080d140f0301008044000d40c0140b10241ea124441c134011f01240c64a0214640c0a032035019254201c200411001017054145600c1008003017a200c159a01402c0c102d080a142c1061710841c1d6800e134011300034101e2004c540701440020b03803000254860f03a060410001510560341c2d41c0035400b9200309500401d4078a40360900c50301d0406200710382c0b400c03032411110410024411104002c6010f5007038074085000072803140010004d0107880351054003c1e00000e09420902da1081c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 637270215 1250 637268965 637268969
    0x1b0e01080c10170a0c0302040801020a110c010c0b0411010309021806041a0a030308130203010e0a0b0a05012102130f02071e0506011e080a08041d1513090804030c 71
    0x142d1290714100c05101c0485046009032841000e04940c40302142c04a0a181c210b8011038403a400e000d460a566055242e089a000000c244005002100e400e42800303020700410780d052070300346004803170104242c131000148074020784020304a040c40c3e000420240d0003504044112174004010320b071040441903410071003002c11039015204918100d407a01c10b0502d00b4401d911500006425058610f06560f0242c920342c0c0c0c060440f01c0c009450551440050760240140b02c2803414140207000701300c280d850149184c00c1e010344803000c821709110040c4180000785c0c1e0050305030789001c64802c9030100030f40041072241044001d020350542c149951000d030301d8040e030010f0000500c503403401a281c11a03082041048403000c0d00041c41500008c00401094074103859041c861301301c9100c04c644455031280b0440c034140c0d46050486c0e4814000c5001c220101c00c89034411900041d4100d42c100d91302d8040701e0040301e5413101e290f46100304030580a010360600d456012400040c1e001c00030300e558588900380140880314034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 637271465 1250 637270215 637270219
    0x4060b060a120c0903050319031e360b070e03010e0c01121118120d0807031b020c12100e010501091b08010302040506130c030c12181b0e01080c 63
    0xc100f060140b503115181110849402401175400d00d18030885201a01201c01d108a040541718812103000c0500d50603020400c41c147c40340014182c9140705110000c14084000000200b44c1d0b104184450082010316156594000560383c0e5a9a485200b0754403200c074081000d415618000d2203011139000001c2c0d40c0162102600c43c0c8030801c0615504505462949520050b03891060040344040d08040200c200c040c00014003d101482d05000301902d0201259070350f10009000d2010321038241d401d4451090b4040c14140840040e02210001a40c0c4d5611030021a0084007401c0403980f00d10802e0045141142170010140102e10561901c20302030042070143d21405031400e040d01c808807590700007a604202c0c4948801001341c0c81c5800f0000208030040c45203801c095414a1400208818403c403c0b4030311303080d2000a00d0844800f802051107440c0b60209030303101d00d414515176a10140d45d144514456000c1c5001c4c2e0040c21038440501008456407004408804c07503c00410940004611174180307581c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 637272715 1250 637271465 637271471
    0x4090c1412160314391206240a1701050f0d02120d0c0c050102010e0615010201090b0702061005060c0a0b0c19050c0f0303131e0c0f030c0e0403080f04060b060a12 71
    0x3c0005103a00300c1000100c02d000c0d4174104a045039840001030305a5021600400c810b14185034440d4529036048203d2003a0700c240780c00940340320301c2500452450301d40307040381c0c081101544c1010080b4102c2c0701880031203072041c08a01d100500310365401d00c0003c0650a0002030b1940c030701e040c2c0700182200c1d040040c1240c10f80d8030440082101c1d40305205130380304038008800515454a408042c04041614030710258115500d40200d0710100d03c8030807419009040942c000c07c02803030648404082540030740c10551085800b00700d4034100980001d03400000c40e80004060540380c942c6035000345240b18105122007412001c004050f0603a400501600190142c6002d40e85070592000c42281c0304d1004888000c07014040c41101808120a080d000c60f1a08903590300c410040400e803921042140315600081c0e240c18407071001d200b04030f042d42d2640010042d100c0a10b100b807c041c0d4014103124001071a08044107181c00000d410b1014540090130b500f10003900d0203640d5143e04800030043c04100f410b134410ba81c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 637273965 1250 637272715 637272781
    0x106031107020a030807020a0308040803131715070903050a081909030506010b0a0512100e1008063610110708180a030c03050313080c01020a120e030304090c1412160314 74
    0x11303c940d00894fd080520213008141c155600e0322004070405001001000a5100c010001030400c128500c401d500070385071141c0310184505040e140d007085880000410030103c3c000c000143c00061380340e042d19141c20701c11340c9515000f00c3c2290180580c511420628000c101800120200e070642482039031b1500b080c0b581103a4502e40c21118000003072040c44150b81c410320024012201000b2406258007a41640401c0318200c52810a90342e10700716000b8545802194901185806602c81c44c900a00342c4001d8034100090364441e0402800799004400034002018980d503a02c0c5c3e99209030304059540700c031500c12015200d00b4456501d800c10483d18003c08410080403950140014584241d901c05074018031040c241941d42c2003550b405041842e0520003080302c90440c1c1d47e001d1001d0000f500b040d0300001a111859000200040500c2800e404008010059502002c8103188225400b070fa400c4416801e411621a0440080c21803513807402a2007a050b00f40104038060f501402d10820b513500102002035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 637275215 1250 637273965 637273979
    0x1a070507230111030a0518041505030c01030905120309030c06040501142809110a080a210f0507020a0302060a030207060b0a080c01260f0106031107020a030807020a030804080313 78
    0x50080c54403d00b958414002040035522a070700a04405441c0500100e0080d42c88000c6000e54500c00716800080c0d002c02020b100c541000c02481c607900e0001d280c14410107089440b40350b2038041c0442600707109807000000031101c40c1c00704103c03048400f800084400714689030401c2802040101041843c0454003070200c0c400d41502c2ea20f04d284240341c2c0540f60700440e10710034003400804000808584e1000149403400d025550b140c201401080604040c14400d0602c0c60710120903d50001c0714040e10104d031001c031600c3d5a0107694a2030480c0d00f82001d035514001c5000250b84a065644002d50103d800640c010656a05401502225110f48418482c005518041200e2a50b2b58001c0761071580c8030707140340c2e4015880b44000182602800d000700d50240303032102da480309045c011140039800c04041c0d40104103080c2d262003101c120b0000f01d240d0501b03100041d400500c02210904c80039100c6d40d40030511106550ba511004001507501421144d40d5559640340c240c1ca90300140d03080d24070740740c24030400a205 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 637276465 1250 637275215 637275227
    0xf0611100b060f030406060902030c04030308091513050102070501020f0414030d0219060b06030711060a06080616110f1e06130605070210020720060a091a0705072301 73
    0xe41c60080200c0e09010503560b80c5680c0741c200810507910301d5181c10380042e001e02c1c42e200440c010402002840c0e80d46007141009400140c015283c15003961111301e418031604010000b554118115500980c00d41400e802c1907070190103541c402801552000440c281c07047c0010000303100b1503222180010b5142100020151160380c04200403002d40c102c01010031907180103407800c00c0e019105130000585044070784081000b941007142c001d030100b0540b11100c69101030800203903521149a01c000d128181c103040340a901c440002d040c032056400c10590307050005020b08510898074140004480f003102c80445a82e544506030310b1001d2216558a10100824501203005031182645c10040c022680582c0d44580041900900000440c007800a05000200c4140001c000c00d42c0200c51803500c2d0300b0303d10480b90f0340c94064040350f440741c0c3d41040b8802d038040c1c00611680444050340f403034030381c10302c0255000310880c801c00344002c006000705500070800e0740911000c600040c0d4512409032119600c08010341c0c130 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 637277715 1250 637276465 637276481
    0x2090f04030914210a030305160c02010315080a0c0303091401080420150306180403021902240d0518070b030a060909050307050d02010c17060a0f061110 67
    0x54480b0030306204601030443c4007102c0d0364024041041d00c0c050302090210310040380714030b20120f0b04902e12030010b140d410300030580c00001c01e500180b200c28100d4000382450043e500d0007814151540416003d201101c00a20010407100701500c042c04c1003441c1c02024240715000440110361505000b041c00b0308e0903018681c95540c181c54802d4181c43d203031559090b0a80c5807140594100c03c9545840c0320b40c43c0d940003c00c4003a408900c82d51a4200368040208140307900184a00c2d01c0ca640c4200400b20381d001903407418110080c0b540c2d14440f2001d0000c41e41d108400421002ca0810110b41500c4202c1000e0041c0b0715070040480421031519081000c402205a401051003558812503085c8004080c9100660308260560350018905075112440d000f80c0388002030075122a000480c500f0280f10092240a046010501c02049491072150025041205068010200710344800c0014025100c10f40f00718090010340102c0c00045944441c024149426600c1e118018020200082407020450003405e00e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 637278965 1250 637277715 637277717
    0xc21080f011a030405031b0d1d013002031303030e06010b2209110c01180209150102151302150403030c0b060d0f0605100621090206190c02090f0403 65
    0x900d08524101012003504013500c1624140020420344c881180b501500c25800741d410790243c030020604100240c00c820300e181501c4507110b41c00702ca8001b942e078010041002d14032003003010307442d00c41c4100c442d00301c0c00042d0180d280000c0c0300000340211004010010300919119560500050b0802c21243d074807400300384188100c07082c05110f142d6481c1502961404c08080c051030440c181e40e6038800180503a0403245008100c11070001e00d10b803c52a0a000302c42b44011056080600f441003503000c241044001000010109034040c0c00007140e0f882030004100d8850340710b20038040e03414107600d22180b4281c4035204074864034901d04a042000707002d00c10b8078122078060300d031044c0011164444800d080700040200340e018090601c04d10000b400d4070013440240e4020240001c4510740003200d4a9058502d4000400340810701600d40c4490f000001c00c1e001d0b041e4415000305100c0c9641c03011070700e10300a580310034008003500444e9041c9540c0c0030f4000c1891354000c549542c074039260b80c000344114031825a0050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 637280215 1250 637278965 637278989
    0x5030c03030409180c12021203120a020c160e090d091203030c0908030d09060c0c15020901030204170307060b0612041101050405030a0606080f1f05070c21080f01 71
    0x1502c00b20303a00041591024101310780c400c81981d50f074003940b08403540000c09503c03045200c01e01942441c200f001c1003902a10021407034014a503181040003a0001c11030140a600020b80140d100000e101c81080c28000c101c0d00d48103141c468060070300e018011130706904c01d885a44010000a0b125405c0c0004a0300891500504051552821000340004607220700900950050009008204000030300c0b0700c0003500c1c00020401c0240c9402420b81c0d1034051002c00308030b40803100d000811904500c0100d48000c0e00c50050742c46c1300200040c1c011f07000d03e900c103800600194401e41400f020200040107101c1c0b003040c0030402840101c00b040054060703003444015100c43d2500041c00500c0d101610650650305040c001d041c00d42d1140080e2510046400481e111920398408000d1030404205500c010401c04001d85801c00307149416140c424043d60000300c2558640d00860600d900442000c04540e400c00c4094512600038921950f80500c424410700000301c524001031241190b0130481d034143d591480b902 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 637281465 1250 637280215 637280219
    0x306040b0a0902181602061b090607320d021605090a090b09070806060f180703020915120703060b0307031e06060801050315010602150414012405030c030304 69
    0x10000900b9a207404a030020030700c1040f049a808440d81992151007107200c0680c00074080070009090440c068130540a45c044400300d09203d080903015a25040c0e8161402c0e80c0364a52828184842140f5a046140a480321000c00c1c0c9a00c0100c10661022550101103460092020740d0481c2d5504450300600d030300e4180c1c650184410b16100d840300d0b030408040540071840310000d890f00d030500c41c010340317015103154051036041240700340500070990301801c22074540d4922115180840c980d0380000040381c0c02650940002101140294151400711001428100f241d48038209200455801160040100100000096500c034403034050a01655030340a11203066440c0c8400030f50151081602612446d6011026030141a060780b041100909103035a4603911075151005043c00e045a000255000140c4071005000701078000641c1440c210407030118000070b6485080c240030451000e8840a01c44d402c00706e02240f40d44a805510b90901c44d01c20114100b56603602c20140d40f1803510300c150350960414001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 637282715 1250 637281465 637281481
    0x41d24011403030702030d0905030c01090b0f03091f060f091a01081b0f04030c080d090521010c0e04111806070206090907080403030f0b1806011214150306040b 70
    0x60300c01c00c00015045074200907030742d40003d00300040c004000300041c248841c02c00c02e1b031034108400c0402810038201540000d0400c0c01600303140c41643c65141c103801c2e002020400c0c81c8400c07c0400b10107402c5050040c01980310f0724241c4007a00091107091141405481c010800a0b80d910501c2d0803410100006c80107000694015540020b004203107a181c400d841c04a0f0318022912401040800c1021840307a9881c0c0c00c5190003048900550085c58596000c6c0038105100ca030405c80c94000d6030707011038450b80e062143c4802008401400b0f408a05a13500349401980d92070b0300a0050400701508480521414560700c04c8041c89020385940342030304c01d80c40c4881c003060741048402001414000703030406180198140100315000016528100019000020001030550600c2800224401170301d0a11684000400150303040d0b8110b504071003420070240c00318100340e002c0c641c04e0810000b58401413007003816491400d440c42608585083c41601c0280b284041d514011608502c2650f01c070040747c02645442d20 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 637283965 1250 637282715 637282739
    0x50115020d0815031e0120030103080904021b01020a0e0111150c16031e0813151514090603061006140c060a1a0306010503060114040902041d2401 64
    0x1c01000c03220f07580c1d05403411540f002e00007108400346004103d526210f060000703d0845241501101d45106e60b03010807001440c0f800126411640c100b0402520b078000b9100260080c8103280780403c0440441405c28005013041d00980343c000101c0e181c0d0502d046018005484011a00a4070a07103034000c09a041d0321005441500c41d000304103c1700d412f04102288800140d40300180c0e100f40c0114244c810081e82402d08602da07804082240d1401c05914141010415160740b00c11800030004440309020b10105121544511748156400490524656950f64944072400040b1541801100c24000280860a00003620b82c094299226400070503458a40c08070f40d030114410400c2184c120400c031680480f402081030383c0c0a59141c010000704100000800c03403103555000700031402070b04200010805543d0216032a81150b0410245200c44003066002500801180100940c000e16014007044911700034074000c03c0c551101b0040700d131001941040c4603c3c0d01d0b06040765a1000b607140e0018422600c0c459 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 637285215 1250 637283965 637283971
    0x1b1a01182319150605041502030a14070828020f030f0a0324090b091311090a0f0603060b0108060306090c19030618110a06020606121e060a050115020d08 67
    0x100340000e11070200c600c04100010700e0b90190b000248040b030b040c0240c844031400c0c564140e61500045190100510010b01184040d0703031141e144906c00f01e53304041c03100030011a14031042e00310038440c5070140308a0000c1d006400e00083d8006101e044d141640442c00002198100702e81100b8550404d02d40342d5044015120003003c1e00b17403480034000003500c80100c8001c0607024111079480894a1640082400301c00c1070000c0c044289403844550700f00c0030603800074140f4581d81080d40c944105541d20108100901020b4a85d60115803070004004140141984540503c600903a41c03584c0c80e8454004140d6110b000380c2c0c500c06103420850803108245007080850070340900d814040520300d613881e150301007110414004442c980681c070351410100065000c5015452000315601945103040071700c02941c03941d006103114081c0d03402c0f440481c10580d04014640300d010980394803d0304541c030311082545480040e40d840950a042200106428021000c6109a000c065001f0a8003810020048984000c05 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 637286465 1250 637285215 637285261
    0x91b0b1903090b0705030f070503040f03032f0c010c03061a0901020a0c0e07080a0c09121103070f030606091b031d01060b04030506090d1b1a011823 65
    0x50700c4400e00081d0f040c0401403080d96541c490307540700c3c9070540a51840d03031030041400042140030070400001950046110803400e81500c9d0001c1c411440103404030742140d0030f914060a41c1e45c5010701d100c03600c04140041890110b80c0700280064865a441a0181d64441c001c03021b003183c02e000744500c4503034410050158803030148103c902c213444036107960400b144c168000e0719540070083c0801c9942c40d0030111581c3c1251800904001126000d1402810901d090084501400d4400c13850800d0005551911440440080507103100660b2401000495816880215400c60601100140c41c038018401c84d800f4003008101048916044d0700120002c04808a9441d0148613040c070f40a1307002c01c00d00c00c8501800021150030b90712410760811914081c40100b43c40c0c1140c0c4001d00001880da4007849034104103106031088614069285450411603144400c0b01c20000080c40000a80d61500d44100c0086c0355500c1040104104c100c84d5800d504003031651246880ba09100414401c602d0031800076401c400c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 637287715 1250 637286465 637286471
    0x83003040f030c0809060415021c02061f1502010b030d02011a06030a020d0507050405040b0a051503090721031b0b0f10051507031704050703030309150f091b0b1903 72
    0x2010001b421500607070007444c50010145214000b00350100703e0741d0f808801c100804003611100141c0290340312401420580f02d414102c040603181500f00c40070305c004d08400c3c898000c038104624002030081c01503400c074034800d01c42c051070030650500620a0010b04c2c0c01c01142c0c0801c0b082d80b00188151030b40003400182c039055007001400c0300b10780f65205190050420740e442030754544c5084200410b4824a01c890ba01c1110300c8035080010b6543d0095035401d903030070504043c1e140e548000c0141d041c0f4505900c03000400039000c582901100500704110900791090300c410580054110784070564a0405000400800003040030a5881c82c4410610754800c02c60550035110f5510390011401800e0080c041b1424200d020810100b0160001c2089520380480614928145819118103542d00c950b4072000c0d06041c1c0da08028424004030356490441542c1142080c401c410702003190100500014034103036036035082c00420010303c1c0c588854282c101e50700c40c014241000c140308114409404030410042c20305035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 637288965 1250 637287715 637287727
    0xa080f07020301153210110a0605220803130203100e03070b1308040e0a020403140a02031b01390b1807030206030c13083003040f030c08 60
    0x207424092006910078020050b0409172034404224141c000e451100f040000081040403030307062080240095040301111003140c107000e045800d42d00c00c0c00c500120400ea0048940000c280b04250300300c10300030030000c02440018040021100380341c49212074004c0c0300c5074003000801c40661005030038000c4c0790300041c15030b420294103804031011a030810300c3d50380d201e4102103400e01c00e0201100c83c081d03002c11000e1405400c03001581c2d56000d0352003a4000c0c11100c1d0108004103c4030a851381c1503070302440d40240a64134404000041c1030b550219804204d20078464403d420684d400352902c0d201130721006842d0b604560344840280c0d40001681d600368041d44d001c0715a04414002d820300d003000800d02a4203855003509040350f40c031416003803002c13101180c3c2e4003054007080144c0700c45049170703132211442c07090b0307a10364800c1541d0400142d8a40d10410300780c441c80d80c282c448070649068800b600701c260f00b0641c8800b91102600000d60001f210f0140100419014600200f40145a5082100c0c401c2c0e80c0139103018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 637290215 1250 637288965 637288969
    0x30e13020406020f06060d0c2106020a031d010b031917030a0b0102100209060301030305031e0718120f02010f050408190209060d0c03060b0f181b07050a080f0702 71
    0xe0010740c0b2800069200c004003d05600c0705010690f0015420340305001c003040140c4449a03100300600c9280700781d0344400700b442509030858110300440342d4802415940c8202451008002e0109035000076011144030a0006481d8014880d00b8140107026001e01481c44203146202c03034a4030650740c1a207100d0304d10b4070b5112802e90048010b602c1090072420004489000e50002442c2c60748226549020340d104000c0300020355603100c140c82c1100d80c54902903a4130382e1081030000040c3e58034249500b50341d4007030301403105058011801c8100c1c0501100c650615a94841c4000c0c0d0080329080040c1950014180398800b5510651398001c1c19909401e1162505503070380c500e1450440c500041c4803980903000785a104600e071034102190130003002c4030707003c01c0400141c0b1580364010032440b00400560380e03882c41440507100c031440422244c0004044101170240c060a14010230b10413111520904641031000d0008908501550b008030340000003407180002503a1840748540c020000b1010034407003440400300503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 637291465 1250 637290215 637290217
    0x30c011209080c161a16080d15210201090b0c1e0a03122702010318060e0c03070e070f02120a0f030c050406021005131b0e01050607020904030e1302 65
    0x3606a020042c100e40c08140d0300700c0c00071111a007101c660746405c1c82c3d030360364600300c220180c0d50b507803205407010400d40c030661421b8034a07880b035252810306240c106500000503140e0b00002800329041c207400001c0c0c2d0b944030b111700078000408139402808075000b02018400e107604000900300308441c650407a044820030340000c5c814126141820103003607000c0c3d25510109070744144001c5009502300030901100b1422042c4000415020b06404007040c260b44103c015680f0a400802200b14910f1540e0042c10440c108000034211140856040e0300c41c0b01c0740383ea01400c0000d440030445130100b200c3c00c415201d02800300e651210b80380c0f80000b107100c0c2d502c040c60081c3300c45004110904031034440468010300420090150749101039040188482444200706198001c164040031160041d40081e450383e901c1c2c600309061030a42e038007400340c500255030318403104401420101510345000000fa11680c0c1c0d4401c0000c6481210740003508212032401007400030b40641c007800000d00004040e2904d9010f9990301c1c10403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 637292715 1250 637291465 637291477
    0x9020306130e030c0d08040b01060f02100f060321050a05070606080d030c0305130c1a0c01092a051507060b09040803010f05010519050c1c03090b0114030c01120908 72
    0x2d20b07000041d84900184c0304101701c45001e0b289003130640c0e10b840d068491045201d014480e002c01d100d00080b05902c8240300b8022080d61000c03600d010445075008400c45070082429000840e1000010020781c000d080c203c41032024140c0c4150f4420f4600b00c0300c1c0300111079075001101c0c210b0340503442e80c60110b082c00c42070191600d8803070f42da40d00266002c0c030000020141d9070082c048140058208400c40040703800c2501c48002d0702c410294040d44291310040ca4030b001c0c42188500a0194030740b01d1180100700003043c051500610380c410107900140c146880e50140041c2e4410940c1c444403010a4254860b6040d0207010f0315800f568000518241d0440407800200b0100c0301242e00c6c0c44c0c00030050240c2c0d0041c5403030717102520080ca0440d06004e0100540210170740700c0500d460500c80702045910070b0300d104100036041000006034140c00b0250410300500640880c0c1421030710841c01d003001080c000403801c20b071500008000c0003410001200b60042d500b8003d14508420b40700e45a42080007c10746100041035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 637293965 1250 637292715 637292741
    0x606130f030803060916080402040c02030c1906050702030408071401090306090609050601090204050918010b1903031202091804080f040e01081b0a030308060a1d070306050102030406090902030613 86
    0x160b03d04d0124104420300c4002041c9020000c001190207080360f5008070504d40c0a0781c15140081c0d03d02c2c82060903461409190340b00c0c03810344108804186083d24042c0e00101551040d2002d2041e620303001c40c140e8903405940581d1456912035041000742114030a01d6505104041c100107105070b0701ca880e4842074941c0342c0c0069615540b54180c680400c10100040c0f0f00400665404500305424280000d4480308050f14142041c001c080000341d05110a500c8441c49120090020030825000b00160119615078841500890f4045c040e0502c020020300031211408001405a05600780b5400e00d1126014040e00c19038211805000c01b00d1060f80c40340c0100040e109408500f2559803402400314a400e07030281010004001840405440c0d0300d5500c208404d0360341c5810040b8603a40c602c0d021810050595001030180040070640180e501620803145018500c2594184011503c0344010383e40c0380b156220300d10014691440c10496285035902443c0c200400070304080c0030a0004100d0360503038440b094800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 637295215 1250 637293965 637293967
    0xe0709111617040f080309031b010e040203090106050301050405060421080a02070c0902030a060816030804050d050a15020d0e0c0310020d0b030a0b06030d030515090a18050c01020d030608060606130f0308 89
    0x2446901e001c09c400741d1128114121081c0c002c01100c0000c1c0201c5e031515800b40110b80100129441c1c441c00e41068002e03202c081c0080040b80b0301401c0856645400340c90550b8500c180e0142c2211422244802c43c0d4240c070f040e190941c803610b954403990300941c400c401c10b81c0c1d6034447c0c040204441000340010350181106600216019080054060404460a0300c0c9800200120420000180700170282c3e41216021602c1340e9540d0f240d8140181040200e840c020220b202910340340b03030621487d40c0941000741007400c040040403400c3c0b10340c0e0b44c0c80c1c0340000307110303415881410f072659198600d07002404550640f0002180c4003052a000c0380c6032012071841161174903090400c207d15801d0400401c40180d01500c0c040c40035003040c4050302e6030700000526450068004200113036a100e900e070016000c0d002c02d44000b400105007801c06685908284000c6801030185801880641d0b1003400350310161819840541190389890f002c0092960010204405c0d8003020440083c0036a01005a240114001c1c0e03801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 637296465 1250 637295215 637295227
    0xc01090b0c090a14031b1302030c1b03030f160215010e04060509240720100f0e060a0b030a0506090d0e0a03050a11040f0e0709111617040f0803 63
    0x420b41200c4d08444074420011181e4a0a690002145c3c02e50340508000101d0820105001c50740c0003212000c902049400001448a0300700c48400805001c035408181c280c2409441c25000d4a901c02640c10130741d0701e8428400714507007a454800e4502c110496004aa4450080e01085130407203009900c40e500d00d000308810001480414083c40d9805490b8201602c0c0d5400c109507401d40040d40540f034640a05081c08c0060701140c003400b29000c502941c20701182109810540050341c3e10701c080c0400d0000b5060201c2d80505c000c05001300542405030601518170755a0701c24034800146003062a4927814840d107654000411818402603020707940c460040c1c001000b80000152040e25480ca01d40d0144d900c100341080030400100d51100e4250f4400782c65124030401400141c0541403202861100038603100f010b841d02500000d0207011981c41c17035001d01c007400f66500f04c0020350192080c90008071581c070740008001191406001d03500302d010354225050603152030141e06c00104a4200b092294000100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 637297715 1250 637296465 637296469
    0x30e030405040c0503100905012412020c01150b032806051903030f0e010801180609020c0f01060b0705030901050f120112021906050406110f191e170c01090b0c09 71
    0x448007e4840aa4107104039450250305080042e0015070f56030740000413000b2000b00c1803141e40c0366030560f18551700a6450345852400f050081941e4118060034880034000083c100d242007042e03d00c108800c2c2400c25107202d1820068180014001e100c20140d039076040c0100f440c0e0340744042e5907130318080740b03102101c0740d8194680a02600700b5400040107204000c0024409603900c101018103580e125001c0c072182c0b0100b1b00060010340415080000154000b05481d501c4480c001607005260025100a200301595080c2c80ca20602c01c00c003010b01250030420024503654014001064407960504410b80f0f00010700440700c803110303000c2e0010f4076003684800311071040d803620440701490020f2040b00e140596291240261070391060707110b15001e0001011f60003070283d900340800013851401e0f00a462707a4440180000400342d40c0c008040341e50304100b2018079110b54604103856442e69002130072080b030030007207501c51300c035904483c28a144a40d21005081c0c00181d2100703145026000d040c0e1001c1c1c41d00704404c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 637298965 1250 637297715 637297741
    0x30114010609030b0c0f3711070e010f0b071713050406090b01300207111009060f20030a0809061602120702040204030c230619030e030405040c0503 65
    0x400244010901050300205a003504485201420004290141c161000300d0301031307440c0c00e44000e5102c7c0e2660302c015400781c0c2c004a4400b401410b403400d8a201a03211242c02080d002c082c05140308049100b0805d000740b040140050492174000c00c8e440240c60403072500003034960300901c400074204010040410060509009280c0a4001001c0a01c0301c54082c82c00203016003d0104074440c1036a54101d086520507206600c4a030396040d4840a658501c194104048001d003c25100f038010126521440080c501c5400241c0a481b5503559a01100820756000c0310030600c5a05000c5280d8184828001e91000c2000106414141d545414100d07207440641e440c1445001850701e1101d4070550140c60b0790950124400007040d108510094a45400d400481c000380141c1d00001c1c003800000f030b000301d03030f403000c00300b050001c141c651041d80c40403c41031080c0b02650003000c46218550280c526168200b42c000d400034011500c140c0101ea0610765900002010ba0b0741c05645140890f500005102980340c00c0c213 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 637300215 1250 637298965 637298971
    0xc03070303170c07080d090204180b060f0d170f160312060e1b03040602070812010e01081c031a100507111c1e052407030b0a060e030114010609030b 65
    0x602d451341030944544034a0418400c00603081c450982d02c2e4600e10456460381c3c844000302c01218641c0c1407140c2c05103826015400c054500b2441010311181000030340c60030105a43c2103e070302c41070031040c0c00040002c0c0c10450f0800f0402c0080c40a080c4041004a400701c1440e40110340240d4850b446070b52929400401c8441c641c1240c034250124004000c00c10322015601201a40c004038242d40d40d640314240b10b4028040c15100501282000448003905504c120200303058070320341541161703141d03a00c07a05641e4840304084804001c640504c040a941c078040c1d07105c2c180e031410b1508038140c80c00b80c005c0014810052a020000030039800314004080c0700b040c11004086020030341d4205c500c01c51155111031105001c130801440b00d1072062403594140c62801c82104601c0d406011550503501d07882c0ca000c2d50f8000b1002e480260304000000800c098420b0003490205000078091800b001e09082c070031610078402500d0281c01d50f40346c44442e1440c07280149980c1c000e10350350359088030050075844c14410f288006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 637301465 1250 637300215 637300231
    0xc16030c081318110417010605041b02100207050d0e01261902090a120f06062318180114090c0f010503010e0703050a060803030406141008100207050c0307030317 71
    0x14540c40004440e043c110b6041d1108400300e83c008904902185000d040300b9003126400600b810010181400515640d80e04cbd8000d80c0c003951aa00000c20342c0c40304a024001c00506a0390090011081441c014400100182030600d020400f116092201c0042854500184110132174a24100200c92185105210948600340010351034004424000b81c0095002d01441c689110020344200030000b6003400c01c1001d560258090180700d40c0e5a407452100c2c110a003508282108104101500c0d190019142c010100341c0c0f11710299070b494614926070303d4081c8901e40b80d03c5658071303143c0c1152010100e224501c00e4152034010b2032062000010300907240c0c180d4030128144001800148400e0611019195001c82c50b8500000c0f83c1d0384d440c4410000e0031803580300c186a4080001400309102440e084034412100d00c541001c0943c07030318a50100700d2000ca120303060550700008100e598000da41d400501d9141d0041c400c60303203004102c600103401d18007964400c0b808509003004582c0c0e61404807002d103500c0300807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 637302715 1250 637301465 637301471
    0xc060e0a0203030f0d1506020f070512150a110c16090507020303072d020a0204050f010b040302061c060b0409050c03070f11100501060309050609060c16030c081318 72
    0x403940c0882ea49001e0b03550315495040c0003141801d030590729580302036070420b202e651102c0c0031a900e1402039101c540d0045103221900407681c001c03409040448610070a414200001d140300d041c0303950341810000f00640111003041e102c1645e2000f401544000d04039144052000d006070030324121801e840c0c0300c00351b800419000e0414080000c841d40220549900440d1400c0010203042c42180000c0c000100c02540c250003511049080e00c095030008420380b00d50b10070382c1e00308100d4030381d10301c102c00100e824801c040f4641c2c2c0c1000288014281000070780b84615520050600414010000d0300c15206190444502c00401003000c101506480c040c07070f9000032241180528506200340002c019942c1030031900140300a005e10010700c5401000b24003c0a240c0140070491035031a440000d01500b030b400d80c16100351013041c001c107a080801084c40e41c000c0c0100100d40d0b10700070500300800c5400300c0050003613051141e45030301140030410040c01402d000c080100199013035410700d03940c10341100150f0031030300419107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 637303965 1250 637302715 637302733
    0x90b0901021201241803120e2e0e06130b0703081303020a020d0813080f071e2702160c080105130204020c0111040306090308091b061312030c060e 64
    0x1450380c0d601c143c40d0214900f50010608211008605441c0c586c001001c0d00c50b04030018511036803010001509210403601c030765460812000c5030348030b2030b444212005000504c03010200c41c40e000f14215108101c010b04960305029821140803800d407980c3e0f21214040800194003002c1590003413040d503000d1903429140464444949009503a58a102c000038002c1c0388440c0310000b400520001da907604084402203a44035502e0b140865143d500c91000c03105648940400411000e60200d400c08a512200c032111005500d00040c035142403088208941b2280040340c03c2403204201d600081642c400428582c0380c140e01d8516000c005243c1c0d69124880d66403408060012502c14a0101c80c0001d404940c0561900c0500d809036005107403a40d00c40c1c82c00074001034000100055600008041802904d40c04250f83c3c441600c2134130f841c0d80644203008031781d0213071035100c0e507150a101034202110b17102c1c1000da00d5500c960000685490303007103068000c14496162003080110700d00440e10350081110181030151 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 637305215 1250 637303965 637304009
    0xf030201060e0c070204051308070c0612090b1909080c070303121416030e070e04020a0803090105071e02100314010801061503230403050a02120f071203090b0901021201 74
    0xc060300100031b00c6940c441022400c44106a840c4040c0c040d08110119542c0d5250314180701c00c010144070b9080030443d0008401e48680a03840b502c6502c0350000ca542c5616518800185007407007100c001c800c80d0b01d0395031a070040480c0d410381c0600302c407550002c020104d00e411800c000c0c007031514113021b00042609207400180c80140100100390003410040c100e440c60000d1050550161036003000d000790707503ca225400602038881c4590140554002e0311020140764403061041e07260310031041554003040b020403170030b0005081e48054280c458a012511a2419266400156040d046001d5140040c1d1501e000071820740e40f003103402d40104000c400811001d89841d401650841c40d629050043c1035444207180d8061101d00350384901006210542002c0345064600a03040d070b04036074802001845903d80300080380044804503806036599074002e60412206690740d0f0038000d88000c510081644030808140001c040c0c0d00c625024810907400580c95181c180264400c0d44016885403028502c1254285024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 637306465 1250 637305215 637305217
    0x20f031312030c02040519050a0204080607050c031201060e100e0a090e0703060609020309070816090f140403122004090203070c150501050111161401110a0f030201060e0c 75
    0x45094074584a6568a030b0304042e1000500e02c200079400904003800c020a6104030b8440e00100031821804001580710031040c070049004601811055030701400109111a010307001070910b542e1500104d074900602d692100079850340a0b405100400c07265000c0702c00c1b0389044010b07078424900300d10f0400c0740308a000700010001155072042801480e9240d80d41c0194400501220000c1c5070005001c0c08504d60301e9040b01d009500485464036280039454000c00e0b9110007090000c002440340ba00b54032002c3c01d0480480040c040500036101c0240c0e02c0011b40740644030500340074072031402500d8120300700d41e07512031480580340503005040c0d500101000000300500c10000b40c0c1c05980200c8030050b2207603101c8409440c80c0d54203010243c4640402c10301740d022000241c000f14141c400a0380c070100161540a1340769a43c080c0340712900c521711880d0b5003e02c8000c400007990081c0b008149030908668415120cd01e0500c210b265003550f002e004902e058040c0b6409000b21001400c03c080103135440c1c600441d00c441c01e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 637307715 1250 637306465 637306469
    0x203040510020d090512040303350601091d01060306150503041e0506040f050714030a060c030b0d0606080c030c0d080a02010209041803030e16030f050f0d050a020f0313 74
    0x680d01003568941c24191390711074480180d200040f15441110010303c5001c680162101300c0000b000c2c6650100b10706c150000405c510703600201c858260b0b040041000240660050420f070401000780000a151500305200c03042121952564880d43e5050140082c20b03116590400303000403c0280c10b40007455481812640c0c0650840c40120240e441c2c140c2403040c41c0301441c0c01800740e106030f0041c40103100c4005101c1c40407610810880301c290b1303607030311141c0e04902901100c9035040c0c12084d5844c01090491308006014400c40c6800510389200100007000c1c000e5080041d120140c1e00d004c24400c0d06001c01015850714001c40c000c2940d90b41110000303040c84d42450009045140201d02394807028000d405840036090700034424000211b01448001d40c044640c00d05030002130170000520743c0c80c040454807081d08249a680720342d0250550f1a441401e030195203084070325200d02d0b1090b400c10036082c00b0443c0900740b6940e9003a5143c0f100c09009290501030080b441d41e6400410091100744c0001c00c485003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 637308965 1250 637307715 637307743
    0x30f15011d0a090e06100603060b1602040e061503160b0417010f020f0c101e020f070b0a0b0109060207050d060e011e0f15030210141b16050402030405 66
    0x104848901c003040101c24035601800e112410286061502180455402e100c5e0441c0c1903110b0015a880c4011801c1e50520f12480900f00300c02c022840e2010840d0942c13248240c002340011900d00140c281d0303d4644042154600c070250084400745029180a0000b83c07164010aa003000038079090141c2c1d0503841c440c6100d80c07a0460f000d89291100884290043d81c0440124002103440d20480000003190382d0003290324020a014010700600740c81d549104400b03241c0320030302c3e0110070310042581140003544110208901000180a0400025556a02c2605c14004200081040350700301e000982264255003000040d03412a0340140119102d5420f403071841900240042110030113120b4060052000040c13010340b00d039200707903d45269407590b009401e20002c0002d0802030f02c260900d409111201d180030080d4042c03400915074640c607108018150340c10395601d030482d1421458400d180c41c0c2045001101c070441d005412030041304815004900001c01082c0d40135071030741c030381030b5074440e210500703810703662 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 637310215 1250 637308965 637309007
    0x5040b0915010921030306090213170c0a17010b010801030b06011d060a03150801020c07090e070e0412091202060703030e0c0d080322050a080f0d050705030f1501 71
    0x76a2240640e0700080c000300301e0400481d00e2928022a503440100d2080d4017007820500c00080d200080e100300c5510380f202c200641480c504204d0804544000c203960502c09208d84440800c880c0d550b80d91078001008220440308581001c412000d0a4482c04a4418180014140100040382045181950043c02482d100d9109080b440004101845030208070780c0042004ca981142d0b60b0f0958080e004a281c0480c0b184541f0b980c50215600340d20846100c1c11141d0080f100400162006802c01c0002d00e520f203003034808150f2292035052404004907402d881e001903078005d2208894010f2144130240040c03001c41c1c12072411940202c4c0f410700c11018002c0c101a62a851001c41c0d02c0c00307003e200c07542d04c8010140030031120642031005080c2c20035100128409203125000c4003076107c203a1001c090ba5849405080e0a0910780c840c0d0724942c100c00c2500035240c40410019002c1d042504c01e0750320910403500d40540300d0405000d0558001f07402070250000d0880014001c0e56a0380145107500b40240e180050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 637311465 1250 637310215 637310251
    0x105030d030908040317032a0a050c010b060a02070311010305070c230303130512130614040302100305070e09040c090b01120203010303030506011403070807030c1e0806010905040b09 80
    0x5509441254401b03050400e0f44044880c101c4842c100640c01003600c070001c2c0c460451070060420b902c100a102c1c0b85400d55080005030b080c1405070019064203887c01c00006240d0054002042a40d84a4210540141c02010050042101e2a40310081c0040d007868100f12900d0541b4000d008419400c070040c00c42c00e010400c20200c28038401e501c0c4135940c82d031800e5039242d080c900704600c405d41e844e160817681405021010440c241c6580f05580d0050b40c511160700060b45011012f030340032070300702c0240800901c00708004005a02c172810184a03485465030002668038083c14001d200700b1030340480c14481c05d00c0e80140b00110b8140b00c4040c040e901d040741c2c0020b9030003102c00141d9062080115028100340044000424036070150304c203601c14402038071026000c2e8850311040d000ca00c021038001e408038229070301007506680720760300041c0585817500b0500d0700d0030700d410283c0710ba048501d000900000c2d01c60041215a5901184500c001c0100f80c0b0280a9000d01c80300080344450000c1428020507411039031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 637312715 1250 637311465 637311473
    0x204061205150c09090a1109102a0209070c0218041b094a0c010e060a050a0804110405240402070213201206010e0105090916020709020c01020c0c0301050105030d0309 73
    0x8c07114880c20040c210588582122005001100082d40e1540d40540ba005445140c41c0c0654628110540c007c024104a607290901542c2070154464203a801ca4020861912080c05540416020724090035915441d04102a09035942c07500c250480034030181406d8407182c0007003603803044100c64910491a00214115501541c10b1100e0480c01381c0d80c280501210740154200104226004c01401e9940c1036035450302d802400050700c101021540041c2d010403c2da80041c3c4140c0d4101c1d0014401d1103c600c1050304000054261082620030959003540301c6080f8554a240b1603541a5041080e070301942846001d8001030494001036012048050300c440443d20f10301507410107020780340040454582c46034407000c400041d04070112000d0307000c18210702050100d0341c000d1042d511081c200500700f00b074030750b80c001034074000030315070f04100c0c080d0311a01c0c0002c01d44034024009040c00075150000180c4881c1461505840d1890000341c15009900d4000180290303100480c5110740c2c4640340c1030200360b110140c98 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 637313965 1250 637312715 637312717
    0xb1c0b0705163909110403061407080108070b0a050c0304120822030b0a0b0411030a0c020c060c070e0c0c070608040b09070503190204061205150c09090a11 68
    0x701d050101200200700e81c00c0140f0305124001040c01a410fa1070b4164480403115001006107100301c00b00c0c0d4020008000340c1010f0b4000d12950350092000e02c1c20241d50b0303030310782d02a80c00031108502e1800003001007100d036550013811035006090000003000090300e030403844840c43c843d4498050800600050343e100300e01b41001202e0081c0705030407007040354180c6820150201c0d000391031a00718402c4c03045403034804121a40340c98000d41e50030554001a40d201e80a41d800106040d19040382c2090b01c4030300315002007421070f01543c07064480380d00c04074901c081405c00a08294010048900ca51018040589003003800103614056690452020f04103032a001000380c1680941d03440c0742900d2103401e00118005074044c5266000d0f5200d00500c0c8500d44807111140d8891741d40f40605501903000801521440d4071514000e40f0040c00504002980c80d04c548400203018050082540c0c1c2e070740440c40c85c50400c50b4160620b98010444c1440780d091003c030340001408080040c180154072074840010701c1600c0b540e00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 637315215 1250 637313965 637313977
    0x40819020f060708220302030406030c032c010c0512040210020a0506010609060305070509090f0703091e111905010c170310031b0302010e040504050118150b1c0b0705 73
    0x41102e03070500e84540c00034080107080300c1110072607000804e40144003034091004101d59605802a50800d0b0038484120014801326140a08051315107500b005000c1401c20009050205042c41400b800100c403546425070360318030216000c011080050a80c07000c0500c103141d800a504542440d0706950641c800c91600c0c000b050040c041d03000d403100003d0191b03004889030046881e03d4a040c0041e5a4801007521980584503c0f603402c45091000241100c0840c1550395110521703007070002c0d081840e42c40700718007050340d1100341d2400220040341d078040c8140e1585141d00c3c400100d81c400d0085403c0030000c21111103d01c6180d0501402841c01c00c10099105803080451141c80601520b900c2c11f841450b00150380c61009071a02503040c0d1442c01384001d07141071170040d40d4041c0c40b098000760198007170000400000700b007980c080d50307214416812806010581c5c00c0050140012520028000d5408421101c543d00d000388a001640380c0b0b182c108105023050f8090700e81003d41c4890a560b103c5040e60b0b03511500c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 637316465 1250 637315215 637315243
    0x60106180e040f0b0f010f0e011203110f070f08070f030507030b070c0204020315090106020f030f07080c0304030803010314010203040b0a051911040807150e13140c0301091404081902 80
    0x1444c03c1107900c1004008450480d00c90035907210806a54841c0405115000c1c06150f500e86603201104000c42d005040d03940a10007450202d40310701891042c0d0b14107243c000e8122010395484000d04100301041004440b0203041e44a281c1000d581c5150340b2a503981242e8403004010503042000992003500075200c2c42c40494028105554a2400014000e00c80703025060261007000d51100124510b440000c4080c3d414400710020740c600124440c4100e09a0000101143d818104010f520900d0341d0078009080154410400d058581d415490080c036413043c2d11040440a030b1042c0b040002003502c1003031a80d045420114001543e80f201d4031095103481f000b2540116050500ca060003141140c0c400410440f007044058a02c002e4a51120b404010b461840b6180050345000129150380350a5000f01b81c0c51459080015000f00001c0e21440c62800c225251b600f1240080010012a000c60103082c03040c803000380303a0700c0d0369250669403400540244040d030a1a480c60612764280c1500801500c6004015 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 637317715 1250 637316465 637316483
    0x20031e0408131403010c08091018020303070308180a0b070507081308030915120606030613060b040911030415020f040308030c07020a290f0409050a0e060106180e040f 73
    0x110f2003201d42c1a0220b002e040c1c080d6283c41c404042e1103200d00c154602940740500540040f00c0100304080150802c6e00441c0d8003440c1175442440181c7d8100020301801e4480d40320b00d9001d252600d510003144034080524096500440282c50000d582e80e08460f901000d41c2c02c29a0b159203c03811b008442e8055264000340303d1032001404100b401000002c1d080c40070089894801c1c101c6000548019802601c043c5410884210301049480c0341507000b45501c100f02526991f6840141d200c00e0f82622038503840070002c488005414030912495008001e0410428241c2d2851401d21b55941050700b490041380740c01d001e50100f400c60a1440707807800c0320000c42d00b00a5651300c0e41002c4c042c1402c0380d0300a0780b04034881c501e000c400050040700181c1e410349072001c1200c0c4409038000aa4690025485003403420001002040007282c4c040d600e208290059030710f0710000590703062450360245481c01c107820000a010805003810149105501448241c48410584410b981c0341ca141c544010120820020040c543c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 637318965 1250 637317715 637317719
    0x191b05010516050405090a0c14030a05040b0106080f0a0c0504051e0a05030705060403110a030f030519140a05070203150112150507050306090711030a0320031e040813 73
    0x241500103034000d41c1c00c1e612020602da0b00b41010754a9118603c10181c00030f803141d0024600300d00d9507200160007012820500e52034500c0c02c8240c0581c0c0c0c401c81e1661210769854040c041401420050a400f4208a050015842c14030006050301c10400030810429075440e4415103000c01d10840507200101000f500c00c44000b4403665501ea442a102a0103600516101c10009101d15000401c2011a00d000d0001841c043c00c40c1c84414201e00b030107149075042083c000000001a90311080d04034094003983c0c4190b01ca0164108402c0c3c2a01400104403c100d101c8400d299610002002c4885038501424503a0f43c90500d480400c0c1041445602d84000d4040c0700000581008a81200d4071040c0c8540d10a100b521904c03034814045400698440000610600016400341807903101950842000d082c12400013100300d5841e0300e10340c0896003442c00240c0301c1c06010380820000c84000741607040c800d1010305619114800e042c580000c0300b080c90021482401041c14803400341c040b5019981c80001840c5003e13 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 637320215 1250 637318965 637318973
    0x402240309010204051e0108160e1804061d0d2706180911030103030c020d0c090e160b030a020703090b0a21230903160c030521191b 58
    0xd080341c416035005031031129203160a1000c06c10f551200c810161501c85072501d0f2812440968030020000320b042c0002d004400c0c040d940ca02c1007400800060071010f16841c941450700b03c0035144039000b5804c018103d4032080c1d41000c004504462002010b1400d5640807420301641841800341901011040600c1d640c0852078039880340042903020805100d9094680d980c898040440c1c04050985052035414001400000d118901ca0301d2507a000400350041e02070981c940881003d820b07131040d418a9920b9082108110f414413125100104400706103d1480c035140010322180700007014460043d078000b443c8000c040c060500d50010300211840c20340c03100305c000005025011006541074030305650903e101c1e450101c41c011550003001307018000c42c45652586020480304001f0340342c16071501017030200c200c1c40c030b07149103000b1221802103071803110591450603e10b003011902c27a0180c0d1108051030600d01d03440a01e01c210f03111042841d440c016418030b0148100c4992000d50310b010203a01b40c07008070400780 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 637321465 1250 637320215 637320217
    0x3020a061e0f0210051e010803041a090609120109060e1b040504021c0807031701050d0f06060815010306110a02061807170f0c040c0e0d020609041b081501050304022403090102 77
    0xa801e465280030301b5980721b08000d5030b28040d0744124440c03c0204241d160424410a0181c07000100c0035080504003405e0100282c0741d04402e03403e90102d42e54401600090100c94058a4840c5c00301c07001410081c1e030764030306a82203548a0325445010302c0d200d1011500b151130b4032540000051100d1070b038841050030f078501030041354446102980011155001003803151040d4a8481c101d54000b0140c198803504d641c0c8500c2d0028003140d0640d0b01c0c03036880744002180c803014800c440200d0f4400c4145910741d0b0541c41d02d0411180b80c00c101c44003040341444040003060f000140d80d0342010910700c080d00c21401d0f10207000d140c040b0b140c004034803244120750300491a1a0020b000c45032203143c01700351000c65000c44140f004469808100c1350001d40b100140343c4a034240208031a08942c000303070078076141c4460f4602080c152084142800d18905404c00008941c0d94802c046c3c030341008006100910394095000000e01038000600041d2203240124008016900c15401c0c02c2240b06901d4841e54403450080301c1e490003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 637322715 1250 637321465 637321501
    0x41a0d05040b0a0509030a0c0b09010e03031303030f0509030a0516061103090c120d180e0907030c0e06060d020f09102705100e011b060603020a061e0f021005 69
    0xf2190800300840c12160700481030f80d642003c00d1f52814440101e0742c0343c0c9880f40401030300400700755581e0400e071041e07400144000e510130b01003c005a10480c2251600804959a20aa072201945070506010781442c000c8111200c40b24503282013611280903034078801280000c180010505072070080c00b425072140007030195201e1000c10066500d5404d0600c1801254103442210508540104941e000030900a840000314030007040c034000c07140d58544100881745c10007a10341b01c095500c035030f40400400c5084105000030704422040b00340c0e01d00748030700829400d02a81d8036a5207001d0700802d8580381001001c00b43e42a8180082030b00d0045c000b060030103080e4244d500501044040358131904e00c2c124840080c07080442b1405410440a110320200031501c01c0b0940070041d041001c1501d0364030030000700032011880c1c03901a03440020300c5031542c0b04002c0f11940315071100c014003203241c1c1000c1c17034010004c80c640e20011160070101268800b03080103c1c03d0180d0a01989030440c5000280300d50340003e00200711b2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 637323965 1250 637322715 637322731
    0x6181606021506030d0c0b0703093216090c1124060a050d0602070c03080a0201060603140403021e010b18040b0109050408220902030103060b010e0f06041a0d05040b 72
    0xa1240c407040145911742c2d1200c5202c1000c2070201c00703000d0024100c0d103000e0354852407502c3c0018a08030f15076544d44a090314000c01c100d402208011181201411440d1542620030715801820000d140d1021290b02640320321a4802050b611855901040d002d0011034184009030382c1a0759026158407410500c601c54103032402c10400050300020000c1c2440319014082d20740082039099a442d2568860002c1d43c810300040340d00c0903d201002000802090242c40c01d035410740c0020038000d00300344009007201c0340510010241c440040030700c00443d40100e28510384c4c018400001c0280c2850070707000c134090b001910110b504601544845111880f580916a00503440303041c4250150740e84203c03071010b555050b50b010b488140d0070400014403180d544da4590692251303403c0010110f03681c8101d041203170426442902c100c0c0c1c907050300e02c0040d030b80502041d5403608100c400780d050100c05c4001c260b10f40903d004144104070ba548045050010b00010f65443e521030382403d00107442c052400309105003090721a10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 637325215 1250 637323965 637324003
    0x1407030c09050306070e0603100306020a050a020f010b1302070614090705030115050a0510020a061b02190b0a0b01020307060207030c030f03050c0a080c120106030b0f03010203090618160602 83
    0x4100c0f4680495440d0140c07082d66075031140c0035103180402c07003581d20142c480a50000d0b1407900100081c41d500103408003030659124103848140a00d400307410700d84500440c0001340d141003d03804080c4d482c400b540d140800a91401600e0b013040d850580001c0030000f010089030003d02040100d001000070380c2d181a2201034000388103a004110036240220000e0252550100d136118043c001400e0400b5100303a641000d204440f00a03440c4e4a42e5000c0703030700d1055032072841c80e03180a415820a4040285c42d40c6401d090080050000854640402401d00646004004c0d80c8a0110203030581c820030944100a402000c21035407251640303000303041d981120301d04502040b03900c034940c0d03819030281c85038500c135081090368186096010700003120003860003130040c500e1910a0150800301401d10314a180a030040c2d450008480b01007d04202c0b0320213159484600c6680108104080348601107555600044480d4080d107020b024598418202000d00840c103185102d081c0c0c00107611a4001401e00e90044908020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 637326465 1250 637325215 637325219
    0x90c01090603060e060d15050c04150c0201020a06180c081506090103051207020d140d020c0607020307030b04080702090a050105041107080a210905100e07060903030f031407030c09 79
    0x15016601613102c1d40c0440c042a10002c0c0d810700700a501c12a601d8810540500000c086001c040c085802c103a42040151a000c14203210011030290740501440303050070000c2c100d803a1a40005d658020802c00144210380318980780c3c08040b080c02a07008410340c000c55084000341c591150360350717483c0808800c286000342030000c0798580c2802012241629000000707440c07035151440c507101480e400032030100c2c0c01509446240000c0384039036201c0c1007810b4001010b4564845454002032034845008ad40310704c6083c007005207500503500015a481103e03484031039640c840c0c1c2d40782081600b5002d0208040d41100f4030404100040d41203902c020b06851003124100b00d8071100958101c11401002c9004060303020401c080f4440a0103a40f44107611a03440c406260445101c443c00019100081c008030b40790b034817a40c0044640f0b802402450fa03010380810040c1281841c1ca840240002802d21000d42400450030100c0c3c031440c03080c2c20000c186034624200032110304041c00014003c01c141702c0e0f1f84d800201f9078480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 637327715 1250 637326465 637326467
    0x60504050d0315230a15110111120a0609090506070206070c0803010b092103040302040b0418021012021b16060e1002213004110103090506090c010906 66
    0x10003e25040034404880964140190781c8002c03480c0d1100c510482030b4400c041c030310755940d08100340081c103045013103103100c1030035a00b020f80700c0350f030050346019030341d040c21904080c86411006481e20301c3d44e0b00307030151001c0d118100b0344401051144c010000c102d0070404a14180507000030400d0140100741d013210401d54406202300c441501214000307008107420401003040341c000c80c000d0070540d08000c10710f18040510041010303802c5e8094881c0c58103900080b80c100107502d4148075400d0741600507a81442200d00e022401d9683c8107450000910405168807245034003885000b218881040c032a00071550f0f000440c1340086140b4000c06003c200d841854421012225010341d650102d40c0180c46403100c0c800010104401128922a41000c620031600260a5100d1160508150304440c4500607610f11003236006072030407001210004c144240740b6041001e240340b19505e0a61164010f0b80000c0200200740c0102e02400c1841d4014219101c2c002c2440800303440851003100c6000700362100041c696071000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 637328965 1250 637327715 637327721
    0x507081504060209030114010f0611010213050103020c030409140604050705070213110906030103120906021911041409010e060907050d0f03140d020a1b0b1b04080703060504050d03 79
    0x1400c0c9000c0c03288102280015070180c02901302e04070001e001190041c0da008104100d035500b64071000b00e41c101c94908004894000c1581680c201829009500e4003070080314485810354144121810140e00061030940010180140d60180003421020b024100c944a00109014402d4510ba0300c501d1426010038000c47c0500c0407184c0280e40600590715400c509524100200318483d9401200c1d02c080203c803215542d501c1c011406140304140081401d1102e0a0042444d42d143c1c00c4141036610820b101c040803800710303a0349510340f41d1181e03c01008803880400b0901800003040038901e1a0301440a1000460f070642258410700d219008680700c565903a80e2650f95113906115040e00800011801004910b4418064010703600038103100d410718000780311100740d0b6440343c4c107001c0d00c040e8013003083c4280700e81c021500c440c415005c110f40d140300d0032140c84840500001a10802e42081c1c4004d02c9211411140c0560b001024020b050314030301d981e00e0406201030001103400300e865004101013400e503540030344 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 637330215 1250 637328965 637328983
    0x403050a08060402040e0f060a090e030310081501090e0a060c02030a0f09051003020c010b0603040c0f0509040b010b090f1c032309121908040501030e011b03092409050708 75
    0x310030342d000e87d22520381800e00e000c07000e0175840d00925215400f003003a14441c015910341c940548015942e03403401600381d0303000308140d401c07409858201c0c210320441c0840007141e107815501075090000d60620807000c200e10384800044001c200c20b0038003840380030054012000e0300200c902e030344516200d40c04101048822908501543c3d074025240702c1e2184040d4070a9010b0034600d070910000082c56800040050480d400c01c850442c7d200a05039010b000712290001c980000b450207980b04000c608050752500c4005005028400043c4400f04169246a40d108c10a00f801200039280b1000b1604824a10214106082085e4040382043c40003610403810684c005980415440500341841d04507400c01243d4582c010440c5643e00c0790091028413506140b4099044512a000c9990b9403443e000015003514029241100d490345050300c815020002031481d000149118070340096132141a1400e00c0e1200c5a416172851800c45800031090341d00c1340d030385c045070217039000f002161980b03991107003441c1d0380341401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 637331465 1250 637330215 637330229
    0x4020915030a2d1419020a090509010905160305100302090415060609050f0a032a17011a03010902010e0108070201110c062502070306051005040c0f0908010c020309190e0403050a0806040204 83
    0x20174006a2040302d580034061045592a1010800d40c0d20800118507140c00c0c1c100202c0d50f641d9070709024030800901c0c1c440e80c900c6214102445146820305040d040c501d0720b03200c00380c007035078001d00082e00300720003a0b814000045511104001c9240c0380d0304001d185140a02455000d110400485901490101480d404a075448001000c0d24000c072910300b00c0740010702d09094041a000c2c100801cbc0c4603403500f0f10a000100c4400005907801048030030300c040072100c813105402030f407400707400c0c0000d40d90203221505849800c1c203285c40c0c10707156040102d0042540311448002141c020032128280030001c10030602074a2002410310302000403140078581c0c50085c80140000d030740060750030000a031540e08010f034051503c6505461003035850000c90241c462040b16400000c003415103040102d50030110b65005842400d0081104816044010f540e87c81442c04151140f00c0d090703515010448401c90100242c0078800c116180c40c145868044c05681124100e640414400e10008509040c02e2003524126945 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 637332715 1250 637331465 637331491
    0x40f050601320301150602030a0f0e130c110d0315061715040209040f02090a080d1704080d06120326040303020d0905061f0504020915030a2d14 63
    0x700c0008214a021802d00030340554a848403035005800b00c420410080c00b4940140d42e40d5105001c00800e1a10744846200c2480801131030280b5585810125049120040c0b100141207000620191038000012014003200d01c141d01d10321072000c1c2e05402c142c80048804560340c010b16190313035080c2d400040c602030b42e40c840002c8000041c03504441e0401002d01c254090303c01407501c0007107008181540e03c40343c1c49407c00d80d00003039540c501d410240b128000408500d80648454441c0100040c40f07040c088952100d580910004103003031011170411030310002c100c1e0004100041d511080f0100c5503000420540201e8460503881150b40004416109900c17200151102640e4803a40c0c103400039000050740600140d0381d40f00d2507000071410841b45d402000c964041006440f11b81c1c1c05101103458039040789020701d0060081140d40e41711140780800303007682043e1160310390380c0740c01a010003000401c015028a030030151940755810030b40e0001d404414500d0f82c081c803821081c90441c1e01c2e0010300340c0d889810240 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 637333965 1250 637332715 637332779
    0x10e06060d0c0518150102010b0112150503031201060f020d1b05030c1501090e0102040803030c071e110108010501030b0102060118060f08010c0306080a0c120c050306040f050601 78
    0x3401c2904189070718031401c094208aa21180803c80100c0e410012083e007584540902086101c4202e503005074031790034030083c806265440002051103c58a03d40c062443d2908410030708600c240710303e14003500000e421030b0746480c1c29081d04030b10001e0178401e01000ca40c40000c40440701d8408a400e40c005c1081d61200c810200ca42281e4444038100c040e1700342c885000c1482001c111400520041110200903820500b4035414915003208a460f0112040c0c69a841040200715048000c810f40364850030110340c01e078071400541040c1496845040c502c14400b8214540e6008014170786e1403501c00b00c902aa00d0f000c25a803550300540c1210f807040240307400b6074001d00040201ea80c140e40e9046520400780000700c0e015a80d41800250041203400c1592540d44501120140c2540b40c8116002070550000420700d12000d034a900035080382e00e00504403000a600e5031103003071200424031000240005411200180b41038104012103203615130045590340555000040c0ca200e04040b100c412020301c2b402005014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 637335215 1250 637333965 637333969
    0x1051e0123041e0b0906030d0e060a051306020a03120204030f06110409061701052a0a170f0405100b01200f0d02060103051005070c02040905070e0c04050909010e0606 73
    0x11191101c8180d10a0301d07124455500c1020030342102004040c50700c01310310300b01801c00b040840203004201d10b0190740004865804a42d0100010092150950304250707a000e441c041200c0c24418000c2043c6048a06c040000b0326071703800140450814040da94002104600010300420307481a4800074147d1f8500540030404600c0c503620052845548030740007031600b65208150741c20303160f41e5840f0503042c4c104060003107081c180078001c881d44448814a1032030b1842403c48040c14900d0740079045010502c000c582914101d01032104821021140480a07000740f40040a004c1c414000311402c49041c000e0300540c01500003140600700071004161a04071030240b860148103212015500d102c0a140f00d00206c0010941003441107121541080d40039011660540c1011460818040c1000c1c018900c2d1104003c501a8440005027680740d04640200310b001d241c3c1030030780c603129254001c950500007004c14080c001c1101c00c01442110340c161143d40c1955204010365013200c4940d00058002d0704103130300096843c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 637336465 1250 637335215 637335269
    0x8060d0f030e120d030b09060603091e1204180c0906120e0a0206161e02010212072a06120b0f0904050304080316060513031416080c01051e01 62
    0x11140075103000f2820f010441c0d404d1030720032070b08541400b21390345401c0e02d08030b0305110880c2d60f40300c4000d5502c03031b01d10300300b08881c80d503503040c0e00b56024819460a031a4a4441c80288603a0401c4001c101c1c07442e03141c0b07440d0301e010708424042a521a56051509980c00b901c64041d449103000c80341240c8801001907624884a401742c6031400340e01000d40500c01d5100010390303424026080c1e40d112020003880034000761901f5801030b0b040d00e00c140c00c101107803080b05006030390018240c0300711612841c0c0c56803a0461440d0050f4440d0754074001d90250402c4000c640301110b00c400400301250215541e003111041181c6924088400d014566500804820b0f407103002030810494458000303101e02c00b140d1403c2c0d5111140e9003107401c120100710a0b5144d83d03822100b840218041c541e000700c81161420415181c50f98090310036080d0703181c02c4c1d141c140080307420310b043c443d40c83d010010301c4e800c49030040d914540d42180030300a02c01114039140040a454200b00140f40110513181603841c040125424041d14a5080b201 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 637337715 1250 637336465 637336487
    0x111010e0106182a02030c100609060e160c0c050301090308040c0f0b031317120604110c2512051005010f080d1202071a061002030a051b0c1f08060d0f03 67
    0x45d8802040074400c080000c0200310103070104454006001030901081406075402c5a00c40c100f2103407100d0500c418280700c0b1050507507002e818203250460482902c1d2964101c0e207242d00140d41540b07070130702000906801c00c91052007181320344890030340b20b9110b4603801c2d002c400c07074001e81c5208a02440080d0020021811203c5214003401003059103a64200f4480210703400403440444801b449030910a0314209070044010102d40703504114144400c100c0820341d5a10400034100b0140e000960000ca0380a240781c1c500064466409181030420b0a420080d0ba541c2c04e250646000c9454507000003180c0f0004140c0c402591600009040e81e603101c840201c2d024001c3c205001030707803a801c225050010340c01d040e13058000135041200744c05600d04038081200c001e0f86582e13020155001040320450060303201d8101c4030500c01c50a80403111503036000c1340b18604941d003c050742e0802034184207440d0003008801150710b00c03041313603030340c04440e50340c4006021010203031440051801d0b681c2c81680f030001e80503000741c001d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 637338965 1250 637337715 637337717
    0x207110a06020c1c050d020a060b0301062709060c050a080906040c0b0a050d0501030c08150705090618040f0209090127110d150503070f0e04110111010e0106182a 71
    0x812844d46494503030030700d800402101c000d40e1100d94040308025030b03406410a0210110002c10000f8070700340038403200c94410705a008240360b610000c04c0141340c0a5210400c040d4004000301f060146070100600f659000420b05000b00b0070032400120441400a0500c0c4641d6108a641c01742178075201240300b40d508101629800c1c000c1c1030000c009038100d41c1c0319a03402540551101003c9925100c40c40d820b2440350f81090301c40310980310402544030703042001c44103170540a4032100e9841c82e070301c0f0b00078180300105880c0302e6010f810501c201100184035005088900d00845801405903a072f4845010464541140d2198000b11502016040e1805034442104030507004146407030490010681400c0314440d60800c1d000503050103042c462400c1c2084400090000c07003403840000e900300308600b8204a4000d0004010303140b0842d100300340380d100318880034110300224000c1c000307011642d0043d070190980740103000019803c48245850f40015004515194958141010a0080038400d007c8515501a00d0130 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 637340215 1250 637338965 637339009
    0x4031701030b0f071b0b072a03180314030a0f03020306361f0506031306050406060519030309170709050406021b0c03011b0e010c030504050d081c06060522050603040302010207110a06020c 82
    0x3001c41d1001805206080cd940042d5954036a41d25001d04001c840700e00f03400801d0b10600410180f500e9884800048140031054405a00301c1c161a5016480c6110300071500744502e00b042c07004102e01c9603079004040e2800089100d6403515241441080c2c003045507142c8042e200d50100c0c0d008641160301040c1c009014400200b0302c039440f00040780d642180301b000d643c04e44459030407c105165010b184803014042c0d801d01d202400d040440040d0381c4441c10702807201320f01d940f900418200302c641c0e411a002d0b0300180d000e4484900700c0d072451544980508240902035401d0100c1046600c15044c10340300f00c4240c9442c0c80c0c20090381c0400440b07400002e96003c50070300008100120b9140d031038641469046100398401d0f5910489a000039001c510085c039001019400c10500340042070704501541c1c03203644074542c0c03803951521440d81c80c090002154001600b258000050000b41503064000304031050080b1610b81001101201380107490f00320348102d50058012a003a400306180100d1140800e240d0a03040d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 637341465 1250 637340215 637340219
    0xa0c0809060412020301060e28020d050c131202060f0702040e100b031905120a03090f0b1f0e010504020a020c0306010e04031701030b0f071b0b072a0318 67
    0x410207550054000ca00140c001542400851809000fa240a094010125161400e0203444902007a6070407404403540c84d0301c02e2200e6080320301ca60582e0740d03c4151310400e1050341050416102640e1040780e040ca1004405480403c1c1401c174500a5090302e60301401e020302e0040000b021203080d4000850403a403047d201c20002d803800e50100b01c00c1c140d03401c991100180c504100c00030185001c85012040100b241946500c0c804a00e010a011004a40c809802951948080411401440100343c01421001148401014803602c2040c1038882c0c048500401c9582c281c11144840c007000e41c0c881c2c0101c0b0000000140071604294010b8402c0303218600490b0040300880000a0401c2d009800c0084a0070b2504100801d050b444200c00c0c0504032600c500408950454a03490a5100e009042010302000c0002283c629032040d40890010044600144508061482e01c007040d91030070764601000805984c041c040507044108072500350651401d818030401c5031036605440c4400c0c210600144003400881c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 637342715 1250 637341465 637341469
    0xe0105130308031501080118180f0b011d1506090d06021c060e0c180d0b04050f010b060f040e0402042c10090506070e030319050403020a1a0a0c0809 65
    0x44051449225440d4991130944412050455400007103810043c01100401050714125020744600705600400b0031015510320100364207460249000b800e071542c0480c035809000d0b108401a050381c1d000c240c41d00f0303100741c940079411a5120583c0c81c260101c20400c5541510310b400001000510310292001d14041380c5511500200d0f0000603011311444100c00995500c01c0261040c08050602d00200d1819410a81510503942c05094202104503800010061041d41c0d440071031903030560b01a43d508210b14103841d08a454080c040b108a05942c284001c01080b4540b4400356024034004466550804c0d01e0110f04120846e00503105a0b00a50f41c2c2c0949042c5140c60310241c0346041c01291440c0301004004c3c0922f2034401d0001100101030700e0118a100040e10114107107820075500d1400601708108030b0700180c1188558010796211426840300d9419850b0400c01420840b8021621038002a40d2014000100c0c101e000c4004808002001110319443c050743c4005600c501030140c8504101c00040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 637343965 1250 637342715 637342747
    0xf1520160f090203040b0a09170c0a030314240d0203010e07030c0f05060f0d110301060e0a09020c0d050313020a0303080a200405011b0b070c02030d0905030d0e0105 72
    0x2016210611030340c0074046507201d0341400000b40701e100002c52440c42c041c1c03a5040c8000024220590f43c41c4c9525815042c002010748180e140b2200c1983d1a54408031461a903503501803215040300030a003041914120240c1a80b50320b80704941400340109c1c9061408070790a0341400003010b1030b5110300c40c002440b025807024440d15582042040c0205031003815030401400d00300a0b0b600130603041000c11024043c9407940d0044d50310b00205c4204940c0c4441d00401840003034681c03140903a914a102100008a0170b034000101d401484040d13648800c066280c1d030450003a881506034611083d80926405420541328170000c690003c14807140c1400d100080d40000c4d86006981d2003a80004d02000521070500f200b0f01c54901c868480480d000319400401d1341c250381c9801544902414000c00c1581d41204040c1c032414011600e80c040344031416460042c0303001c2c10f04d4443c0c2c442680284140d40d01c04a00900034454801940c1c4c0080c01003a4500300c40400f1030750b5200520b0040c0c1084804e110303259020307903121 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 637345215 1250 637343965 637343983
    0x50a0912180e07050a093f02090408250503090108091006090c09080c0a050906040e070b07060b03030406140706020c1507140915030c09030d050d060f1520 68
    0x20b500d071a85c900e00241c008215a0150b041112850f0300090041c07800581002d960fa50b0786400752248049240c849625600c4461291000e900f000c0f0940420040041e40c400400c8007180c1d00c506079040721501d10106001c40c41d684030041c0b240d4001c004408056024410035680196410201c0f02450411006001510150707406214490b44400c422884580c0054015020f00612401001c1400014000483c8c03840c0c903115580c0601c01040c0418240d44480c5c0118510b02488400c490304035580d40d8600c101c582c818682034403c10310302145c068961a000c4115800c50b8019039428031910751011980c01d807036103c10812600c40c0d41c00c0101560944040c489460b03000d40d514807580603407603d20806005913010140f4940440e10800c8000c4130341c0d540242d403c46529248d00c0ba10b4403640c900001d03404500c40e41c042e041d41449140d400f0210f86501500600700022808400c0c050f040d0b54400403a410b004a004c3d0640380c07150b140c110a5814410320100c003d0907c501224094a40c000400b6070804100c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 637346465 1250 637345215 637345217
    0x20405030d0e01020c15120703110c06090c09240d0f0f0201083303010b0a03050325120302031504060f09050c04050108070c051f050109050a0912180e07 67
    0x882810142c940e01842019070015041d00c2d2a209403298000003c0144161030102d41d240003101c0100d038045120380c0c007100b01c0824104a0503591720302e600001c0d50f0341c041242c000f513442c41000600c0040d03050189100d030080d40302000c0c80301580c060250700c4103015082c918250308000d18005c0c1402140102c6e9002c50418012400c504090b20203000060004000600c01c01d03280210303c1d2101e140c640c0e12030080d4616181c1208080550711443c000038013429414001a074842e80c04100441800700100040c00030b00452000300a80c003443c41d04460258070a400084c00b205440403500d10403e0180c2c004540c000b90819104111740f0384200010100d60346600941041e6584075028407410000340315194201000880990074145040c0c00202011401810102041001c3c440c00040140402c048000c03080c4031035a21031036654003001c00004003401d10803581e101e0f0812001c90702c100c100b07100340589143c100c0d0389404100403d601c20b1b100303401030040c0c2e1074250800b0440003e800f00c030910740901a100c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 637347715 1250 637346465 637346477
    0x81201061709101d01020c060601080106030b0f1005070b0f090d02061005220507020c041a0a0308090d050105012d080d080403030608030a2a0305030a0b04020405030d 73
    0x604100401c03070320480c90080e034040080000e110301c0010000700828500e6007000040383e900040c5000c41d4010082ca4800941580086400640340c6800b10301d0601c10f040a98491989070799403a421815030311310803429904090f058981c03c600e400c1507000c5c0403031111282440c40c07400ca003580d140381191b50102c03000207058940d8002d010001d1414030001c0325080e1980b00801443c1000f071807042441045102e5a07100780300990320140260710411a1220f009400d40c8100040e140180019441d07035200c0c601d451103545404005100258920100080402d001e8600d40740c650840e80d07140c0040d440240e07516848100c003981000000c400f40942400703450303044002201c0000b4100c0e050350140b15400c54545440007510140034421000845415a8a4900d080300c00c0c0c0d2220700b410b400422098000342100e010004400d04900c0d00a426880e2100803e401380520700e000085c803c1050380e51110040010f14204080f8422103d15085030394200c40040c00180750582d1440028581820102d614000c904 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 637348965 1250 637347715 637347719
    0x302100806090705040506041716030b01030308060d03080a0506010203090d06090b0604020f193c0306060903080903120318010b0109031113150f030c080c1807020a081201 75
    0x20000c0d0b900360082c625040040c141170034036000508074042c50151304240d9a440d1020143d40d40f0800c005500a400c061040d581c1039100d00700203a5224003404158041000710300821801d081c551120b900030354142c2e070751000c183c84031395440c0042c001c0901041d04512050103041286e03a5005101d00819104000001e41d80e1114501101c1080c0003c0c41680318620500080700c90b06090b108491304482414a0342001d2288004c040d5a07002c0c9605501e041c0300220900079103116041d00c00c0c1200d031500c801e02e01e01da50754002c038120b044c0c2e4487c1c0250800141100800c000080c2c140002e40502940101078420303c2c84107400800d619042282d070b440c51083e0790070200c01d40000a114110345400c0070b00c1c2100055065451b500d2400703036041c1c2c0d210700882c090681001955a19444040d12001c0c04504400481c1c4e580c6010158040b2400281c401e0000340c2d2000074a0750000401a0315620060109047c000e08850090786074100180804158000e0141a82c00102c012004018801400904101d254 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 637350215 1250 637348965 637348969
    0x60304061814012f2203050307030e030f0105091903030f2f09030607081f090b13090b34090e09010203191a03010f0204060e0102030f030c130302100806 67
    0x244109032003200800307031150000c84d03100c1250802d048000002c0c20340b80d101c10061741d100056620180083c00042905410143d20402082500104400312a12030450300303002c5d4200c07141a540820107500440e0000030400020100b002843c0c004d00b00012104000880741c400c2e1058111600d4100480390420340c0d1500398141c500c4039038502c2c94052418a0f207000c000c42c0e40c0314805004401031158000024000316110092402c42c03003070010b090540d1381c0c1e81c1c0202e00090070340402d00b6407240039024607202d0a0381c0c4034401c8032299a00400215900d03218401580000801c9014048180d840da44030310081584840b581d200448043c0d9502d80c2d29481d0008011071200d01034541d91580c0d0040044c051000c5c00c002d900140c49012003400a10f07091541444601702c50311084194041d420a2040d03c282030103a8043d008454043c0c03500e203042d640c0d03030004a0300c07445203000254801c030081c0f002c1640c0c05130a00142000301c40040c101001e8588030740000c0c0514500d00178000c0000c40c140100300040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 637351465 1250 637350215 637350251
    0xc011a01022109010c2907080c0c060c0a020703051504020901060809100b010210060f0e060102010228140c011a0f030703020607050c0d210e06030406181401 69
    0x2d103040c000381c00c02e0000029150a00e20032410564104800c03a03e9105c1400845107070303070081004c4145068034860b03031018800e1101c00220782640114180c0000074200e0b41000301160703003590158000d800940e03034840c031001264005d41c04401c00c51007003d101000044040040c01c0c00c004800200c030b00f261906204012004405130001000c00c8602170a015504000160240c801080c0180c0803415203034200040f890f008210481b034401e07905100d40040c50120000b900e10540b401021540060360f50407005900b42e20800405611400e41c5803140418441407480c00c03902c089041c5041c100507009140c942916030860240340c41280d6448401101600b61020040300303584054034021b10341e400c510002501c17a00d091201078080c0324006500002c101d003e10000c075020000905815140c0e80a00300005080c0c0841801e9840d0385c4c0d800b03481d981c05401801c0903074842500600744c1c0e03d0369a07155500400307031140e44100d010f803981d03952811000035891041c102c2402002c0e00001144820a070b81050302f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 637352715 1250 637351465 637351483
    0x18010c030603021e0d0b0c0a09090207020d140106030804091406040c0819150305070f09050f0a0b04020c100c031802030d080702070b1206041a0a03020906060c011a0102 74
    0xa041c5814020001070b01c50305907419503030f001c00c1c98000840c0c01c00ca0200c0d5a0f00041c2c08020645070541d4108280c4c540c8030f07005010329013820b07078480f690f0036119101d4404074480c021020794000002500c2d00000ba001e502d000410440d944000308899641c5d51f9003d2950704140c010b50b41c01525803201910904980b0803642d07100000721401d104600302041c018004100c090401c4010800507030034040046007541010481608075035030071152560300e0501544610190243c0510101813880016112510b40503035801000028400b4586494117030b5218000c05040e07030090382141e024070901100030810300204c2c40014044c000454024040c100040464003000e4007490f044151451040242e1000905140c1c00c807102d0514034299141c3e038030180c1c07400c0500d6012715806040050301c081103035124442a8007070502901c6c240314002500091024640c1c101d0131860b00000f285208002602d02101da0580051018203642e03d42401c103001d1034291807800d1005a141d100003041294203503410081d40340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 637353965 1250 637352715 637352717
    0x70803070504091a13180f11040c050a1b11040507090e07030e030d09140d2303060102100b040f09060b120a030813030e060715060603020a0c0b10090518010c 69
    0x2c1c1801d04d001c0003c041d201c54100074a00180d0304d1015031034446100088501d404d07080840341c07401059510f03020b030302c0c4682444410301a50420b005590240d010b901510301e203a040c6e0701c401c0129144540e031040240342c500000d9a0709169a00084141d40741c900c40c990144145a80d20b841080c201010f407403041002900010405107028505c251000f004025120b41c1584000040384000c0300707007402d10701b01584030002c1c01d03d805208568103074207400803200008114080c441d0050004d082025000502007142d21a01582081c403413100142600e920003000708200034000140c4441c0150f540003110010340c011510690307540d91040c02403a141c18030700090b0b40c80600900b407550721650010f00703100000e820411024030220704141054014041f0403c068070241c456a241c80c040d061860b10f04405400c49170510785010000304516100b4000c4644802c4581c0f910f441c2c086171a6510780200d80001c080c03504490202901080c1c03007483c0e004090041d6043d44c01c814064280f0444142180d0032040914 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 637355215 1250 637353965 637354001
    0x150807031413060b03030f070b04020406081921170a0e070617060d030c0b10120605011401090501021c1202040b03010810020408060f27010501140d0c0e0402030307080307050409 78
    0x690fa000c1f080807070341807660000580c0d1003900c4a1001c00c0241a42e500324081502803040415003801c3d04100c1c259910b40580391407800c41c9117911191313400c4401039245c400002c05c030703031a13034580200007d060f290040b001500006036a024149264104600e580002c0700003075080c112540e5941d15035010f903402c007004031111104c17000165400742c004d1048110080034000800002901c9003007440d9404003d040c16224030500c00440d280c15001044240101423400342c050100d2911035119031000010b03528103030020000480b52010b03e40801115511007002c010700e46000300300c0da05041c005080180f4101041310340304c0d410012858180000e620303003052880d1052100b088400740c00103082c0e030410740c90500659940c036801c00e00d00c2c0440e98122280b04990240258001761041580024125030800445030003080003441007240c07646101c2405822052481000e10511103450382d4160040c0c4001c040380d00d0075074035a4074440990422194100880c2011070708010f0741402e07004401299001072050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 637356465 1250 637355215 637355227
    0x501141009060b2b05070e131407030b2214090a0f2405090601060e0f280f0f080120070f06060504020d021c0501150807031413060b0303 60
    0xc40703860141511340c0340700c01818500c0011000310721006200707132000c000c4240000d1610b52000780141d100000c4207030140c8060741c519190034800c2d1182450a9a040c00c1801d81c40d126200100c000c2c00c608418030741c0c080c1000d02501041c4003020005d41480303101040c04a1100c00c00b01c0c80c0207600c60000d19490180d040024134034000f4451300526044658484c240501c0e0410225445590300717010f0080c0303000c5500d000103229405500064180c122402d41d03031034842d050313042400e02134011422035106803c210074a000305e25802e00451060710101400c4c1c14084659070302c5d801d402c01075000fa03110101c4040007207418070640e602030240304064509840e501d5009005a41000c0079441409009404042c0d0b264000f0200400c0c0e400c0007000b030034000d105644a44100340c51400a500104860741c403200042d485206d412100c0c06594100d17280d007d03a0610760a0061310988040a00808078810076641d180c03140c3e03000ea00c441850307004811a410703c0800d140c2c4d1b80f52200460300d06000740382c400ea20034041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 637357715 1250 637356465 637356479
    0xb12161403070303080c0405060a0e0a0f1a0c0c0619021c05071b090c1d04050412050d0b09070309050f1b120c0621100b0f0304020607050114100906 65
    0xc50b104881d814a04104c2903618403850002c680110b80105511120000700d218880381d0021303040c4800b5000311101200c00b0381d00d9049203aa0a620710482138120124400d80c1c42c0d0040103c090203003040c0580079105c40000b00000100c09900001948001d98090041c0340a11341e0b040040f49140380c840b504001038103960707142c090954003846800903d1820f01030481101e1f00d43c004d500000404106500784004240c0900103010350300d0400c0401d10350030b034420303a40102d4903080c080c03e03000b41c1e0096000d141c04240e0000071900b644c000c4101000c05921601c003581261101488507100384c00607540020450074600c0c0140c02c0c121140715400c0c1030b9210801e007800c021080d10401c40420404c0302d03000105035801a100703003000c5e403480030140d2064000c55050001d05002000010440002a42030480d07030b5614803100e038050144c0a1240e52138818450840f4400c2e6540086401c03c2c0000c203041c2c02c00840b40d4409003502c8401101c0c002443c0220280551184507040a01c0039103500d2406011003400c105d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 637358965 1250 637357715 637357723
    0xa06050117090a0b01081b0a0b0904020310120b01090c0c03021005130b040c06020c12030904090c03060513021903030806060901050705070e0405070b09010503190b12161403 76
    0x415600e2101c0325021400185040042c500d07440d600c851840c5207582d445465a844010108088014990f8012498058940f50880c0c07015a01c00c00503050602c001c41007484001c6d0002441d4107404000d806001c61104c484c0e40401c08028030580524440d981003a40c400152002109058144201c0c800d030640040d4021070713950a018000e250000d019940d0142c00040110040703009803411619909200a20100c11240741c281c3e4925001c48200e004d158061100a80c259918101c4680040c42040e901c0e00d03003901702d441c20301e000780b2442805e607840703031107413400c8501c02da611754103003d00300b2001c00c218106000204c08401803607800c03024161840d03d018080100040402d48540000121202070360f004400307503601d46400401f2601015112189240007800c10f80301a903c9108500c4009201c0c1250000c0380c1310f03244182d5642e03055480b04001c10015412002502d800141c0300c2c2c284401075101c4c04050082d041c0d41d00010004900380d6000c140c40b518460f0003130100a00d00d5003a601513610001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 637360215 1250 637358965 637358987
    0x15070f02090c0d0c0201021206030d0801170a0c15030506120c042012010806100f05060a02071a04050108010e13021e041802210601060c02060f0f040e0a060501 70
    0x107101c112041d0b4800a86029a1290b40b200d50b848038038000c03c151000b541580035080e0000c0075038001d47c10703481e18030030907035180c4580f03042c04000b500950050161000c020342180f1038100e0741007140c015079007540e6031000900e101d412003100c401d0f03d199002c07207a40d491301507260801c0342030f03036407290840340d07051580e0b168a040c041013070203a500c51500c021600c0c82d03c481c2c2420403a0981410303071544800300c0e104015123028800c00c402e900c02c4001180500d8040e44a03813048456680c0c207041568030b0b19003804569082201d1010079070050403000a0709940e2503020204c5800b40c030800c41c0d599400c007400908484010b0b044150202c0c3d00c40304200715110003d035640301142c1c048400c000b180c100c0d2003003440307890031201140707800074104400c641c2e289002c000072403d11752080340c500300359150440d5401000c2102c0b40b013100c4a50b20003001000050300070300e074076150b80e4005042a0b10b0081c05d1000405142e01c00003400d448200d00050411455441814507500300740e03060310511116291000081002c0014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 637361465 1250 637360215 637360219
    0x504021c030c0f0614090c09010501030b060c060109020d1a0901090207140f10110a021b01020f071401020708030711150c0a0501050a0c26181b15070f02 67
    0x1920401d150155090200e46580110300380c0c0e507200c4034a0040040d12410200001020303049021a00002005c1241c51480b80050b02c030345050307031032b000045019051080743e65822000800a58414020502c8068080c054904000d41d03103484041141e01100e40008003080d00411030003881d9007035070310040c29a0450745000401750b02c6010300c1c01e0400d5a1052264055024030504c5100303881c40700003003200210704001d00401c21540d00c4480484001d840360800300300050300002100c0d02c04030400c103101c40400034113204039480c106e68000240d1801e59190405054051003c8100f003d03503904020f0680036013800406542403030500d5a500c50481280030317240e4032039416049250f0004000340700755001c00c14484101c4814104074189140201320036103202420b5418500010f41c0c550140080c603d072950f00307401d400c0c1040341500303002c0002e45020f492070a030b0100c45940040c0c640c0301000845040c10040c940003092401040c1009000c8842d050f144001400900c0f50402017001016a40992601 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 637362715 1250 637361465 637361509
    0x110f0d12030605031c1b0803040f1707110a0b1c2a0e0f04020a0504050d0c030b040c060306060318080702040b2706121e0705130903030f050402 63
    0x110041e405071000da00400d4051046005c07002050b522080c181701403054030345031001b8444510711500c03001c50b18074070b000c3c184000400105001601e00c031007120500d8011142018840b25042081d007032544000740c161580012050190741520700b91445070014240700e08100d03d0509104000c0340110014203880d0501c44e9240038a4000307400400d5500d6591040001301c000701030b01c0400140c5103054101103140940c40c0204546503a043c179100711058820291200c80c10701345030404201c0e45a07440031044510800079400000010400340e1424001c520612400c02d101303040500c0101255042c2d4840401c044c10050102c00d140340d0400540c00c1640c03c103401d42d07510b8480340080b40203045d4440c9040d800c05505042e1440801d040c1540800c0500003140200340754403030804104406003441780e1156a074104a80e084185030030030700000c036410039240550381c4299613000050907250b004490502c6050b10341c039500f001c040e8544540400042051410401800c01da00807441010380c0c0b00110701d03c0c0300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 637363965 1250 637362715 637362743
    0xc06010e040f0f1707031205130b0a0911060415081003110603040f050706020105010501020f0c13051f0602010b0406060f1707110106090b09010e04030e0603060609060304050a110f0d 80
    0x151401c44580703900131400d4603550881460300619117510061510310851500002c02d803959200d00303c8980041d0400351402d01c2d42c640041d000000c00d0500d00c215030901e413a01000c026074a910000d08010002c8401ea107001e4801880c01801c1c016000746215244007a80c5020f000040136900300c141d4505041d1001a200e642e140f90914010140c450090200d1041420002c0c4250f81500000d050740c80aa0a403046000d91b49030f610382d40c00442c0c402c20362180e0f0038045105080c1044e84010350103060203440c4901c030186508034194904031900010010b075140c0403001000c0c02d040c001c00d00241903e141041500f50780301001411030b8410100620007031102800314812500c10a45001c084096800070416556280c0c449402000355610036800f440ca18070002501c400c01180e00c511440d05501ea0048650981d4204205a80010001030f40044203200c0032000d9100c00014601c02d80c4900c0003080c5502103420201502044e5001c220b2040480c00703c000c10b5901d81741601c0070b400b680f04034240d68840c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 637365215 1250 637363965 637363973
    0x1510080d20010513170a09090507090302063c0307030507030204050301060b0c010c02031c0209190e09210702090603120f1206010309020a06080a0b150c06010e040f0f 73
    0x250315040071190541c201014420901d01100c0c041e036045101e42440c00040da0780d403151141d10b01581d05008040b520042d02040b442c4081d0300483d61018080c505500c00e2030b120750003e010b581040088401055400e01125400490340b04000d081200c00102002010703c81d48080c00144002001c040400d61150085207100b8000c3e0180c0d0302910000b0000e021413501d030303c40c002c0c158112080e010002c1d030900c16150781040c0040f04507604410405424200780f004000620040c5d07000c078040395002541070880d4407400030683c0d207100117040003001d910103e00f4950706c030f98503105414504618110f050350320b40f10600600360071100141c2d816565600695101c00c0000d06010f0b900a0214000740c00207205868610300c10000c180f9030400c4203404002d43c0b81d090044045502680c5d00a4204c00035001c00d12600d8040c1181562000d023080c0c020400c0c2c1c82440204e00f44554000e00c400c2d117042c02081001c100c1c1c001b07100c803a0141c96000100c800515080c0c880040300b42d900301c0044c21210307072100040284 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 637366465 1250 637365215 637365257
    0x105070201110102030a36030f09090f02090102240718030804060f080702010501030803190b04060f060207051e040203041e0c0603110a200304171510080d 68
    0x2c2c0710000000c541300d00c0d00100320b0010341510041094140780f43c0c9035000d512264605524078240d50008010b408038081c0e901070300d035206500e0f900c1052203000080000c00f4951805034100c000d0b001302c2d016841e40c0c0c48000181c5031420907092241080d80320000921008862141d079039016440c4d10f4648607580c14101124800030031904007400b0349000003004252686c1005118030ac280c041c0da250140303581c038824100e00703c1c0c2d4203000003840329004101040340c4c0500e80038948000c1699140c0014510b05c100e00290881d08940d00c210208800b104040050a4060082c2401440c0580702283c5104c01c9150707141c1d1264401c0f1489202d103a021000c00d003031081c0d00c0010751000c1078244501c030071183c20b4142401000140d00c14540001d0500488441c20264501900c00c0c1c06d080745c03a0204c03d0041000c01000007607038210200058842808000b03182c02d140e016120311000303620090001503400703806025940200600f24400c005100d003041080c8440007400e24100c0c207071460842280c01c2c0c004506828 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 637367715 1250 637366465 637366487
    0x311011205160513210219080d0302032d0a0516200a0c030602030a0606050c150403110a06050a0b0102060402010203040603150e0a0b03061605041a070b07020304171204050105070201 80
    0x2590354140d00c100505200001e480c005c40d00031039580d2802e202caa90440f5114049008003490340d0041300850380c5050082e0040e641042c174045140411910313100e03520b103039a060090517282c0b451140003030040400e1135205450304030414000094016520f0840585100c0741c1910401c280e003448114154290010b00038a40c05c3c540c44015000083da407802d0200181d00281c640c0e41e0010302e01000007032514080d8040300d182c11001c401a103ea0803182d074081d840102c00070400da0611442807480741d2680401c5c031059490b0361244500141c0c90a1081c0c0c1700045845410219041d58003a030103210141c2e8000064800719042c1c1d24011413541c003100c0a410030000c0e00d50100400102c44020b01508007134580040787d01c4102942140c1080ea00c130764028105000500701400440c400300810f00039500c4110001d150900040c150b01d2402803d541d43c05251a4112008401038001080034000d8030308800940c1000490f4030010300c0d000040f0850308011344030318440d480c1804000103103c0216400754206d41b070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 637368965 1250 637367715 637367729
    0x6150f1103180d020409141006060507020f0d0c0509090d0801050307030507120602041a1c150b070201210605090709060f030203090f2a04110405040e10060311011205160513 76
    0x40341d8070140f041c7d40c3d00d07446000d01031100c601f0900007240080c82501a40c00b1650014000301541c09801c050122424103072400f95641704146c1c0e00815543c0703540f220640141e02010040c03042c1d00c0d03034a900520b80f40042e0441c51181c0c00800040011420004020341a608107070212100040b05180c200300920803548111092000c2204128008802401410621030240f0300d00c0f41c6180c03200189001c540c043e100100901c0c10b0030000707008000822004d0040710b441810064205201da6070b0351f900f0200114203414101e07881d00800e2009050401183da0425010b0502055007400d24a02804108118240208040c0d01000107662900100b05214050498000780c501500044428281c851030405940700340000c100c1b030806940c00d151091642110b4042a00e900b82814841044050242d608801c81603116843c00018140d2092140c2d50080d44280300c002c44014040002401002002c07110021252920080080b50340030b42460490070207103441d0a42d9501c1e000003c0c01d40c15000c98108803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 637370215 1250 637368965 637368983
    0x14060307090e040b01050a06030e21120c07050c0105030408090d0c030f030201050a1b171b031e060d0b04060507090909240e10090606150f1103180d020409 68
    0xb0091001e500c041301c1c1641c0040c1c620f00105038503050309509403034488200c80e58951214001d004110344402115400440420060307160400d020000c2c08040320956000c3e4807080d00203040d0040027000c0021081d684030070f00b030990440c90f258071404c0c1380d4010b00481501644620840b441005014000c2d40701940d81710070803028403981c1d401c000707009000443d0074022451810003000b4031488410100c0140c07290340c0c3d0320744041c0c070b00040741110071000c080c0c000c0700c6943e06000041e00124650000d18840c00000120040904540806641e0b0417406070000c0d000700103048100012a150780d00d441c5c2d100340c01110204140d1101c4004a40d100300c030b42c3c00840090f02d416414410855401e0614416908050382d0041d91a02c1040c036100b1180319081e07003c07860340305112810300f00105822403034256024a100107200d5a8a0a4a9441414103035030200000c3c804c29102508540000c4410200701a9900031130400c54881d40783c40248040d840303c1480f826105000d1421507460303800c40190154410300318 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 637371465 1250 637370215 637370221
    0xc0203011515030608010e0a080d1803050c011b0c0b060d02120304030b0f010506121008030d0902100306031509020609041506080c030f071b0204060e100f14060307090e 74
    0x80e10303109075075042d860009041c0000001c50700014000e80c02c07040241005008071440076a50044a075006c2051803900d00e44810f4003807010444200d00900b214040e0f00e0741640d600081c50700c10700b16021004481c441c2400130960310b1001d54807480158070b055101400418644403400081c0002c081a03800941c040b1503411040700c0244040094422203200d103150352510b40b20b00303007600d04080702401615040f031006e02c1880d0b180320329082400d0300700500d4103c00007010345412056085911804640c41844c2c2c80f402c50400714241151029144401482e0801025041d40c2e21030080302010340c4105095626120558150340c2c80000701c4441d030740020401c204011514410101100840c4907980201300301d94001400701c860402128030404c0c2200b140306450380d40c5541981c0075400304110300e80c20080e1011500040e1a0b9100e8a005046401400800e03031400e140d40020140f09a04600c6170244500c0003002131300c201c03004804141001701c030402c4e01d9546490040b04c600341300354041c078010a201018 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 637372715 1250 637371465 637371479
    0x50d050a0c03150b01022113171e030304030c0204021c0f090308180307171c140106030905070e061c080403120512070c0c08030c0f07140a060c02030115 67
    0x1805450701c0080b04180244004c142c01a03803a55020320f484184040c450012400400b800001400c1006e01204001e50154540c1448501c941c6103060200081d4001c03080005422810700b68038007001030000080d49986055030f401000b00c2007036540203000c1c3c1c2d000300d4003100001d60b41c2c1d0800894146907104004001c0300703040003001f81140d600140c000c9030741000480c41c00866071680f888070824200046180c803086680f16103880c6044006500d90810903c9079941c0c00e0700e040d14441503145480c4021840404500d0b105082d2035060340160b013418030741002c8070001140810000c0854040f40c20b400250359031100400d0004802600200c1040070a06401c010414a02c0182054034041c210203a244035403650240c0f4143b103417400107841e950740da1000401c0d0500c02c51880319031920802807030743c802c0c1e0756101c59441c54000641c1030700941c1002e0f44070b070f19000c0100b2503040144841c8204002548075000481d4039883c107401014200720144059509648003504107003442c032003003100c4044650356501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 637373965 1250 637372715 637372733
    0xa120308041716020f040c1d03030d09050105092e1a03011817031306020306120d020c24090613050d060c03050603371e03020709020f04050d050a0c03 66
    0x4203d00c5607030012178940a6090030f01c1140c10003540c0c5c0d01c908402d900206840764402880114250b032500c020001c039400b03002580a00701c11300f440381c8004122400c100d5042c60901c00d64005018000c102c05050703582d020114400e108414030b40c1d120009002035850306c42030805030fa11700c6082e0598280b82200107240030034081c440f0a5800b0300070300e441c14201c00301441043e11055034043c00e50358540c1700701c201140300e40d4000e540007800140840804400481d0507802d1200706690200540c222a102d88814100044101c00400300c2c1c0c248851340648a4140c0707001805030303000090048401140c05c1d6141c050f809111009440c2c0240004c00b00303900b524012020300000300e00c030000281840080740d090b04001626401d40c080740305c1c015150b0141e14031100c0901024200c0621240d04501004010426084440c4211840130000116010144c04d0103442c001199100f40d0350a0710400a40300795038680c03800d9809a42081354140304c1a41c02c1c0c07c0041c5081c06405024000400142000080040c616 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 637375215 1250 637373965 637374007
    0x110307090e09010c0c15090c031104060b092110050a0b01032901050a0c0602040305010608120307080f070507061d0c100e060306030f0f03180a1203080417 68
    0x40c1140d4450b901c1852003070130f9a504210490200380aa105000091107940c544c25000542c1800052080b1a0780c544c0f03003000761182e105480050302028280e005041c28054103000e031840130f480520b000000d80c08120f4414680f240c04402041c0c00041c084041418003419000101c200c50502880c14a80e00e000001c0c0001305280f408a80380c0142d4017114842540c0b921240c48403200382d0226200e880c801991903a000c518030034100126202e100780014128405070010314012800050036a04241b0114542082480c4c001e0040c00203004205a0303035400f61259905c0704c206030303011001303489108050310035005500c070040545040c0122001c21114100e03031460103c00318001c41d44445d94a034280a00c441e1100030070400a08840c08039945030400400035a0400c1016040300c03003201c5141c400c03e040a01c03c2034403000c1a080040d00d50418400c4010302e000010007201c1031100d140c505000741080e40c0c892a401024402c0c6113000405000c00011021103071240d011301c055840c030b0141d00811101e1240 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 637376465 1250 637375215 637375229
    0x5040305100203061e1305150301020403110307090203090a11041104030f23030412020d020a0609030b0108030a0503180a0210020f060108031e0c0109060f0636020c0111030709 77
    0x10703804000e0455a0910503c40e04440074080c102031b0700c0150381d50030243c540180303000c811990501d90102a900c003440148019400b40c210030b4040a455410582005820707480007460a0051003440448900491a42a151360120725500e0707144205000c64003800d6041d480070400c0c58041070010520841c540d16041851007906805001d070404000140303074541d10b40b2248115401800240001c070590100080c0301070006103c048002900e83c0050504502500310310f0014400300000c00411a0b1002000e024103612405142025036480004201e400020b05011898003554035002c0504405d000a12020790060445490100600c402075520f403602c86064501c0d02c20038000185249011041d00c407601a06190343c0040c020b0b54002d00c0a94014090070540c556030740c400c440010b040c2d4440e50400f11203000700841c1c81c41c50985d6031522505010811121845a04a8250b0701c102c03108502501213403860b80141c43d4101c0c881d981b4010480b10741081022a00041445203040d04000c0401c1100d0381 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 637377715 1250 637376465 637376479
    0x7031709012d03150510090e011205121b011a190305071703040801020d0515191e050409060e06090703080909070e031c020d020d120c0504030510020306 67
    0x1900c07142454541c80031003402000040c405854151501c280c22000e10300103556100c813440342e142c0380001d8000d001428a4000701d0102202000a120510380440c01441c1c20984803004510369180d1940f03400c221302601070040750001c1c1c110703101d007401d03400d0781c0002910301f00811810610b0492001d110100040061294104c19001414010960005c00503251f06c0806015600e25043da0100307115003142481585010622006c28176034801d2010344000b881c8980081000d0400d0b0407484488004145041e0068000010840c00041c0030074200007210a000341c55045c050f8810030180c09441687c10140d4460b050100c804248186c0750052200080880150707100d54603004040b07541c41406120080004005201c4d0740414540100b285038000150300380121100b400b4000241402500ca00d59100324580c0703039038a500b01c0d904018041c00c3c03000e0f6000510005200b0040a0000200c101d10840040d407030f140006400d07840ba41c10744d4020f40e40070040b11000381c0171040c40c1001e90002c03030b0028040c0d40f03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 637378965 1250 637377715 637377737
    0xd030e07090e071a07051006030b0708070f0807050c07090501230307060807180b030405011a0d020f0d051203040b0606090f0613031e11060c030f0c0703170901 70
    0x4003489048440c8414000500d0b00f207280034001288031207101881485840c0c14081400811014000c06e00801807020001404c0c078154030f007102a01002428a200300b000d04020040d22981110003084515114200b440c010b60358801d0440303441c400c1c442985501e009540c00094504480d410850686658600035020040c0105861031012003900000703605900410040040380c2c000e071030741600205a8905103082e1001241c04c2880d0741001e61020308116000010001441400e206520903202254804084418044000781d2180c5603081c001c2d1180c15500c50312015030781e03810405092650700c04140c403030840855455152036003088605580e808040c4c4002480d40c0303030144c21202c000c00c3c024210000244020103000181d0000c00040c501800e15034008808198501203c000c0c0b10701c100c894400e44456481d202c41c19107506550107001e0101403001c8000315402000303403215485501101522203d054003078502d00015540042d0811141c00c0081c2c800c19209402086140420380354011107032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 637380215 1250 637378965 637378979
    0x90f0e100c022a030105010303110d030b0f01110312010b0403030f02010908030f13140d030c0924090e073b09060607080c0c03010507090f0311010504080d030e07 71
    0x1885601c0044010380010105030749609030039014564800e00881d0015840b03404070040703800c4845c00c1e041075000c680400501c012844080010042c1011340785402d12140429a01142a844920300310a05002540b29940100030041043d110701410400e210101540e450100070900e034010701040d030000d440388100b541070307074014060301c1010381e40044107914503911a551440c10107030151100652a800040d00004180300343e0038140842c03000b6015100b60803ca4401500720783c0e820310844148004c00c007042041340f082000c80310044044400003404510104001c8034843c41303d030091613561140509001c2d900b6400108000d8500b1010700d003aa00301043d890050301d41c220300441080780807240d140f1055030300313110015980106020349a141072109035503a0f40c0854029150501e020360000d591000c261809002c3c41d46c2100361401d00703a544500b04280c84e07181c1e503141c1c04003130301036403240c0c4801d0541d911407011100144400420b1311001883c400d4020090702c40380100392524070500380c010500d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 637381465 1250 637380215 637380221
    0xc01050703021b010509300c01050706091a01180507110a060b1309061b030605090a05072f010f0209012a0f1a09030304020f0f0307090f0e10 62
    0x10359056001404004000390000c4004604501e4241c1000014085040180c40391030000c5881c00107c081c0744070207407010f9142c002d0b00141c5142a04594868580d6070741a0740c0000807a42066000100420b0790980b03402d140c5080d1985400f5000e2001582000040c225804080c0590946c0303502e20900c0b00d81c4030890202c03110341618274180c0e07442c1c10902d00200000c442d903211240c0800081d00ca003003a217101d44641b90440302e003100182c890540f9480f0035144460301710b41995148a090034100003080c02c29010862010008020340c81c0c8540d500042803a06024001e0481d9101c1014050b0b6010a1080c20400c03881000442020066007000348843c1402030b54029602e650740103035110440f40c00d0754040715054680c0d02100301081c40700200000e0110307084c01c0c0e03406c000e140503012446403800c0785540300c54030740700017400c0d20b50a0b003040c800d02006075211612a4201c0310212000140d070140400000c1c1410359651107000450714010018200c014a034008400003444502940e980c0c0041104100035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 637382715 1250 637381465 637381477
    0xa120e01050f0106080601021216051231031e030221030705070309050616050706080411042a02070618050904143f070c030201050c0102070f060e0c0105 67
    0x45240c11100501c0130310310803c8002d901100520443d04504140c002032051a031188041c44440a100d08054090000410420000340741c405a268a2700c1c80d0307140ba4685041004400e1440d0303031b8144403c01b46690503a0341080195410034038041d400c0c3d0344c1541d05841810300c5941280940600d030410f55040c0200004d01c003000304c0101c400c928580d01c3e00c10031120303031303024404c11001c0c041c0300c00012800ba11010094151502040c5060b9400501c0d814914503100c2c0720350205040021607001c1200140c040d65901016a40c00d44021500200104190100355940311074007040284240724a4029680098140d007290a40e8903034a004031003a07a16114150201d00078550445440c038003090005100003040c582c2654500191344845c0410070319192014154218811904d55090058084810100041d91000404000989041010390b641d143c1004684406814086c000c52583c40b240020340488200c10381c00360425007001d100d850b010004202c0000d41000f24400c0c142c01d040c565000c0c0307007110310b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 637383965 1250 637382715 637382731
    0x5040e0309010801051c060504050a1a090705040f02070213050a0c020a0218040609020603090d080709060f2703051b03010903230d020408011d0106120303051b0a120e0105 75
    0xc00e85c03c24040c406d08030380401ea100d07548084e4090b14070120302c1030301ca998002d174030510227809605c0c024186440c1034011010010201c20140e828040300381070000f41c1d141141c0042d1004a0304102c24050540240205103001e90020244124882000110741c0503603c03682c401082000101c0098508981d82c0c0c043c2c4000940260510351450f036a10b410114055116104050101d52040746601240c80b0742c206594040f419417224040c03480107500090450303401112440c24040051610100410100c000107903181441400180b2a00e50600010060f210421030520300c8240b9a5a2030030540d01c130203290420744000c6000080c030a0600e410b00900c901580c140d0740310300308aa82c00701e4075400c5144030700b10400200c800700646000401035002a100426103240001018414207454505a00044420103403036403418009000c0c1a0745903409642d032540620700082c4583e5440c1200c464481c800b141d4180108001c51802e01e07455000180c03411555091409014190182e003146080e940c0a0312642 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 637385215 1250 637383965 637383977
    0x10e07030e161a1e0d06080607142d04030212190803090a0605130b0711120c010f06091b08281803090f0b0c07060516050d0905040e030901 61
    0x8890320460b4204507032040b0141140d4585200f2240007161a004504c0e504002c400200b100300c0c80c41d41c11300c03407000206000c1000c0c0100341340ca024000d1240c0c41200c030480c04000082281c04004040a419179907940003009408079162440039040302940151008920504c94101d032211f07002c002043c040c40034207140c412104140803e54480f40240c000408141b1039100f000420f0010440c24000c460044143d8100034100ba0140c2c00c008103859030040070481802100380310310701001d60016100600c0301035005120f48501c049080d8a0240000c00503220700340c1c0c00c1c2a4040380000e645d070700200c82090704600c00c41a842d00030205581d0301c030b800c56102822401343c2e0342461801242c00c1c0c110780201c1084800141d58120f900f003807142c1d030602440940c002140300d602403110050207009a00906548000c1e0360a2244028040350341d1410340c050a4100040402c051095403000c030b500d4900c86034000705079094414940c00c018000c038403502c200780c0b00760700b440d0340d14440035004001c54040c1107040c2c1d103207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 637386465 1250 637385215 637385219
    0x1308120702040b130f02040518090606060d11031e07090602070e060a0b180102060606070203031e0405030d03140c070f02040507110a03120c0e0a170a0b010e07030e16 73
    0x4000d0400c0c1c611542c11138801030b904100300005102e0000e4805061200580725401c0a0a00c0541001b00c6211110304070302c40705002c5102000201281e10032411203826545010410210001d4050407020405641d804802d11850130b1f40c4104409100c1c2120000c854640e4031910112608400d9110306405600040e5007400446640204280e00c00303c0500b041101590340c00e0210019031007114a411900c0c0e007410120015a81440303002c0d0010421540207080c0003064000907120700c5094161004482c0c4c17401e846070360100c1e09041d00c0c01080010300741ca0700e40c0c070220b01c0940075104000c8000c410450390390005a40d0300d403c109658440e90072210f031610010142e2b085c00024a005040403090003056600115600b000300282a0780d6442941c0d0070740002800c0d40f4403c180c9200c7d180038401d0110410308200c00c0d8950032040da0440310400701c0c4000304004c20340c003141003183d00d01000c0d00c4003444000101e81940e640d0b007024040c7c20241d50401c003a481e40d03c10716850700c1c02d9904290401032550f2007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 637387715 1250 637386465 637386469
    0x108011716090b120111040b0904232208030411011e1d0a032105070605010e090d03060321050d050405010506011806020d0309030519051308120702 65
    0x60311004140c5203044540600141c200658142500d078806001541c580c11142c400e803e03c0d194054042c0c2404d00284254011071190072002d0103103014844000700041051903040ea02e64201140c0158000c1d1101044a41c00007a80d4010004803046c5502800040d00084040f440c1c61840c0e490a40100185082d52100c1d0360f00c03003895600c03944590400001c071f400390211000100408e10703a14855261940016503144c039108038150b0010340c561066103003035420404120155184907100403a00c40900d0440000c100580b081d0041d490064880c038505800403030386188030031210b801440410308030307020f80408000807410f80d425800010b0400a110b01e01140c0d80c00405415a440001800c101c0e040600086c4404200c400440341030b2502d079121000e000380b95030400e101540520000041c0900c4600b4040b010303540780c08241c0c60204050361800d0340c50034140300750150781c802500c3c88a240c2c507410701c030440103005401c907806600800784039000020702410300060000c603058100803114103180071502 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 637388965 1250 637387715 637387739
    0xf0e090606280803040807230418060207050604020f1905041d0f010c0f260c0405060a02071403150408030a02070503040b0a0219200316030312050f06010801 69
    0x6400744107005140d415001c4101c21094680140007043c000f9600e891401d44003c0c50000c4a0344034102c480c6ca002110b90403e0580804040f400c642503c1c007288500c1e000c2d00304412004810b101074003c0d84089480c1c2c040210110b0141d003d03074022204611060f5145c800c01c135003002f17051f00340901e107090341c0c4040009041170340000d510056601c01103850503900c000d10500340042c114014000341d540341c49903102241c0140494034840390038a8820204034403c5d0640c50825215400603294811120005543e0324400702181c1c0030b460007500c1152100c0d03000001950340c100601071105900c50b02002e014844c24000b03a0903100036406444481c0c5502d0715101c0c1002c5600244c002d1030065020007060011480c100020701c02450081100d039514a010719001b0b0030200c0350100d0b04070354a41441050041044c40654849000c2c0614810074402c0700030b03000030715081030381c0003c91814044903800001d06402221089e00800c0c4d00d04140010f50300c2c0c241500984400310780c0c00b800704080740014800818160 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 637390215 1250 637388965 637388989
    0x9060e0915030c032b080c03010e09030d0212070207090209060403020f0f030d020706020f060f011401030608061303090902030402010813080d15031a0705090112110d060f0e090606 79
    0x350650356401c0f182e00100b400c0050700307100c10300100315408a4402000b0703c54040d240f082c94030f00d02035059003082d01c010581c0c1e11062165208110b8980085a80b41c0070510454048041000086580c0ca4001010b2508008212100710250098400014122803035008a5005242c01042140307080c0c2190700300706000f110070840d65001030906410f8a43da490820414240340201e8000b00565031034450700a1510294100a00d225042281030294441007170b02064103552300c0844d400407221305200100d0041400341d0104059108071003d0244600706034030590b00081c0039a0302c000c0140c0d1100720302800e0b48801e58000f80059200030000310400701c2c4040d2102080c0c410100c291a08244140c14805d0744c9110391000640c07841d80c0c10400070006811441c0c0d41011840742c0d25041407411a4024140780180300141d814840203c1510800d99010781c060720501400421070b81d210000484403200500581c041c1100c2882400c00205490200c1082c16124429050081500b0b5413100284115200b00e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 637391465 1250 637390215 637390219
    0x30212030108010213140102030d0e0c04050a05090d0306030c14011704030302030f0702010e070b030a0212150f01090828051e010b010e010c0b070203040e0c0a09060e0915 75
    0x1a1101400008084005500818100c000581c591010002074074282e0720651080030000b141070071220710b50360040183c1d404607019046c0040c07460071030356640d42010f0f00b04083c00d07403291904007002a84801c96100c4c0c4d008582140803110b0400d00d41e101a000c54800713000250400341414020482a510b40000102e0018185040c540842d40303201d0b114255402640c0403404289c011003000003030700003200015841000d510091101c80c201800d81a156034203401098001c400010000b200144903030110798104031281042503991078041c01c07802c040481000000e100304080320f0b540409621a46400d8142c130000800b0b400000d131403c0c0f901e0301d850101d042c003c140b9100c0541c83d01c08110180080c0080c8442c010400320380000040c185400c444c548254075040c0700580c05a4992030741d02002c01c901c51544402071803c0c1d44c44040083c0e280d402554810f40c01c0e6401001000120a040405000c04103a1902c40e01280c0341c5400c1c083d280c0c0340d4a84551a0041c0120000400c034140381180c030002d50f880 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 637392715 1250 637391465 637391473
    0xc07090b040213420c11120a110a030b0109020a020a02060403060c1103040605040317090910060201051e1315060b0726030601110f06132003070506070302 68
    0x4429400c1180c4016900ca41080070403c503000d49482c5814110344c0c44184180752404401d22450554107049400200420420a02120100400c40303140d800100a910080a200c11211000c84080d581d0500c0301e0202c6052503c89042402d5081040c181c6064903840314031480aa8203005030303207000790403048901c0c003180320b12492000903868690040c0041c40c01514081100725172204046c10007001d1b910003203543c0d481003004002c400da10000b07a500380c2c1d921070000101f82c2498035080c83e180c01140c05007940300641c0781c1070000c01403081c42da06003280c070a40c000f8042c1d40d03100ca8070a1411000300c2c105014180003c80010041128001c02001d02846040000484030340082c020003169481d81010131130b040d0000d072000c180b10703103050b200301c03c0710020248101041250040340742a010141c526410302000d1502014284010300841000702000b40c200c4800c2d29000304c4254804107841d90595000001003000a5034880044004a030701c880034005007121441c0c0403c0c81015842100d00f5421801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 637393965 1250 637392715 637392727
    0x1b03230a02091f030b0f072307150c03022802060103021c0b28020f0a0c02060f030a0207020f120d0f03021c0e060601020604030c06020901030902060d09050f030c07090b0402 76
    0x140f0b402c07000001e1406203804400c2c80c46c09014441204d10082c01401c103000301d0000c030806071502035030f1240700580d00b42d951a817103558624201401c000403c0c1200b80e413a003460403890101d41d2540c090500000c0c07000007171404040441950000480f250f819000513080440188007500300702c00076580d150f8207145221030416294230b0301c22030400152840e114001c2100c050400d0f02503625425101407500c03903021840d12058130710341910780c860b82c00c0702c2061200c6411003000355565072041d1244003005001d181d03079a1901810650080d403181c02c04900c00c60b01e41e00e00c4085401d150443c02d2400d201c45004003a216050f1005980c000300c100b51170070800d030b0200700700003044080258403401d1101ca0301d80400c51950240000307082207801000541154080c0c405c01c008240d210044031030082d0007210040e59038101c440120301070f02180202035080030002821702d113620b80a5111003807950080050310f00c01c2078610046510303403003640c04940740c5901258051205a043e940004043d02005100600d080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 637395215 1250 637393965 637394011
    0xc01050a1205150906040c2a0209040506041a010b07020405091e0c03060708070504060e031203041506060809151e040804060905010e130c03091b03230a0209 69
    0x141c003c4611445044840320f4600041c1040000030703400c9042168140b000c0c84070801c0050451604440300e00c5005030f13419000e103c24039010400101c0d00c1d000341443d411446e090a140d075659005503002c68100300fa45881c1d0803a00705509481c0e06807802409554035008081d020880a071038094110500c0e405811260540c0b00040d00b0820794403404030003e014101c460a080600b058070040465090242c600d041211f6a41e01c40103e509a41070360500c04c02000b0748001083c40c2641c00c00510b02405400000d10040c002484144000c2c001c2c000810f0008648400c01141e800c01c1c1951800e100b6480300d00e429001050f150302a5501c100301c0b0b8100c40101d880b10198a0102c0e1b015601540e01c170400140c1030000340d03840342c51000985000e08050000d00b6040003c902442080314501315150340c0c0740c0c040000340e4420f8005030303801c940100190111030013112000740c4441483c4011100458085000070481c007070091107510000b4004007524002d4170700e400380300440000501024840e403810384127030904 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 637396465 1250 637395215 637395221
    0x50a0b0306070c02010315062304080607030605031b0112020706020c0616120507120c020c0d0c090c1803080a020a050d09060314040b0408130b04090e19050c01050a12 73
    0x382035075540b10f018010803800050129241411f505200d14130a9030306018a580002d9400304040305201c170700c10109450b948040c001c0c0240e800001c0c3d00c3c0500400d01c02c0300b642c950000425143c084040ea0011880d045042040540088183d8003040001c07004a030860007a41c05400b0040c01200d02501d0004030a000f80e043c060104c2c4d010340840c0000e50045111644032130103e0342e100f00e41408100c0e904180743d0151494203c2d0b180541c90700d440d4490703d4a940c1c424451001120707805032581510128031300e80114035061900401e02c0b224580b401d081354071442584010600d80f0120f140c040024216100d00740c2030340c0560041425482880f1107100060020045080701250300e075179100c001c0303042c55401015a20141d40359000c01c0a15410f0002150401d040f0680081c3e2100b1500d9558101034800340d05031400c2d600080c01d80102260000b45411140c010822040210341030700c82c0c0c514001c10300d0300314100f084406040b60b40181030801503940202d000300182e1016043c01c2810311002d01c071400039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 637397715 1250 637396465 637396471
    0x60b12070809030c150a0905150106181a0c070509070503010e010b040602060a0c1b060518190803040305070606120303110918040807050303100e1b030a050a0b0306 72
    0x660220604000106a110161030380001440020b14601031100402517501c0e410300b100c00c120082d000001c03480d80c0034150300100c01140d110b816904603c611143d02c0005c3c6c0b00900c200b038041040007a44040d000b50120015080c0e80d101880403c0140103041002c40541001c3e0310650035119143c03010131143c2d03540e840b16100358882d940c1d080d603070744c18007030280366485060340032403580c00c024081408403a4011030341704d0b070080c0003200c0054928000607046450107001e03099200185c40400301013061108a401003445640c0d20759911480581480d42c80390340b401d00d42c013802c0c5e02c0700c4071002e000005a1088000c5030494080c0c60600e08000d800e0703d41200b150480c0d0300000b007240419000c07108141d01400344062107060001c4450400080c04d001c80c4190202c60070300012620a540001d00704a000e00c00c0d5140c10340c0100849482e45441c01d0500d11039000d501a101074200c1180c0003641f03031401d072250a180410714001c040d0a40d00d075280d00c50b0203000044c00208656449130300540342500cac1081401c1c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 637398965 1250 637397715 637397737
    0xc1f020706050f010f150f03050907032009090703030801171005180c010c0201050412030935030a02030414220c0f030504050a0206070f0602030411010e041a04050703060b 75
    0x83c2075494104c0d0f0a040100d550702800c203603040341c01c002034a9900b0a034003086808080c100490240e0b101070341e0070b05190316500014043c017a403130101b0041040000300300750383c04010344200310541c8070000c80340d9032021184402400100a200180030494002c0c1c006494860040c0845841d203280c200808180d8000302d40030000c6095410a02d003900c0300402441d59101c40a0a10305d400c00c80e241c00080c414815070003002a140d07201940401054401d6402d00010192203240080c854010240c180c01900004894060b00f86040350300200c40d0740c04011510390703103110b400940c039051900c40030002040800415075841121141e0160301d10b0b00b04041507601d40c01c2e281000800904801c0054244030f00138040200b01841c0030200800500c00082444d5201d80468404e40c441c0810302e0b0062101035041001030a40c0e0010043c081042181c019460303000c403098840480741c060040500040318802e450029a070214223918071980e04199002c1c5802048510f40418003a448081050180c0c1c00a8171f501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 637400215 1250 637398965 637398991
    0x109110705190b01090203060a052103070c031101091421030706050f090a03090b0c03211506091f02120c03120a090302100510030b010e0a0c050c1f02070605 69
    0x9040010083c609400340203107140450550800d64081840c4001500030341c0d000340500083d4281301e2040c14a00c0300d480d103503201141d42d14400c0f445c02003070b0848a440103d4960449118003c515170040c074000081c1d409003040c1c0c580b41c00070007040014003034895004001801ca120308195800300180000c1802d54000e20000c560b50a085685000c0410000d020746860b801000c581720000b64008048012a840e8512858581c402541241d05520464101d9481070329404010100089491400c500c20b4141c40e003c007500700700090030b0051512400e41d0b100da100310088551030120300c0181c001000c7c800d09204642c400d40c05a00b010040307500c40090070312140e00c080f600c0469456100701d050b51100c022801844800340300d54000e59241c6400d41183c18168580303001032032528900594800564020f0304081040d6910b44403920920f900390707843e1002d00e00300510404820700490840d0b5102076210010004643c01800080c1c04043d0851101c035016020091040800c0e640d0250601403c9102010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 637401465 1250 637400215 637400263
    0xf0a1b2703051b1302030a15050102010e03120c0c030324030712140f10060f15020604030f0c06063b061201020c1605010207080a080405130f090818060f030109110705 73
    0x24102207480727603109904580c14000012205107010055400c0b00d02c0d00d100354041d80c0c4500c0503404a5001e2640182c21900c8044100030300c1d040e49000d480c4594030781d0300b03090792408000018107031101c1c0039005180210102d04000c46c00505007078a9514504010010345896013004001c284c00c0c01607032071191208030b865603400d2007a84c4a9614810003030403141c1c00c03003000c8800c90364040d465050081001c0d080c45042d0810014582c020341c100306515038040c070200b0806444288050041381d804000f0700c8419001e8004501444030007615915500307400d1104400395803507004100317401403d079681c0e04541d50240104c1c1d0409804001014000c0049052902840d0030840024680307042913001c0081e543c00482c0c180086031340c7c6d404031810b5800590701004250490588c4c44003800711044030100c05031070940c2c000107000200019010442c8680000303004d51000400308901c500581020703021061b401c000410000d00c40d42d20488803000a50815400c000e2181c488500b043e0060f030001c14480303552120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 637402715 1250 637401465 637401491
    0x210020c1e180f0408031e090706110307170915030a05060f031507030b0d12021513020109090902210304210b0f0a1b2703051b1302030a 60
    0x25800b209920541003104a2808602d0980c014002a10250100200201041c0003c40307148848103040c0e4a800055240c0c1428800c180c0d0f5180c4911544000584c0f131091121009804001c41d000b5580200d0060782d50340700c60031300e500154018002180d00c14200b59090039403040003400307903100e400c451200084528140c81403182450700c0000c89442500229042c000000d0700720030341c1d9000041444e000400c08040c1700841d01042c030454005d49485021440140d00c6580020040c107141c2c010003590f005a255044151804425101c00030301141051300b081c003134441654404601140010300000c0c15500116007008400c80b104001106500005001d026040c01c0710080c0450041c2190100d4400e5400d4030b4011f0213480161190503000007207000320360f44550300e40007070391000c0050f0a02c9040c2183d0782d40240c4610585483c040000740b01510703c880c5074a20400510440350410040c4c0000850300800d85c1d00034034903601542d40091402d0140741c602400e031000e14840c2500c540c0024a903141009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 637403965 1250 637402715 637402729
    0x5090705040c031e060f1a0f07111516080d0204031a0a06050f0607060504141c090f06020c061e040b0909090d1d13090809090f070c0210020c1e 63
    0x2143c1d1136003818040100031003500d038026141287c40000c498050002400000a06845202050f004c0c00c0800b25882052000c410741c40074201d0b03001c80d25841201c000c450704440030702503401c9040d02c4404032502d0303d0119104c1c600401c0402d50f038020062625803640d903440c032050b143c104518103034284d040400c140c110040c41841c015210858109581d20100400500c1c18800c1d00070017080603444001090400c010721803040500342804098070300c2e51042c0c2c428240c118203850a0f01c00042c400080000c0d40380003400b6a03070f0a0703e2803036000d4610300c1c14850510806521419503080800b0901d07595485001c9180040c00c040c00116041680c1d03001584d0800c018103a000d030100f03c841e080080b40840046e0445214590010b00c103031800c5080b003c2100142d40f02c929403008144c4079080409900400034404028a40c1401c00c0394946815107401c81d0041c00a8001c684040106002103800740c05454480c8025040b07d00074411182c2c80d200c2480030950b003009007103034011080d50741c0400c90081d1401035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 637405215 1250 637403965 637404011
    0x16181d0c0301030510090213091407090509060a090f06060b03070822060c050f07050a0201110a12201504050c060a0c020d020402091f020d031103060405090705040c03 73
    0x2421841c15941141c49903601c40c107145141c240480c0c0d86504800c110340780c2e9003501c1c103c0c170700c1c2c0c1e00d00300049089030504002c949065000c04601d4021204007090040c50ba10a0340e018964a400030300c1e65a0380c1c4420003004100c0c104003500d010121b0110345001400138007a0300c0c05000103004c0c103130716410803450140511310040c0142c030301c1d680600a2004d000303c08111208080e80c02410121700300c4040c0100351b0b1140708600071a04607010000d046003d101e0b000490042c0d0501c01e9860300e52007400d0a80d055140c4408601c000c03c08031060384c41d0460644580c0165020700c01440d508030031942c4030070300d1500d04004142c0300f900c1c0d00f41610402003405010310480100301c8099800d14608502030100034980451004024459500100c10406540703541e4144d03120140061311004c8030040c0440e600022100c503081c14001403051342c000e01c040034401c0c0102d00c0030007204020241562a480200720260034000c01d200c003144201280040d4640c1c403030040c90140c0d080ba80700040e83d49080c4c400c00110005031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 637406465 1250 637405215 637405231
    0x406170a0506071b030807120f0203090d0809100209030118051b061318020f2208010606080406090302210405040609050601021e03070b01141002010903050316181d 72
    0x326144010104d40c4034059655141c640580e055507542c2c41a52040506011a04502e2501c0d4691041400c0e56000798011141d201c1241c100720040b480c222100d8001700d0f088801a0805040f034180c5c02110740140c84298401400400c015450245281c45256820803d941960090912049140710034005041d04001a210b0500d80100a00b00a010070707403510442081c6c5a4030034a03001440d0455054a440b0303589401180ea4584082c1884040c2280c08031090406101001001803118014840d4000b01c9081e078507201115640c030b4803414014140070400387d0542c004c2544480d54190020001ca000c01d04c0442c1058840d8101414041110010b40041d06450b2414040c403c1c1c40c0c0e0002440070307062101c006044141c801140140b811406040c200404400802c4004a0714510140081c000180309403200342640c0086a400c03403d803040008007070049081000881d49020070003500c0c19036003140d0304008081c88100d005440103045e40354003681468030440b540c00e0407550f08400ea00d03008140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 637407715 1250 637406465 637406477
    0x228030c110d0c081606020a0f050405090118020c07060f020c010c1109040201050409020301140f040c0f18050d05030702120d0f051c0203131b0317090406170a050607 73
    0x103000c400ca50340b00701c0d40311001c052244129046082150b00c40480c1c0d40c00c060315041d111411800d00e0040c3c00fa400508500c004944001c1446568621a6050303030210b0b00010140003050b4a0300041703e20642c41ca400c1d09010300c0c2c007002095407600b401c10840000304030954400552070040d01c0000e0501d000a20550b04000b02d0500b420040f404026110704007420403220804541c40c0c5100580301c40c400c527071041111a0011000088a100c005205030001d0015180403841c40d0080c0b080004484001203002d0101c2d0085820900083c8601c8201d9400288000500455034075003001400000d07401204070f4055100040c00c0c4214205220003420313401c2c1800040402208880e0003401c40c141070041142080008254611002e010b17600b48880140c02a008655a08001100d95807885a103c02a94182080d0b00d200c100e00ca803240b40801140d070000310505285c00d9010700c10380d455002e90341c0250700c941c45090100b03150382c0d0221400103a1404800410f40c66003586031090521030000c14a0b824090 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 637408965 1250 637407715 637407737
    0xf02070206070b07110d030e07090c021506040e0f060406060b091c050a0f0803060907080c160213020f03040b0603011b050721050a020601050a05030c010c060228030c 73
    0x80d02400c0ea46003c0d03024000e40380039520180d088403110640c00040015208682c02c45040542603031040e180c0001150545022680300c480000560715000c040d0b00c0181d1000341d003081c0c24600b0603000c64010304000c0000c9400890b02c014240360800022150003190888030501040101034880c1c1c1700102030707010710301e410074543c1e600017054442150721010b14440700000c28002c0210601050080c1540b143c01c02d0a840a58240034030580c108441c0d180c041c80c520000b00c0d80b06802070841030b04c42e01041e60081e1620145d210412207800074040c0480e08000800b003000600215400546142417a0300d104c181c0320300d860b0500320030076403001d440c1500a13454102f03030340d407200396421404c80c0c0c036a2a410429070b00c03100c078640b44469a000558004030040d81c02000740b810755001008018180d166400c0718030301e90b240c2e03040009642d40f9102d244d0341030b40721002c00f08041d409101404000d40c0501c0c0018181040300342c980c03c58892440d103120710085400071140da80c0360180300e9450007602901d000705a0311 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 637410071 1106 637408965 637408969
    0x10f0c030b010801081e0a06060b0a1805090a1a130e0f010b1011030c0d050a110c09011e08010e01050405011d06040305090a051207090f020702 63
    0xa05126a8011540c840d1001034181c172170a030040e028900103584118109000381810b49400d001d01514103002c0b820314422100100001180700d66216a04940285071514440054610fa080c0c0042070081e52510051107601071b2644000081d03003110300038001c0307030b001c0c60007859035000d41d0b00c0c14200400d40c1950407048080e5040411501414040d984032420f8a04054107950000c1000d90344450361071103045009001c1c1c0e250002c3d6071500181d00000c90524049020f2078012400c0082c4115006900500d03c81500405038050308400050f080010305641c2c0602c04da4140820303c1c00f114840070381356250f901c0204002030003044500c00340600540a44012101515194641000070344a250100d00312003415200201900c3d840e80d681c0d4040c0c3d090303040414055004103030041c0205a58a40d5000500d41401180080000e0740c40d000b981010b9075055480f44040c1401809420016 = true := by decide +kernel

theorem cover : BRFrame.Cov 637230215 637410071 := by
  have h0 := BRFrame.cov_init 637230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 637230215 ≤ n) (h2 : n < 637410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
