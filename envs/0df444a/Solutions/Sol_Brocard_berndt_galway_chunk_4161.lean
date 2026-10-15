-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4161
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:44:49.895648+00:00
-- url     : https://prove2.me/submissions/d4cb0bcf-1a6f-400f-a76f-478ba4b76c2f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 748201438 ≤ n < 748381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 748202688 1250 748201438 748201451
    0x140403020114130206090103060302040513050c0906100809010902090703090b0a0c051803010f02040f062304061d0307030804060306080a050604111201020a0e0f0d02180702010f060806040501 84
    0x500c0c0d02d506030050401c85101a5109126001c1201a502644d242418155280c80010060302e49008661003028401181c030440e0b0fa080c1800c40c204850401441d100b40a00c900f00401ca0342c54041840c0c0c8042585041c107a40c0d643c91002500600351504040d500032064000c100c0c003a58142c0044600d103116414110b0152a8404c8443c151122144040082401848803110204c0490388821600100500200c0c01c041011020012039210740c010400c009a001e2060100d980c003d032840303100810001c0c0030044646482d01400f418040e0740540304c1002540d81e60801b4100008511991410f0000c09642505a4038070f0440e10a5106105000100f42010700000c4c1800b000b103900c1140341c1d001000f0386425500c0b179654103092501c0341891980900f00c03608442e120342c000d2000c0d10440701c40d40c950841c000d8a0314104001c001d02003552a119403059000e9070016100c071212900348000c1c08140601e180c4a44a042e03015105014084501d64902140050324110006901d80194000c20007003002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 748203938 1250 748202688 748202711
    0x20c0f120a090e040210112109040b0a0b0409050712142205070b0d020417100b0f030a0b0a020c030c06010e0106050304120f050409050109050708091b01080a0b03011404030201 77
    0x70f482c1c0498002e98001080303400341954a0040d102c22028800b0242036583d00c40b0b0740790130704070f030000c0c1b9081c9500d5402010421000c03508052040c108040b80440342d2030b42682ca003100042c0144224000c03641015100d5020858560241c2e01d0300d0009075a110f814400c091012207040074600040ba41d0128051802850060740c7c10b180800301490707034000015003105801d000941d1455884104141c0008bc0e0801000030032015601038140141c01c0f0728090300c03186041241c0300f400d40e04071042c181d00c2084240742c040b0b6640c0c2c0000d45441035070b6002c1c180c040310b41d8801103448000c0c0036003004e140840c00000381e0703924548000310341141030741d84007902d049442e41c9401003180c4901040710700403c5100510a230070a141e0081100040280451404a10740303519074940c902618000c0c1e1020881c0c82c0c03640d0500c03541c150014800d40d801901c50008000303c04a041031016a20240c104c89818080d4440201306130b0000394010500700c8601034024006422044008400300a08880580040d403809025201 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 748205188 1250 748203938 748203959
    0x50402040501050909090c0d0507170102030705070b040309210303050f0708061207090606051b010b060d0f111204031206060e0105161703010f05010819020c0f120a09 73
    0x540d50180d4909040072481c01c1030200844011b00129280c0c400d0b50036a001690f90340d21040da21030301c941d001d403100c2d03450840101100741c1d202c032140f0405d034010300400160b10340c400240d4100903000305c5400c04330b0700c5070f0500390b0b40a0b02c40c1d0401400c800d440801d11070342c2c1d88580905990071307129903030400c00c585d180101000b00e014280d42000c002565403020420514000c4445407503c150001610f10440e40d0302203941c100c8444d0f80c0110b020036004108100100303c062040181004110b00a1181d20b400c44002801c503c1081030b41ca8035161303151804407403400968003008488449001a0b03a03075076801580500d040504540890002d000d000380700400c0d00f1036000726011a001a140c000c2c185500a0040d00d0907048040780040d1408911030b6040428051015101c200450402d81c940c7c0b0b504017080505c100300250849418071404070180310111500e48101501c29050000050715003102d00041810030400da811100c0ca403141c1e9402c44034003400200200300c251900e40300c00ca011580c1380e2a40c003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 748206438 1250 748205188 748205197
    0x801050402061602030f0a050c0108070804051509010b030f0a0c0f0f150507050a121b170a0212030f0105041a0f01030c0207171e03031b07110406090e07050402 70
    0x941006040c00100a010001ea02c1c0c000c282c4c1c4024242e910100304a25071510b0540303540300594181d0301c00120a205540c11040c0c0a0b000a81c0c0c0c9454000b600c0d01d0740304c40e5650b607038421050840100203000510a42400c0d4015000604014199000344106800107680d51200400070f480c00f002c9120001009803051100c10202d480202c50801d0052901802d0840c00c916640c000b010301604101307240014406000d035800d414416484625a07003c8000c005000300710f03150f100e0243d00085e100080201d0522051804011800300006a841004110480c10425070741642d5417240c0e404401d224600c0c100c0520a416100156020003404040072100070700b01644020a5030810079081c132301421944a0307080703100701c0c00c0140102c58036160b07a4a40c1086080305a151010540c0096145070041c500140d4852400d81f82c0c0c200550450401e240070010101001d0010380c0b4010f00000c82c5020840c03101c6200302803070001442040150399810380d0301c004d4070703200e0010b020b9030285d008049072510b880d20994 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 748207688 1250 748206438 748206443
    0xf0902070210110a1406090105010b0a09050d0c0509040510050c1303020f0103150f030302160e0f1305160510090e0c070c0812121005010c12180b04060908010504 71
    0x254180d03031403109443c0c240b03003a03034000042d00806449002184460343e100b01117050351402498203280c4201c4080c01c581e0306822450b00100c0411098201d603034001040001d45004441e200b0004d0f909143c0303400003608691001e90005001c9082005001000c98900305c1c0901c5003100780000e503500c4080c89000e115120b00c00f1940850702d401440542071030b2500121055040c1400507030340d4030480d02220f24080590003450348248080e010700405034140328404145030001c80d9100780b6401c299824040150007481c54040c80840c00010b8034280915038190348803a003143c16600120080c4101c191194100e00419004601c0300c650901c0a62007504807000316645000c02803540c0d1102e0382c00c500d05d544010006e40b504200e41c48c010401c0001404030825040d12540c1480d9106001590701880700b2000300001c000560f602e00c1006241d82100030103e001d42c0c4101c031001d52071100d00342910b035514100010214520b40c0c09010460400c1c0382300030019507a85480d40e100d03040e683d04085d801d955003107900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 748208938 1250 748207688 748207699
    0x1505060f0d02300c030f01300503041a030609221a041a07090e060109030b0f0717163603020102061b0904020f160803150a0303170406060f0e010f09020702 68
    0x100400c1c3c10a100d8440c160055144048c00410502e1192910030350441055034075800004040040b60095890310750720042d61039866003945071280002d02c2a440c0100700d183e055400c0946c1400d82031038044a04e81b01d035417008603112101007a1140440b4000100c0c0c0850304070000b00c0130141045a85281c41c0d00c50481075403176403903050030f28400714440d600203022070741804a84c540100000e00d81e5006a0b214800c01803100311140b81c12030005251815482044030000e180034140102c4140140c026580151141080c04c4444004c6c0008010a40b0345000c0707001c65030721002140304000c0284007140c1180e000740d08072100c0f034590f01c0880c0c606501c420740149061004020012482c10540c000c1c1401c10350f03400d000c40c1000380300410381000704403111003221031210003c100803072240c060308941007904094590b51091819031f0703030240100c000b8110310502280c0d41400902081a6600000301800645918450040c0c0c0c4648076113151400380240c650ba000303912008241400c280c4240c480d03907038000b040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 748210188 1250 748208938 748208941
    0x140607060e1609021305040c0f0c23010905060604020306031f0219020307030207091e0b0a0b0d140f250512040c0305011505060f0d02300c030f 63
    0x240c0000900d90310209181900030002400301c08100d084009005210a20000d80d0b100200501c0d00525442a00000e01c118a85140c6440c01ca9020154031600125401d00c10f900040e0303410418451814000c0444425000e55070020b08004190450011a41b19204a0f140360700c5540801c0241d020440d502d03038240c2c2c003c4070701c0b4803040750801c00600f420a40740401803400030b00b002c01040c500301a90122002d40e000041b42c01c100750341000300000400d02c0000c20040d0882c0c04808002c4082c80018919401d07441d4078401003a40d441101348001000c01c000c0150341e40d60170b000070740d0141592005200741c101411000800c281020701226100780c20071110220b011001c04050b590250404148104220051160442c104c2c0d4100c042ea0190340100c1111700d85518502e09182035a12502080b8032070b4650a00c20403c548510058940400c10b450240752184100c0700010b00900511801645c144907800e111507a2801c030562079052800b480c25650180d54514449005a10064a041010005110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 748211438 1250 748210188 748210193
    0x1d010e0c0a0314010303020f0d050c1902040b12010c180506032707030b0f09031305210106030b09151b0d0b190e0603070602100b18090304050a140607 66
    0x8000308040c801c14200054500c0a2104004080100f40c0080b00980d006052018480408000341b00d04480c00b8608140303000003100318503881d2107500204a0242d4840c052a004540c4c464005c55107154024058590380c10070203001c00e018040d1621781d04003284d81c110b2042445024030440c2010b64a0180c01c0710300e1740e02c800d42d050301c402194900301703010080b501900222885041c405c000085010398101849070a00661005070088090655016030380104403003008401c8a1490b042140c6048503d140c525010300c003162002480180e0012155280c08000f10421140010640c000c031003542c01c46d0085a4070349000036400030150b031034070701c0c0c0d101c0d4001c1e20040060380d10040c40184070360b02c000b290941b00100498080c1d510b040d844007000002080a002541040c2c03001f540c002e804034024040f0b549440000381d04c42000c1002d010480da160b101610b4180c403501c0003a840072162800d4002c003844d180544035140c1d009800f81e2841902c41410024100850424a07148040020007691070701c00e096 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 748212688 1250 748211438 748211461
    0x80a0506060414131107050105041b050102190311010f2007020604030816061811190e0903040503070f090c0f081302040906020a03020d0612050d05032208041d010e 72
    0x24000003c040317840300745d0492002883d00141c4821362185001095034145441d120504140d940c02070300f500d008002b130070040c0b070381d00046070f02400588a408d840c0031840b9040841d26120034018000300c941c03c108480c1442d0310158450301d0500c020404c0d0f4901c103100800181407901c6000e0020303500c20010710082c0041401100209040320314007130403c10f070301040c2d40e5403800d440c281c0d40c3c80e101440303070034045000f0722903e568070618403001161b0b01c00c1490165101c0a0ba154441d0040142c1d42105200140842c44100215000381000500302c92a056a8820300381c0418844d0240650150600c903075051014001c0308010048060790301e42e07407540c4c3e440c541c595070011290901a030344981ca03042c42e0808104140f0060100341c00507500982c0d20011150684143d4030305074040000014507121a402280300485d1504085c1030a142648c3c1d2911a042c1d400b0854002085030340e0038000b64540e803030422000c14010011100c03420940e031440c070981d03283c0c030078032810074480c406541d00004005108000107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 748213938 1250 748212688 748212709
    0x70609050d0b060603090a1709130b06180d02030f0a1a0621030706050403090503010e061605091906051b030a020d1215120b090d120504081603080a0506060414 70
    0x4080c100c40c1e4003801c548038822002d003040c82c0c0419540c0c000880c6000341c00d10317502e58155060890010b001e040503d0012034214458140c4901d090a0dc080c1e041882d5590300040d001c0b415002000c454ac2c440c001c0890544a01c240c0e4000c5800710074210724406241c40d1400380038440c40c0020056a1000f028000d854580440107505002d24001000203d00180c2d10740b09950085000f65030760b051040c1400141801c6800100d00c04103194885001c2002c0703490006555000c2c101646040d40d00c45100c3d8011901c8000085412100843d401001007000781c0d00c04013504d80340301420b01011009031002c205039200d201d04492000160080d42003140b0721802035112008070500280300042c00d01e20f6400c0104400d2540d00500078240c5c10351004024400ea0840264000501d40c0c050544080c4001010b032082101032801c003003103600c0e0000070f024000c460042e50840c548a1351000c420026615005010301c038200c4020103c9440c18000c00d8082c18410300703444c01c1c0e681242c0c1c44010441d51b80100818403c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 748215188 1250 748213938 748213951
    0x10b1e0105090d302f0109051f0c030603022107170f010e070608040b0604060e090a140303190b0a0b040b0c0d0c02220b03030a02070609050d0b060603 66
    0x2500080c050014812a49010003504183c0e032010100305002d8000c2e00d001036600007441086202c0c42c5030f903402c125a44801855170b5986107090091100752407060f015046400019103180601a0710503c2543c1c1340307240001030030031440b0810107510f07144019011561103010180d044400160720030100c050050252004d45100300850b40c00c41c1d0b0310003003122151a0b20000901c80d401805400404007001d0150150315440c0d130000e04022402d001000f0440d84c00108060320401e00340001c2011604c0300d40c005d201405809010420b14a4401c1d001c0b951200e0450041344d40e00b2403000600b8030701d41e011040d00d0107040c3c0c10b032554030406001c0314164040c080c08150503902c1006140d0000381c64441c80c000340014203a1248541e12084006c1ca15804c10b110740e05002c05001055990030010307581c030407100404240102484103e00b600102c644014040c40d64460307094071002034403c00958000a4400427119070395543c0308602e4803003050000101040c44010213007004400030640310320740300d030107990300c0b58 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 748216438 1250 748215188 748215199
    0x2d0e01030507031b0903050105160c030c140d0c0209090c01080a2a090602060a1a040509030922060503030f0a2a0b06010818060105040f0204050603010803090102010b1e010509 77
    0x1a510ba0b403240d9404c0e0701506600110300d80803020420800c080c0a86035101e00d401c60504000050f203e8061710071740c40044c0050401c803030303c100003082101048d00d44112002d07401c2120b4150299001c00303001e0345c101000a070312580c0c0c030800103410050b001804c500c8400301030b5a41d086684905001c1c80103040090380000240c3c0407402c45441c11072462001e008a1501c07a56004d403014074040019007025400707404440a2410669881602000c05481c4e40d0102402e490000741c41d07842103415400e5015103180c8aa0011001080d81c40030014500c04c1c0302010409103040013400e580380201aa030f489210810040044148003401502c0d024019400b405d040e01c07a4044200801c52140d032840c4428058101c850b10943d0041c00007079644900b90aa0162861031075010140a5041c4036903510414410584165160000640c0400030354064400400000e052680c030395840300710f41c03074a98028100350703070041d841c0c051980c1c010725042055400740c01c041d0005147d52880c4100469555005400c0b058004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 748217688 1250 748216438 748216451
    0x515090709051302011b03050901140f181003090c0b0a0905030d02030309010c0c200a090f050a050f0f010b030402300c061c0209120601062d0e0103050703 68
    0x40186001e01c0344503080f00246907204862074400546110340300700c00000034000c082e802d01c0000750424200ca5600c03009080040601c0c1048148038520b116105803400000c401150030400d41808440c0b440c160402124000d2415501180c12821210003040c040c0038150754070000c00c14138036620014083d5840528004410b00d4503040803d01c0c1800100e101c900580c000420068007031800e10420b0021003c034588002814100d4444461800041c0d0683c02400030350700019080340d44660f0500000d080300001800400c06960300308004040407607000d10081e0034040044c08018128041c0d5101d41c04106404030aa42081c50250b49074000800032604885500c1c4440d400135000b131800d5483d0103000b001040301d525004003c50809241c0360100380608030520941d07500c00c031402d254403a900403007200140c6801403c800a02c03001c59103d07554003123020307500000c1485507100114160b07401c10051b9441102515400601140080c1c820610000d50300b10060b402c558030030b0700081d4010110f0315000c201c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 748218938 1250 748217688 748217699
    0x307030605010308040311010201060e070e010314090f0f01110f180a0b2d180f040507050405010f050408070302011b02041b030b09040507032a060c020103060e0405150907 75
    0x11181c080e0002d4030100c1e4040350400401c0007181c40703242e00000a100a2040d285050340c1e0f1503d20318040d02e00401e0100c0d00c02e983d00e10f40d102e94422031036080148400721250070045103050300d8404020161445000d50300341d4007480d00c01401121200d20025a015161201c01c01255215030070032408511a08007044a10550740c0c3e404c142c400103490103221543d507607840c8e2180202c4860350110410001d000484031550101c41a80c1030342c000031003070381c2440742020907600020610080440016445071504041c415080d6000000e081911003c2c0ca03a8a11800078100a0741d40f030060f88030309034084d03100c90403d01c010352003400006044160b15007054003100483e400103051750742c0c00400a1010792404588005580d041c01140707807034081603c850304681001d80340e007511821b40d404044c1801c28107140c8003140c1c185000741140300035809101d4503c0c50b62550700062181c09040c02c103034000790400d1404260754284c456514001d540c454010540f4842d42080f402d20f0500007024521103025420740001c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 748220188 1250 748218938 748218941
    0x302030f03010609090501060e0a172d07061e0e041b0e01030b060c0a0605070e06030406051005040203072c030d0306050a09090f0b150d05030d050f0c0f070203070306 73
    0x10382855140c000019040c4a01171046540c16806041001507007003003c521515220b501009441c80355518840203040323000014a007495511310f803034146040c050070801081e00f080e0401c0726800207005940700d2030355548003103d00010450b4584c0c0049981c072a19001e0901840d1640020b004c05040030411480c920b407a0f81c001c80c409035070900031440301800c040070366a0601c40c092500200320b0f103950418184044c1c00303654040742c8000405450365800841c0d000c90280c03090402d401c0d801854141d59181c1843c1481c090f0400b41c410311f1032180c580d100411140307858000d891042c042c9035112461542ea207100402014115541c0c6501c2c200e0715098a004d0751000e004480e0350460311346000c101e13240b40c03005200c1c42c0c26050f4440143d15241824820000301ea0034102075085822a8604600b0b44526802802d00c45004003415405800502c500040103000b1000d48400740d44500c0810150351505c9440c20f184d03d04a801761010034042048116004121020348540c41c0041c040395075660710780e682d050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 748221438 1250 748220188 748220191
    0xa09030b1303030b01110d1404270c030506060a032003100e0a0204060e13020c06010f080c01080f061002030f03090717070e04080d200d0f14130302030f03 68
    0xc0241d445581c0a20515805001d01c0315030f00420b18003180c0030010350828640b616400d014041c208000c61080c0480f01032044295000742c40c0c014148907060880c2010b003243d000c1c0340d0f00341c0c0c81c4c3c0d00e08000340841c0c024041e01c141c51203040060900791920420100032001030010551a88096010303555400480d40700701d001e035120345040703041d0510490426400d100301d443e0051900e80103038010002400b03802e87c8800b880070a527009481c0540f003c01d410707107a02d02034001d03280050124070504000280180d000406a1700302c07403081040d18243d0a000004643e80c40003160303440d801c40b070310001203451824081c13040d000a514910580c1e04002042401a00c0c5a0054400c051346030b000c01410b1003003048002501e48541d04800040840c2d43c9800c0310030b034000307100800107450300d03d01050085694150750407080302d500c2e1207000c0b400300d4981249201d1540e00401d014440080c03403c604256000c0b018411007d0100d014000c080280c2d03540003282e040c20070342c12030031811030105001c1055004c68260245 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 748222688 1250 748221438 748221451
    0xf0a030305090f03040b070b0c04150302190318030e04090813050a08240406020d0504031809060b040b0703091e081b0d0210030605060a030506030705030c03060a020a09030b 76
    0x20900c2c1c14910726071072030826948003c102c2a04104000c01a0207080401c032032040303a01034482a145da5400309180c49502071a404450440100014403440a44c10350040051107015181500d0400104070201c046079045280300e260048240c1d0b0701e4000c24050101c04816800040c4082951122030b030360110141c1001080034010103040b0380030b2009180c583d20103400751141000515110900c21401041d0000328900600d00f41d411b00045020700125070110340d91030161100521181c1010320f4000c0003000600120f034407125100130080b8660b9001c0c041c5404035820b5100560807c0e007069096011540501011828403818510014400702c1c481661003107240810b0380e20360f401d8902101c2d241840155289003072159404500440c481e91103403000c800d0250107903412501000320500c290014061a0030090780020042030085c1400d034541c00940c40341030142c0540358202c0d511400c1c19500c00d88c01448a030f1642008001811000c0b0316070242c9001c0f4101e01e00400c940360780762034140140d0020b6441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 748223938 1250 748222688 748222691
    0x609021c0501090b031c140a0f03060501111209060c06010605120c090d080d060e0115030b060705280b0403050d15060e10050c010f0903022e020c0f0a0303 68
    0xe880100c49140300e22030041044140c00c0c440a040c4400081c2c03505003500325040020b160308808030385180300c0c1c25107460785004900501d5540d2407454028014440c000e948800003410884040340552103241425145c24101c4010102d0908040107003480fa00440000c90708400103001c0300440358402c000e981c0c003c01041d11020b6a03940f0b010050314030300d10001c02c0001406e400700894100b9450b50024903404940107c41d00b40c0b100e001a0506000d0503403540300e4041300e50341000200c3e60b6a800c0c00b05600d40c42c880e0b102044881b091205004050103004405026504109040b41c4070101800b4410040710507024070a658541c1640c0349000c0c0030083d5810780c0000d501044980101e80c2c01e104d860404455100030302043ea01d0940300403c4200b800d8000c0d800b4001c1e01903400040c0303016905454081c00600c000b0320250343c0400541d0000c1030805400d41c01445030040c5401501c10308480d4408204543e2031000c1c101417030ba643c800203903100c161400f400781f00e00000d05001c41428030900129502c01d030f90 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 748225188 1250 748223938 748223977
    0x30c0d1a0c0702030a0b070507020a030506090d1e0309150204030510050121060c020f01091511030c0711280f05040b09150409051501150c020f090406060902 69
    0x244004403400c010403501e0140700c108001c00141e030300002c030342000c3c5078020040c00c056070315074804840d01c1c020301c0402500444070040c040b0811901207441d5200307080705012105a6094084215108000d04000145805949282000141c4a500007414550285a1701d2042c0c0540b0400b1784200d80c095401500e180e04661442c2c04088010f00409004184540001080d44601c0300201401502c8000007404941c0d511181d4181c0d42c0244540a0440c0394100200550121070620790448101e4070001c0211030f20f403040c00000c4020950a50303004641555a040c01d1031010343c0d075154080742400302240d1112180046144080144261048440c84080c05030903203882c1a42c00d5440001e140c000c40d01c510b050510384181e80e200c80702c48a52003010307031404000e40c02c0c00c0004280200a00030015010740a0048a01c00000307083d10707100c0c1202e01480c002c031450f0124280c00c803480c4880720700007507010154082c02e5503e80703070250b0706942140c01182c3c0001c103596120018400c0b80c1c0900c06c90440b0088170329 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 748226438 1250 748225188 748225223
    0x30a1a09060a02190305102114010203070f1101110c0a0c2106021e0301061d0d080f0a090b03090c0405100608160201060b0f0415090608070e030c0d 65
    0x1100c15040b00c00c405065042a801000c07000d181c4050601c40000c2682ea034000480107060b40920000900c2040c0ea40d20503c0421540c541440c09002401e646000740181485089181442140d208aa81d035684844842c1d10f41001c44003800840d00790307100c540d2568941c01c03100360118001d01c100b0003210014070814050f40780499024080d0b90008a00d101c11182c040b501d81c0c2d0f04118a01c0481e0720150060340c0c1c0044c208c0c0c046000c08204039250f400b50001c000810400c0e000800c1c1e4400c0b4030701c00019004444c104c1c0800c0020584000c0082000e4001d101000b4810568005400c2c00c100382d0070540d40c101d8441114104503002140e0343c45860744000c0040c10681403034400d41c1d422282d0342c0c2c03030450840d08090000d07040d0703540174101d9102010701d0300b100d0388507520030361023500502911944140c0d1500480090461500517000e01c99900a40102c6c1c0c0c042e09001d64903a000300c0d000b544408000303560b80c42041e152099003050468160040d54296080c66543d5892080c00c188035002200b05d0100c1c2c80f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 748227688 1250 748226438 748226443
    0x1303050d03050f18030f070302030703090b040b0403080706020c060702070f0e09061621021314011e030608061303030507020f0c09070e09040501090524010311030a1a09 74
    0x242400e00030700d803424040c810841c0b41110300a0380070315410040c140c0f4183c00d440c41032451003045500001200081441020142d0100081003914001d42e01c0d00d20017501e54031081d80c148103610880b468540200010800140850003902d00a401221b005003014030104100e03042500445006005821501087c00520418400980902800c00714060185440c124207130795600003402c0005608845080301e0201031055010020f07c400403c1e4070100220003080c1c81e8007942150000c00e81690b0b90107800f08540da02c01c0c4201c0c20801c4143e41d9421580030b000301c1c0071031030135041600008040e00c0300800301d520350b010003d480c000c00341008000b030741300590300300141110006030007017085410102e10850058000154202c0c01b030802c0f200d400749526006800c0d551100c0d8208220341101025041005021040d803000354524058802d642c06412083d11801e0a154850b0708080d07240c1d2200c00510100d01c0e903001d14010360303002400b19018000c09403a2000e182c01000c248081c80c2000004110701c03648107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 748228938 1250 748227688 748227703
    0xc040c02070509010330020f1203060f0d1b030807050c0f0112050a06050d030203070209060901050d060203060303041e061403070503011403070902190e1801120303090602130305 78
    0x8a20103004480c0c1498005070f0442818400074002d50300d190b40c9907800a1042c28905848003102400e40044031001c0c401075104c5481416803020f9000d41051010229900e00031240b041c1401001400c0108500c001c1108446044005842c82d681898001d40c00e0310f012081e02d0040d50103000166165841440c10034601090b080609000320100d0303d00b9002079805c00d16180004102074001b00700ca641d060b810100401a41d4025640705200305602800d164000c4010008980261001040d0399549024416a1002841929001844a0500720110f25243e01841e00030400400f600d00e0147c0d1000a044850b0341d00d40d0100070210078500030080305803c8590080040c1301440301c0ca080d85445c01018200d40414070800e40c401070104c403001261f0784c09200c050040c06050300704640783c0041007162140c0000b041800c40c04150420030004540c50400c212710020102c906c107000c516800c1504c40418001480d20450906480707114190001d00940064074a071208603820410041c60350404a240082 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 748230188 1250 748228938 748228961
    0xa1401060b0909091c050403060507111903050c1002091c11011b170a0e0a0503032d28030e0d211e061505070215040909050c04 56
    0x54a282009000101070544102c08802c03940d141080c1e48400d140c5084c03444a00d44424a0034040085900190704500503009981c000c0108000550300d1041c181d911451401a240340d661041c40503045241c00f507003216500030f100340342850808a107849154034000f0b0795000b2500041c1c000c568481c2d50b0a05442101001c0200b030a481400c1c180d685441300c404105001c140c2c1000b4084510080c5803512a80310a0250b5100b03821071300300c0d5003440d103000d05c9030030047e1080d00081014165494929181134114282c0d00020051480e0010108005039003c2d0741c02e081c40d8a05848141c000d080c025070f00e000d8003480041090130000c440303a12505011b0010a403e605e0149450b2400450207118000740c1001510402d060129036008156207203c7c4144211b40c440500604011400c501c880b0402110701095400c03007400e100d00d6460380d0b01c80c581882445e070b810b00061401d0000784094038002051210303582d00509003e26068030b4640d0b45042d00c40e01c0400f500c1ca64410b80302e0b0200c5050a2090219062 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 748231438 1250 748230188 748230191
    0x3030f160504080102040803042907030c1e051b0409020603060904062009151c05220609020906030d02060f0705070609060e06010603061a0315040e06090f030a1b0f140a1401 76
    0x40f12b886100e40305005079000078040280c1c3c0c00303001e01000080c00920002c541d2125088000752402e151031503441101000510789549d00c0300c0300307052508180c00362001165004003903a0440e1340d540e052000818000300151246a101c1c04a501c414440d000101c80714183d0303490f041d83e1083d2440521602401d680e2008071149010011000e00c112040c4041d0460b5410100108941c2ca90f5507183c49112410083c034110305500340c18500130031086900400780c4c14030030b0301d0f034180a0707860078101900c824110100c900581c0003440007411980158600590181c01420700c41e040c901c25468900884440302001c03a1869943c40008480441c1000198010b061030314080c44550b0400c0b0a0203400c0d000078440c034038800004404a030944001c004030343c510702c85c09003082100045410744256298816180401d003030150111b44003080c85c001c8115282034009449150710640340d02d8950840350b4400200351a0f42c125880110f001450f06400e51070030002d100020a105091400c1000901701a00c85490382d07603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 748232688 1250 748231438 748231499
    0x3070506010b0a09051905090109020408011103070c020904031b150b0a05012304090e1c050304020315040312091b050a05030c09070c060501030c150203030f16050408010204080304 79
    0x240e00040d1a0103880095903405000e02442500e406d10b100e094129030307800240200041443c1c10954040c01c215030403400240000104e920005a00303200c00d44800300054042c03416800541044086070760028840d1900d4110f2151000b1001e884491450048802104628106076800014020048020300480c6c001d00b11500c0d24002801d00c007007100d005000e807160700c100c228243e002c8409540040c8200308080c00440c0e030490307003542c41b0007541458030460107000d15076a01051080d0244c0307100d540d016000704251010301000c09041140144110304020210189942c180c0341c074001c003c05144500000b44100314240f02c2c410048041c0e802ca03a01501420f101001240d600040d101024481620b441d20203881c2c014040300c607a9004e941c050500c0d42080000020880c0d440300c6142280c089411041100803041c6040380c07203101c10f1307507540c2505003514040b645100c0020f0940790320300c4150912603d4281d80d03000f200e003680c02990101542c5e0b0070102c0d0400210f480105034002c110201b68448010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 748233938 1250 748232688 748232707
    0xa0606021b040e0102130308090103050c03101406040503030c0c1c08030a0b28060f030207081c15060c17041508060103020d0501030b150405130b0c0706090503070506010b 75
    0x39101e040303071118400c41c1c85a9000b07208003000e44c1120b001c400146e41015420f40c4a0801e0555a440a011280064175120004001c6801c00341a40e005e10008400d028003d880c040c00400b500c4401c2c4681ea81c0104108800640340d58104020811004e1203800f9040040da580c00300504040c0c0280c04a520352840e610b49400519200c0480b0362003c803008000507240780c91000b00d042a048144459401b040b003210a00c5030104040715001110925650720b50107403003416040b400d90203035180080025406010113404d440552100d0002100c0d0528002000c141880144c0c205050a500c441d011035074000401085c0300c4800e843c0d00c1c202c02d03100d0b9200d141c0fa01d80b0030314014041c01072040c0302c1007000d40000719105a2181d01144c88176084140c09110071b5869003020f001031042510003071104002e4017440030403400d10703000300c600ca03002022080a21503007507122180307181c4008100e000e00358810458070002400600c540260240a07400468a03081e05180040c642081a000184450b0084c81000070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 748235188 1250 748233938 748233973
    0x30a02340c0819060221070203070c09020f1b010b04021c0b060f0919090f0b1e0105030a0f0b06030907031a040b01260d030e191a0c0f0f030a060602 65
    0x10740c0d92104d00166600649001404404101c40d40b5010380d4408200388111540d002029241203401480900380c4160707124544022131243c0c071000084424280314110b03815848619105114115000209030458000c0008040380d04c4001685045040410b2440840c1038134421925101c105813001c2d8071308804154a850580a01e900803417240a001c4521009200b04203402801400000814044c2e00d180c1040309002c0d14141d40340724090090000914401409204100440c02e0181c490500d9030303d403068034401514842c030000c00307c561030f000001c0f5252a03460065108040036000340c5140703421031615032031400250034614110b0070440c09220114044440300360444900070034411048000c01000d00c0b190322415002d92640c02811100c0b5540754054210ba160300c40900e040e100608040249000d1014070540e000d0170100c110300702c2e181e2100c0e1181030260003032080324945040424150214002da408828410500140407051020a03080d0307001d008050305060025000c0e86212494059 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 748236438 1250 748235188 748235233
    0x60207050a1e0306090b0f13020a030305090411210c0c060c18041b020601081f020304020103020c070b0a180308031b0d062d050303030a02340c08 64
    0xd190200d15060340b0a524103803070202c01568450024807a0503424205218045000c54102c80004541400508850101e1602521030303540104a40381860445d01e0896050b04040c11860b041540e852010b00262181009032603020014950803040804c19075050100c5000500040f1900c0014000403540c0c04012034490380c4500007094042c2ca400165222a4285000a401580041c588008042000051106068002d1140d002c440d00759a071400e4180c0e80d1400c550680d0605d00c18400d04805840d090b030001e503003250051402500b00587c00c100f00341440c00395808043d068400181660409400c0010008040f03040c0c900c02d42d61a00d5a01c96050b0f5120084c112003104001c814189448601c51064495000103d101041001d4880c0004101d0303a0f954410007003219001220703112105240c0301c0e01400c0e18006000b6506544910040801030340142034a4041480d03800c0c05415003041c01c48214400d40c040317051f02e84010300c1e0350410005c40040768000c0496a0400c0681300d601e00901240325 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 748237688 1250 748236438 748236449
    0x3071802030403031e0209030105090f0c011b171b1507050a0306080f0309030c06070f08310611010501030c1701060e01082d070e091f020a0207060207050a 68
    0x241e620360b142e1804400601003c0a000403620302018010804102c540c003030900200160003c000765141d1030f035855174600b10400c0c0a00e10b50721035201c43d6403d5108003486000314544c1d400080c0c03000a903641e00c6c1a82182040c102c0c0c24841c010440c2442700704481c0510400e13900c0c001c06031a400841481d502605400145550180031000900c3c1868034400d40c0000b0082854034181c4e0300230030314402255181d502101072103110b8480e0802c184000d1034010200c43c115688280c5203e8110407a0390340f00016009420340703004200b241c00e01882d0490445008c2511b210300d0440c01d00919040c0745003d40444d454403590813044c1c0c5050014400208841201d8090310940f140301c5c09484140c441c00380c0903048541220b00c001142e6000083e803107000003000a150b0000c2880102d2704111240e00c0703d09007411205107545948881d204000200096094980100c82141681c0324944400385849840241c04e0800300015400140561015418040700001d4240340c80a0010245014009140095a8000c1c07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 748238938 1250 748237688 748237691
    0x6020a0f02072117070f0606060905060909070e010c0605250201230604230106270e0414190506100f03302a0f1401061a03090c030718 59
    0x40c00c4200d0100103841a07a03506c25040c1060303c00d1454150080c0c0340c42d00c12100400c80546003c07465240000c1924107105000d420b002d1241d440c094101c40040c2028403150620001c1e082400200751b584c050b2074441c080010ae030840340c40d0041c500c400c4074000f0408220441e49420040e1910307002c02c802000e503944459800c50b0054032240c0c00500284085081080c00120f200c0c1005481488040c405040360002c3d280c28204154407801020300400c50b1a1030b01d1035a955040c14407020100c0071250307401c6409100c0042c0c0004d03107000c80701d15060180d900000c41c803400c040e406040010401111380d010000d038610f682081d1420003182c00400950000804031041d03007044681030365116400b0041c0d004001c0c10f0072505c00c10044003421451041e043c1c806c0442d002c03110514100c103d188a84981540060070441c03820464580280000010f80704418554031407400088421025848948604a5000090b5a81012010a0302d8242c90510b080d00035040600200104864409104085101c1d40e00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 748240188 1250 748238938 748238963
    0xf01050c30070b0603071202060403062c010e0607030c0e01050903030f030c21010302010512060a090f0f1b0c02103b0103110d1806020a0f020721 64
    0xd50300d4032520707507141001507040c0200b400018000400300342d501640c03060f02a1a82c9039101e40640d11804a1088081d41107141040100300282c01c65110f0003928210f43c1c000c4251200f06404484480200c008804ca980c3d120440c0ca15180018405540c000c3e0b0315090810100102d03610141030080806c4005050007008620300246440c24003c0b94291001100c440f40c1d03d25114001900980062611030844200141c14071170390300c07034100d049050341d405071035150030005180c25025032502c009000a420804490b00003c0700300c007500515201d27418040d400300708149048400c4003101e10b8202d103804800b12a2425181c402c1c5c02054502c0410303016109030200341030001090701c1c41040381c040c0544030740da8942010245640c451503a45c4450b40300e040081401d000034011410364020001c0401404010070514a00b6003079070b404000500250300a07a12401002c0d11400704903004401d4141c085034044014400e500d41c1840424054030342c0001700c007a0a406120700301901030b50708030020181400010b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 748241438 1250 748240188 748240243
    0xc1603052e020a020c061209060109090302120309190506012d03060b0d120801090f021c0c0320040f23060901110609011a01020102041d040f0219050f01050c 69
    0x102520601e01c010b030091f980c400c0d42d40c00e078910500d42101d006607140580c000110b011101400b03543c3d407040c1c05500a08020b02c040c00d08801d181c0c400f4000d0b12283c801e902c24015008016500c001c8224001d0014203140d600d000c088948003000402c0041d4203402c0140f0440f4034503034030502c8000f0380e03401c8503000485154003008a6080e20345403801800359060b24070b4000c030705c070762101003507060b224200c10510400490340307042000d83c02a02e20b0034440162880d040f00c410000755214000404c4d16140101c0c1080300c3c4804840c0d10940e1014116020b20000b0301400b030710520029840042500880315002a140c41200070344443c01c2e240d040d40b1039400020b0b200c00982c8a03c483c074030154280d00c1902c10608101d104280241600581800c0d85001d143c040300c5650300600c203850465041e644141c2d614550728014405000001707108a41000b044d0012001507210b1603640d141031078441d140c4801d041d007080100154100c504001e141041000c014030842e010300818642d017144840884420500640c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 748242688 1250 748241438 748241443
    0xe0d02030d020d2304030e09042a09020c010603120c03050403030c0501020f030a0e01060e01120227090a1109010b04030b10030b0c0703031119080c0c1603052e020a02 73
    0x446800c100c0300e161005204c4908201c0040c41c01030703101e81c4600318848090024840f8980c4d04444c043c01b040da80108921107021901e464005c17410082d0348900d00039440307414000c00c0f0b0300040031046050303641c6c0e02d041c420480d5502c01c18100351441c0c285102101c070661b500601f2489140001010040840301c00c1781085425010b0711342d0712002c00030080d160310300a00100f00500c070b000034041c85036003048030000d00d8800c1390503958103852a440c1c00c0d8035070a0054081c89000fa007444605002d551488a44000c4910a81040741c0a1607400002d04050600f504103411460030f00e9812501c61800c1100400000b0030721070440301202d40c040000305a47d0340e00100c04029203901d50010b40854600c0e002c201d80707034010384002c0c050580309450411021000140800c498001c660380c3c5010310079001803280025010301c100c242e1011180701250310708007544070003d040161850300704e424840f080d00248200201400702003944d00c03411001210650f98004041110744035000101d03011580000e0104031a40309 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 748243938 1250 748242688 748242701
    0xc0d0204030807081812070b090607120509031c0503040f020303090a0308040f0e09100b0a0f06030510330905150903011d0312070c050109150e0d02030d020d 69
    0x412034007529140d207810410155804407541420b140d075403405e4801c091628140415001e102000242416030070150043c840364054145142c1c41a414040c20340016100c160100c005100c80d5180c039204d003106418035182141c02c1d203c5501541c01442203880c1e19074010203999110344c200c84400542661030020a0651154201580d0011a0000c01006000000d0010021202d855484e0341070340c2e55030000903103440000e0300e020341e030794010100c051401c1c9003580000400544c02070112024a03910111a1001030386688840d001c82e403184200b007000d06034602503400514103410210701c60f0340d140080034041503401426610703a0700c00d0345109240c64451004003014020140030555100544104c91001ea00306d800860b10940c2032403d103c0f22142000282100059000d006506082c80c650343d04201c540c00800350700030003010340c01e41303404160300340641c0307030f1450040107000320400100c0b05400c20743c1c1e07803a14140207075442105842c894650000031581107a185e4500180c0b28054904260060f004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 748245188 1250 748243938 748243943
    0xb120706020a122f250306050603030f1602010806010c020105161506080114150a0b0703140a05180613030b060a080313060f080c1b0a050f2d03030c0d020403 69
    0x44003040134181d20100d150b02c0d8401040d071002c80e0824007400030710031250340200e40d540d4607649001e101000010116040301d500f05100400340d03401d2a501d416a105c41c2d4101d11030402c03640042044030420b650f00b00800980140c82840c1c5000165007640004e03105200d03070004035802d0145a030102052000540b480d1f03040f04003008044c80780c196a001c4050233480003030b414014041001020940d400d02d560030003210164045e117070b10203041c0b6103100446035804c41c46d000d406121000600b1140c505030f0400914807418681c80b044e4640002c40b00440384001100920303802018204401c3c8542490358445608495000c0001c403d5a5591804203110b140e40da481043c0704c1c0b00c003046143c45d00e46d03407190340e4050f5896945da0103400030704040c044962210503180902503000c2000540701000c42040702003861105001203824490851707075080c0ca07140407864000d0061300084010b641c0c003034150041d1894401e408943e42406404200619201d10000d08201421074001420324001c04407501901c00658 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 748246438 1250 748245188 748245227
    0x301140f030d050418020c060c0708040503060c040e0610050d18050a06090b0c04030c05010c30030f020f12040201140c06100503011e0b0609060403060b120706020a12 73
    0xb858100203000d907000303402040c0b41042024040d100560851003542c0d08400380d40c0c020045078541c0030300300040d40d0010b07005840300f000c100008541d5840030003d45000f81c8442601c0780c0c2e43d80c5000c0207000b400d000036001da84541100307641314403070692100035517029400b010400171341008041c0b183d900391a0420790040642c0101c14103141444043d0380f10340100c500031407030700900b60340300045144c0c14450390200030002207035a9000e00c11035118038110300754140b058240922003400b0202c4688510a036403108080300108010240d031603507040c01100884c903001ca509500308041e209501c0d0190044006050440c03a00f840060290380c800d4110402000416541654408200c05130b1a01c40c502282e000c0442d070500a00010300341014460040c071034070340d011609045084680400086c1000c400c00071352007601400301c0c40003580c0e0200108000e52142c14000380c40c0e1288014806a10ba0003243d0b020503030402803003003110980104200d090b40368004a6440c1c1004c01050039103840c0d1405c4508402032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 748247688 1250 748246438 748246453
    0x2190e0f061008040302190c0506070c0303020f0c0603010512070e0406050103031d130518071701050a09080a031e02070b10090614090411030d0f0914060301140f03 72
    0x19000c09412801580c0648400c16605000001550010010b0b60020300682c002c840203420141080c590366001403240c00c04c055120742c0c481c0040c2c501c1e0041981540d003105d69000c100100354040101200100c05030001d04401001038000501e5808148142801840350185d502c02400062240402904d0f41c0000e0500310300703050908000030302c000d01040740444d08200c1c194891350071744041c3c1041d455000f0942c045560702c042c11140607000181c02c14541c0300f400f09000245220070302c150070180122450f01b04200d14282b0103a42902d101400c0f180b109440c1c13600b010007080b80002240c481d0300c1c0b1800c000c24003080c0300c000e00c140001400485201ca070710201d0500200003400321000d0295104071080c12145031110b00100842d0201c0c8941d0001c418449100308a41c2420a030003030b031290042c400800c40280c0d540c04a03041100c0401d804002402c60f48040d800385400980c2031002d00315456030790300d01c2d554901c042444da04c410f0003035010b201c0c5681591890307540c8100c01181140b01c0074041d0b0340036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 748248938 1250 748247688 748247701
    0xb120105070941030106080f0a0c0b03060a05010507030203091c03170702030405190e07030509072309181506121501140d060212180d02060402190e 65
    0x1011030034054410300380c8480c0000e042c4454020841880721036154521000000b0740205200203024250303d450300355484201c00101c6070b8051100b000340c0744c1c400010713004402d4a450440410390303154100c0010840c1c14003d00520b80c5503911075500b03903402800c010f40e9504032420164654040e02c04c1c1da940c81481001c04041140c1c00510f0488601d220380c80700d4164590541601c40740c0c01c4222004c8005900a10081180e0301d4080c044041c282c0f2446800400c554030f030603800e142544100c07500000709803500113124484d2030070000f650040481c0325164041c4500540009000042c02d1845c83c460010782c0003041350f846a0030b00382144124200121003207580814555072000c40101c50300341c0320fa46418840c00c0080804940001c05c000181d2a14403940e0828011741890001d564946810010f2440000c000800d1840105804506008260040d00c4c0590a455140e266281c885c50f4603000301001c1d50701c854001800742c0c2c00076030446e10141c100c03141d4038444003100c025501084506d01a4030030f0109 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 748250188 1250 748248938 748248947
    0x60910090203070c030807210b130905060117060403090b0d0b060a0809100204030b04060504031106130c1a0901030c120f051e01150804030903020d05030309060124030b12010507 78
    0x100e948251528000d90755503007c00c1d146103d8075007420340700c005840494032400f030381d40d409403030500801009040c8192004120a045981c41603040307840e40d010304014404000360904001c5c488045070300401d039604d0195002003c1c1741052180001d005004110f81401c000310703800070048120b014010340d4039800d47c058001d008400680e41e1a4032406040e0440300f2141c414001c0f201075a8105400f50207945481d07642d20001c0000030030603400c210318046848410302f4140442800b40d1007026441c4c545000f1410943c003203010301e0340300f800ca0007502c190025000d040d81c000e9400b000c0c02401e000494481c105230030350302030300c10348405a007003881d20400004202d4613078461400707600390904a0702d00480c000a2103207100028019a10b0403041e035148014400d10443c01164058401c1c0b6203000300c81e5407940400d0030400082d500b20340fa90030103c10044481410440e590050403805508100707441c0302d1a041c40342550088401c020180c40300e82e012150b0701c4042c00c8543c000842c000030445490034080007030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 748251438 1250 748250188 748250207
    0x7060504110a08030a0c1e050708060601050316081005060a0906021c0819060f03060c111501060f020312012918090a0e0a060219031406091009020307 66
    0x340d00901d025003107891414403075845000d550b210f0008601d80880742c039041c0d9000c1480d6004446140303c5441211041d1074180140038090700c510014000182041842c5007090300c028030881c100681801040360441c5604030710702c258409400c0440050701c42142c1a004076010f40c200ea600140300042031001c069001e40354400300c032080c0d42903518442e25802d18140c80804140c41c40d002030900c0d40881c11600412009208200d90504001380c2c6e03d980781c0c1942c1c04a00a50320030b072609a5200002860641c001f0000c0103480107441c00742440c0b4001d0400700b00400ca040c01031b0010480714030400a41c10340200300325400e901410241104030741c0c1d104900104101403540054104075041070351451600358106982911180d154008018000d80007442207400005004524045d121145414619002d0040ca10700301d0141d980581e0f030f0b01001440e1a2007100c03402440c020503141c05d0100445c482c1d0300c400240c000f0422a0107284c00d494104100c54104496040300402d107200100780000d084e000032518 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 748252688 1250 748251438 748251443
    0x1f0f0327051e1b09010f0303051b190c09140f130506040507050a05011403010621050712150614090303130b030f010b0405030c01140f0406080406050f0402011d0d020607060504 77
    0x39400303d2a043c00340100000b0038030850105400740786042c00002d00a2002c0c0c20386202644000c2c280c5403410348081c1c40e04011000c0301c15402500c003030500c10b00490744144805440402c4061208100c0c2c044802d480e1100244000583c14210000c60310b103180040c139110450380c01c03004607031040c2271904109072600ca040c408c00784600003c500010b800d5001da24400c1d01c00d1410f00c000c60550703203084019620702c001000c0040c1c42010903a03044100189911420b401039049030341d186200704808814508482e0240c012103c4c4200f021820400703154031044002816403203c00b416114032a090200307255010788016486994111303000030901c07054042c091403007901304201210040c0d0380d60141d00740510a82c055142c040d08011540c580c0d9500070b54441c3e204411600190b442e10200c070040003020740143c0c0052000076600808c1c001800702c20700800e07030001c410030000c0c81e071401c0036400a094611500e101d0845060f45103115803190f0340d2556403d804d00c0d0080c0940d80e407030781c1c80d1520740c0092030121400c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 748253938 1250 748252688 748252723
    0xf021332180d0c110d08030613150302041109091303020c01231c0204140310022109010204080a1a0a0501060906050d0204051f0f0327051e 61
    0x10300701c00035140d9450000114501500d40402040302c1142ca61080030410350713090034204501480b9032100e0401442c0d96000d0a00151203040800812080d1440503e000a200b41840100044584081407080441e58101d40016035044003000a080c80e0190704c00c1c041e803085242d010013908004003200010301500c030390700703960051148000565004804940340f00c40d0344244820b000320760707100da4020240300a18912544070301d00c43c60928001d80c2d200e50070440448410081d0856a07007003c0201e00000d8281203000d6040140b210102e950340300360f20b844d840d03ea20495020030035498017035040380c3c0502506419503210211506280c2102c01c2c01000340c007031070001400040e0720b80c401407103258180d0710705550b08441c0e907140c600116940d800c01003184280310b41c02c11000526640c2d610350149403401030a280c10304002800f9001d801e00011030408000d05091102c00d9001c862444200519040a490742c604640f8103410705900e00121070314015031109804503100b148600c00988040340c0c0e00e02100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 748255188 1250 748253938 748253941
    0x203040506010b0f07030507020d051b03100e1b011704050102071104140708271e070b041e0306050a0501030506060d1104020705010b0901030c031704030f021332 71
    0x503980c3c030300e21035101500c5030140e00380100740c00280302c0c100a0091394002050340c42000030a4840505000f03042040740707181041d82441d403105080900c000300448440300401c200c0000d45c01e00304c0c0e03101e1003082501e102c080740f00120054981c1c000d030380d120301540b0b201055901e603150900c0d0250013980011070a0f00c3e600b000454516a528190080246c5c060290340465080e49416000b96000c91019209841103400f040750070300b2800c007081025046040000c000e128454148035a1008106c61014603042c9800148080c010f02410408907011281c4105400c2003028554180b100d20b011103405c004e01503400d080c1841500402504414180c90041c81600c1107074841504029880942d4640148a20450400c851607458594050803506001d07100106003a070003100003d4110740300b41c204a034540042d200c14001c6c84074244052513504c6205132400d152504503119040104080c8900070702c10903010200001082154010071401e00030820800c00410049800940700c0d604210681c03801150a030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 748256438 1250 748255188 748255199
    0xc02011d0309010309030e121b090103022202070602041217041a0904020903240702010915020a1103030705090102011a060717040e070c05010506030d0f050913060306020304050601 79
    0x208414a05200d0001036180030450401980030b09000340050381844840380d0b840200c3d488802c0c41d400c20f09007600c082c00242c0c420207501044960744144450280c0d41180c0103100580701c8049544039801d050341840c40c21001c103102103010784181000140064000704000541102c42560f41403914468004a02d90403010400e54266010303a101d0483e048116110817032484117400004c02043c0400780000d4034002031000481c1c50301440c1d900141c5465040100b44400c0004c0a50054101c030440c030090000355519150652101c1d901c80003803054030b900042c040e900038042d651280c03146180b0310640b6187d00c0c0c198400f42090304809003042c05075003001958440300404203002403681c4002800d40e820100c4070740320003400441803007030380310308050030400815401903604000d07105101640d0340110070341c542c0c60610f0a641020700406d0096004588002d8116004043c1e20800440c0e480d00765120205000081d180c60007a032404101c0134503192010082c00015002140b1480c003d404841c2ea0f81d80e40c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 748257688 1250 748256438 748256471
    0x140d0305042001090915170c03061503160308030a0e01142d0a09110301021801050c07030b090f0607050c0d050d0b13050106091208041502030714010c0201 68
    0x310760003800c07800320708101d8039a000c1c107000070180000180b60890070b1a0300d64282e0002c4034001407081386061040b0100300301004d148030301a1810800307100038100396100040865960380e0701070800706c074620701c2c0c03030101005450801080b1149250446d00c440001c4d80c2c1e080c0440c2c1a84160794480d142c600301004008490f00502408401c030102c07206007901c0e6aa0000500703401c01c408c646140303640340703130110b403010038030315841070382e002d05102000000c0342c1c502c510f07010644d0100c1083d01170003640180414a4001504400c41e03003400403c1c03d10303698900000340040d040a50340d07080200004a83c0c424460345c864001041c04000c813480c0102c4040751500c0300c1c181c501d130040031285600c0f607000c108503c4c2514840d4004c1e20340e00015031030101d2846280710000304802c0c1300a0f002c030150f60360303040100b01c2180d124807d400100080940211501021380b134040a602c01c601401080c0000d9541d820495442007040320b841c0c94200d491412a04011400b641c040d101142410340158208400f0a8016040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 748258938 1250 748257688 748257691
    0xd05010320010e1309080301080601060e04140609040501060801061205060603062a0909010303050a0e01030c12180f080a0201240312020a050313030b13081b01110403140d0305 77
    0x16154000d0460340f041c1088244680b052442c52010b885020250000f0790450243d0b003e44a0000500307025814800024400030342850311512079401c0404010b035051030100c1064012030107841d200200d130344504025014006617848940c1d0b942c40c00100183d842c9213501c1a6080c1842107050752a030351540070405a8604040e0744c8140416420340a0b00080700c07030010007222442c2505242c81c2803221150010700301c80800d0340141c01050b000a00c0d031024a900c2902c03800811f0090808001c0110010300083c018148001c00c9801c069413880c014540c04401c109103d0300941c440300c440c0d1a0846454a0446030308451007001c00b56090807121400c410800040c218803d00c01d00020201500d10780316103c83c0c241c60541c00c029400354a036182c01044045c40141343d0307204001e075444007072803840c50281c903150801844252a048940707d640c0001d5480d10403a103483d0032502d0510710140410b20f8803401812006409070f0a0b03440010008100511f01c0c84076000c1c62030400a40301100b151403820340039101c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 748260188 1250 748258938 748259003
    0xa02090a1a1603020f120a030c03060609090b0409060c09080d030b0d0b1513020a0f0e0a0e06031e01091703070807141c020c06090d0e0402070201140d050103 69
    0x10b124001501c0301400700c0440990082c411208240340300c0e0002c41c01c204100d007440c075844100180f0303444001c0e0140500030312492245010440285068001015a0524024243c181d40c81d13981c0700c02c0560340c4d600300104076900554100601c0440d000040e2000a591140f81c4490044892180015000340f207a075100205c040c0104450700001c1d1b49401102c10010481f000c42001c100c0361480d5500c8040d41c6038418a141280184d8680e041c030b07405010301c211f403010b40c0e003007203029060380c40a604c0d101c1c41c1c8002c8a650615640c2c01d42c651400082c207000540441d4a040c4140c0145e80036104070541150045c45d0260a0351214046403444c0030100d4801284c2841c04070708800d0200303c949104006840c0c5c4400c40041c0f01d070800f2540000001e0544600d4020400e20707401140f6074210310300070722040342c1001007003004000c0c3c184243c0b07000d0400000c0c3d1405078841c0740c0c0860740c1000e5900884070041403590031242251b69415046055005010a00054038403012043c586101d108070004220603481 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 748261438 1250 748260188 748260239
    0x390303020a0809041b0c020427260705010605040c05032707090e0a02030c0f0121090212061b0309030f0c0a02060c0a03020d050f0306041805060a02090a 67
    0x44948500d14583d010401003900240d88001800c902d82d17003030302e46002c4403206603074100544a8a004100640b44404960a1150100c460400400b0030000d000a01103034805c0130740d07038440503000519803c0c420410702180c03035900000c1d10300304124065201e40140c2d0011203042141100d0b440c0c1c129240c0c00201c03106801041c015510102401c0b40356113030112000d40c1011200709940710308442081d40e4142040c40303060382c08400a842189824003074941103001c00d880b022440000700c400245900060355420030b0214803000201000c940ca500040074054000d0503200d031940c0355018007503580f5801c58410203501601142d45040c1e5414104a902490410000b18240807005444403025032015280045521a0030781400040c2c9524010f054040200c5d00545410f0409003000f9041c0302118100d0000c00004110300407410f20321505594000740c00b59400292980d080b442007080c944e0145002c2e000e88941000c10032030503850303001404441800d480501031150b03a4004149200d603100c01c040d075030700e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 748262688 1250 748261438 748261453
    0x2010e0c10051c18051b1005030403020f0706090303170402060a03020f0d060311150307051204050c0307090b0f0102120412210c020405130c05010e060739030302 71
    0x40c400c1000e012a140302c2c444203001020b80f101010115040b1045200002c500c0c42411030a2100c02d0200e0710350700881c10700c20514080c1240000f101c214040c1d441c81e0074801c0c0880402c040c51710070030064410031044411588125252007002d801070105110440c0042ea54041c4c004a05458204540c0900e901404c1d040c10650003500950194100aa05004d01d820601540603403d15a0240c04011405144000b060201e65001c0c008c0391071400041e180040c0003041401990340d07205007141c3c40711140070544140754480d868100c0c01c0000300310605174188a04180810032609a0b070042d59500e604030343c2036003508202c0c4016a02c800b078080c00690240c40510082060b8580b001c01c001ca180d10070301a00d03500c000710504124200c10542580d0700017503401a4000e04500b410300c80c1c00d0b00b01c0509900c5d94460700c02a03580701c1001845000e003a04200f410341440c48140c481c031050b1807040741d002c449a07280f84412000000d5810f418240c1a0b035000b08a2174440803118449086070903a500740d03001c0c1020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 748263938 1250 748262688 748262719
    0x702090a090b04081b03270303030708010306110d1d010c0207050120120f030109060b030f15130f090c0b0a0504120c030b041203060e0603031b250602010e0c 69
    0x25402001c2c0318010f0085840a08500c00810300c005c000c51f03025007070b4841c000c048440041d841d00c40d905c08040d000b50702c20004d00c0b5845070040d8010341100d81c0b201340490691441d44a058881c0190903607400d0b030506000f00e05c42803c0310200038201c9260984020006030300581400c0340d64000038400d039804141104440280b0350f6002803c503400781000c1e02142c2d02c12125034901c403c0c5612288200c10403280100041c4646400e90003200020044041e05c00c0c11414000e00c400c0e1010702c0502526003800c110140040c0d99180c0702c2a0f0b0b140001089010817590400a000c3d00c042e1425001c129200c1045c2e0780049005048070060720b02c80c0c1005c0d6501800d150034815505507400b031042090f1958a0404000400124540d030000d209510a0b44030800f00101c2810140c15076405402080f41d444c241002c11600e51800001e0f10030b180c51a0003004900e1121082540c10241551802c601500700c1200f5880d2004030b041005003155004d5000b04110038980d0109a03ea00501d46d81941c48659484201d04d0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 748265188 1250 748263938 748263953
    0xf04180212070305030304030203040e010f0317030a111c050604050907051509090c0c0f0706082a070b041208072f060709140909210408010c050702090a090b04 70
    0x1031054600c0112511070b43c680d22001d10b90782040b03a080b00140c0c000213003030001c45203800b0414010b18000200d44001800d594503105e4400134203403c802e44040102c0040d04c005904e40107007503d803034803a0503076039544c03101901c10304681c64000300d07205028140b070003090b82c41c14248a000d105038190001f811981c0d04003400c0025031000e990702c1710381030039040c40940025601d5400c0d1724082c081e400c08190b0b940c94400d0200f420480d410310178a025410000040110755040910243c4c032044010400c140164054030082a542d0082c02c18443d070b22000c5510020404000522801940a0001408000320500d803c4030b0500044802400090b808a440e15110103000704142218800000b001101c031013031342c01546000401c54401001810261080040369044440e480f90004151034030b0b01145450281140d840703600080710201810840c010102000c11803060710064145803009000d80021103200a246421400c81070f03100f82c12160201d02842d44510904400941c00080c410159032651100032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 748266438 1250 748265188 748265209
    0x506030c071e1509120c050706110304082505060c0a020409060b0904030207031104021e07082104021504081903020f0d0903150509030f09040b060412020f041802 71
    0x2a014a9200440040e82ca84003803c07614082d01c100041e030841d1801c01d088000620301d0f0f13280074410104850b00104101160346d00903079409042401d80040e400855603d14452540440310501a01200d041724550b1400318640c04213001d41a49a1280c85604201d1030f071041e0344201d5076503840b104020005007810f80000c010907014400c0025580c0018010890354030048400302d00503000040e081c001c1040c00f0400007030704041990114104a07001004144c0011105102c1100000c08070340e200030401c00a045607a64101500b40b55035485e0082810002c000068904900c80c00001014041510dd880c0913a401c44540400818981803403900c40240d05240f66015002c5000c0c8007400e0f001803408010510074407401c3c2e0346061001e4910304020116540100344e42001354108028400402000001d42d0b100d0402c0320803450340c4201502c009070041c480c445840d90421004a0009138009002d081012418003e88525014207140c2c1e04120485410042c40008a42130401003c00b6081440366003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 748267688 1250 748266438 748266473
    0x5010501120e2b120b0d061503051c1d1c0201030609050106050a021513330606031d07140303040905090d02100b03150702010213030302160506030c07 66
    0x10f40305a0b100700c01802054080da2448211203508000c4100910341c01000d00c8800c1c0c2c01c00c1c03020014012100d0000340124400680600b040d40c0f41c030038000342e020040010400440e8010200c800324080c180060410404d081c1c083e0300440c0700328000c0c1403803405480f4040f00c501c2c0700400d0426842100c48074074100076080f0009904040d55800d020510040307903c1031501a0049840d403907161008440d00901d88040c140189045130140c10038010a1243c158041488a610800e03000c0e80408543e55118071641030480c0048101007002d201d080c0003019404107058480940d410304c50605490300c514881070300c0d2030030b40e0b0760780d4082102000300c80c440f90746941d01400e005050742d1070a030741d441c10300301504d2082d41c00580c00d40019400c0014507804203d4000440e2a1410600008100384002603c0302c07800c029000d66040c4000004164134800e5048907100c120307054804c1007007916810f0086d5164081e5000340c00360b500303210340425030f072070258160b91142141e0b0581900d81510303540e400b070940200c020300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 748268938 1250 748267688 748267693
    0x30f120c0d0f0501080c01181403191a06010c0b01050f01090b0c012f040618030605150411120c0c150f0a050f010e0a1a030a0501020c0f0105010501120e 67
    0x1905203501c1409400c20b02010880c0109565040101042c104960810558140401c8031074000300841282c0d1450211805803212404104e134440129042038020b40e030b032080507070984410340100000300d030482420700b4210001101543d2048019555041d6070236000e4200144040108034929000710040700da444123151100c01d540e61809602543c0e00b00c80b90740b4540d6510761207a00c0d001306410300255140d18400000c0300901003103c001d40c3d0184541c0c040c1c40c2c2005106a05c5d0110710300803540820045601480030419403410601e824a00400b0a10380c92040d800c05044501c441c0b070300d00c26280d2801d0080003907006515440d0515025501c0030a00c11903a009400402c0044039140411a2041d0300f20004e2501615000400404403a001041c103c2800c20410042c810340f610810748035031180b03c00e40c00040d0103050440005440030b900c40505d034076200301c20b0000e0030413106401070f01100e55803004681d40c0001c2210042d080e42d41c00d018107400a21160600c0b850100180c110000a0400805 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 748270188 1250 748268938 748268947
    0xe090a05040c0f320616260a030c02032b0e07080a030e01020a0f0809040f0c03091a0411090714160312060b1e0c1b090702030f120c 58
    0x50071003c42d4084e07404502c181525014005044070594900e1a2031964454040150300c05040007a441d80607004403980911040c2c088042001401d11a4040107403078405c0040e007101803110100002c3d0301403035420002038206195045410300002c180d40a003131541c0e001044800350121001c550f06c0402e40c2c2991800d4484802954146090080784060716420300500400a0b95041c01340441100110142c1150710286124002c522841c000404050b80580c08541d5140d10074001005800541703490100c1d80d141030091288150154040e00d00e607880703820720300703e034615000d4640304c2581d0455000c4e10104103001c1c861207070320b0514982d40d4084007504041c500c0c01c40c45a0307042e919030410f82c01141038001d41c50701c1c44141500024074228001c0b82c03441c184803a44c05c2000490702d41c041d848591001500b118140f8019190440580345101010301c01c031000104080442c4d2600012410414010030285000c81c060710b00c040225681a94400d00691800c042e0017818000f1420081c1705880444080c003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 748271438 1250 748270188 748270199
    0xe13050a0f0320120906130e090f030414150d05100504060806040b0606030c0c1b15031003060b0a090f0f06051008060d0201030e0a0b0f07030b0d1103031303060c0f0e090a05040c 78
    0xe5031f10050001450103c141c1d00c1e045118519201d604a206c200582c0140403c01080c0e061a424640e032140c15102a00b2221010521344102d000301c00303050103058180010440981103000070f070030840724100d4050005990340c0002d5910345e1030a44e00135280c15100e0000a51904100d001141c0011050354200d18026900003060304150401e141c0750300c80d848410780411145001e48100607544201c0800e036181d420501c0d400201c4040c02d10004000c1c2c2c0d01c2d076603190b0813640c807118842e0040c01194002c3c0850047c00c8246002003400d205000080d0303242000208483c00c04d5000380110030705a40f5404071549440040013103918421108904042d255208000035280030312800c000c1501c5900c41c0201c9040100c0400c12401c80180143d007010300d0800903407225070b100c103810115144c0010648502c07400c0d000100341540304041002c0001078100380700100304a01e80c1c6c404920240c1607a10784c00c0140da20003040b142c13600c1c66841d65a20880728800703d05818825805503802c144603202c124843d0350b403503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 748272688 1250 748271438 748271467
    0x4090308162303041101050306030a02132004090f0e0303070834020c120309010c080d05010b180105040506090f0d1211070806040c0e13050a0f0320120906 68
    0xd1154007800715011081c070040005a500c181201744090070f001d411840d254004c240e4884508201910600742d80d17103806541203141e800092110031100c820884080a80743d1840c0b194014481c02c00d526240c20a403c5d1b030342102c1c0c494450104a4100950301d1500d540c01c04841552000d002040b0b00320203140304000c84c5064999028640c03c480070307028010101458007034140780c490b0350710318098040140305c0020f6030404000ca4032a0b54090070940c5d103803801802c0000c0c09000320000861868988000494000c0007800942189168038200024243e5004011a15030081c1c0c402c5503000442400910303080e16048040800446000d42265601c0311103031250702c8660484448140482d040001c801e8031070380300b400441d000d8002c0f1b0005102c039040550f6900303c1403520744a0007480204100200b0040c038071907407190f501d25400c07100f00c51008016007480481c80e2600c00d41200447c00d24034400480348071a2415131850100c8201414070401030742c45010323180c0e000c2001d0031b90000b801c0201c01221100c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 748273938 1250 748272688 748272737
    0x9030c06040c030303051501140c0312040c082a061c05010b0301092f07020a0b0307050a0e1207030321020705010204210c03021c05031801030b0409030816 68
    0x1e040030304540b074603604002e0f0403034a001c0c08915441c07099141a603003d0341c201100340540102485a0344c0da030105410074030300b18014584032500012881083c802404400c030f50900658a0880941d582c42e0a043c00301c0300343c0c2e41880c0d44000d04000344544034031a440e042d0054125001c00503800000c029590240d01d08982d0309030440e0a50441c01b00061120200c188141003c09400c20309401c00180c090100e108003424062119a14080c0090503130308546074854620020300e090580b6544a0400d440090081e80120203508001408240aa401840c2182c00880c8180b032103406000f040781545c40854a2020140704901d90042c14810039076684a90f1000f03182c80d41c01200016121401c104090581222425442003501218140500030500316002c0d2400c8940c100c0310561540054015100703400b660441c084c02501021034902e920104503c08896950300980c1c04100103405081040100d039a1808080c1c00144803a0008419002600359103640009600f04059400d006002c14032400e40c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 748275188 1250 748273938 748273943
    0x31709150309010c0207090e03070204090206040b12061801150804030201180503040503010f06061b0201020c04050a050412180b09040e16081501120f11040c0c020a091b0809030c0604 80
    0x541d20200f44c038180c3e0501105002e05100742041c4601d00301d13400354994034020050b010380b10300e56a040d140115640c0400300e030018050b08a030980c9850351200000c001070b17012107405000349646098285c0c00c0101080060581d22413140d0300d640d0300c2e82154100d400c500000d00481c00c1d90350710280050303000b9581340000e0f0710324411070007595218288010705d0b09480280d136540d4205414290b051059603000000384041030343c80d81681d00b58031450300040b49050542103a15800501d0841441528003581c2c01051195008109410320540322010454554104d2440300c480003c0021040c08941400c20003072403050401000420b4000301b00c92118141602c055603441d8100c002c500400c002c01e01808044a5041e2520300c10b241c0e50325050080740d00d0150003000410948890381c000c1c040100004aa8488090240c020441d0742c4c3c3e2910098900510030100764440c0c04940c3d00000c0707104540c001d03a603400200701040741403031000c10000d40b42c080019080021500090008031240034040003654070490 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 748276438 1250 748275188 748275191
    0x309060e1b01031b0923180405010506010c11010e04060308030708040b07031a040e03070609060c200a0209180d0503060f18011e0305010e0f120403170915030901 71
    0x14164070026003200c00c030f42c6101c202c410088400301c0800c0d0304104c0b00000c6407100d0074056110813031034030030000500b694104198000407081c441104d010482c403120348124480c40081060f501d9180040d508410075440007400d81403106060001544515400c0c194548043c01c00320700b0742e0726a580c0c8001500b0480c0d80d40c2c002102c08081000f40410841c0700c540007000c07403c04011070000c401c40481c0181000009602458a600701581420b10820840300c1035500010204005822480c1200150400c03407101000121704480307840350304917641801d00c206a0240000c100300300d00c80c1c0c00d100141d10000c00d19410b14915090000c60940e003403082010b00c010b01ea42e140d65a2a000c801c0005240e01c3c041618000c000e81c1d400c0039151031341584424191200440c1456102e91101c10110411056400080865007007069a5445020004100d80d02843c80c0003a40c110440d105a824080d01032448040c0902c00707a8015158a1032030440104941c1c80081c0801c0c00448841030325441130b42c015909030045a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 748277688 1250 748276438 748276483
    0x7050d020706090807050607030e2e14160606030b070206010e01060f021e190303020d0f0207050a03080a0f0603110f060c0c04110c0609070303090819030309060e 71
    0x603414444030780940000c2c200f1071102d90800d64410b66801403409018003070720000a00e00d003854021805810749200081507810441840442810600030300c1c148c01da11141840e40c07400c001070240c541d1100100c85083c5050400c1111890600c0400c400a401e403a03003691004040003007107075035001078030560540c1c00415113540350909600311901c1c140d100c2000c1010031280702150560116401c1f41c0b20504031b4819118007010603489083c010349034a54141d14812401c00401c16400d074000c1c102040d40040d0800035a42030405603020303841410401803294001500b01d03000240a00e200d02c1c1c10140300a00007400d0741c010300c108012200b60750000c0d00d2545502d09481041d14041d03900b041c1212048d01c000b0701b42203d00c40030942c0d800840905034400e40c0c64980c3c1d4580c64511400395506c2007012021112941010080300782c8a050a00041d80042c24031940030901c0c0c1000980000385d61b83d200c04004e0050190344040340200074010301107490b503490710b0003007580c032408100200c204107035800d881c8150f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 748278938 1250 748277688 748277713
    0x40306060609170a0206030402090403090f0801090c05030a050c060a03020d0f0b030d0e101d0405010312021009030203030712020d0515040c1d0f030a0503030106051b010924060b0705 80
    0x43d4034024100114950000e120f00c8011380b40c00b02585c0e00140e050b035900f50390361124a000d0f0b0354034040703401801c00e0310b9032804000f8031500d0542040809500076501241c0442d125010b150321204100805000d550000c01400007a09141c0028002c1007128a8010f041c03800c400d4404003680d5000f008024500d4a4030780c4052030345802d10400c484584e250070114000d56041011989075013500b540d00c1e0910070694943c010a03000d000c0b60814000d0000d10030811580c691400c5c01205c00c80c08400c10051048000a01c04d004817071041ca0501e44e0550011829681c3d50343c42207035204100b0800b1103210360280f0100000b8443c0340501805054202480b050a070b080301e0034002204c0ca100f11280400000d00303400c8020f0042d4041e01212090151011404a002200461b24100351404000c1c00c0384000000000e01030707404000340c04800c1c60500710401800e00103d00c02d003aa44080000790016a1020303c1b940c00314840c007510b25100070b0320310700414103569032004028a90803140043d04c8903080115803490 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 748280188 1250 748278938 748278959
    0x14030a0b0109123c0c0e010602030c060a18050f1005060103021c050a11120103030e04020705060f062205060a0e010303020628090318090e1011040306060609 69
    0x60407004150701024161134586503540c8419103034150b0b6000d00b03a0103400c150604441002c8541c500405801100c000c0e40c5007100d44406140b080c4001c08800400210f90f07544044111101880254010016600c0d00d000040c001d001100b40079614250f00b600751000120148400303035414880360060702c5180c0f01101482d0a85070000c00907410944100035940d0003817100a007462200d400020001025030310044c62200602e0b01c005500710340c0c0c04c0800e0b04400343c50f40600311816244603681e500b0b10b10103080280016400740b2030740181150031200009130301c07151668a03140e11003401400f5107c410142c49030381445113881c03503603540100c0d00c480c1080007d0801030402c1c0010000c6005005031980340d03480003901d490000d401c1043c1080050100e8105811074160b03025281c40d04002000702000524020b0078008011040041c038801d40c0030001440902885180c14410460016201003001c800307413580180580d44130b54030080414080030012440601c1032101074185611007400c035508080e082e40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 748281438 1250 748280188 748280207
    0x30f0d0b18070503180601120b131707050f0102130302010e03120c0705030f0d0c03050a03020702130621230a1a09070e0610080405030909190b1207060f14030a0b01 72
    0x10171580318078010049810b488800300101504003503000419110142c500c800c11305010400783ca11681440c2d00c1e203120004100403c0da10307104804803881d4240c0402c00c0d40c00d07400341c17403072000d80d8699808042015500481104040c50710080544101054406144070b2540010005000c0d96004880c184118101001014814000b2034001c115080a80d0ec1c010040389004200404000011551031200b6000350140c5541a900800b05071410304000040b00c01481c0d02d00c40c001e1401c15a420b4482286040700858080c0c5410202d80341d00d46404103100d080c818503401850030140702d5500c1c010007040d5041c0c4607088442000000c4001030405251061130003415070000e590383c103d140d041c81580d40d0b4050742c2400d6920b8604024047c2d17070725410080d00b5401340b00d901c6c0b0b401481105c01c1105110400c1101804c00d401980c0420500c02550140000f500c01180d1400065105010500c000c90146648803d00d007142d251074405089403e50f88289e94000780d440c24141a191380c041da1081d07822a103c1d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 748282688 1250 748281438 748281481
    0x1a011a0f03010b0f0706091104112701020a1e0b011706010e0c070813060306350c120304030308010b16021201020c150402040b0102030f0d0b18070503 66
    0x560800c061500261058407040c0300351081d8050029101c281c80540b1000c0d51002034008004001071050390a168602103c442c110510844c6051404c94204c0300c40305c00c0e58070340c00804901c0d250040d4180d200c0b15260f4007103206c0710705501c64504080c0c00182d1200c2d103400a0340d20012900a490000e162188550750103030030070301d46811102c5c075400416200160171411190000c5101c0306580b18039405800605c140d5001601d40700d80024a052851030301d1119404880e415030f010840b0703541e5003001d950a07143c1500c025403052508807003005074052000385480342503281015545140003140c001a080c1c46038200346d6800740c1000c1410014141c010040c02d00415620b0700d4503140400711100c20051100070840244500201800004401e00c250305407640c21140700c0496180e020740784149001500c2c1103c040b480b40303040c6a6825090752010003a104010b241c0841107003820702c60140d85010b007455800740380d0844a0710000303080e15014407a141d030080c0465101d883d52414041d000b40f5905003201c7d0036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 748283938 1250 748282688 748282739
    0xf080f041e140315060112290f010c080d0b0409150b04020426100e0c03011d060c0c1f021213020f01030f140a0e0d0306030c0b0706091a01 61
    0x2c00c0c002d48011801c500d00c0c0009121003d0700b0750329031006039202c0741c5806803103d940f80303803c0b0f4140c2440e1036021072240c0b45400401c2c20441c65001010810348101030707684140050211031704c06000418203400f070150203603000c101160806980010074201d6168050503200481414035816583e60140300b4000e1540c81a1025072030581001c6130103441527280e80c4041e01160801c000d452800c00705002c64a10360050500c03d1100d000c603003803207560318810744d10458420351a1005c0e1156550074010780d41d88802c18903024241c0c581d00d0510040c40c075081015400203600460b548100c5800d180b2600024660307036020b006171600c643c001c46800c5031400400040d01544032030b00c524003681d1660b08241594009283c0412060100c07803102c8041c15030200c8202d0070f20b034440180001600d1903080700c098210248120344200820490031010b440a501c009081150428805d2052004084c01010300740e00503035002c1041d01c110f584140c00d0302174005860711a0055a4018000455040b5080c0301c0710f610000f1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 748285188 1250 748283938 748283969
    0xd2603010f03080904090605070816031a100c0f03020d1d03152a04080d0206100b0a05070f030305090f010c0212030612060406020309010c03180f080f041e 68
    0x4100c0c00e0301d0480d0001a2541c0300101d03000030b20344c0d0355400510705594001c005101c14145480090000101900c080b81c0c0000c50a03110380242d8031a108a4086106c0e5042c0b19035200c0140382401078900881d8a8081088100e000d40c1c000310f90380c41540301c0300f240300b91300425001401e01002411102c1020503409000b1254411030100c1c1c0e400128032107500d0762001c0342026511011001c136a0072401101d1070341003100000f140122025060080c100711a40303030007960005a0f416000300d0b1920021108181030005002d010301ca0003580c075011300040250780c14054542005c40e00c0d0f82111101e418022000643c0716020403000c442e040c0b01c072a0511f45440000d00c099040f403803000c0c3d240c10f406804042c4818011001503101c1c6e8800d0360720303100120b010090b940f40741410300707200f400780d441220340125943c00c14080580b1207220f446070b40c2c2c4014443c11810740c0d8441564036140c01a5410406070307032003081030041c91203004643c401040100a8810031011901140341994024522030380404441b440290 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 748286438 1250 748285188 748285199
    0x30c0a0605030406110415020a110a08061b0f03190c08070e011d0d050a1a01050a0b0a090b0d02071437080a09081b060d020a0207050d260301 62
    0x1026a50400d50106010980031800c440c5d07003d00d0701841e40300200000c19085007014141c2c001c640e10078100c1c001d1151106191084041c0070b0400103c2c42802030b59480000000d540a40e00180320040a8100d1121458400100055030741030300143e4546810755800d19031014544414800d5000d403d903142000000c6280c0550302402281801c2e4440d418415240c1c184500750049040110502c027008041c4500510300d4109650707100c008034404c40d02400b540842600c489901c840d114107e0b0707002810b1400d041d04110030b059a6801c000003403001c1c011100400f0503a8004600900a021101100181c0303074845400c1541c80c1c40c410b841110700035040328422207500051511001c0c6007900e5080001c410f0403050000200381030b8a0704026080400120b1100d42d030981c0310b90ba00781100c1102c0d080314045501c2086210140c840c8400041c2d0020042044a01c1645183c0107896640a18016a0480743e0ba550108010918a640494a002d10300310b0952884664200c1c605122001d000420704560604 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 748287688 1250 748286438 748286447
    0x30f180706080f06030a200111030301090501050922061a041d0111030121030504091404020a08010c020c091018020c160b040b0d061701060602070501051314180103050c030c0a06 78
    0x5002c3c4c443d0540c1003a105020340c0e400740e109c0002e02014001100d5996940d1811000140300038011103104e90010310224004d807100d002d90035080c840344c960105500344942e1350000181200700382940c1051501d10314021603555403180102c80202003a0405003030105038004c0f42102e241035400e168081c5c0074801841400c0b0b40007405901c1800c07030701800c0364807072032801c0644d454081c07035206681613030910040ea5034030310349800f030140181c1c825258000300359180c0303100c0e900360780074a10f411005a07c020141251480c0226190307401200c448284003000380c6520b400c50720101c18400301e01241e074000070b025103045010080540c1961900006404881c10304400000910840c0300d100860040401d41c6900210103600140003801c01014078030f0701c12103c10821340a070021348203900c00b6008601c00010194090000c5031010841408410075a604000009800c001c0114005821049072400c100b482982c0c030b10403601035030084000b0501c060b10ba0342010710381000b414106018171401c51040040c144c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 748288938 1250 748287688 748287713
    0x40c0801050909071409091e010603032307031404210506010e010f12051c1d0901050d0206180d031107150f0e010c08040f0918020303030f180706080f06030a 69
    0x100c6c1d080c00c8940b19180c8072442c01e4040c084901c400d1643d10740d140c2d80c0080c150b009404680c400d480d00c03610119002429880c901150280000c815010042c1000291050042c060003002e00301c4501d0600e91185292000c10401c203811242502140c5010014020f040082c18014480501e840b4a5503041c0500328550660074031449803022070016a4104010092081449900010100090344040781400600440620004011a40c000400452541091030742c43d03058500141c0384040d910040c0e400c1c0000c41c2e02c032803411400b1204c0c03140d9400b40c40d9100d044680b465802540d98501c0111800c5086d814017840385e0200c07842c0040c2d040b14001064000403d03070762141c454101825180d40702c400698000040300c1004000010018020401820709883d410950700e0400040144001c40300070100b1070014004040c0d4964000d00010700310851400c04268000300518900550f103941c1d1100d54a0050740750131000c0491508010401c804107460007056010074214000d156640c010707222540c40145 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 748290188 1250 748288938 748288979
    0x212703140d230a110325120311160f050304090b090f01300f05060a0f090503070807050a08160209060409030c12090b0301091d030c0c090a0b040c080105090907 70
    0x900301d203444041e0800b80f050352424484450707490440c2031b558120305010521040c040b5484a1400c1c1641600e611038400c8c0548146c070800c0181c41d054050303060151107102c00c003007140c14200d10382800000032002d00c0034000a0070102804515007920340e0800ca4140f100528000c80c0100d454010420a02c4130919011003a4139802d0158a02d042c0c41d903440c0480c800c81c0006060b240f50341c89a80d042000c0081c0c140c1c460a05450104415085602c0b000265030300008007409503407091000a001c1024140201030b01d82c03084c0210f4035010304a80d0754040b290440d0301b01d160941d0041d000788080d07081201c1800d501c510300700e8040002c503d2594016084c2a2902c801405440d0b000ba488000a030042c0c0c100350203828843c5a9545969550002e40080c012044140e424243c41031001103041c0c0b400020348007200390034006001200c02c44414003803086030081984014644410201c03149071614818501285a81d603102111907040c4001c1c00011803000e040410160711a683c1001341c001ca002c04042e00c600d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 748291438 1250 748290188 748290197
    0x120907060f0207031e02060304140f0a020d2901090b0405070e0d0f03030b04020c03041d01120303020315060f12070527031c020604212703140d230a 65
    0x12010300303001c1c90745c1112840c001c1d00040000203200c2030004517118075080009900856a5032522510001e407aa44c0302880250444101018400003c014010004c401c1000304150281c4960ba000182c50f506402e910001c1d1556441000c28001d0038140a2300c1d9004d0001d0a01e240c2c0702c034080e4049440400b00e070501070252100080820704052003600b0045c00300d030f402130082d0344517284902c1c020345940c0240f081c003801400744654445e101181008030b90480703c030040400740841203510190041d6000410080701c140035140300c443d465a54501404240d840104615180c9016103d014656400980100700344807041c404004c03040940d14685600c050940300c1d00d200f21110002103450071010241c40074100c09803010b500a203a50020700103214a01500c600c4851914031000781c54403400c107004990000d00e07042c01000300c0244100d5000740c152101d4000c29421656501c43c0205800d1260303070105207402c10361007092101c0e485a84001d80d40024801091182034918240a00d40324030403102d001d02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 748292688 1250 748291438 748291463
    0x1c120f0e0f01050c0c03030f04090e070b070803090f151e0903041205011e0c0807030b010815030f0105041401110906070215070c030305040501110120090d08120907060f020703 77
    0x169045c083c0d03441009001d0700726510b410090900c1d01c50b60b0460302604d211145010880e007410500004d107041103820007400d49103080001c1c2c403160955400207000350047c1c8101a801e511404003001044010b502040000803242003607841021550000150445d800c085a0144540b00d04048211012030b0000090024480010f19105002d000011225042c0c080c11150040e00c4400a802003080c4038100c1e81c614102d41d0700c0c26410350460346580400360001d80c04130002065a0b51030601034a540e03100604540b003817041041403d094500882d001c66290031030300c0d100b10300103500f4080d00766207152081d64a0b040c2140c00c408101c084c0901d4002034480c6600000041c49449640b0403100d140780c210140d0511a40ca030708000c0c1855109100c3c45000034600e49a400b4005810300c10a030b0600c1e44400c084042000d9881030312030744e0b0403c2112517400729540c0d60100000d0805001001117440040c0400c041e45000100d043c1000d00580c0a0002c1c400384003c0506034541c04105241503076845140c10340c45 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 748293938 1250 748292688 748292707
    0x21010b100c240b0901090c0906021516090806070c030801051c1104020403080d02071e050c04050405011506020601050a0b0c060c0a03090206120f01090e03181c120f0e0f0105 76
    0x140c410403e5983d08000007000204450026030001d03040c44400b0346034440c0d8a42d0380c04003241d942041c840354038100040c1034040f643c1100c0a44100940d040d481c03a00ea140d40c0c1c1c60380405400c00105135241004a42034912035000c051308151614010001225080d0001c0d00940c0c141001c02351401006011203000c01c4924610303aa030b0742c10342d0003440c4c00c1101140c989548110000003503015100c00d503440d6143e1081c45402030600d04001961603480809070102c0c4040d481800050301000e4412140748d5290902c1800b00408910950003d102550040c40194541800d1200e0302800d03400054a01c5420021442000d40001e1140c1e0001c00d0150316039a94448404100c008100781a0000d42c00704001642c0320501d401400402d000f032100c15034400d05e60345ea440ca139804440300c0a4030504280c0043c4241011404540e008900c4030b08080c051405040e0701d0741408244040b111401c55500c00d280d22080d00310346e0305c1250140c1d010145e0038140c2c0f0f10481000014200e51a0380245d50400c90300090001c00e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 748295188 1250 748293938 748293941
    0x3100b040e0321010506131e0e0a09020a0e09071502030c15150f03060105010309061407021f0203072109060608030a17010b030c0921010b100c24 64
    0x8090304080582e501c80c5800e003d90b000f01889036814141c6050010004110b0b4a00741e403c6403890b4400c003c01d6449a450074981f0070070700c40e4003040212500410500080c421f80184191403003000762090002d0301070101d104018000b0b1158100110031002001002041c80e40010318400b0340f10b00316490f210800280758200d02e0341c82035020002040c051080c3c03103840e981c04400394070301070b07407460b0800a180e034890700500c1a120381c401134895043e8001801048954017070740c840f241c52070103940081042c06074070000301d090b100b0a5682100590200c2c000c4602c8a40405007600c0002c0c480320b0551460514100052030380011509498500c210714440540151031548a40080b96100a0602c54566900d01041d101d40102a160002c01c144541150000380d0210305d05050750051105582191120000e2400c00e820040186400c4101030b40c101c4003406825842e04206840c0c400085290359540381408444141080020b040c8200308202400040c0c010701000030040503091010030800582c1006030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 748296438 1250 748295188 748295201
    0xf0402030c07080705030301050a08030c1c0210020708030108011503170d09050a050d080105040c1d010c14071e060f08060109091d0114010807060c020f0a090f0f0b03100b04 76
    0x2c02e02c0200040034401c0050206c05541280ca00300c0f0110071b402d40d40c2c0211034427449071040f003000303603045581e1302e541421100034800540c0606104a403030901c03c44014108aa000d000c056580c4100400100701c008024042c2309036440f9065401d0f4042461a50740c0002000d00c120b14000f880c402180c0040c400200d9408800340c65009001c90341340c001d140c01c0444c0c0710748001e0001e600082c0c44000103da40d0a02e40104010000e40303985165130f20000d6038075001c05060301c691560400800d40708140210790207040301c560823a2580c014201d07c514120114071040460400810b1902124030108202a0803441c1c2c080340542d03904040150740c0c2c5040040719007520356040303114140d1030300004140d0082d51050b4a0f155902c0f010081080901c45003608100c0482442800c585510582c800d1042c4c61041c1c072140203461020749520b0b400c04c25400040c050380801d030400c5000554074031203010b11400074015034504143da110b04100440310a0701107500c41c458008031203001502c07003c078104a1f450310f60100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 748297688 1250 748296438 748296443
    0x8030412030c2111030306032a12030a0306210b19020a0f083409090204090b130b0a091a041a011d01020303040f060b030a0825020f0402030c07 63
    0xe00319586643e6040500381c1d403c4180400144c0844603c5071030780700c0001202e000707480c01001004040b2a041c0c40000c12401400d02c580c04d005003011582c29911a000300000c00150032000e16158074541c403000742100c0ca550b00a03039160310081c45500c040c860165610780340a410800a80095485030848042c0100c168000f1b0301c4035200184c0c05840c81d80c05400d01b492103180d5a11950316443d0700748041c0c5401400192160f02c601000c01c00400c861640c0540302c038107403050070034800c5140d903682c07194100d800c01c1d4407a039991616404007601d00c0c506000c0385014800241c104100b0387d20018013007a0310111a016844109079510313a102d0591141c101e034040b800000074814898045401c80c6504070001c0542c103240840e0200b0000c5007035520242b007103150040107030300540c11070ba00d90f1102d0b220040c0020381954425590390300c46165031000c0c010040309901a02c41c0b1551078003840c4000c13191040e260816606060660132038001a56503c00c80010148200c601507266154950080c01c90302c28102e00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 748298938 1250 748297688 748297703
    0x9142701181101141c2d0b240301060c020d050609070e0105010c03080a0218151e07030f05090f09090a021e220213060c022e120e0a0b010f0f08030412030c 68
    0x7000300710080394111821f2003205075455024400c44030740d070300c2e05c3c0400b074001c40702c08500030310045c00410310034564141481e00040170003405209544039a401c100382624054090340107481d00340041c8603002e21980c0100700c00c1c41c140032060126103005000c11005000c10805a800240406d000103141001466001d1700410381103000c0e40e1001e0035069640210071004030707202e50701600c0c02c034080c0180640b10090b0301500c450807401003402003115158003100b01c490303001103400c00d5400181ca8507184180b0030a0403500400706424240100300c6e200310801010035611542446c10704044e00d8040c60b514502c1d40b04001804861440700b030281c040d009003502142d044594040020369258058211a4124001d60390414034484401130035000c100c6441c0300040c40c11420500310940d52260604041d9845800c2d000640c07c52258032683c14804c0e140300030345050780307408011f02c00320410320407000040105e46020968903147c80711280c0c881c082c2d80303e00c041c1541205461014140685054508a0740c0f01c1c07131 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 748300188 1250 748298938 748299011
    0x8090705040c02060f0c040815040201180303020a030e06131205030d0222060314061306050310021209060702070303050708041e09142701181101141c 66
    0x4d40d0741400700d481c0a040d160803008161344c10310b56012102a5035074038014110f0f41e444d003142c0160106016208038100300c40000f211116050800c035010256200c0d41c050007040990b030500900302d95400f00450300ca00010020f2140103400c0d0f000325000c0700c5210744c2c0c046030f40200b13081250550048051289415000062604440300101d000404402040201c45925510340720b0850454200016003081207030a03801280e0b492401c0c000c0600c0b401141030b000b04181d038a07400844d040c0740c1c981c1c41c21500e190700410640303071040d5082030341580200220001c0400740340010b0300a64403400c5200140a0060000d01042400b00050840340504140c00c200303207000030b040e0740b8092000114420440d00a2400e0f407640c682c0320125070654010603034181c000c00c0490801414a00368507030440190203565a50307810070441e0b0403103100e0f05100e500484140410074080c000240c505000c00c015090820002c00040041000d25000344ca2603059a44000905000f03c8009080111240c014250101071002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 748301438 1250 748300188 748300211
    0x18020c0f011b020105160318020a0b030703180c0509061819061e0b1b012909071d01110303040b09010605120307080a03090206030109020a0914030a030809070504 71
    0x100400d881e0b0452862040e41d00d01201c4040b400c8690540e600d80210704501081001d9074426080800782d500782d0301c3c01e01c0d0014842d0740050400c0b20951706c40d4034052004003c001c01d03d038043c401d230001c040f41884800d51010140d0744038911030600d4043d86100d0b6403884045986516400c1c2c2c00c0100824030350010760907003016184607100c042d880d5004e5841c18113160340462907072031200c0e100a413180560b140d000914248900742049030088860615003911045110b1061a401d008a80c4c400d03401c4c440c000b040c040d02c0340c076071a00c0c0c45826448a000c1c1c56031005021941c1e5100110601d820b006030003a031046268900105c071080b6560203580300501c0080103110038428080e14060040403050020411907035124180b0020489403400900260030a01440300841c4881e8014000600c41d0301d0001460405940010096002070b0042100aa800300d00801995001900d035030180004158103101c0c42208000207642d8198000001c0400c610100415103c0300201304034030103407400401c01e001061806 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 748302688 1250 748301438 748301441
    0x1e140606040b0a05180916060c0c06080106080a020309030708030a0b010809010b010c02150408070609061202030c0d0b03100e10050c13210c030609260418020c0f01 72
    0x649a16214500e401c040d491185010741c083c034101c0760094030004510032100d5025024981c01400da2110740128401c031038000c4007075501c050181580352a10041c22042c2d0501c007821007030a0b080001801105d000601051342c204481a9111a1143d4056035a603203c0c1c0700c040c2540203145004101810100c10321001d140300e60851056981c0c00e03a5040e41030340e1241005403d840341c00c403000e40882c6004000070090b040801224442111002c00e0301c0c58030b42c0e034075242032601d400b96001c8400a04414400d011881d4400203807000350b8280002035043d810410b00707201203480381e864113010151b03a81c45100c110752410f00080e5044280c0d0241000592140c10040e522000200e9219150300c0c5072000045042070a4000e480b8119600c040708180300e400d0190343c070ba22100b0b99800d0380c1c134500c5080c5c2c880d0001e109070f150040514445d1102040e0b09038649000781e40210320450941c42c00c0000b008800716003103803800703890849201d007160750200d0342c90448543c006d109895000d179690107000d07240c1c0402c8405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 748303938 1250 748302688 748302691
    0x70323040e0f0403050f09010c0507080c090a2009040902030a11040b0105030c03070503070c1209060e031b2418010806180106031a03030a0f08150307031e1406 70
    0x30640e8110180c2e1000c40500844070100d5004000c500203001d0100d000c4070320000b4066004c018104014024102c0c0c80d080d24089440e03008108a82c008400f50340241001c0701041e8001b4806841880b40c01601d81a01c0140140410795001072140403804076982d599035040a06c000c0e4018040d207410048508089162820600c4190702407401c100d034045d040d511850880c2c1c41b441ca080b10250840c0c40c0c2d0380040b22198400f42450041114004108000c03600f0b440b02d0040e44141d42e1500c5201c0d91500034050a500c441c01d41c03580c0701340c000101c55002d41203100e00110380e4540445a9503c000500b0000f01801221281501503041c00454241c47d504c5001c00c0c0c0340440385003600c800b011036035030104103e0301c1001d1007280710500c0f9807030004001c8035001c1d801c0001d1000c1400084e41501c0e44900200c1c1c69508600613080c002800088001140390b041120150022080300400765074107000301c00b00340d5907882440000c02440c4d030000c0303031103400513009038401d0043e51141401c6690f4184109180c0e96010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 748305188 1250 748303938 748303949
    0x3c0405010608030a08060f1908010b1f022104090c020a02030f01020a050d0f020d020c060f0c0415050313060e0a0c05010e0901031509020310091a0702030f07032304 72
    0x10702003010442a4000080d04e03401c5070107584907415903485001b44041c5110141c000c0d504004200101c03000241000300305030152003004000250200c0d92800c000402c52501c1050403c8849003060600c0140d01140c105158160b07256500886519441c0c480c10a1141d94801c400251400018000350365001c03510681850084084502d1817030160341d0a4202d2003141756034004100c04014074461760106030018038101b80d031040010706001c2c0202164050b0703400050084086d400050800c906401004640d54100c100f0050241c2842d01301494282024240c0002e1400e11070013000007075100e401810b8084150390721000901070031075610745469540c0707030030300089601408143c008101944100e1423480002d6008009140a07440c0d515440c00000412507120301c0a40c030380ca610070240c0c07000c025900440d0303a40040050000e015080c5010340d908010303c03004184802c0b50501511983c00020741e000b061400412a548000b5031906860821481d00c005403405a46500303950005c100d480544101c60 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 748306438 1250 748305188 748305191
    0xd0512010f05010c0311030706230702071503020c011116120509031903032a110c0607022b060b040c051303080306040f060f030204150e3c040501 64
    0x1d0329035085002000c0c241c010076000960200c030020109101d410400155034104065914201031500c695041e90903c008880e0103c003007495140301085003000f15a0b21040510180c202c1d0386c141517040c085c01012820400415401003141d103030380b0b5400e520114102c003200e480c60b40d84e01c544ca000c250031908011010b450030b40000c02981c0070341d8001da045502c4070000034080c09440c842c8104003080c109881e03000b41c080603607417442e01f02d00710000c940600d503e18803108450441151818001c050f40d400c1c2c180c4a200342c0241c01c02c0740d0755440d40c4082e141c40342d40c1119104003044078820582004c5405000c0c044606170001e10070001d002c1c080e80103a10002054a0500103140d8540d8156000d01c80c2045599107406042404c20108071140d01450304140b0090020400e1080d101c2400240c8071207402c6000c0d5190400020421450144182018400c240b841c550b02107252200041607400004d1140c0003048101d030800fa501186000d42208041c041c1800200403150302000c0754a6880c04c440c01c1300d156 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 748307688 1250 748306438 748306441
    0x81b0703110405011d0a0f02040e07091e06050412051f0506272a0a050301230307121505010e090d050c0c04020705011103011206050109020a08010605070c05030d0512 73
    0x240d124150170854041c05645070401e0389442c00c4450003000b640d0030000d49584d0074800414101c1c9040445801041943d855000c0c4904298164a80b60810012095018005c850400407650803409503000c87d103d5640d003194008080c00c0407800c1c110604541d8851548410118006000591010303001c2c0c0000d86062110789890b4041e41c117107140500640418002a0001681d4030f000800300050341c9940324000790f8001901e0300c00d41ca881d0001145c81001c5a400300052041800c4000c6140704149200c02c03504510320041c0100b91a00000d00401c805561021002c00c1480502d0384060300b6000c81c1d11040200b5a903903864a91080302c241c802803e07500401c1140c0b1011481102a00c6071a1510320182210580140401000350701c250000ca440d9501c40c40c81c1c0340c8101041c40514000c141da01840000364804c0c0c80d144048403016041410440c0c418407003403002c1a4404041e50540c0c5107410500d50320003290800c0c621594042d800309615202d4040602c1856601501400c01c0c9203040710000480d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 748308938 1250 748307688 748307699
    0x309090c050319020c011104091a2e0315030f03020105070228030c020d060606121a130915020a0f1e260708160206040f081b070311040501 61
    0x40c2c481034540700060800c43c604841c00b00c99550040021700051000061700300a4400c156001d90810790043c0c040c681c0d0381c1c003e10343c5401103054420039a0011507140703071280c1800380d40c0403801140140c4014450303038041d2410300d00e502a5010080202218400100c440d54a2601400304480c10b0000c90047d400c00c804200c6250000880300080d180d413601d602c04610811a5013400422007220960410850382d05050151301ea400c002c880d090300615011503054101000602480c03a41180010300524010301a8511002d0840809040c43c0807529900e502c0c0400d802417010781503e000290503600410740c0d42741c60b58080c1c1d00800d00b005a41d105c0d446003007002c603410b4071000c01d094110204041c00c02c0b5030724480340c890300040c8080355120204586010340107165952680d002c0f2903440200d0600001e10200c10340c07682072401e030113400348010101b074641550780c0e000310041068010001c100200c1e00402c003801424502292000000442c0c0301e95949040c4600e207401c5080d02107000302d1610001051 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 748310188 1250 748308938 748308947
    0x1020418090c0519031401020a09080601180c0e031507031107020901091d0d020c0315160804020105040503030a03050f01080a02010215040602160f020103050702031305190b070309090c 81
    0x1d050b040705039455018a0842401081020000840380c400e05056010000034942e52400711801d15a00005859140103040500b0544c0c1e29004043d484d03225000420460540d86ea46140135141c0c94001300c0e0040040303905445c000a001041c642c5809040f80d04c0100c00858251707148252001d9400b4442d54145980020551050190107034001a40c0780052109041e960800302041a94070569184071003e402054101900c1c4500d01d8016000070451030311916040060b0003a0b41c01e06e02d40d00600e41072080c080f00d0b0030011900c5560a02c0080000a808d5a0080043d40c3c01010301030b094950710400084014014035045400f20000000c1d60000700720302100084400b078465060b0001d050862017800d41e2016210300074003c030740743da80030060341350544108a581c0d040703030380b0803a210380302c1511502c00075040d2580203050b0b604541c824001007441c0c401030f00c40071003284d03c180d41c5080002c00c00702c50034891110700c0d04072004546000800404056002240b94202d076070a400401100c10350020454 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 748311438 1250 748310188 748310201
    0xc140102030a0c020d02150d051f060c170a090e13020a0e041b170114070e0f040e030408250303091a0c060411010e04050c12071b0501020418 62
    0x140181e10910126036020b0198006409181c00200b842036020324503400181001001c44200400400104804610002c03900940f0b4002d05a030040c2040307086a610042406a5103119a0b41000fa40c1c06c201c1c000c2c400204454400c1c50052002c59a40e0000208007801031405442400c0fa0301208400043d087c1c0e02034014000199802070115581524000b40720b01c2c0b403d00600207980d40850043c010001e020f0301c1110400074040114081d034071801d2003440c24210307490b82c1c6c2c66502020703110040028050b8013892841141500b03c620004c03802e0000041402080340d50440071091000143c081459440080c0c403145905801d150b04504024100810000c0c1da5184001008104440d1080c821542e000e01501c0400c003001740769500f003000d03004005240c00810b94003958240e29200e2003203959648640c407040d01c110191018415402d0450090300c091140540d03851084103610041400d03984102405442600341c10082c074201c080c1e5040c410300030f44c00b0b403154140d0002e521011240e102e00ea0301410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 748312688 1250 748311438 748311479
    0x140d290f120a0308061903051006050d051e0111070b010f080706120f0f0c0e0a09110d0b061201080c1305060f0f190306050109060b070b0c0924070c 65
    0x104101c0006580945801c030b0040c0c002903000c1d240218408000c40c402c3e46c60300056010b80700034142d1501083d29481200c98580000340039a100f0840480031800006044a405101130902d541141000005c24010140404a032002450000d4504140904000300606864009000f030980c10b65491031030359134000070703c203041c046412400c660110410720741c0f1040c43c0340314003000840c600303450641400441e440f4940c170b07501180b0300d40c0300c1d40d00300e0404070038510180280a0040140c03c84000c69078602d406140780c00d072491030712401c0e0809e0301e0706c43c0b1080d51700d4280c10003040e0300c15584951132180c86404e0003440d10b0181d954020300b5181c0d0030041c01450701a000251070403025820141c140030041e203480245607002204031145564046c07203c1c41c044021805108000340f99414080c001054403882e600c2051214030500106d0003040d09540401d82003035030048001d0f0b4a40c028400b141107007900759285081c10b01c1072051914045400b03802072403101c0c031846800c14040c0c0c4885441d00d42c0180300341603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 748313938 1250 748312688 748312693
    0x1050403020d0c080d020d14070311071e0804080706170618250507150e0c0910050607030f032a1805030f1e01050601140d290f12 57
    0x202c08006004441c0d4900e01c0c0d0280700e40c2498400c0c5d080c40c1905981c0030002c04010345560720300301e0340c84816071041c40360480c0c0c00386024454503842400e10910b034010504007601e46242a8049600980d900410110199000004076104d5503189091901c0304a18412800414010b8100c003000c450702850ba04d2096030001e10504000400b54803840700c640c4000c00a0b00403019440c18598a103082e9001d60741c0801080c7e84055a9050a14044500005459224440d01d00b451140441d082002c964201405010742c0d5041c90799941000944c20300030036501c050b800c5800018804181688451124ac891109846c05c1c0160140e044010440c1c00c500d031401c2c80a2480b00e1000149c2d2407042d00750f07690120030100c00f4400c0301e48a2001905140d003a001e0007079503a1040750501800d400d241880b4003001704420007008a4546080041c21300c0c0001c02c450901c1c00750010304052426840e901140710009c10013403094080c410031071103402e0240c90b00300302d904c14410100d500e02c50b45048910305c01c00c2581c0502 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 748315188 1250 748313938 748313953
    0x80304290d020f0c0a06050612010912030b130e0a06110c07090c0306030219080607021c0c2d02091513050403090312261e04080f13170105040302 64
    0x590310020b42100d030f03055189250401081c3c10a00c4200548080c0e24080d0400140e40d040c40350820042d03403542010940241d041c12100d8006c01d5003000301508540880c280412901c8980d8000303040041c2d038050451820303181044000f103440b80020701d41c100c00c2c0701e40c408101010708445055030500405003050540d80c0295014400d0160542080400031000c0c240420026101e9001640006070080c005142c14034000c4100480c3c5410400d4641150340ca0016080a070000d02d034400c03c00c500141e030351050110209404d02040003070b24010300d8252400c403200c6038000d4000302c40c8408980e4000180d2040e861100480c213109900520440600801007035651031050048414004d060028416010320402000c00400f113280350200c0d101150301c5a4604102072020289555810075000e101111031044208021100404006458680c00b0743d10617074a407560b07a4944244c9511907089000c0705041c0110b028202c007603a04504000b611030b50b040c1d01002441001590f400c17030304210340190041e400b07581c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 748316438 1250 748315188 748315207
    0x160207120809060d060e0c1804110412060902030c0406080a0803060a0b0d0b04110910140c010509030a02160f26010213051503040b0c03090c091005030d08010305070b0f0d0608030429 80
    0x2e00520001d10003034500c8bc182540d800f002c5c0d003c00040030040c0c1d071b180c0d2504501011403409004451310b946044900b00012800d0562403681c400b401d00008142c42000000316160b41e0361108a40c004000002d110b41c1e0310341001990304060700029900c42e005904080e1a0080e83c2291400d031030b0015005404266154030f808012030300300b008090042c81417601042041d0b408030f000e01410f44680f10040080d5030b60034150700000c0c5440d07000c3da0200055a0074050900003644c98803241e00403070700c116076a600d140305124410004c45040302c02006083d840004d101c552a50401c1c900c0d411260101c41c0da24034600000f9075451a44030440b002001d001785d50000500303c181c6480038581040c245000c41d16000305080220b11844420740d01e035100c803880c1510401c02440c041040c147c11405601e050010ba52556558550b00e0009000310b141020000c201e01e0320011103d401c1e1600400640c009001550780d4440d080d4072540316000b101c04102c2000d41e080006c08910030315200c4840d0840b40740e45080c5140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 748317688 1250 748316438 748316441
    0x319212c10030c02120f12070e090108060606030c1c0608060106030617031603090b130312020a050c090601020109080f041e1202150d0203090106060206160207120809060d060e0c1804 80
    0x100c0c80988400342400400c10302202401588e100f90001d8840c00c10300c1c44000c0410a81840507800104580d21010030000c03141c031000f040d6504440f4820f1a25200c0360b208014200409a4408586000e460010b002658110004246040b10240e813420411aa203481203c413062422000600c52a8401c00810820440384010000418000c0c074120242e0340e201c03606242140e1003545006a00d810f008014002e10110f60040c40c0000c16600003040382c031a82e940e625444000440c0107074030a80c440d10001d203642c0d0007901300c1035a566203c128290b5660790440803035490f03007041c0110800311800343c00a9810143c0f2201000913900e4111003003a80b4144c42d82040089000c0880c00320103024280f04076120011180043d60107181d0751000854181d00b011002031801600070240b202c2d144010000140e00b50700031030100e081e50003101d420440c4a003681481c0d08640705a6001035000b940018052000c242207030b01200948400c03e8005045403682810f0340b40a002e0300012a10566140e44015010301e840e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 748318938 1250 748317688 748317697
    0xc020d020a1b0e090304050103060b091806040f020d150906030305030a0e030904110711010509010c0f02040207020612160e0a06180302120c0319212c10030c0212 71
    0xa0b81240152521001e03905280f080964290b400c40d400414140540e41e01401104007620543c940c0c01e05101700f8a001800601d168845031903200c1042001c94000d84075904241d2000c0f0901206559070520303181d031b281c0104482c42d01c01181902d02c00020416000700e00808044039010f40c0c481c0e0031034030ba030910b000c01003c0801005030f25210402210fa029112401045d9810b80b003040780e80e8440a1030b04118600b01e0903511094100801040b105506130380200003026415006000d10f452242e16101080c000d00c640070020398860740114940112010f0480394521420180c01124184240914269019032a810215a2103201010b060000500c070300300728507030341d2070381800c3d841902e07520740100e11051a0512610110742009803c1031007400c0c2048070040706c001003503002445400c262180e62510100f0400314031101d4010811610080c49000000303580390a0070040701124009452191030300811210140c0a0710640f01c42e950b13a28024411540c6000d11600540651401101300c0c4180703500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 748320188 1250 748318938 748318973
    0xa0501140c0c1806031e10090f170417071211010e0d212105040f1b180b01120519020705060106021912210c02010f0c020d020a 56
    0x192a00300769265440802814a14011121865144c10310500345802d050386101e00400010786c00100442c11840010303202c1c44010032010003d0b5410705440d280e00e804000380e038054030b41c4150100c00b02c0e02082c440010000c480b0030b2494040344009a501c004c0e1646900e200700398548685107103540114010b103070705104410051602e280c01144220024050114403401920710032031880c07201d5907001c581e032112510b07004981030440c0922102c030300a08040c1c600e4012400c2880d00c440208040201c0084000b4616a0055241c084160588000700301406203120b26148030185010030202044540303d10141e00c10181d45441c030340000c0c074404402800014125402c081c0c131184002003c00c030288040e00b0f04905c510050a42c5501d4008028645400d280406401381c1c10203c1030000903c030a442c055550003603082413188a01d03011707801caa11083c100c445100b0b050801858188442d419841080080b403140003c00c4902c103218022030359004141d4420025a1010703400f1400700340307603945d0602c0206 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 748321438 1250 748320188 748320193
    0x14010e06040c14271002250e0a0906060e0403051206100c0209070e0d05060a15150e030727051008030706180501020a0c03110627160f140a0501140c 65
    0x1040485c503d010500c0300803005800590303032440086440c0192442094400c0580d020903801c184198251a1020f894924510764a00390700c1c080100b103800000081410305c074400071600c0c041c00c0152543c0c0c804001c03001003210132000540586841c00c0003004120213076440081201c2e940d800c0c852810400740c40c860a001220065500d940e40d540e035103d00c158490409031000d8204111074400340e810640c200c5100307814069081c40103060400b103e0040030080e10b080f6200c1900030012900f404129040410b03e00445044660701000c04000408a84d0101108000c0c551b0f9001e0b000e6166060341c00760490a1b0803c00c00c0341c01240da070350400c41070301a03020b60215603407055507a01800c80c1d12408040000c0b88070700240206040d0000070350101c1049403400740502d4070301155241910074403500311001c1300c126042c1c04140d290003080740030115803c1c1c4e44d00d0343c80c6945950a20020505603c24103c0f900402c12246002c0d04001d081e40d0119003040c4c4170004011801420795910b40c0100b901a901807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 748322688 1250 748321438 748321507
    0x10141308070201230d11090f0105180a03081b0a3507050a0c09050c1204110a1707060903050715050f1315030212040201050d14010e06040c14 62
    0xc4410b031580100842030804a0350368804055003411b640501c0c82c5550b800009000705c094035243c0719968450040c00346041c95859070310301d004144240c04a0b1090340c21071000304011040180f020300510561400e61400d0054088040c1281d41d581e801003001408841070890002e00c1c0a28040700c1ca103100700418060000070b0101034803013055084000c050314560300c40786545051002d052181006460b050030140b11780e00e415107001e1610b100d9035104881121031000040c05016800d45e00c800002d030001c10301c03c055607403003191250403609014000018001c004001907258050840c030710032240d00030094100c240c41e10031092080300842200105000003000300320301011000c001008069000640e404800b410410110500000020110149031041050100180018030100c1c2c0c420b90919140c0d41d03503a19a20100c0240c501404003110125030b8400100301110301808251080f03006447c20081c003140141d045481c201180d2214001d41d004001200034041d0401801d03410a40d1800001d100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 748323938 1250 748322688 748322717
    0x603190203100504060f0b030f0406020405030f060105040b010c03120b0f0303070f030201050c030433181a01030c1a0f07030810080d0906080a0b100210141308070201 73
    0x50780e00456503141d460715015410b015524051103684007400c1e007001c044e08180d040c1420000799100282c4452408240940001c0c00c01c09107804450140001505464100080d81c910300d41d511800c1c000d481c400c0f82403040395040c6501c180102c142e502d81554800c0940541783d0803206c0141035040d20650804c100248106958804100404540b44a80c07086507400110b070400a007180c5001d40360b036000030030070814070011a164030110007450741c441c0540e10042a5150400b56818000e07a90b481001741090b2170740703980390046058803050b40d00035141110112030070355020582d02001d010050100800d40014807030f030b004002c0d180520450460b400d07441c0c102c4050480c0e13aa034011800840006081b0401c200400344281c485070002d0084c000104401c00790040080c0c01c914540c0203080c10030032010b00041841c5a5500280f006600160007500d03030b1900710700c00030346070507410780e804150500f040301c2210362405410410380b1410450403070030034500751580c4d0302e842390380b240c40c1c141c1c10414040d014815 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 748325188 1250 748323938 748323941
    0x1407080706110307120605190e15190513020903071a0408070f090b0111060a0c0c1b06140304030e01121b0504080106050f100305060319081c1a060319 66
    0x207104c250300c0d82400c130528141c40c0c0d4140d0341a80c00181c09460811000740c41c0b00010303829101a03d0000c800e4401c1f45e601c510280007180d90001074540c0c440002049003462000d040740304819102c080e0307540c1c0010300300b80d44008180c1c4100c05040c0e03010b0384160340402161614a64044246049052561500d591170b803116240400541001220154441c81000002c1c542d10958058182c2802d00340d8200903407004068a903040205100742c00f9403121603001c100b51203514400405a8894401c201c1c14102e129034966401250040708007147c1c0580c0640c003850240e0041d2442039a2503915204107286003001103a203c0000e040030a00141c0358824482d000d1160018003400c15056592161a1480d00407001c0c03d58640350300240c010003180d040c002e82c41d121614a0302e2a0b4540c1d0401060075110b620109180555910b000801d5000c1564141d00f0061002c00a01c60884540c0300b10b105401818983e000712041d400b0b04c00c0201602d00e05251403030030440080c9d42c4c04408100f00d030113141100c000e80303030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 748326438 1250 748325188 748325191
    0x3091508070908210f070204090b04030e1c02010509040902090a0c0e0d030203043b190b0105071407150c0204060b0c1207050c040c03020c01050714070807061103 71
    0x1008903804104012180ea0b214052000070036641e00201207010604507801220795800310303449981c0c4800030782c60141c4500d6000b15503c5940c040c008219001243c01e18586403901942e003240041d542c0400e01280c0d241441c9040d61027a1981f0b01609403d00c180c4c019111031b1700148246070007030b40759400b03100075030b0395120801d207d010104008a1085a001c0c4003c10050010301c4880c49130f4010890200800d41c004207840c20340d50400143e0001541c0340c513600c11801d1103c000023800408040507014106828040940603050315200340841200301050101900d04a00d19140010700500c407400c0452010055038001640c0041980c0c100c680342c80b444c8100c0c8101301c00300e01c0450320310342e0480300310b050a224000042c5060b0300b00e5420031080c0e01d203907500c030301c200d00310415014000324030882071087c240302c074003646c0d04000d1040107482509203029000e500414201e0010794038040005801300e0040d0721100c1e042005407c401d1422400d070766441e40ca80c00c03407c4107482c01560303005000359030011f00c070085 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 748327688 1250 748326438 748326479
    0x91802130b030c0319031404121a0c0906030c0304110604090b011106060a03030f11061314160b07060f1d06100e07050a0e09010306021b0a0c120309 65
    0x41096054034051515110f84142002c0c0240c1c800249040780030144d10805003115410300c1d02c42c0d460030394074a40c1c44880c040c6400029070070260910400c2007040c00102040002000b40d10102a560f070b44298040c0c1b03000b8000815008001040056000c41401005650280c0f10303915243c040740d448800b280460300140c00241141d0b0365241014095070704006a103e100d11083e0043c801d614026001c036000d01d41031301c001010f000711640e85c043d0941c05560300c0034000e0010011121507181140d283d050344a66118141c484404640e020612600b0100713080f100c1050f00c40040c07200b1440e18003c4003580d4401d000590b9102d50300c103852401c0340c01601514442e00802c40051440b012001504c038100382c8064404031031004440810801907080000d40c40d80710301182461610341680d101c1c10b41d44104580e00007907018000c20004001c0244650140906504001c0c00341c001100400c2d44d42d40e10507030a507014006080c140c90030005585280442800703035102c0d16181a00380d81c0e40303c0c0060b1002895220 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 748328938 1250 748327688 748327691
    0x106090b03071202060405121f14071d1c05060109051803070c0e25090f1406031504180b01140103062402071a0715110409180213 57
    0x100003992604000d403a025040e003403d0060a0065a40090303100d04c00d44c454903010f0952481c00404181c0705125541c00d4104000001c0e240709440c1d1043d4006098845007442900d000c400410b50301441942c0c50300d98024521642d204680c41e4800f00064014030008000c5640d82c41d0322684005102402914020000b1142c08101800c09403408445003459101816041c1e00c01e11080020541400044040728410848550162960b4159010001015054540d4821050a03051182d81c1c801c105504469103030030740c5141140c58041015004a903e03860719031200091001c910030350b803400500007941400410018500551034455960101111403c1c2d4807882c00e88010495080700100010508209190030400f040c00c058003241c40042c2a5418401c0c2c1d001d241c061003a060003045060f0141400080010300307181c500c07000c4c035045e5118503021546001207440a00030302d61240203c550f400140126142014140318400c80240703046022044c1400f985a010001768450002c450361401500a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 748330188 1250 748328938 748328951
    0x50304050f04110d021806040305030901020607030204120b091014011706010e01120615081e01110f0c100c0306051c0305160609021002010902090f041a0612010609 72
    0x2000780d011180040140900d05241c920342e00f01c0c450004a5901850100700141c88103070441044007600c0c002260150070040c0002c011040c00b00000c060030403035800b6403c40b16261740310582281030740158031902440207501d0f0072000010750122806544007250508862408510a4102086e0ba064500c801c2000541038010300591842003070400d8072200840091006525100c21001110014480c41406400103201d40081108540210b144c04455220700070007283c4074200c00ea02e0304035400081c0398040e085150058001d1042c028880282c6a84080324103007002c1041e1000503038003807030468800e07026008500d1003440d20b40c0318000703421060341e400080312401c007418840d5925040c0c2c0000c00c80720400801c0000654440c08031100804169014548042e40b403400b00050010008001d6210041101c483d040701d905601c440c40302c600847d1010342c0b0f91501045101c0e01c3c2800d40b806410242c8694500e03000304120000c5c940c00500c0038200d1502c1d00b100d1007040703003140e40581002c2c90498442c031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 748331438 1250 748330188 748330199
    0xd0c0807030905031602061204060f060503070305120c160803070314090a06030234052e0203100e0a0e07060504050303180117040813060804021c1e050304 68
    0x5509a521148508003001807565a40f21a5a24000c111520584580c40410310045480d000c2c02e0355001d00002c0f0603540e03141007515111020345903405058800b1440d042000800d85070000d0100c0c1102d4001c005841d00301415550160541d2200100580342d200b00040402c02210748c400781e0005148100c0515100c9210b0718004007582e24000d50a030280c0d43c01e0107098080d0341d4a852400423903034182801691981c0c240780c030140c0c1501184204d040e04543c2c26607244160001d11500e0050b0b403090041e243d02e07840b0340c194031082d00707210000302c211090359039205815a24180d00035034200401c1410000c00c0b954410b100e09007004111808000344d911688403032042c1c5010005880540001c0c00d14609142c1050040b0341d4a0068030460f50f14400c070400020100e90203280b03240001c0c00c000640083e240781c14241000d403075000c040c103403842d03020f034460014500c0c1c0b180c0081c0e07020300d90003030840c04007100b078140c0b8080046c0e112205079030300c03403842a0b101c0e943c070000e2007030380d1103244a0009561550b2424 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 748332688 1250 748331438 748331447
    0x60b0d081c0b10080f07020f010c030f0e031207120603080f18010201050712200c030a0e0f060912010e0d17010e070507080f040518150a3005030d0c 65
    0x1082d0490140c0e0b4550018080c0641215a6581c4490480c4014445642d80e5400700e1500d44c6030315818005500e0030a501c461030f0743c950000c0000c618052030500805010348406607880c40b0b101944000d41400d0004104a80e00c03030020300300c1c01c1101c050085085502c0380c80301000d41d4083d500b02e40380700c000051442c107500800207111b1340d400801d00007000185004080907005030824014081c450303584608102c1b10900d1000c4043c1615009642941c40e8041001e80d9aa070341e11022901001c01d605600407191442d006640e8003071450054001800c1031520030501c10014141c09503074095540b0b0b815080041002005041c0c40620240c2d5103814107601c0328a05011b2100c1030704805e402e10048000c2004240d000011100451341c010405956800481d0314101c43e03024581150f0392112000b908104800e0784401d41c03601607a4100010010304600800300700603080d40f485160300140d00c881c805000607810903c8643c200c10070120088025600d50346641c29540712881e030000c0300c0d94458900f0101540b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 748333938 1250 748332688 748332701
    0x4030201030b0d11151204110a09020a0c0f0303091b090f060b2a0f01020406080f130201050f0d060801050403081b0306090c16031d030c0d060b0d081c 66
    0x80c2c80f0500050441d440300c00c04e4100800390503000741c2c4490354142e120500002201c240c244a144060514246803815a854900341d114070b51144590030808100740415100b140c40c03c07105a1603c0ca1201010340e2070740035180c140c58066040c503544501000129a4103403440e140c004003910b018010a00307141c009070469000da001e1000382e52404070203100400100b8111406100520f0020504400c5030407020b801c484040c441e56140d00507850f00042402c01500548107131012921401e0a030b54031141c120254a83c122000d681070403030381000402550061009040b44080003200c0703850202e903039020206450096101070100da40d208100720505a1007410345030070040e9034103e00c806c42018410b80340785000103040907101d01d040030049001040300904840d0740551070205681611000d082c05004a81c3c2d01c0030f000300c0582c0e051301001c100c3ca4041405208090002c1803c10300e00000d854600082041e44101c54220350301440d0403000c0b80c0814003401c540c40842505c10300d98440071407101c059410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 748335188 1250 748333938 748333961
    0x5060906041b0e060d0507051002010903020601050427080903030705150703060b0d0c0306170f071406121008071e051518010216090b12030711330403020103 69
    0x10000c000d12000b404101d116410110451741d08a0340351441c01d185050408503404641c0c400c00b6804035621882d01900701d00340302d9009400350785140c0ea841d024041650000c802910006071500f8074500311040b0013000700303021809081d0460510100380082481d45c0c0c4240820307680d6074801c1d502c0075095200301200d20b43c0020700e03140074000f280c80c0c81d04051a60041410454a6545440200c060644030f42c0c44040109607004c104210a00701032500d98484d40c41e10561032090084401c041000841904101c1c0b0203100038058518211a58909000064010300f0100d03910107602e1000521a004120020180146046030149484044090003004506074081d82c0070710201503909842d120403c013a10803564111018142c140c4080380105d041c02c146000c108904d00c0901008143e125503580039086401041c2d440480c1600c441000c03136900c0c020b600d0003c0c5461100b06000100b800c00485030003240d0302d40810b403007020078045820892608464a03641d031020380860b0800656905000b0080ca840c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 748336438 1250 748335188 748335233
    0x3020d0b131b080f0c09010302130f090b09101a0d02010201090f08130f03052e050f07020d050c06040f080c0a060507030f090c0e100902030f010602060f01060f0f0c0506090604 77
    0x40306070700030034a0b5040c14031010307200710203410ad10840900307190041d04265014200400031074006290200102d81e040e240440640706010f0141c0340d02c6410310070a40142e03c0c900341d07a106030411004100d21126058000c80c11075403254548800244401d2f4400354031403003115040e45440c0b412800f5101c0f40c2c8964810781d04807802041c20000b20704081382d80c081643c0003200481c0d452903629001d10b4440f0b012500305954510b03150400509242c40c08100d40503196540c01d4500d01a40c0d07510803501c80c000c082400130160403c4001c580000e0324000c0d00c01c00030380300d000c60740c0c00c0004015020f42044000d02054800c540c0741c4041021803a031521500c00c010f440a07500300601c42c29900d600541841c1402681005035a08000c20380c0540c00403040030091425034010340d501d1900c003072410102036080c862007026200e90f5010610b20f0041c0e101050598015176102c10144030100c104994203440034004000340904800072802094003440130b28032400400005008a003003515003c0305941c5505812000e0301d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 748337688 1250 748336438 748336453
    0x91b04031514041e030905030a151a0901050607230706021501030b0f061306060903021008040f0305030606070c0617090706020d0e0f040c0c0b1003020d0b131b080f 72
    0x81c0d03c8040c4e141510519a5481070141003440e05a4001c845a0170141c0c0c1407007990f588108002800d10840f03841c268110b4103000317030f0300350002010710000c8612003280c0c001e8040006120301e0070003801810303800d402040c03003c052100d03a102043d80b20f8000c08800002da08100c10520200d50100300c55060003504a002400035072550f00e62069049000e0004806c0b0030218001c0b80143c1e4036407814a11404103000d081051941c0c4417000b414000c40b40c803089008031808188041080d008401661040b600400100d00d890702c030f81d44c204e078182c1c00100140e5000400340080c60101d5103003840c08010707002e551540021802040440d503000400108174000540c40850140700c0103501080030056420300e410b060083c40c5888002642125410050a0b0000e00c3c14405580d07031390b0b0020000314928094107103500d407504c8411503c2c0d2501c2c1d043c00081c0d008211690344200160404801c10b50106104031069401c03000e80e512180c400035446440c002c0c01e0a50403050040100502000031219a50401454003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 748338938 1250 748337688 748337693
    0x7050306040308040305180a120b0903030105150c0111130e09120a1d092e1401140c01091110020105240604030b0112110409030806091b0403151404 65
    0x540001e10050400802190415911400c5091f078180f00200410401000b61942e0001307900900010043c0d03030001103d000b0800062002c011241640c41c00b41c080040029880c08808240d880f41c00070a1003590b030f82218400701d00c03c18024088594006101e11a01c9107443d421640081000d40300352050b4101010420b5800c801a0417151202210b050810305d8566844128181d0010305640310f401103002802c0001e6000310f440da41c4200209404010f5044c400703441d2101200d0058060704030401c500344046213030756025241004001400e00e10803440c050f2504111401e5409001c0221245445402444207a00e07002c21410982d0314248001c10281c5418001d1030781c4640c5101d51603040340d18101d0b8500703007074072000210303400b035034110f101120903594520210071802ca10000a840f1400f424050354810310b068024243d090344c01d50f032120302540301c000030072400341d50180c8080100301030004406007848207500580001d41c000c0c100e4000b4068060a5401035540198620312010b0b03203441000300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 748340188 1250 748338938 748338947
    0x50118050405090109060213240206070302090616200f150304051e06010501021006030b19271b0303080a05060d171b0f100218090103080c070503060403 67
    0x1160001c960124040d214241c0080c010301904c840079050310300004001c6028402203002c9001c0b81e241e03402e90070301c011009201c04075120010102c900107811038004140706512079006018a1140141900d2a180e010389081703121303850340c0004803407000c0d039044162070600146280102c80a0262030340801700c44110300060f21075545e54800c921000c0007002160503c18104260300d14401c085c012404080c1d01e900f00142c1ea107009100e0680184030b01c01207a68407940d03c3c09541e00b1030340c4c003013007811071511650300c58400100004d180c018600c1c3c1d40e04100750ac4400d03c84c2c150252070502092284065a9814600c200e40c040340000d0180c00360040b0100f00080c2e02451055100784807407070025050701e80000182c19042080400f0b80301c0c0302401041c03415100c40e140140003011403134030f20765a107445e421035440e01c5a07c03401e0704110f180c210b010100b0380c000440e0018920f1500b00e04500111142c0c0c3c40015928120a0b0003e40c0c84450110341c000a6140410070000a04130850061a075403909950042 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 748341438 1250 748340188 748340237
    0x7080313030204090f0803010e0f07020a120e130510050405010b0a091802070203060106030f150321030905100b150c060a18060501180b1207120c0902030a02090a0501 73
    0x83c051550707014160f0500540f641500f481590180c8015541d5075035419044d59204240c8070003800030109004129120300001d10044440c1e1b1012421006030b0b00640b040e1160841385400d90381000840c54102002403141c442d180c8a48807100c241441d10782040cac03e001c110740058100b0403a480c0b08010080246400030340c40c1e400c49000c141503869250511000b00d02a00620380300075014401c000022444540540000117000b016a030100300c8440013a80c0500c2071200ea02c005800b41d4001c0d01c0380755481306e0f507609000000e100790601154194541d03441e14501642c482c150750a6031381d03440c0102070a14140104841c41c00c00e0901e441d041400c242e0180f92924000740142c400c00e075035100311040b83c2d10003001a911a6412103810040ca41c0e554030209460079030700001144191a001151220f807034407456a210f20785003a4000c055a0b410201440070b14144a10245e400030b12410001500d0b0b225400214400d042045015842e0b42d8914144115500b08d078102c2d6050080091030000b6040701165102d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 748342688 1250 748341438 748341443
    0xb0a0c020409061b090e181e030702010e0d021323160f022a04110c0106030b090307050c0405040606150207060306091a2101060f0e01060203090d031211040303110708031303 76
    0x100c1120340980e01192606001308d2005050b9405004c0703000c6e6110010002d440720703034003e889010150360310000b00000c001350030b00000d520410004801e0210550b540c40151a80c10300c003190561084456501001100211005c0d039440d801c05034005480e6905c60b203042060001400100701d1402025070740c141c00b880541001034001658000d100c2681d40c0e45e000804041286500a03686080fa5112a8017800640c0411f8034031441c0b110100740a840004201d417402a04000600394041c10038003000042d10010b0300598000c0e44940300420810800d283c1025a00203075002080503614103040134003656015402088841e14244250012100000c040d04240100301d40c10003010950007504110420b400410400c29031804001081c1e80d100390855105980b210a4081d52a80e030703c21003207031b6034822003e04640041c214007020340040d00401044401d6a0805004a448540c82803400d50710b801a070b2040e00000c1103c01004402401030107035001800201c00914030340901000401c46100051000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 748343938 1250 748342688 748342711
    0x13061a122a0616020a030b0c090a270f02221502010903091e08011805070b0301050a27110a080f0402030d050c0111030c070506010605130b0a0c020409061b090e 70
    0xf220115070710105160b0155601c40204c194500301a0f503800c405802070142c883c0074070010140861354074005c011480081202044c0303640300702550b08810001d020110701408a4030340900a042c0c5902542000c000300d82405900e0b00680d5103401c00c03c00b09042c03170203a904c040d6450000401c010980c04203850b42502c1c08400c804110540d141c003907840f0149a50b000440329440c111407400d018a400704600c08181c02002207440241e03c9108031541c0d480b0a2190541c0510624404c10840d68103007400302d101d100001c40d103080500301400d0541034a1140060360206540082d08071341c9142c2041101c1d811100400d00031146141ca0f5021a0b87c503442d4850403014001701040741480504250000e2031460480c1031002d88a090642c4d0b6441c00c0c0d0003a140441d22409010300104d40c1503c9001501c026000c1e1415501d0400d1410107010015405a00c580d02003104841840000d030301c95019021005104d41000501030b560101040c260303991940b2810100583d05c0c1042101103402d056a540041c5449071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 748345188 1250 748343938 748343977
    0xe0c0102073f02210f0f030a0c17030a090b09010e0a020f190e0702060c13051c0204090311011503081207020a050715030c030513061a122a06 62
    0x1d010100c004042d0000d610141c01c50052400c50940703101d24000740510022191100f00d40b8214548820400320000c1d055030041c46080c0c0c0741d074400c800180314036008000740c0030341200c40c0d1840002a030080321003040d00ba40319100503042084c0594034550040500300208095205059074079125118188007a2040c600d94110302c4050759600141c515542021994407141d60f540d0fa540032072404101c80c0038015000743e00009540162980440b60403003820035000c1000f60801e030410084038005805440040358686903400182c0700c80c4102c401c0d00b4041d454a40143c1f113054aa00e096640c0350050381350a100f204d4082000510384c80a9a01d403800d40b24080c9a07558486034200d146c40450030000d0200d101c1c200c00058403200b0030992041d0030344659414801c0401400307043e01910800d6500c8a0000d120354015004075070554450403100054000054a48030020000b40d000c8045036040f500d0394010030004414880d62411010508050404c64400800c0344400106203000710040c401e0342401012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 748346438 1250 748345188 748345289
    0x20724060807060e130203040308010e10260c040e0c010804080d18033f0b09010b0d0b1503040f0602040e1005010813050607050c0109060e0c010207 65
    0x30080c40c0941580002c40700d01941e81ca40c0100b2814414110500512860000c540c8902250003102d100790380507226600240d203004d07078030700706e1040050040c40718141c80e600106010194407030b00400300300b181107000409201d8501c1302d07007020913208003180318524082040c0007004000c81ca044c421502401c020b99960755904040d01503105945001c4d070010700d081d1281003004c3d41140080079030360007940c0e1801400004407440310144101042c140c0392040701c180c00070110341803c50004050301c0001e004510324280703001058140c20203070000d4426580c080385100211a85200d2500b07007410032142c507800f0310080c40d43d50f621032001901c042e00172711031104010244521601228002d14a81f031544110b8a49503070f400c8803000441c00b0b101c1c000380c200f002041d0340c0c811082071008126000005041140c541000a4800d075002c0721030b10900e075480310035910104000b4400c011700e8030f0039000980340310000d00d000241070180310b400400054190b184454201c036071004402c0d11760b035900d451000d9080c0c1d100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 748347688 1250 748346438 748346441
    0xc03090b071e030323150607020d12120c05120403050f1e090a050f0f120f061305010b10050703080604021611010f0201091e030903210210020724 64
    0x108016000b500b10410b041e0205507141d40140c0c1030103080700c40401424103010036101240d8041e1080f030131120110005182518014006001032480182000c240c44607035600c0c14040400a005000802e01c007401c0f104000030f00e4040c031300450a00303280032890543c0304c1b845c9907013401002d0070107010000042a0400010030704400c4401e00c40301001c100300b400c0815140d54856a1024415a0282d6215107001440303090417035540c149440c008005840c030640486c10702c0403a070041c0d021440c80b0300c501c18408108150503c5264040d22140703411590f601007504000742981d1550440c1b074054a850000001800e5001003aa0702060741460300c45015141c040c0003c010740641404124041102410401041504c00d03a000b806078083e20b4180455140398801d90881c0c1503180041c0140806200b0317600c0e4a41d02880e0041504e1282c1040c5680f19241e4441106d040d1000315402008a4000b8441c010107804114a1034032080c039000c01e51410043d40d64104003a1216003241341501e030404410040c0b0b5489 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 748348938 1250 748347688 748347713
    0xc060f0703021201091a06030c120c0423100c02010903030309060209040c03150812040504020c070e04080c0f0d0f200d1805040b0d0312020c07170d0c03090b07 70
    0x39070f84502250758403440408024043d11004089060302141601400d0800d041a680301ea14100c0d806030403c8642e00d1146c000c16802030406000b0b100030807001c5555003100c03050720701411545070700e0040c1c001d90905000010010381c10180c144841c02007050010f03030344001e01d8019070f41d1501c0c02185605852030241d003e405408209503025041c1810844a10341c1a0310044d080c03680240e402250036a640002038540761030b80800c00203060100300900c2142032a40041c00400c040d20211440e0582d10ba0f940c50100e00181c6040b2a5504006142c1c1c141c04010014141c84540c490080c1c1000e6a541202511180a010201081c0022104000c0405c0350700c0c1d1504601407208400d9580d4005030301d100802250003110b0016241c01e10f4000820a03080c1b51192440e40d240103450350b000003149031410344840038519561044c1c40c0d002c02c020005608140004d02c020000382c00e1040103501040310380d50503c4440b080e040100200000080042030740944900101c3d010030300140e544041070b0415050201e003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 748350188 1250 748348938 748348957
    0xa141c0f0c0e0613050f0c07020d060c05040f080f151302030f061b0c0c010c05160806041217041106070209090313060c030203191205070306030b0a020c060f070302 72
    0xe203000001d4403000c5080083e102d41d40071908414400c0c40390512030201d410030b69030481280142c0300060301e1011528000c10f500303800280400c3c2c0c0d034417042e80c921056802c0c94502500050011a0070402103005600c00c40203010780b074000d8203a001060200c696a01602c0b026044180025008036841c0c40d498600d84030302c00e401030b0682d202403000400d19a50313800186c58140b0016101c907030140208040100f036504041c04400546000b140400044945007141e1a06840134011084012411020b0583c0c0500814400303000e082c142c501410180e40c540403004e060030910680c0c408604804900c1002140e00c00c1c0c3c40341070301c8a1031804101080321400b80c580004d400803042d00c188000d50740e0000203032500c3c101f400381c080c841648941e0201c0e01d4000480b0014050307401848000324421441c002c2030020300349403500700824000e4059040550380140c8840e80030030703910b500030710a0080b40041103500201e0303001c0035031500c9600030310f6555400000301a081460743c24400b20701c00d18400d404403a540074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 748351438 1250 748350188 748350203
    0x1e0606080109062a080c07051f060306050a05190e031c021911030f030a090602070807260412080c0703050f0c15040909020316080c0a141c0f 62
    0x1d52501e0041d0051400700307042c00b2034103004507040a6451000f480d41c91380d40899540e9200755100e5040d040d0180d0042d160132160760180c10042c000b5401c991605106855a080000c43e1451860401100f1a80003038141100c0074240403c0008010560312404561010317400006860a003220710a415030003504c1c0d50441500007a003406111140daa005481303a510303810b411085c0900c24903010354604900c415070003404d070403d0003d60b140111803000785901c88048031011070040e60075580c403c00c81e402104120b65030200407031104107114911040b0801e104040d207491020554030809100140a14031075540c0c01070074503a5000400804900f0745804861702802c940c029603c80c40c1440d214081c45500f610076120b00b521808140c600609010041c29000503a0381c901410628035070007a00010400342e070144551924400b201c210200d000000b40721900180280201210410130491a158410542600311031b0400d083c03503403038190070301c000c884855103c000c4480514004070101004000070f0841c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 748352688 1250 748351438 748351451
    0x6010f0f1e170a0501081c020f0a080a020115061b050c06120412020102030c03150111101509060b090105072d110603040f081e04090c0e06071e06060801 67
    0x907a000790a1103000d94140c0c07200215a03030fa10300319604480091040d450594089940030200c84d114280b43c800343d4580b48160784907d1031455a442c03820740414012a040303c8001a1000b4907682031040c4002500c9808000e0204d62400c0c10040c60055103121004c00c414100c45440100401007201540388040500b0968480f188c0d101c040011440c1200e0a640d00c40c240138003012118418400c42c0d100706e820307132141401c588407010403500e00c0462100482c1440003052403411085020050040d1680c88528085004002030030a40340748400d40d408070042505020060002c40e00d034206a882500382807030580c1c0c48144909110300c02a10a482041d40c0c03040084c0c036100717580750780e0310030b01c8a090040c19600e04444101c014032070306200841d809400089098007440020342060001e00d04180c00400f218880c03d07401000e030340668819840400501d907142140c2107555009901a603840c441201c07100c0c1418069101c11440c1030725030610b11004c0c00c001442d14100b240503409080607103200b20080042c5c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 748353938 1250 748352688 748352747
    0xf121e0507090f1805071a030c190c0614150a030503030a1104050d06020405030723011103130e06090f040b0a091a0c0d0608010e0706050c0708010c0203040f090506010f0f 75
    0x2031b42c5c0c1d2800361002078814a50000026090700d006c80b4025040705d04828584082c10700c010554600600d14001000503081c404008514240074a08080f101d1a42280081c142007142c2c00d03800380010800c0b8010010701c0000c00220b140882982c0d4410810744003ca004d1040b0040840c2c02e1160b5000385034010f00e980000c0b000d1001c0d96000c1d00a940003502295078043c3c60b504426192a5103001c1160340301c50610036191a540310b211003450114901040b0383c11b140355910301041042c0581c0001c0e00c1c0c3c05409007045803510700300160540020100340984172134102900c42580790080104100352268490719200204036019108590702100c0111b941e0311400c02ca440400c0a910000200f09030b03a061020103d0140c606200d03103210b0409410040c94258070b040b9040d80c0640181d000c0300e007103010799080065040c1080c0990302e1000e84641c0070f1035855081c121650f1580368660000303900945080100a1544d0308143e45086c06002410000003055a29108032180351b070b010b240010414602c64134814 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 748355188 1250 748353938 748353943
    0x50313140a060506091005120106260111160b041b0f260303151c0b0402011101020a0e13090606080d09140f190f121e0507090f1805 58
    0x50891081e24180080e840e01410040001c0046d24022012900ea100401280c500729000c241c500c01c5150000c03031900c1e6075003122000d0503c0e4864a01d031242c0c41a02c004481c44080c07141a1002c40c5004805003051030306d2038190049a80488004e000242d40c00c045030500445145403000a11a4a0507110381502c030403c10714406603507c514040006001e260140400100c0d0310b064040401c0d40c01182940c1c1c4a002e611039100d4008040f54004144007610b02c0485501003005035201c0c010243d90585003000e00c00149950850a00030425074130521051a000358040020510390508031481c200c10760080b25140c00400c0e102000070400c91910b000040c4400d00410307032210840c05901c9050049030b50720b4103000c2041c005112540e01c48140000b01c10140b81010040e020349a0341511100031580b180313a00140c80d01190090030481460340e103054100315885044030f001d2a0010200303100c4400d6070369800e03a41c9110340584a0090348516083c1c002081d5035100c02031003d042200036032171070301c641001074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 748356438 1250 748355188 748355203
    0xf1202100506010c0201020a0b070c02030f03091912080d1e090c09020a120509031611090a020c031602040b042c0d0906120b0603010e090d0f0f05031314 67
    0x100d48509010001d40c003503001341d02e41910503406801034440801c069440700030100c0002c00744030611010000800150b00c04100041d00c1c02c0d0104019903607903020704100801d40c41d17018024030a0900c08842401701c00100e6041190b1180d004401039100c01405c0e50420107489a1060010742c000c2800000890301116000b0582d800d0044406800e42a01c0d1070000d0103903c668040c060100329002803031400b510043d800990700c800f400098070b090120540982886142994040c1c03104001070740c2c29412440c0042010703030406050740c401c625040609240f10780f030f40180d80c076081103001c280c1110025500c85030019254a0b00050082100d001c6440b03c41c441c0044500e41c500d86015040907032818214001500301100b20a610b400030503520300310007150840008d04131084640d850380303210803803510780d00c0103180078010001d04c01d0518038000c5103941c9080101d81c0d0000801000d8240c00516540101446002811615100d541c9650b010703600d08080b1f601d040c000b0b01c4c400c50440b11100c400e60115000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 748357688 1250 748356438 748356463
    0x41502030903190f23280305010902040e071209020a170105060a030201020c190b0a0e03211c200903060f07120c02010e0a0c140103270f1202 62
    0x202c03d43e11010301c100c811140301c91070000825241a650800c036070300d01c1c1c0c0d028100714031403003894688082c00120b24040300c082181c40301160b45078654048041d4042c002c0502400c1001030850405252008420090030040d0024007030025403d00c20f16607036001c6d0084030f4440d0b00507126842c0f4070758806500c11443c2c4c2c50034080c0482e521b02004070364640b400031040011260141c1c000c00b00111070004010506101100c00035520b10030b0100007075000d40400c0546a4000c043e26001c10100b0003c003814140826a40b9406020150340c80c80d1910148a10a803580e43c12031260024402e2038428100000f0200110151030070342203080030306903050b034002c000c00d43e514055083e15801c1e22001842c02e202e44042c0d400c00041107000c00350350400355840d4003000310080588000b00d4035640062580342442c5201605442ca44a1404180329000080c0031a0b103159100380380400041480c07442000340305070400c9807424900081d01c0c8507828080818522001107411441c8004940309807007011f0f551790402c0410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 748358938 1250 748357688 748357717
    0x70b09060c0706022416030b0105070c090c082a0d020702060d0b0f060a05040501140d05090d020d090f050d020316121502090102031b011e090b01050307120308041502030903 76
    0x80da1700e445070b40d201d107020b40c1c0130190a800010140205030050312888030a181080001d001140c0800d041042040081ca00118000380c2c8085018004201e07010085c1110b100c20349400c203a0180040c1245011800d198400003d40c4611407014180060302c500301c0c001c3d41c040780119658818264542c0a028004c2003200c4103201c03000144180101d50048002400c08510305205c2044994000d44c00030700c0c401314940c1420300d04003403902c07081c1c111841921014110382c00841d10503105501008030062104c0207060101d101e030700c1d0402c80010a102c90041d5030086840c1485a000c549040142000042c2e402065002054540d58000910300c0224000d50340f00f07240312000909000b04d81300f2199550010f80c0a54640b001c1c203543c00c45949260140031940d5941d031a0440c0c140d164038140011000203510011940a140741401c105034441a0030252094014201c1002101400b04e5500c0750300b9894103044101781d540e820300c454100d43c459150203045000008220500782c001c0b00519a40c0080b601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 748360188 1250 748358938 748358983
    0xa0b03062407081810080a0c0503010f0315060902270a050904060203040510020c0c090a05010f15300e0a02011b050f012c060603070b09060c070602 65
    0x18500301d55000e6024049003040800c0b140300440c03e1080207001d00828030f022000402a801e01041c45480002e034803500040c03421041c410102020b00803110550301e1480c2250035075040c1004504040001e00c0300600c51034105034640381382040c0303070000001042200001c6480300da0302c043d103840840580d40106a0310000002e050128034011a0030020380c0e10140120600d50303520b0340d07020025031010304199490320500440d105040c80900092040c454180007070804a444601840b0554601901844049041500500c480140f04110104803607420481c481c000c5940b1500355461404681d0052040e402401e0400c2c191420054004480300303401c0d020020403545488643c0c13a46c50340ca00090004440980e00e4030300d812074808444a09024000392034652a001c0d44150841c4c4511050030624400451046a0714645440d0354032040890009018585080f40010b9100c0c02640070708008400003160340c0d556038964000b594060034100089030005511420040c1d580c0c196180c4141c0a5035400c0b8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 748361438 1250 748360188 748360219
    0x10e070c0804050105070503120c04140f03030703030c051b060708070807140a0e030604140610303005040513050408130b0307080c0f09010e0f0a0b0306 67
    0x46240d004030342101401c1d0900e4100401100c0550004100b5039583c4070030710018a030410310101c1c403801460b110b0309680e039491418104101c00c4242c007006510400020800c040a07803804000c071a0840c2c1d040c6000100c0d64031951080e5510702a01d00b81c04c100158034240301d94400b00004555000d040310b51941c0341301d0b5551200860300101c044400c2000907917000b82c0c0c1c4051080b40d202070240d00588c0d007420300d40c50648001080c90200100c505917940200710030300c040360640901035990410f100102d89407019080105a10350500e01100300040400c001c92686c80d01064035080b0340c800e6910052400c140c04404140f006255400544100e13058402e400c12082180038400711421560050080c1d8981d6400c0e540d00d100400000b00243c80c103000c1004040141410b108010b00a40030b03a120071390312806c01da003005080707600041c03c1002804040210110820450302603a4090a092038000980078008010400e08034000d20a1a000300c041c0d02c0100b01d640d010400703944100810f440030b050344500b44 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 748362688 1250 748361438 748361447
    0x90b031204150f050d020d02071e0b0f0901020702120607030509190b090c1914180606071406090c010809031614030712030b04050709140418050312010e07 68
    0x1445920300e031080d00c1903008036460181943d48007406050034410304003174011301000e00303a078441e00c0018001c80e03002403980104003880c00c000341c0003005007803805912002d42c0d40d1886031710009080d60700030610b11000a940c0810940490b015668090007544214181e01c000f60356441c5d09660540c0801d041c4030000d241160000b0701a240c69a02c8080540000784640392070721101d0019003140b04d01c1c0116001c110740c58569490a0f0201c0300c50003a411842031134585080d1070803000da40d078140301d013080080900400001021041c3c100d80203c48895480d84140781c51501c0780d2a5684110741401640c00f00448100080340d02040250281ca99001a5980d03d0100c0e450740300300d04100c0a20301010394081e010034102e03102e00e10009100001c0740c0c504529900e80483d41d24440d010540002d48400b032000c00b50a050096540181c0d0900704031882d581000003130904040c14103a55401143c1d2052184120901050020b502c2c54000c01966951894904000b000550901402c8802c100300d20114014904c44d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 748363938 1250 748362688 748362697
    0x40212010905060909120d090c120b0c0307080402120c151309091208042d0606060203033904030c090531080c060f011401020d0801051003020c07090b0312 68
    0x512000e4038800302ca010b5001c003140c207c011a50003560361403203060b0020350002c40c0c00010b899404207000d50403400d89070240c29204004e2003007050b40c8051041c485c02d2038200d0490ba4100d5030443c0c0311581c0e50716140e102c1c1e10744415503a02a5116508291802502e80c981e4010300c84240c203154141c1c14951503403140b0003030b6440084010045001c0012903224244114210341e0480d202d0025084494030000803490914050201c00308514000b240100402c0824441d220091003280055821841e200d205013020545012003000c0400844940d0700032000245040b40a140211003099243c40d01d03414004003850190090000741d0b032070705020401e030401c158241c8807020010071540e0280e086000882c0e82200c540d02003158540c0013806001e18040c3c0c1441410702c5a2000c5403c00a590b14100c4c0e4031103002c8401550b1415900110280100998045210f5040d10742c203075050001d84245040440c000d1040d0b80d14110140602500800c90020540000e41c03104021011145503044803510205c45104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 748365188 1250 748363938 748363951
    0xf05030408031003140609070e0103050616200312101a0c0106030605070e0315070203251e030f050306060d0c030b030105070207080f01051e150402120109050609 71
    0x1060000400189890005680c0100120800f4140070766a544040010041011000c450b411032030422030070100c20130040009003664a004c070010351440d01d070b45449070300150402880484281c0000e0890740540703030004170501c105132100c40e0407400040140d01c80d0840b4000c83c03881054080400c010310306001480d015100541c600502007842000b001c3ca0302c1c0d0000c5003c2c0000e54846a0000100712540b185070711070401912a82811040c5008041c02c11040303500c007031801d03802001400a095400015a00b81c030841185426043c103822110704480a25007000810b502d07881c1003184e00c05030010380d60080440c426224024522591413080e42c0601044a450382c10003001c2c01942048a030740e41001c0d03401070590900084440300c03000480e003501c10441e684400b590000c84200807444041260400002c0d80a008020300e0800d0189844502c00d000307220303038044541402040e050800a0a0f01400d540002e00c11540e440a440100001403001d2140140c9240f4110000d01541424082d040c860039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 748366438 1250 748365188 748365197
    0xb0402030a05070f06081e07050c0f060705031509041536050d020a030c0b04020d02041b0e0d020a0e0c1902010501150309150510050a0b04030611041d0c0f0a0905100f 73
    0x2340d8a04045403e03801510755010548a00594881c02c84801c0c00814000c404c0c5a0340c5c2940d910b010501c24440460760404c0500900c850002c100100e045421419a0010840c2011840c90888844008040b0382c5190800c504541804032a0141e001c1c254000c00d8940b040c002c1d0b0324400c0141c01e0598465085074409004555000b84030f00014102c0d001b0241d1083c40101581901c4100d900400c0882c0d5a1009114034031003c550302c1480305810822041c3e10000845811072030403101c0e80403c000d24824455000004a4100801c41c880c101405580c503403110700c211040b000b819084000e000c0c200c00e10405816070101d0503007040140c840d000d400b02d0a074202c42c0280582d00041c4890000f881e0050111048106e0302c0c0d400700d4103688404200c1c000b411101d03c025121411801c00c48101d41d14140001403404041004010b11110a941d4201e61044045500b8280c1c1d100c90300c045a0381701d60728189006050004200c00032580204546003070355000d803844400316142070002c0d80c051420b21000030104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 748367688 1250 748366438 748366441
    0x120302060f0a020415020f010f06050d08090409080d020d06060c12110c0604080714040209030d0e0f040203071e02030f12040602090303040609170c06070b0402030a05070f06081e 78
    0x4018068000e40010b828140149003a0381c60341d129003030040711025480143c2040311240c038a80c1c403d018071410f05210587c00c204030780c50f1034000307444580040e0004200c20400300c1d11710400e0742d81c1c1d440420350035085001140e481143c410b0755002540003803440c20b83c440c070b00400490544e200d42d0300140b81680c0508032480484141109480c1007070300410414041c810320716801f20755181d04006d04020500e500050100904006040746a1811400a1402036105001c3c0c2ca01070750380000c541010068a05002c6840c041c443e02041120803880c0000360014000824481201d0b0f02004950059490000ca1075010301c0d031b0482241c4034419028100700308541032010152220245611982140c411540107203001c0050000c40d042d504a80c0c4030102003101681e040000500003001e03510310b07001c0603014000c0b0b0446107000403c6170080040140c003500c040300000d01151010070100300050380020441d07075002e6075003480e18072010040c0601400182c440002c5200300011102c0e130303140d208940a004029 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 748368938 1250 748367688 748367701
    0xf06141b0310050a08031c02070201170a09081206010806040b090601031d251202011727010c11030c120705070b0d02090f1905130e01110a030612030206 67
    0x16040941203140c000c602c0c410004080d80c5806200d001084444055602c0e0301200d558101c1a841c00c04201c02818010006940140c0c2d004004540d0300240c0300d02c100103610350350209001480c002c20000c00a07840000c0c07512840003082c014611581007681c0b0240142d0b188802d20058a040c8601c0741d41020740031010403110b41c0a074001030008400c0b04609030b040140c0205440c0f92045a04010100e0303445001d000c0c000303500242c03145000d06006285030904201c15800204081c05180e44903003010500e00210308505201403808116040540200040301048181280240f0303078a02e0840c0410f04040c9142051840401a50101c890040140240464103035005405522820013200c0c1c5000700280411300350200c8000e014500c2c28200c0040c2c50382024001d10407000001c11201e480f80030400d00e568109035100d900c0c00169581035408080756040fa0030008041c0043e030102804a500380310b003010410080c0405001e8142560341c040c0055a980d14207120142d411040c042d00581001c4001603d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 748370188 1250 748368938 748368991
    0x40b03180a0f06050723092206080c010203031b030c0f0a0905040b010e031903020115060810120519030e0d0503090f0f060403030c111503040501140108031803030d0501030f0614 78
    0x216100090300b203200342001000c050390b0307480008c80035110a0360b68060901c0b684204000784106010280015440c608110070025005103a91565402012000000070202941641500c4409107101340321611040c00610260080c0d80b1809094029441e0404d4501c942d80303c7d00310700401d6400600076251144071244808452401e03a44180c081d50340301c890008400c000d01000d1002041c880c2d43d149001c0c10080c440c0d401c501070907400300f0a8003c5071310011010a030003284060b006000c0c00024031443d08603180a0362501c41525016074001050241101030060110080010340001c64040502c0d405900401643c40452241c02e80c0210040c0014800640a0310384660031a01a000162804602400051420f4040360f9140e6071f1240201c1800100842405414071500171314a03284c0e0191b040060312a501d01075091380d400880e03880882080961028401c880090500f81c0f0280015038503420040f083c1c0036140c400f1a80310f0f162406460400c622504c285010300c1c01c0880c001d10240000c0a181e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 748371438 1250 748370188 748370197
    0xc07181d0613170f040308040602370510060b040821070201180b07060b130902010807180b2208030313030806030f10050703060501030e03040b03180a0f06050723 71
    0x82404004201380c0b6250110800a440114403e042913a41d541c01c0480090400c8600c04044644488003140c00e00c2c40208103001080900301e000360600401c3c6182001e524012103805908117052625502040c1745100342700400a480290703084905107809100c80d198200145018000150001c1c00070600540c8203101c0358504d07030920303070310403401c42c0d10748526203190350205d50102c4101e96100008032160601d441c1440000b064404100302601c207540018102800007080081000701d04c80010400050000094010b016241c01c01a142c60700c043c012100d8800d1031501e05039280c050701d03002640242c004200d0b48110851051301540e28895a4150f5103c3c5000d0051641030050440c2141c6500b420004450a8003100c031020405082c901c0028040364495084141090704250042c1c034642070020480702200c510800f040d64a98403213602c40c1c0c11064442c88821180596031455040c41582e510090880d4000c400410150301c0301c0c0002e40c0c030b040c02c020703011040d0345900740c203103a02d800010040d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 748372688 1250 748371438 748371473
    0x31e031b0912011e180b0a02300103300509060f131403010c09050906031903021c080601020607030908130f0f08030a140c07181d0613 59
    0x1c5828041c0382c440c2074a02e04218500c0440c1c886449202c2201c04d400b899801800340002110050500e0310b80200d80c11004140100e0507400007002c0300d20340158400b0080382d42404a14034000440348421501b142d20a01c42030b1550540031050340d81170142191507480c00740355800701034908900000e080d10260000d0300030543c4410180035507900050410020b06021500d2001507a403075040c40308409010b814803100ca030090389462510218160000c0d0715100356071003190469043d80d12000060724002d410034401101d47d035800e05ca00e04043c0c0004408080602a0382da5007801c680c103c10469800e002211032a00591003400841d00c168040e40c84030140c24011484c5910b4500c24040c0d201e4584c003d6030100154010b0303010204180e070481c110340406003201c10061440c2c1840300000400c0c181c08000700d528180d50014100610702010002640102601c1c40300c80e58450541422400400c0340c03c91440c1c000e8a0103210707031048000407aa10f8400c812a4518464096060b11a1032b00c414040c10310 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 748373938 1250 748372688 748372699
    0x20030703110f0405010902122503180503040608010303030b09060f0904030c08041203090911070305131d060102011a03100c030209120313090203040b04120c0f0302031e031b09 77
    0x10407503a2a0f034011203010300325415001d80c0e07480f811350f80342c04000c200610703400c207420100c0c20504074018818181f6000006900e404251065a1080e4200d0f60303610340c0300240b0b2840000350000702d294002d031066040f68001e4400304003007124a400e012842800715080c95101c54101941400f52801d03550041c1c0050181c81c0c081c1b1031840f90340d20314500da0711542060045255140d0b1031402c140c0c1c40001003000c1e2201d0741046c00709441846c41c1d80d02c02d004080713006041c00070102d4118550611600b0321401032442400e40515810201410896000c00740d5000d4010350030440c034000034002c0801c00c00d880c158098010034000341880300385001045c440c0c10341f500301038080014400c00e50382d540d03803c1c11021190018654481161500c0403c0c00c0150f0300202e280b80c0103000300030101d250b0490780c640c01500040c0041145240d09403c40301d6a08007180207000040311b46041051560000103050020011024100102903022190b900390008490601c04810001500d5840c41c2c8020054081c40001806 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 748375188 1250 748373938 748373959
    0x80f0f09191b0b1216050c0106090b0114030601021513021224010b0f0a030b09040b01170304031e1407080d0207050f13050921072003070311 62
    0x52440d80301110165000c1a5981c0d00ba50520904010040184070220020703180011115002d889020000e002c044010003248103691080c0c01001101d80700e104c880001c0108584441d110b0005211200301c4a0000c1c1c0008003840640e903842080381d000301c00c1600204142201c0321205012040d000345101c1074020340280c900e00503141c03408500401c1c5000c0000d840130f16a8074507d5241c21000400440750505144010003203100084200e84a212070201000c0e80d4006071003080c1c0c06801c4c3c3e80c20084c0c200240b1030410090215448410303060300e0000343e0f00814440d400b82c440d5640d0140e40005040c0d00701c003d6111801d40380100ca03120510380b0590a50620808a84515091000c1d0f5030103c0c3c03642c0c00c503180140040380e0520820b0064001180c020010540440101d101c9100c40c103101d498440e43e907004554034a804100e40004000d08a42c180c2d640003082040d00d103207811540c401c0b116451041200c0c4418210030400000c1240b01a005104082c5551203c083c1c0a00795045160022a10340 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 748376438 1250 748375188 748375213
    0x4050f192a181407020a0308040f05071502010209030c01110705240708070b06011805041e0204060e0a080d050702090a0f0c0e1c0b0c1e04030b06090106080f0f09 71
    0x2d03414100c80310000001500c0c035030b511840f01d66244028a1102150420400c0c54002a0426a4070f60000c3e082070350848000c0b1300b4500700b0b00d40841600005c00d0059840c1071326504943c1500204a1880c0c00da055904180d022401900c42098401c110851030708034003020311060500e00c1d1114044070b4600d0a4200740c03920400650800c3c0c1c8156001c0e101c1c05400110042480624580103070404001e01c0c02c03104240c1038100680b0a181c02e401003501c01e685500c6a01c6400c00c2c4602004008070414100b1035030745603580030161100d4440409a0300418051000242c0e181006c605140c05141c01c4e2502850894950300300280104010030070f00205980707032034030410748940d132148003d0400c0c0d640f01c7c1c001c90072581d001c000461401040d440e200c2000b512903080000c444035005500011040b00d11a20361808580502c0042e612421400200c1004600001446806c4c07100c0c80c0a06020390391069142d899000860301c00200300c07158250b4503003000c00b0403a2540c0f014141c56000300b0380c0342526815810391 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 748377688 1250 748376438 748376459
    0x1110309030307110c030604030c030201021207091701060e040327060c0b061c020103181506030308010e0103051c0e04020c06100501110c040e030903030304050f192a 73
    0x1034a01044950002c01041003103900300080b698041150304c0184440401000025941c6da0b0090000b001c11101c49000c50805000750150341c01410b10010b40080c13480c142e200107002e01d81911400480c14160700320040c2005040c0b01e101c0907110b1403001c696440da160380f0191240540b91010180c0e40c0308100d140c0320054601d0056401a000d01e81e40e0205111035400c03c5060208040c288030300c03840000fa5600040340c0c000100301825582070901252800280f10086400f0700c000304041e140d0384c4502c00c18003110700c00b540000c06480c1710351030f02d1101e6604e50501c800d00140074000181681e03c00d014041407000c4400b10700320150301d82c0c540b0302454824040071030149c0e084020403101c0f41d4041010702000301c1020800c0c2c00604800e1a1081001d190034080726540d04500e88818040c4d6643c1c5040f8401150901c2181d5100d280a0b085907940e080501e00702d0364968007000004698040c2c910384460a01800309108809500300c4040840c08000c9007425400c04140101d420300750883c1c00c0b0010701600701c0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 748378938 1250 748377688 748377691
    0x1110d030f1d0613141c1214060f0f06070501050a0c020a020109091512050313140f0d0804030501090b150108070f0806120f030909130803130501090c09091a04051e011103 75
    0xb46c1341203812000c1080040e002c14180c9192000d544d04180f840300182c00164603180e40800200d428603042108071006c2451000c100c00c03459088034000030050140300e8150011400f1301030180040100300c00c0700e1012602e81c002904005d0002d040c1510030046c100c1d440d048101252030464007020081d555402e05642410b2030340742291981c00c080b4645208000038502000100b4480d1502c810010b542800155481f1010202902c103070003079040d081c14448800159030141d0381c818001c00c260800c1c0d09040074041c104507602070701300031031001902c01544160380d20b40c0114460380300d0444010101c0b00503900181c0041c210358110701e030300c0110041c4034010004203440900c40809144c0d1981d50708144040c00704010f08014941d00c49884000004000c00d0859602440190074085006c440b4902030340540f4464902626101c00d507000498101c00d994454035580d0302c40c4030981c5000c001606054411074041390041c1c50340d040300d1020100044e80b481403a141c12a0613000181c480b2912405102d140c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 748380188 1250 748378938 748378963
    0x6060d0b0a060e032103010902070302070308070b09100204080a060209030f061006020d090f09020906070c1805180601030b0c04030605010314060615071101110d030f1d061314 77
    0x3d12140f88141e900341070008900402d288041d0b408074000c0318200da181c0c0d02c418840c0750307000399002441070103151080c0a00009180d109241a0b5140d00500f0b050300c07441000d65014949000b0174040c00360004080c4215411124000003902c01c0c5134054aa00300290803071f400598050181d0103405096400503c8042d104621003045000d4050824a000f46082100d02c8404144092201c090100f00203a10901e8102d0f4003019000d42d41c0c41e40200421060300070000e00800c0b60541c0040030841d82c6046203880c0d89407410031010005036480301800a5140480400725950b0303040f550050011a007440200e660015001328a20b00d803079a41d03a10b0340c0844100364801d0700c0280e4030070702c0c202c1511014006d082c1c0000f421101041104001d000c00e10103845039560007000c1d00c8001b40f2441b0164003442c080003a20350110150380c00c0400c081c101070050003002444859013450030007a5481d9041c0c4008024503d074134000148103035030303c07440d514908030b0003e642030f18101241c0c00544c90410040141482d4810b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 748381294 1106 748380188 748380197
    0x1909050c12120f0414091905060f060d0605030606031204060f02071715060405090a0201051602091e1315053d12020906060d0b0a06 58
    0xa6003000941c4464008202c00501d420b030f0340041c00c1142c0118125403000c1000004001c41c41400304c0e490b11921000050001400d0f07800d600c065442900541410650614079000440b5600446207211301319850340d6090056060620503507802c460190000d02508445401030300081c0601d0180f681000070300c826202860380700700501801801d101d02c1e210315081e44040999240c0f10b140441c0e01c07001c240074001c1076690800740f013002d00c56400d1070060201c1c4250b070ba004603111b81c00b0b030754041701d030140c4504e14a0250352140d9409014000f440d040a01144d80100c020f10041c40c001c1040d000b1710807840c65a004140c07401720b9580c65084c1e103200041c45546000c460b520001500646507817501c3e003001001e80d8245030304030b5035400c02c0545003031010190341c4011040c031900a50400940200c05040401c24604200340038044030480b055010602140c070b800450946e0307550303501440014 = true := by decide +kernel

theorem cover : BRFrame.Cov 748201438 748381294 := by
  have h0 := BRFrame.cov_init 748201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 748201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 748201438 ≤ n) (h2 : n < 748381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
