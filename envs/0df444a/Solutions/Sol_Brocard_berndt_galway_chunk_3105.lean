-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3105
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:40:38.591231+00:00
-- url     : https://prove2.me/submissions/341f4ab4-72e5-46cd-9d4f-73cb29bf0ab6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 558273381 ≤ n < 558453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 558274631 1250 558273381 558273437
    0x3091305072a0605090c1005090d1a150405060d02040504060f020a110c100e1002030904050a0c1106010312030c0203040f0803070201170f060411070b0114240d0504051510060f 77
    0x12a01040c10940303a60713280441d00b04a5480907002c0c80c2820340c2c0d42246480203003240c040306101403104000215050074000c0323f109a900a00e00603028100b5400c0100600000d0001d0382e00ca5902c02c02c0c0703030400007e84010a00c162940d15150001c4045c8220b142c6040c100d50361080c00b8615118800d0f103000e4200300c0c1c240f40300c01c045601c000485c001b064101c2c654003d85e1542948141000c0038885254280d0340f00100e58411a0ba40d518064030844119030350f400d0a100c010581060240c9100d14103100364003004e182642441640e18090b5035408071b800a404641040d009908000340500441d078200c6a1880e0108a408041c405490200b1400b450b1000c001c0c41e8501403600c5a1218040c0c00c0d1140840307c0c181e52084080d60a56141e408618589003c1202680242c107031600401e0800c0702412150414055450605e2030324002d41c417000c000c0e11000c1d104503241e2142c0324500c0120300c00441b0140c4100800e0080c0f4a4a84c50402c00802c1091040e510105006440d100d48100e41049070f0881144 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 558275881 1250 558274631 558274637
    0x109020a0e1801050103080d0c021504120c0b0115030e07210c081015080c03060105040b0402160605040b0f060303160c0503190b0903091305072a0605090c10 69
    0x540c2e8400c0c58041800e888041c0310015460a00003004015001000d00386401500d402004400c0e071140090781d850010004c04104850300e50005000291085001010080580340c044c4062585070389000001c20281c10401681204c0444e001000354540708440241d400100100691490208400f01e0031003040300c84100b85207600f000c8814441e500d0b880344005c00340038044502103030356440e080008100c0340403100d501d400c11580002c1d080380005041c1ca541d0100074058200b507480d0108100091018040e134940003502400b01024850018080f0405075004e084017142c41d240903e02400b03240402000e07002d400d0903090910440341c40020683c0c41280038030001d50829129403c248222201560000c0d40c1841010200307001c211100b040c170380641384030780c0f9410b9076503d4107a12140c80e0f02445c1a56500700301851802c150024494000c80d07004180c0d424107004100b0040e0500015140400362010010f020000c41400c00c0300b54482c00b540304500d038018000880038880041d501310f00c7c80e0301c40360030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 558277131 1250 558275881 558275909
    0xf11070611120a050f0603030c2503060504050d1b0c0b1809010824010602030f0a1707030506130c0f180b0c0607020f0619020a180b040906080109020a 66
    0x6801c803108540c0390341e811049042c124904002d030400902000c543d0b501445500001203503450030700009442c914144d520203803c461301001d1a800e420740003515000c1019100b21030000102e070b00c41c810780340600c3c0070341d01030008601e01c1240500030b17161011220b0004550101e8001c08a54076409142c02c2d00c2d07040c48000e60307076011000c20011001c1e08180b8203901103507a4000051810001030701009116603041d000390160b000300404001c801c1d0921030200960000c0010101c06034959001300415032540c24501075a04401e144c41022810440f51080030075915814030089103007104145284064208051007071050401005001c6a1241030030700030320003d405020303241c000c200640000ba00610b154036884110000c0e005603070301c0c03003070fa0200003600403882c3c001130401c800308900344601140c0380041804d001d820300550082d80702c0c0e80380508000c031845181f11800180301c20319008010a0b2001c686590030011480b0840d81907a01000091b0b00d400142001030301c8100303825040751410342003199 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 558278381 1250 558277131 558277151
    0x60a03060e070f020601141906030b01030b0f0307030210050706050115120e070e091504080d0506010903050c0120010c021f361202030c0601060504030b04120207090f020309010f110706 81
    0x9405d0750108e2212441001c88501044141d03060f4084110302500760780901142440d2418420000240f402803509038000d9242440907081000d03d5540e280945d02c0c000c1d1800d00e450302c3d62401c6032420303001514030324400011441c0d0158040341042408031a11720401440000c01400c99481c42c452041100101c071075400103c0c14901800300802c04504101038004626051a2094450707001c007081e040000d00c0c2c41c000c551194400c0b80d401c401d49600500500702c030f209000054a201d40d10340d556140c4100c500142000c5d44400707000d00c01c82c1000c550000e210200014111000e14070341d0001c0803807914030700314864440840d020410b0204036800d6000c2543c56241e21486030000554a102422081c5042c02d0441c4180d8004010149050140150364959899484c212006c0c81070340f101a01141c081c002107030200d01c00d44054447c0f2069030040307404499840f5814003d45450182c01c0301c401c1e40c08420404001003e0040300b21150360080200300318420346640c2c0c0400d000380000034003021399070080d0745 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 558279631 1250 558278381 558278389
    0x3140301030b0f10180c050c07060e0a0b03010509180c15091003020a120b04060b210c03010b030402060c1e030c01060f05010519021f09060b03060f060d080702060a03060e070f02060114 81
    0x1c0c135010605003982d05940d103400c0301404030782f003482546d40901c140c51750003d034681c091000e503816070703a00600892250701d40224803125030000303c07504212801200000401343d920002c50301444034101006688803083c800801c0440c20005880d030081c10700411034800b1a6a0009941d01c04c0c4005800002d0030120100201c0c1c024401034110350401800022024518040d21504140b41c50720762807240510303611a88182c02601080c4907003000c44005201244c0103103050000703040e194803840100c90180442c8080041c000300d840d02c0d01d0300f0070b03000000d13101070484080c007032080038009014a00b00002e2501000801c684140c0c18681e803c6c80d07441c0300504c40984284900d05611051b10342e602d01ea8043e00200f0030090030742d4002202e042d40341c0b00c0c3e02c2c2081e0030b011602d03910604285800c0743c81e540d03c000a02c003002034000c6080715004e004100c0c000042e641c04000e001d4051a60344e00062042c01c0c21840305080c880500610148101543c10031245540061071030305440b480f0710b02c50040c0c02444045 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 558280881 1250 558279631 558279637
    0x10504150305073305030912090d060b03010f0507050a0906031b03020c1507020c010e010807120b0607081308011503080403060f0b04022d0c150403140301030b0f10180c05 75
    0x18034410b426515610303107005d501a000c2c0d4014010041502c901d801910b0110440d803144d00046a0810240d0304040081039031a0b002e000030ba5005070001c58055482c04001c41203039001c41c0c81c0e501044021544101d516405484d40f00501340c0c42c10704100b9069400f00828485140100a108044d0005031444031a1014020b14000300100b00c0d802d5040c1c1130110010f502d4400c0d281402e80020503420f940012503200b51a9540102c4060300d40702c612400000c01c540c040c20859200c01d401003803c0140b000001c3c0428020003102d00d002c07541c1c8000c0c0742800c0d01c1509403000030b940c2c00c68031440385900b8004241800d045500b1a45c1c0528000740314140e607103821000d40700d4404565032240c0302003144044c00345504048032205900502d2101000c034041907040f080d01402c130300c0e0f140617400b141e100b007841c41c8081c290580107406402c2a2903890705044807650240e02c240c10854010070f4040521101400c48003185e03070001007130306400000c141070500c0d106d07246201910f1402a0340c0c031054218001c5d4020411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 558282131 1250 558280881 558280949
    0x30c06040e071e0c0210032f0c030403060603020a080f031803070302100309050f0601060e090621031209060f0411010e03070618080a02010f120f1401050415030507 72
    0x102100300fa4503480c050302c640ca91003400d03402241c202841b114210b22a100d141d100a40c90541c030103050020491206102030071124040c0411401c000c0c0340d50583c001c0000d03100451003600e0100d409411803040c0982d000f459030003c01745c0d5014800ea0095000044280c801d5181e080c4100c0e0030700446c10f00000e02d00b00342c41c2d2000e074109a02504101000354190080c0401c1c078056022686030000002d2103e5550b8024420140051542101c0c0001e901d001004560461001400480100041c0709a516810101c3c80120700982c4000fa80c1c5410079080c1d0030b401d1b8800c2d24030340642800c1c50554074141341d20724010401040f1a00c0c0355070307400f1282e029603036454a250000d8125101c3e581c644401030b0880d8100c0a038540d550f140303203170b00007480b03080014144c5174a45c2c103a4468441e10755010081d2002148403088510140d140c0c401c024100d00103108681002d0f80720043d030003242d4904814081142d806030005101c101c1c1c40c0d40e0600c0030400c0011548102c0d9561110480840d0b41140c880c1080036103460 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 558283381 1250 558282131 558282167
    0x40e19110a030b040e0d02100f0b060d090312020304020609220518010e0a02102f010c0311071101052109060f0606132102030f01060f05030c06040e07 66
    0x200700071140e9055000c1d00920b002940d041200044112103966103503050030400f401a80846040c240e0460a60406c0c240d5114648010424039200c00001d80c0c1504070418140a80359690030081c2411fa0101c00c55841c0429508110b1841c240380e00803a1943c8510400b850003443c4400c04001c510110246190982c4c541120403c03170340c28090fa010028084412840c2c1c6190f0a0620000054001107070004126600804a184072008050251411035202a0001c0d04a29616034000d07415090f50f0828411120b02c0e000140f00f071043d510107802c03a1103103c1110048031044c80910300080200024080c911401d00b885903c8004008140c9110140c4071070625003010800107020b51044001891401000f403403010104554449043c003000313001d80b812440a01040040400803c690b981c0c05641a0f540c0000074044244550003091503c1014000184207a654080030814850701c60a0b5201912045018100341040707200000d010740907502850451400070b0001c1001603005020313940b150020382c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 558284631 1250 558283381 558283387
    0x334080f0d091b05040e100e0705030d0f0f05030103030c0209060303130b121f09111e03060907090f0303030b04020d050c030a0b090601141b061812040e1911 69
    0x700d06404071040f6000442d200b0700d10b121001c60140303858000e03507402150315002800c9044c0c020800310017401144148820034042d400010135203032402c1c01028060f064503240c17120966100c16005000812062061080000602c01400081d510280345094160103d078241c0c155202d200c0040d0440c0f29400100f403d42043d80c100107503010050b0080d0a404184100500070b0b60f5401e89108000542aa100f07681060000e90500a1000ca5405401d0809814104504003d034844040b207050640719a8200d1840d404001c00c100c3d4500183c0c1198020750510340300c403040d4507240b980c000414050100500780f54650303610010030703282d07903050344c44070840900c090000b401e0950403901d00c1e51003900c40080c42410300308141000c1c01d14010180c0101c106950700b101441c1400306104868011a0f03481c0c070841a50902420301c1c040400003d809414046032000420100031503440c6403036141182e94899100c1400304200104109885c554024194904031103e140e0003030202004103084524001108008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 558285881 1250 558284631 558284633
    0x80a11010c0c1e0e01050409020901050907020723121c0e01030b0616020a06030513020108040203010f0903031509230603070807080604060b0f0a23040e0334080f0d09 73
    0x20f085044200ca424440d0082e081e41c03034105000640d8007800300a500080003070700400c02410300142d103d40c00002441034130005038940501140c000320400103843d00d00030581d1015268130303000aa900c040e82e00800280000c1d0105000c03100302000594a51090142c0150216420790181d000500c08000080c041c6950f0540b118441c280290201c1e000da0090b100f200010494600901c1032070b001b5400b0170a424a07811240d8011501480c000300300701e8140d500c0d6050b0360340c21341c058000d000b5101e200e61008070f060100e80c0e07600500340b00140e01c289601c9090814081c004a4206483c24800e182180108104d540d941e000c20701d00042d40d84042e03e180300d00da2000441d16000b0400d940260711500c010300ca039540e50380030410005030084142c1c0d03200745280c40c104513100c403011501d094941c1c091820070085c8a001c001408443caa00328203201600005221782c110720380d0408070180c6902d1080c1c101d041c03c002000e88005500e495800800c803040000d40388405861200030f8410412000034184868002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 558287131 1250 558285881 558285929
    0x20c240d0f0509030403050714130e15060103090201121d06180d09030b06090a06080f0a050c060301030302120d14190f11071709030102030c070c080a11010c0c 70
    0x9010038070300490b8600004207014840100c102c0e4200c0341c200000302483c030700380311000d956010004141c590140c0252442030605c000345c01110224009800944000b0004120031650040018000c60405103001c049200503a0000801003030041804c81c00204038102d0342c40840490881100410144520800c003d0a1042004898021a2a101130b94201e0f000c400040d02c0d824904d0100411200100001400c242084100c10303030310910b86d11011849550b14500c46040464825000406030450007440c0c090210400200c1d80d40407040d41c0013844e42d1714688000703444040c06480080c150340002920405402c1c95080b02a001a150442c50b080d0704044600381039140d110000f01384030604185103c7c14030325003442040144020280d95504d007c1403951580c54281034607021103c0486d0074444c0355441d441c04d1010310f20403049a45c5050340e85078181010324802d03d5550005555600c2040780384001012000c2c403041280c0c013800c00c2c0700d096003145043c58103078082e0340013419540c01c544403010413060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 558288381 1250 558287131 558287141
    0x207050109262b02011104030f1b03080a0507020301050f10420e01020f0601053a0201080907050a030303050601020a05011a0a0f080a12051303030302030604060b030601020c240d 78
    0x1051390020032560003503001990160240384006014103600d654040c0220b54442000c0000005000e541c0780443e0301c3e17aa0b022843e40201d58043c00007000400c0d400b0450401340f00350f80d04000121119490b501d04a0f0481419a985000314a40e14800940c5d6184240d118480c2404038610320700b0040003000d8a038051101e0018483d8484005000461060344e154000301e0340341c4032f461151003d00364a80c00d1605100141258a02015013005260b000040707440c0c0c60700d100710038903960340d05d401050411400010b00104001d043d188a640142100b0883c56995410110440358903041c045520f039035650060381060b41c80031004d4001d501742608001d4441d00b0300c0000fa4998802c80303004034002e03150041c0c2c03809103016001d1540503912442220300800e8101c0e00d01034103100f00f460002d152400c0718030380a070100030302d03031007103002c83c1d004400d124040c6418019040605080071907503003549000750000b543d03045602049406482c100b102961140219134007004c00e40340482c441503032001e0403903482004103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 558289631 1250 558288381 558288463
    0x17040308030c0a1209050a060515090a0e07050102030f120c0706020a030e1b030729040602330601030e030903070e100618061412011203020705010926 66
    0x349138068030b900c460b400c1d1181c03100d555000320007080410000d44c1c82c400100b0020f000300c902d1506001c0100032560302e04050f14416002c40c403001c00c02580e0301980902d00041604200d05540040c0080e0200744068401d40d0b4400340045424040303a201c081d5040324138804c00c0c078098402800040c0d5045020f4040c0c00c9001c44000740c000312041d540301141c03403141380c04218111f20f905401c81d4074108202146070f00b03508841c0c44140d4107100030081c0300c1c9a0034440d5101c0c4c0d01c0071000d030b0400b050003c0f0b0840003801000313040400b950a0060700705c003400c0c803e0101c00d005014505150340e0303031000c100350041041581c4104c8030140c1201c20203519000000f00000e0125101c00d12981034082c0802c459120b2038040a003010a2081d9031443e42c14100151201c28100303150384080501400b020019101e00b0750340038000c100003000300a2064441c10001e0502007903400c01810b0004d01c100810164940014450b04011815480d01009012800d8503040c18408806801c000440141b103000810384941c409d0926 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 558290881 1250 558289631 558289637
    0xe130905061b04060c151419020f03161101020f120108010902032a09101706010b0a030f090c0347130506040605270a17040308030c0a 59
    0x30307682c0c464441124075101c80740e40d503651000340400c02080d03002d5200c110b1503512600c02004a036419204040807581641d80c01c0301030115420078000b00c54a503007070180fa010303006541940740401c000401c111510005d0300c0a40900300706040259158072a40c82c003c440009240290342d102c2c2c13081c1980400f904105008554103a1240000516410503c10100c0407980500682100c0842868034007203507201e05000102c0c2d1111007030380f100f255501c41d0020f20410b11900d5004a160070321016180070000300a07884aa81c1c4410010f2000b00401c506a600200003490007003164202d81398898080e000c0303800c0041142401840200800c00059420321038001180f44007001c0c45034880922540d002401210ba03404542c2c2c03800d818040151020003035014460030740400d00b8910a81c0c1741d80c0350000488003034039050ba49005000d50706500c03d078000044d020740c5103990011501e5561507511440d602c4001842d9040007040351a03005800025503008603040713000207031645888000c038565a4071155000f400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 558292131 1250 558290881 558290893
    0x60708011e081c050c030f04180227060d1103091203072307050a0b09060a0b010503191104080a020a05010c030c0b07030f090812090c090f070e130905 66
    0x6480d00741401c28100d80328036009100814000740d4101400c0d40d180c0b0340b1410070038100314074885504204010086400100030b03540e07489190142c00802d443c1d07541102d00e2150b0041050140d1000300f402c400c62005600c1920307806031030700c650008000b4403c050800598030f04041c1503200c100700a1000d18807401032941540c584010300d40300c00039184011a8100041205000c182d000c1000c85840365030b04bd6010500705107082165140c591030103050080440b5680d0a4108000701c01c2d1040c062990002844030741070040ca29081c00280041c000202034480480c0c104413aa1a681b4554220011940c981a0040d90766610b6039846503c03001c0c00c480c00d9008800403140040c065229004240d2800c1c2c042c1d55a0f424188155180f0102c0b45002d00410100341d101e0200002e02501d9100b8440403a110b0750000c2c0d030f00d841e40d42441e41e1066000380300781596001040c42c0799980c2c40e00d41d08e507940a1105000e81c0400d0395116810745003e2502c502d03598000c44494100e00200780c1c1a44490011070044045540c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 558293381 1250 558292131 558292169
    0x10b1207031103060123030307060501180f050c181f08010602010c0e060d020705100618230403050d11030f0a1b050a0309020a120606030b0703051e1806070801 70
    0x140d619020320451b81041e10007084a0004c008402e803d5030802c200509413490681a0740b100c00a91f00c00380c00151002103d0349020030100410f1148850007100c0000601c9140b401e00e000c000c003401124803403004030300a0303a051011540c0d4660741841c441d800c0e0762440005034808000030b002105c240a0400503600e410100d03912103019100002c40d010004020524049454004001a40180070102c0d80d622420700071401003035141c00380d1006000c000c00601500110102ea0106071403030300010382c54180c1000c0c00c5100d2a0742c442034060f40f141c0c06061944c0d85600c05500b100040800c9403a0444025006c41407107032040c4d043c0d0b8102c3c00b0b03008000041c0701c1030742c66250307400c40c0e0741d090381140010401c100060700800b806600884080c030700042c552a4407070b640b00c0741c00080d40301c2510700f201c58540c1d44c90180704004490756029080710b441e207810800c40ca0311941021661540a440398061207446000400d100c07100d40410441c0b0780200261085820003400191101c08203000300400c0d0440044440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 558294631 1250 558293381 558293383
    0x1c0f151e15020a030f0e0a0501050d09050d03020c0c0402090901030209060d06020706021308060f041202010f1107030f08070503010504020304240c02010b0105091810050a17010b0405060d14010b1207031103 90
    0x259106c01c02458210140d02d42001507955520003171201e50f20315144c0000c030000c500c00344030b800c282c00080e841c0542d58a8840a5840c180f80c04c0840c4148928810b12100b1a541c60f0000d92a041d03a6054403404855242c1c5000907402010000b801041640001403400400000b0307006004800001000b0a1006441d860159150001100c400c00308451420015001c01c18851200040071200c4c00001401140960900f040d00c1c0c01c44241d8141100000d00c180130540d01c03680075482501545001c10082c180a0f500812604c0107200d210300c210b8010001c901409400f0842d0504443c40099040b400451220200d001c4e02c01380301c1e048055482c00b800483c0700e50207071088034a8054024078100380081e0500107408011005850b1a00c410765001d804642034840b546200050407501c0480320303024664180762420b40e158a28028003660500c002e1000b640c680c8001c00c0241a07001007540c4a00342002e42c1103004146000c1940e40c01419080c220107203400114031401a2030184424841600d00d0f10141 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 558295881 1250 558294631 558294647
    0x5060a090e010906050112110c0a030519090602060406090510020d0e01060b1905180a030506090118031704020f092d060d031409061c0f151e15020a030f 67
    0x24031b01103034801e09040504084c591100b840412000042803e25080ca02100e19004604d40d00701c001c10400070303d03144c1404901448200070740707051912084e540d007440402511b03004060030050106844000c0001040030030300c1000c00d840551401192100d049071150409080d4001c50b1480075407900101003000c400e84405c452404035441042610b506109408075802d600c80700201316510b1320b940300c855183c3d851001400007140140020600390800240160840b11207501c02c0300b1020078203055100180d00f201c00c8010311840c07601d408040c1d540340e002107000c000100c40e650741c1c401031780b40801814040d4800d03500002101c0090401c0040182d0a0080034010265440ba40c01b800711041c82c000640f2401144d003944c0c40b43c210721420134084001060305600904d00ea00c0807180c01854641440034603100d00d13407081c061030209100d5001415140c501c0c000690050403112580101c0c240304164015041c00018544240007150008001e40029111941036000300c001801100040e94014400c03201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 558297131 1250 558295881 558295889
    0x30601060e1c02030615090709050a030f1b060203130806041a070c05060f01032a090b030a050307050a060510180f0e1501050f040c05041a0405060a090e010906 70
    0x100320700081d070351081004801c0c101e07074a100020780c680c18000c0141c600b4845503000381c456400034a07001488108002c0d5107200103100008100d0140300402c145e0740c80c100d00c0004c8030f0300101d0466020300c5605110300d0010414040d01e98081c4006800509140d000005148030000b581c1c0080703100c5c1e00d440603e5250340091360f01038440f1074814600d114950100070078a4000070300c8d0038800307003280d41992000d041580072500081e103548800c00405c180543c1c06015040700000164100302140e080440f0583c0703840900588100719540c0d000410292020058818801c0d045006c0301d4844206281407030703444c600000103c54a9090201295038500c201d4254030a840c5081d2000f0b040703215a011540c010528040b021340307040e888117456903041c84103008404820b1824016200d847d8184028400c003005214101e5001d80d20300100f003a5106d51000c01e44081c3c5440000c12107002c40c1c81c003495010fa01494111980c032200000301d50341c08035000a0f0510803124403410010740c50380da070002c6900b01d600a00c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 558298381 1250 558297131 558297137
    0x405040c0207080f0705150d2004080705271f12170301080d12060302060304060c0f08060f190f1511010c0e04020a031d0307030e030304081f060b0a091403060106 71
    0x903400b407c2c0000707005041440e09084000aa4070780440d08152502d00396400901c0c14840002d06200e00601801050054401903440e0316400c0b0304400c2d400480040c05100d60544540c0102003041c101e81507948295406104e000c001d101d50300c441014a0010000c030b02142c440d40e50202c9000d11070104002d4034120ba011001404184401480c2911080768141c1d013544035954603000030005075154006940a14010680018100c0c458040a01810300c0e03200110f0a00410a080101c2942d83c1e03071003030b07084000c2907890341d86804001086003509220794001c0d40411000b40d50200701c2d0390b20a11030002d80d2005070b4441e00802d01113040c0341c2c00c84501c0d0540000140d059200d9014030700341a002058110040e2800107120428040c00c41d091075070040324040150070004102c0181548100c122600c014120040d62601c1d282c1500d40d6034803070001e0f11607125181c020105902c0d100f441e500c606d0044c04110401507031004404402007288910303010744000d800c1c02102c00c41e00e034207000442a0503905551 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 558299631 1250 558298381 558298399
    0x30607020304060c05030405031002040611012714010f0b150c0d050a0c020a090501050a090b060901030b28050108090318010302031f03110f09070903030c080405040c0207080f0705 79
    0x4104d910004810040d1078900c41044005100d44041000c1d4480c1e0042c00001138440382040c10061001c4e03d40000e0b840541c0c18106008005101003500403040c1142c6607002c0d006803e40d291a109401c00e50141c80316a5181c841045d441d505141c1120502c10801c880b803510162821840001a0180c03c1042d0116884904403000da00e028800602240c03880342890743d0320200d035900050701c18200f508145066a1a038004121a05001c003407140605040032082c400d141280000c40c1e458040c03d407039030f410551550403041c016228022956002c0c007280740350004c42028022004ca141d0b800d44900c1d400520f0141c002a107081020043d1800781e0303628000000e09051500045019400103800e0f4050b014620000003d80340040e1803080041d0b100c1d560070002c08d403000302004004034041a006024211140c10014000d92103a1440e040e0780d8541412640d40c40769080c902e95a0095821864029151a40e050b0102d500050740304101e581e10f00403070301c01c030034030411580c0c40e11010310456070041052 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 558300881 1250 558299631 558299639
    0x501090c0507170a090e04030c120507020114071a04060207020f0103020a020c04090213140a0c05040609150302071406041203022a0f07230a06090314070e0a0f0506030607020304 78
    0xc0010122480d007468013181041d20303164041021b090685007200840c070000c000408000e018402d5600e14146420081d05204454001234240d505502e094001c05400050350b904000c10703802d008074201c100b03949680c51450b003880c0c035000070340c003d5030264843c4800c80e5003001150300ca4002c40e0805407503903014000c00c03072810090002070086440126445000e480500d07522141c18440c440b600f07006c503c020501400c2848034003007110301d420340c80070400004000038800b19402c4002c60045500c106444411180f900f2030840090095280042c10314403000c0981e081146c000030a039011ba4024096661174101c0102c06808078030511a04540561801410f80f01002d16002640000010901500c00ca40c0d01d90f40003034103004007a0442d18040014069401c0104c006540140411200b070740c04901240c00d0940151054060744001081000780e500700903200403051008500820613035035a81d1150820501102c040d01600d1030b000090351411001482c40d02e00020003a01561490300551319041c20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 558302131 1250 558300881 558300923
    0xe180a2307140f0d0b0a1401050f032d0a120e010c0507060c03020f03130807091a06030403030209040f200f0a1107030c060c0606063906020d0501090c0507 68
    0x18280d5880100d4104c1ca038042245280101e2061824040c0011a6900003420910822040c1c2055002d0160301010400588001444105880102100608400c0c7c0551200c41703000e4003600010307003801380642150410540c070356040b0400340f42d900da60f11800c400d900110340b0300480d00c00180c51070b03212100422031203001e1989034400034040c0c8191142ca1060140751840d540c840d59880501c880c0c1500c0812002c03200344040006081001c00c280300a01c0d10302d004014074031145010a210340e0303000000c02e04060117941198107400010b0014004425525100030040c00150340007041c1c2048503868018510213202120301050304820240d041a04c10041100c0703034074810b88244014462104048003140b0041703011002842c05540d18000070303030181f6042054604a50001d8180308200e507840b1000405107496001c0c4030444c0c500d0703107003000740011281500000f84d00007428140c80041d154074406c01c660440c4d0705807440c510041c0b0810349a45422a681e11410078081c245500100c810b15003980 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 558303381 1250 558302131 558302149
    0x605090606030a030e0303130e010f0b0703050712110d1106071803060507050c03030f06150a08060d032102030a061401090b0c0a0606090e0c10090e180a230714 70
    0x1c4040d0480382440c070804012391107000030380c00c161461140712004000b402c3c01c12031580b020740500d0415504145e840c1d5005052800342c8580240080c3e48161180d50061041d42c0c0c0d4200d458070b180455070602c2c011400030b402070380507911304840b50240c50002350315a4012207140e01854604115042d40c1c0c2e2941d03e5000c01401c0c06483d02c0d0400c54208034040448500300055402400000d00884040c1400c0040041c50401c0e140b40c28001802400541f541c1c1d03030030400c11540060300781c1d00c07684500c84600e4116101010f544410103ca41e070740b106c00400700e8540c0d01552084004000402c61b07141c41309106810000138500b6540004c10b04201800390004000c054110f90340100300b15040b03034000365104c0c0b040d110650413018040d03581d4803084400440070000c0c82c80e001c9050f60101802d45020701c00610502c0d03240103800308581c0c0c450200d001001c807038a025107840c0c141010350303610700d030f4524114a0000c00303268280d6459a22100d4100b0844001c00c55100b200c1004d0f41034021664204244010b80f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 558304631 1250 558303381 558303407
    0x160f1a040801060315230105100225060806040504050303071808061302011211180f040c020f060901020a0903020103090203150f0907090203040f060917040f030605090606030a03 78
    0x1a509020009011500340540b0b0055845010301400003602c0020140840700f100080201046a2554445041d8444030f01c0c58150307101a00c3c103541c0c02d6603494060786050040401c1c80580d14007003140e130841090510804041e138016039101c0006403111001c00c01a204161400380c90f0350020400f03e1002070203407041c690a0090416402c681c0350b60350400c0fa080490031507100381c180040c501110115a440301c0705108180242c2c10401c03080b4044154034005002d8000c100d0642000d0090b1049542e0318914003101321b07240140305220500300514002c0d10f072409a010547c040c4144400b281d43d541d03060080e00e00491103503a13000c0c0b01c80d2450300110007514101800366051700412107103501c0403000c5001544030b4001038400851604140d6007061502019500c1100d4591040c8140000500c0c2041041880c540084001c160a10942000724170b0030100d40852800200008000980042c480c542004582c0503060400c004d80d9002c40550721094200d4040e54550003042b134450001c0e0050441034014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 558305881 1250 558304631 558304679
    0x905030a2d0518040e250e010f05010305160e13090b07080108100c140c010b10020114070e03030730020c040e01060501090e040317040f05160f 63
    0x40c05109201080c039848552450000380001003c214001102c042d080d600b10064408102e429251000b89880740a50342c0882001c1c030400540303060707030b103a10042030015141c40c04541c000e0b940d651801d040b00c11030610034107000c039040400150600b690840c0c040031460281d1600d001504c94041000003070303240c4c0303001e040002d690b560511005c24008441d04d84035002c952540314543d410801d556180001480709541824105880c543d0380d41d5100700391403140803856980c170b0784a000784016540948804681c1d20b820019490060b002954150070150403225805002c0e119034403010350490341900c44080c01c81e0154020070900000800030840201c002c0007891001c01140154514401d50b112078811841c01607201c8952003190380b034244241c616802035100208422440c120018107038010510840895500c4500050181030040303040d689400c00d8048203803030900d0146490b0181e822414404d0300c0380c0c407688000841ca814000d1501085d60b0900343d151180901e0b1141103034036400300301b0007180305d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 558307131 1250 558305881 558305927
    0x40506070c1e060b09090f0d080a090b040b0406051b090105070345050a03080703180906030b0f0f060609150c0106061d100c030216080c01030e010905030a 68
    0x34280c030204804900b02c0c89400003158042c40c4208010120381c000e002052180c10200e00c0044c04500003071103042400140c1403400440c1e41d0030000c200142a201c1000c0d00e010300c0201080100550000074a00c0346200360703c00c12440d180d00e05000034034101c0641094000310b04100c0c00b101580950007070300000d0300c0780c505941d005545c0c040300024050740351001c45035820325961610f848078031503041c3c83c00c26200d180802c61082c588400210748440510010307103d890001064018940301c2c881d02c00115108900718003040c0e60301c011401c0101002d2005450481c107900103d60f240508140c0d843c010220004d40e60020303110101001120b0340b12a000c251701450b00302c01844000344e010090240c040b0380d1030001a200b441e00c600030b0400341e9030002c00c007002035400810f010b0b11b0760343d072500c0313030301345145103090300701e015040ca402e80c07801580703c81030300f0080d110b12400600444c00040208060130207903001d00a2545012480c3e0a998a003000200103400905c40091003034440c240c00000c0300309492414407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 558308381 1250 558307131 558307163
    0x6080105010c11120c0f010c0c1a040b0a020d12020a0207180209030a05031803150412030b060304120f03090312020f19090306050c07020d030e0301021c02071a040506070c 75
    0x2014200121444c0d200741c210700100405840d020254800d80e150a0900c54084140e9580c3c0c003400d101503002e020b00442806501c0e4110389a03840641e809032030528070700b039a100e0f0352078030185d5104084240b107000074480e1040d070140c00744036000b0707152120072a40040c0b180d03e04110405010340403410f14010215030038000c00410341d50822116117014000c1010f985d9403080c00c01300240c0c030004030014900941c000100008501040c503241d903881a003000080414840b0094210040c0c07200d07518260b40401c001c41444140b201510b2070700445ca425468180c03103407501000a800b907130500310f0080d012524207056060b0b8401030350010320b03e02e60701038011444d10708400e14101c000100e103102d5100041000d80c06100b0170029208158111000c03440b00c0b410080710b603001030103542e0034031401001c01041704140e00040d1070035010354a00907414a00c030200b02003001c0454000307420003402a160040121404c0100d4405030030b615028682143c00303005103a41b1940c090310500403404c0c2c21105c0040f100060b035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 558309631 1250 558308381 558308389
    0x2090415050f09040f08030c07020a080309241b10090803010e0c1c0e070e01080109050613030e010503090307080d1b140301060c031707050406120606080105010c11 72
    0x21900e0649601003511909000c18091800c900e80e0459010b00085070911000c1800c0400e0740c1402d55010002d19a2aa00e4442040642c040d0500c0290000100000821200c2c0e01102802c0702c0ca905564202045880b524025000d41842d03082a20104c010060740014001105000c1840e40d40c020484190700304541c84081114070301762003a15450004001030100c0d00308000c00c981c018514900c843e041010300302511504003082d188110f00c095031303142070081501040c0001401032005c0141d0141540e9640220307800f03071513a000111840d009110005824a0f55114001000c0d80c141d5150110114050011755550380041e00303103200d5200030f100381d0000910800050040c02c254900214545030151040c0c100301c18521481401e100d165131240d0700511080c0262070440f1480c0c07030282041c0e040c80c02c040c0c4543c0607410541041b0a180d004108040b40c000c4000c2046419a903202800868100001c40c02c4502e1070103140c0000c0c03044c1004102d02c5d0311414801c0c09a50103450300401030306400c4001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 558310881 1250 558309631 558309641
    0x71b260c160609090207050303010b030a090b09010c030f05190c1407030c1122020f040803070c030210020304030503040e0a02090319030f0c0c090513020910030507270506010201020904 81
    0x1054040d260781d1040c01800c0d40000103000810383c508095081c500196100341d180e00050048000c59440800000c0e1780440e185c100c14891a040b08000301281001a401406005900b0a0102007810b00043e04c20141451252034425905120000c00580e421510040509051120401000306c80d0040e038800c1070300000100b091600c2600c0700c0ba80144940f515040100c40380c803a1910903c2c1100001c0c82c1540000351032407145544c26070050361005c86090100700d41c000c940010620307200114041c030401c071402105400303483c02201e50101e40c442d6184207e0b0b0303d200358000103000740c0040c001000780444241c1107980007891190f0150038104c0e00320102e4905039041c00e909005d020f05108074414180c209946141c21641860900401c0000e515207829480d03061007201d440c035540d900000d0340c0d41390700c80c0c03461150b950090a28015003000070714407070300080c140016105030091044c00038411400f1001c824801641c1c01c4040940c0345140c00b220010400144603605654081182d664541ea65204d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 558312131 1250 558310881 558310903
    0x6230c0714130227153001051f031b0c110102030901020304061d1207030605090307120c050f030c03180301111c0204031a071b260c 58
    0x1100c281c0103110041020204405019a80c01403040011080e111a00710700048580c89240c070328200080c502c004907188500841c00e020328503902041c51107041a060f000700400d000c1880001c10348080c0d034455250780380800c0c0700380c0e54030100380745071640850988003041200c00d116041c0010054072600028541756444002180091032144d041c404200e070080c4204801c0e4802c2c4021030400400200103503913882640a68000e1001b030540c0d101c144040350a403241c0d9100050401d05a030203a001145946400300e02086920f01e04003400501c4486000042c0c4854941202c91610050301507101541c03001c2c40c2110030380d60ba02800001a40c440410801003011804050082d90340b1441082101030f91024004c0051099040141d03040c0c0760904e50381520400141180242610040800064020f100b15400285041085002054a00400c1c520113200c0c80ca507032202c0c01c41c032403c4040c6548100b01310500070501da0b28441c4ca051210394039002d00341c000c0346200007980b0301042e0b0180c0314500050b1401e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 558313381 1250 558312131 558312149
    0x3070815130b0103060e100621060605030d05070c0603050705040e07020c030627120a210c03020310050f090a0506010507061803090f0602150417070506150a06230c07 73
    0x100e400c6c1d0035003000b00e80b81840d180f00d02008030781e0801500f80c4841c00c24a44020402d15408109428001558001402400002c0444500090100d0042c003242c100b1401038500700e041017400070706107010380501e0744510f96139500e02d072600b8100302c10b115540c84054600000c62084840305411a281082128021480684030343c40882d2803074540043c188442c006004250444294910303e080001e0944800315894104034020400400301c10b04100b40300e4200140311824035034a154259015030043d8099102c41000380f03100c60316442442824446803030202d400c034000c000010a113a00d00e500454200d44d0514016103040469222241540c1d100654540c1210f00d5031a40f104041e00132034000c008043c881501101203240240107911510994586101e20402c040003404101125984800d24402d940c501c40e206c03085c1c1d04000d41d413148121a000c0210b0711145507100341c0e141410b800710888050707692310b0640308400740310202c805518101c60045004c0922240d240c5d10018800f01c2d0190030102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 558314631 1250 558313381 558313391
    0x20f0c0d27030f0b0604090b0705040806010501091206331d090607030506010e060304120806151c1b0804030215040f02010c140f07080c03070815130b010306 69
    0x20040080019031801e000c401c141840e6030030000280c5280074618025000202c1c440c0c16a41d07600442d000e82640f210040031b591207202001000740d08080944140d0b161074080700c0903aa01c4d2001074400c40751a0280402c01d05c0c507084030400064140e0854455000341d1540701d090300c0d13a01e03008017219641d500d0301c0440203048110b042c003030701d04031000745d03c103421480780903845908001140355117800340500860109501e480001d43e0a13405080364240082010388515681d1425080c100e0300540400c409100107a1040c0124030940b500c03c440a95044d1804070052a1400104d2880322810300000440000743e00c40188902001e98002543e4114029498902c05450140740090518040c0002414081c43e02e601b0b00c00801e41048907400100c0d420f0074103034080380040c10410116400700d5542034142c131445c000a5124800803401500321240900bc0718144e10148e01050b45601440c000d204c2154049040c030440030588021071a00500341605880c0c08070f4030380d00c03408000c202c242c2054402079154 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 558315881 1250 558314631 558314657
    0x503100209030114010e0402120c15121005031b0a121202070b0310050f040e0a03020d020d020303040b070513120c050901090e0c0103020c01060915032a0603020f0c0d 73
    0x1e0055165014024a00d502d1560400070741d2402060081c0c4060b0113048000d41274601030300204001071241000030800410008102d00e1600e007a4420440c00700c01d04a41c0020a85100700521507105075038006001e01248103580c0324a900c20000c01400c26030100b074230000001c02180208408025030301401e051209101c520001920308155580905c550550400800105a550b1404042900e600311661100c40c815a00014050038121103464048d00814101d1410190006500240090541c00361100c04188607001c2e6101d01003207901400c03400c1010000741d002485100148800a480030440c0001501d4860350743d442c20703800404440c0c07001ca5540030b1143e850b00e216003d00509400a0500130a400f250385140c446e140700b40014107054011501c0c0424503800c1d00100090301a4000800c118402120b03100c82d1100ba0348010380e15840d02c0ca03c0c20100b1242c2c0840306468002d204401d8012034135080088009501800c070310402584240304c1e4043c0c6450500100404410b82d580300b50011002c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 558317131 1250 558315881 558315883
    0x90b0c0f01060b07050703030302030a0245010507110102070b0d240305030d0b06160803151c0b0a09060e010e0705011b0303050c12091e0111040302120106050310020903 74
    0x94000410b036040a004c004001500020f200f02940e50510380541c030303600c884c84020064080c000036040e0003542901c8207402300c0b041c010703d201c10280240c107040c80340d4a05540385e4101c4081a2116000075010048680030270707280444080301e05018412545407681d55170f0b07112100e8110101102c645a11140d0017130100a11035484014602075072aa08903561030f682d03078140e491148400484e24203407200884011669007105845ca03030410001207620460251801084540c401c9070800032414040000003070714200080d2901c981200201d01c965041800e80351101c2c0010020300002000d901c555038000016081d0080e00c64403007401001140500c3e8014200e42409540d0b04080d0400864070080d2040550049030aa001a09401d0000b81ca0311041024285403080d04c0982280503511000e200204600240303400074000d031045d40e84103440740c000c1c2030b46c241c1c0c2e041c00c03080c100c0410a00050000d45000c80d0f004113841006800002d0459407803000c130b4204150742c809007051903408107110400d400c2c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 558318381 1250 558317131 558317141
    0x807140a0b060316170106030516210206090d06090f03030c0f080c03060607051504030207050111060906040b1e090708070e060603181510030606150f0f090b0c0f01 72
    0x400c0b00503010344c81440248104100c12841104140600c1400703a022200081d0b00c00c1000c0e58001c801d80f4408480040136014011a81c400d4149180410103000c0703103006017000c10109250f0042010b4900b00b0800200012000044415607410760344000400000e40b0382501c0769034291007a10003103900303044000098040c2c0118180c04082c0302d40c01c000c1201c00907001e000c40707a010504644503610743e85182445881e200e003811000c0c00d00345000042c0000e054002548000304c49090760794900c03a54501c0d003100d0b21440b0558081d2680ea12076070119002031a241111580300f11405148682c019010584000729082520030a6142d000300d0400c2c082c1d00401e00540c4050061300c4040307a1035040c108003180301880028041d91811004030141035541e00b003400000480421480ca5044c2810b08401c0340360300c54290712048960a190a8002411901c400c1c4245031003840c40c0c07500c042405121406490f0305084080300320400c810030300d000c108204802c001e0170001c05000c004203072180340c01c4d000c0e9007100c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 558319631 1250 558318381 558318391
    0x8190c211716081609031e0b0901060524040603091a041a1303090b0a0908030307031b0e060702040b0a050406170c03010615031e0c050d150506160807140a0b 69
    0x1840034001a156945c01c141c548003200d602080b2140c803880d46002c0c0580c4c074011030000402d030008034424030501d074405400c45010740d10210f4a10094401241c2c2002a4a204081030520030300e042c0810000706000c0e5001a10040c0a2500c0c903080d081803e200710014101290100c500009200380c005054100c441c45551041c90804040455000340d1409072000c2140d2083d0b8102c40b000103500f03403250744114818402040000103d903180d0503c5c80c1d01601400550072190429450001510702c00b901c104000d00b4080c0001c0d04544c60075501c0e1302444080c013a880c007490b4004840603000111604c1d580f05650040c6881c2c101e00c50707071003110781d20a41424404110584280e040420500190300d1080005c0c0504c540360900291201d1583c0394450007403040c5000c180f41070700e0410000d40c010341100051802d440001020003080803180035485141a09004094110500b40401c00108216481070b034a100d00401006081840c0d07036175140401900c80104c0120f581240c0760060411444108040d041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 558320881 1250 558319631 558319651
    0x190c03110a031a01090b07081b01050103051b06041d07021f0903090b0f040e07030b030114010e1006050a0507050f010c050909090a0515130f08190c21171608 69
    0x81807a085011001e400b404601a12a8800045001c8076a5a00c9d1031503c00c02d03c01c10080c042583e4a0034000e03110a800800c10781c80042c91300c0c0484091910208031001d4038152004011424958440c60f80000401842e8006511801003403048900b021040c4140038a015240860300440c5440d0080001c40c069120030120751050245124080360041a1000da40300114041c840759600d10049002c0c0440104054141d481e081c0c842403200c910300c02c458140c4100340a101a640c5442058610314040f83c400c2c03100040041c0207248415105100070031055000784102d803e482480214142155409a200c001054001441040b142864036003281d100710b14501030101002691a13480c0c40340d80000c409810700d0101c05c0001c180060841004130a035410050804880100d40743c00c1000d07a11200c0e1400038021020000d41e006886000405111640002124112242c8160202e907001480b9484c1c0180b02d144614071194040d801811803150031805100328a07406400c10240211102400ba00383c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 558322131 1250 558320881 558320897
    0x6050405090a0902010c0f05010605090c0c060105060a021e0a12020a05060a0b0d0614100504060b19030605060c01020706150b18040b2d0306190c03110a031a01 70
    0x5190388141c50140e12540701c04011070410628030041303030a900e1200c40102403031501e500420904c00154400c00075990140c410240c40e8651260583e40360184181c41200c40d841302c0014416820003502030705050704980100c84c1c070100084181504d01d06602c00410007644129002014007070040800e1010740c001c1c1c0058010090703951a03541d22444010011500741751100340c10440745d240d43c0344149429810110810401100620441c1d20b2001521a0b0712682d80d01c3c2000b051078030b414401c0a00311010041424540a0960844080d03d40070218050a069071400300203815203980000b45400244000010f0361500300703180c074000326003580e10b51f0301d4169600c803410700000122400f11400c81c900c405542403400d441400140c05440701d040303030640202c44e1003245103a58030b810401e9524904030f0f40e24404c00c0d5030310300309065071510700301d6143c00a0010b0243c0080750900503070010307a1410051030049085000e0700307880b1070240d01c800c0981d070011350303240c09180f414502d4582c500e07500c00c024030380a19 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 558323381 1250 558322131 558322139
    0x12220b0705100b03030f0c1e06070c0624030c09061508010612060324050a020708190c0507121a06012c12010203010510030506030303010e2e0f060504 66
    0x42e4800841000894960b0b9a0b00074600396079007002981e084803540c0b540c00c0c0daa0348040c4510354035031100c1811010202007880550108a2021036524031400d40756a40e00622485621408081c0a44108140d044003c2034012611002252000e00195014004c0444e00714600b100c0c2608a501d142e03c08003c4400c21184c1c0c6601701d038071901041c115401c030701c0c02d50000c249801d5100004c0069500040041c2d00104120f0b41c583c0350114602044002d0b060704000310b54440c204441680701310f400017050b8100402452010703010b2444200724292040c6440301400b400d03a41d0f00d81c500f0043e5041071021103c03054400041000c148a201041d00d850b4242c03400030300b03140c00040c202d2521a48044070300c000000035041c07940500700040a84400080c82d03289444405e82d0618001e61082c000c550240c40000c910002160080c0500b50188801400541ca140e10b00000344a510740040c1c1419032401d81e503920f041c06c0006285030100741c103808802c0301d00000e1400703504d0700f82d002096028206111040c44200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 558324631 1250 558323381 558323383
    0x30d03021b0a0f351b010c1206141003020714100504060506120a03050c030f0403080a031407050301030b0606041502060105091e0c03130507180b0607050303130512220b0705 76
    0x84c020141d20700480d00d03601c4041895481081d0080b0f28555503203010140d45115a0100a4260400c0c9030302d010005281c851460302d002a400080700c035040010303c070490200b02c9c0320764000d220b01405850042d20740c41d231160728281086810351010040945032014041880524802c2c0c0f42c02c01c5044a401c42d140030011032403a102c8000c840d020f000d02001140d44c41a450003031040f15002008504a1a9101d4036441c107142c0710780000d010400080d1034090f10740d401d08031043c140ca02804071a164241035031310310380c0c070301c1107401008010a070441800e02c40041c058205040700107075060103801801e2198103003024007108907c0180130b0310b5026521901c007400f40780002d451a41002010141366542c0e03480c0d007007030140c0d040c4007200140a4403d8040014040e4000d0002c40d04001e56101e00380f154009040801545025000c03002d0180d820800218a01d016500d250b00c01e860f2244094801c86c0140e000080c0d11a04841c20320010050b0506c4c0802c072010910301a5005010b400c1303000ca00b02151600c4035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 558325881 1250 558324631 558324713
    0x1805040b07080702240a0e0105011a16151a010e0d0318030209010b03010e0f0115080403030b091806010801090c0e070507020402040f06020f010b030d03021b0a0f 71
    0x40010300c504440803a110704e04c00e201c09140c03001c44a40f0361011042c000003101c0b500c00c04980041d82c1d1490446510009241809081e04032054002d00c0135120707050b0a29640140e003c180c91000303500c480001d400004416a41c410103c805410000a04104c00712448600e501c2d00f4109a040150302103010303907103175100c9400034001601443c0c81580d121174250820703a03558007608083c0d44180301000005141102030000d605a440450010030a900c5a81521045c10420b006200c070b500e045c0c403200c43c6014403580000f40d10500902e00451030103041d002040524906989900381002d280703c0002150408010a07401400c5040080100303194070b440b15014010280107901b510b001903004101c6252013001510344098005104550312030366403440c4146007205100d440003500400c1c41c200415201071080c0c5804040260291009040c0b02d4022002544121044200d04102d01c8038802524010810351240901c94110b2450b60b08007801c000050350188003d803065114000c4e07000400390702a40c0d0b5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 558327131 1250 558325881 558325891
    0x90311030f071a0d050901021b1903051c05040804050f010224040507080d020109020a050108040b0129040308030609010b03011203122a0806190e0c090907020105011805040b 76
    0x41e0400181ca0b2074070041c0d0074841d10b0321380640700d401d04003405152a01903000700440004110604a6981c0500515445007145a0094058100e40c4100000710340144002d003021740d207800700c04600301113040e808000c880701030314151024032020900340594200f00501c0490b9400900050820b00345940da403080030145500d0300c45018100002040400130100302d2030340600240b1094490300081108000d0080c20316840691041104010000d80b65000d070303440c1c50195412943e0800c6a03801d1148408040c0030000c4d03400c098038401400f40304812142d02c0900083e600c03401c0c0d22556410101d0820409103410b8201040742441080104601c003480200c1008817540f6060030861500c540100900500c0903001c0ba00c20b0f001110340c041001c19661202040100498a80185640ba010244401401d1407494600c411400e444180604e0300e0f05210203600c106124203c80c82c140c2100003188207110180c03001e00250707455200610044007a00c240e400300400340c1c070041210b490a0b888500b421000941 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 558328381 1250 558327131 558327149
    0xd050c120c030a0f0f051b0f060f1206120304030c080714130c020c06071208150a0306050c071205040602010e0c1305130204020a120e030403030801060f050c0607090311030f07 77
    0x113426420014043d181140ca40d4203d4190707009400041d0b20940303403e0503025901e2081c0885c05a1038032030710b01101650408010b0700783c40c1c0d0502c052100c114550090203086550f21140100910002da00d0401c0180702941c800d01480160619261482d0329100c1e4a0f04031104201c8034440c1d94000361500c0d0ba480d000340b500d900010450300c140031001d030f041241001680e504a000028940f003400a008240c000007852070307031041820350311001c0746d496400060401c03641c4050055000c02c00b04816400040e00704108007102071500802d0343c0c030580f00000020a00c8081030700420308001d1a9020720802055503c5440549000c0300e07000d001031641c03210741c3c500224199403038001c1022201c0c510a0ba640c4140e02030700443d542c500c410707005440301c0410a0f0400c4068240490440e8014010056608030f0307a00d03031205042c590a04505076010f4002d803802c001000420700c00e55429000420a41c0e0190440d03444007071000b81141000498280126180c030701950003080b6841c40c80c0e500094800c21244010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 558329631 1250 558328381 558328403
    0x7020c03102703230a1b021c05010204120506010e250f020c121b040b030307080f0c070e1803030f010e090106050d0501051f031e110d050c120c030a 65
    0x1140130303902d046408000c491001002c40d582615081600000d04440b03066869805280000300381001324410714500003500f0840091200c051400c01304d2960391294132035400541007944600c0c40e200c900c2c0b213451054499602c1240104064060200115001481d445526001561006140300c4000381c5800d030380d042207540070820503201c0c03082c00303113460020000b00080e4221019015a550b102a6426803008850030842d070b2446610f000c1c80364010744003001e8095414001142c42d100038641004003031440300e0401700500d011440051200c800608590302002c1c4c540c2c144115103440b00c0c0010308030311070680d0040062005c02c0405d25003c1d030449104c0c0900928940e00d00591502501c8a603120541020307003803030102c00300311040d048a4441c18907901c10300d00112811003001c1900d0603610000e4644114501211003000302035440c009040d01400250704100034a00209042c28294881950140c002680094403840c2c40395030284160a880020401c0043d1480000d8460b03181315402400d0a0b124 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 558330881 1250 558329631 558329633
    0x10e04020910051f02060702030406020c0613030f060c0e2e020f010204031110090605040905040816060e010b01030b010e010c0203010908030106080709060503010b04050105160b07020c031027 84
    0x30142c1100500350282040703801400781d009036034044c812401c0050160142c1e80000c0d0515100005543c101d606075401000f6500d011818000d882d03111f04100c00c844404810048040344000d000011703882c0c40ba481c00070b80b925603604014038410842c2019840303450310b003000d003848003800d09500200d41000b0700400c81e602e01e0244141c0c9400c080a02c000701c65400440c00100f030200c030820780045e4420540d0001c0c081c416440c0c04980407400360154401041081c0400c0c04990a00d6000c241c1c0244034100240c03600304906079090000300d803810100e0305561a10595000e02800380504084e1901c01c1c2420b0081804500000e03101c070a03400078039410400002d50020566400750004590b840c0c010700407603a2542c66002c010807840d81114540007080c0b19000c0012180c0c803910441e4101c1c2c29250b00c0d41c1c10a41402c00448141c0e004030ba2410b104c00008150310046803405170040d02544042c0c000700314581c000d0040c1800c0408071407080382503a1a14080030310452061400408949055061075010407103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 558332131 1250 558330881 558330901
    0x30f060d05060903090a0806091213030f11030d0305151e0d0606031e0c060c111201200c0604020423041a0121111302070b1806010e040209 61
    0x1221400303020340c481d02c420f10544500100082c40c1c83c0009460204c002034407000742c942d0f40c950654034850b15600910518030404032000c040c01c40010800d00301035030079540342c0311004050908030f41506c2c90a02d100300e5403524a001c22050620a601c0d0274140500d1038403000d090070a041111a9602407030201139090a00c0340c1030040c6020280c3d00034140c40d1860042d043c500014035040c041225100f1500c062841700d40d10034820041901e92082005500c01d0400504540c84840030000322800b080940a003101a600e40208d01b541150180002480900d4800c2d00c1141041c0c5141030000c004ac1084030002e8201b02185880d0b0154054070089420307207125226280e0020008083c6040c0344500090108120321208007a6620101e41008030342c590301c50281e816000704585840c03000500108403d800150412121400040d0080081c0c002c1d14119010000345d0b4401c1d20200c41c0070703020358100003006501002d4024100d1001004000ca5030410181c0790f624440a440644580381000c001040400c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 558333381 1250 558332131 558332149
    0xf0a030f090e0114030d05120121140c040b100e04180503071202010f0b0d020111070f0b1e0705070b1c0e03030403030b030c062b110a030609050c030f06 67
    0x42e0454401e603075920b140c618030486528441d01c0380c0155816003141034401c2d0151403200354a001000b92a0b440c000d07040c2c0c402c481c501100da06901c680c01c002c001103042800003940300c69688002d8980007031050b00b044125511410030030310860000c86201c4038903074082c00030342900d001518002411407003c880f2176141d0103034443c0100648800200c240070050559189a42603070103400034000e508140101e1401c0c0c80700c040e1944d03003200203c1e24540140d803203654a80d810042d0032042c1d55800b40c8500118507002c40e10f401040c0210000606000c401c036044600600722554140500d04110b010754541d9150f04c4988284141c12a020a03842c02a800041800c0e070244d80485042098440304200c003910798104035001d0700400e00d01400c030b100f2414086480c110545000381000d182c140031100f407500004203a00c1200c001c2001c4410400501d05500ca002c11855560028a4503a001110000c1c1903401d01d070030015282d400d00c024000031000c160142d9401007142c100d500724640d41c400108110070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 558334631 1250 558333381 558333389
    0xd0f0e030c120d08010506040b070605040317090a02011202180d08040b0304150e01060602060601141207080f01080c03030304140a120909060603051b130305060c030f01080f0a030f09 80
    0x5400e802c512502e010700007a8401d41c0d030846448042141c3c6c1e170f58040044500a522910411900c204404000907280d544a0b96000e44281005684200b0b04280c080040d14125141101a444034000e81c05568001e4500f910b8503040140c2540f1f044421403000680707070402c2e02d0190003906080c1840d0100800710741550064015031400c80c0d100d180034140840ca807820b40915484070361401e4400107000506009081c2503410301c4d001891a921107400440300e040384500320083c001d0040c0200400c4144203041c050084651343d8802c4124240550815544241a800000703140d1110120f90fa02d52804415658803d400101030402e4504203c45141801c1e410b0744024001d15006180380407164001c44803030241c86040300108170041d1148010340c2252400e940115010840c9000355011150640c0182303201591448071174129552540d8480c5071280c180c9100c25112404000c1180b00c60450002c00d00402c8680020601450303460141500c0c0c1400420241c104608500844071050180106170010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 558335881 1250 558334631 558334639
    0xa0c0e0c070f050105072c090604020906030a09120f020a17070b0a050109060b07050613020609090708072c011d06040603060806090a150e0a0f0605070305090d0f0e030c 74
    0x8140b83c070b04a4001d04080762110040b5401e145030030b80c014410318090741744051041140e4046024481081521200284800d50090f020040c4a2141e12000041c5000f450f040c40041481220b500c0c0c2108e94111800342c84080000e0074103501c92559001500780262034010403401000a01c1220461891048480141007204510207209004103950721042c100d8120910801c600307900c5080541071131040c80e002a0860b4059004181c80040b030b150040011031008040d5441d08403400c010403030b241130450310640840c106030200140b40c1d80000341f0102c0c01c100c906142003070750f48148406908414070f00c401c504000f031001403500481d02102d1103207503050004211680b629500c071801400b92000d40500300340760040c1c41c04110460300025245010726441505002c0320120417032120014030844100d00014481c0c0f00c4100049070504019540c21030252001281600d0324400180c203590002d0002070700c541c004459403071709540c4803003081c00ca03c80500c0c000f0112185400041c1ca04641c0314540e07640 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 558337131 1250 558335881 558335903
    0x1407110c040914070e270a0b0f0f0603010204061b15060f03030914060a21020f030a0c0905010f0c0203070e0901051e0c0904020a180b03010f05030a0c0e0c07 69
    0x30320209481880a000b00402169813413a10303818038929540d4281c1d00c00521501800c4000302c10101e001c1e103031122034080300c12a200c4005540710303d10307000010f075408100b50148100b8003120700c0350340703240fa684040290b0003545440d01c0c0c542c006001c0e40010400d00441c5003002c00103420412403003041c00b00070003210024804c103078031560010301200f02d92004802040003c40006092403080480f0314000c00c0040046013010000c44007503440310521005124003442541001c1034584a81c400303040c51070040401c01d9128502514101d048031070507000c0e10188000844208001c2e0707030018024441c0d084928250440d070901c2d00c0801c2c0303466126004048009440380400092100540c04070784110800d0031a0030488070100c0c0d040840050030350f40c00e400d541c0200301301d00c4036007005d400403e64404540341c09404210380c18076607030711005181c210b491074810000042148490114180c000303808200c1c098480000142e660703210711007151040446d2890090002001c40000c013044c2c40ba040e4210a034514 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 558338381 1250 558337131 558337133
    0x150203090c04060f120f15060603061e050111031c09021009120206180915040510141002010e0d110610030f060f0b0d050c040507031407110c0409 64
    0x1941085910403298469100340300c80e2032600e0b001d040100c07428002550000b0703052115264a041d1010300603108810f003a0f800d41e0010b0580d1b08052074442545100250690810230000e0940340756511a08101c840f120000d410080c102e8280000c8a0007400c10040031303800c9110302c508600515a8869000d46079000880f03008959402c80d400030ba100b01c441c50059880603034142c40c1d40150f4091074807074444141512005040100090800034400c00081003850310000c0041c4004804969100030440d0310082c0c0140350825010303a81e00080030800d00745001d4240007404a400683c81e200d00c0c07250310564030142003603000307600014048011a0689461201c5800c01400f12407600041942d60301c07a641c0051142107801079508141c07a03006503805117045058480130094a40c040d000b451003a500d0360f94050300e03610000c0da4000709119030040c003000214201003001b02d94005180b00705250408a03c038107501c11680705161b20030000c3c10004000c00c5d00e140014507001800f4a1076030050b140020401c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 558339631 1250 558338381 558338423
    0x60b0a09060e1803041202010215075d0204060c050609060f131103070603060602010f0c170408090a03060203040506070c03020c010e270615070b1302010309 69
    0x64251102032070b240c262a10343d08651079600044003098400c40e0010302080c40502181a2140203182c014412500342004030002800c200405403503203001b1920181c6030103092004900801c01d455420714000064589c0e18002c030802420000c0034503402d0740429200c50f00c0c00c0521410801c2d1101c0900b085445a85a49000c1d000136043c510658040c4a400000380c17000754000342c510310400340c42000051035217455a988400c9d480b10f89084842c41c110203a03084443d101040752100910702950b010800d43c0c40e10001a08580c0c8510711025030a042c0541016155003100e9000c3c84031684082200b410781e60360a0941450003042840359020780c501e1400030610629030050340c01180036105840d241d49600750306a59400d0004002001340e003007200360301b4466018440b01c88901002514600108140d101d0120007a240c5000702030042c5401028000d10381040c49074500c440725601812072030714004c0e4490001e03080c0000d180141c03810b110180001164071940004094640c4030800c030a01f6083e0507020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 558340881 1250 558339631 558339641
    0x10806041a06010509010c1e12200c010804050709061401121a210a05010f0606210c03020c19121d0f031f0b010e0109030308060d060b0a09 61
    0x192004008009614580c1038075608850054005844551411208030010f68019640000071f072084000848450807105c080a5050401481440c0c3c0e524035040a1034060700e03038500b004602c1402601c42d440c01d41900b80c009101380641809082c0100030356560724200f403510081da0031144c0c0840c00e00d0070010300300c0200008201044400d889410000c00d01500480807035002d40d0340a4020fa886141d0035181381820218000421110919035030840500f04c6114506580354400b1203040e950350079169502c1e106c07440f07040c000e402d041c0340900704034107104d90250142c154400401c48180d031350300011802a001b50704603003600c41d03c4c2007a01c2400710700140848111409602c107803140082c0c101602c0c40c541c402c034002202c050214100316076110100081c800c032b10740400d8403d6094460301000d017440340701c0001001e280c1c02d00d6813008100500b180c3c0c00140500744119280e418409041024030000350130020080c1c0c89801500d000c1000300103410640e01400e0420b0300a07401c8042900041001c11181d040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 558342131 1250 558340881 558340883
    0xb01081f2c0d0f0516060b030309030106031112010b061c090c1e060201111e21090d0305040b070806150f0405091b0301033519020607090b0a0201020f0301080604 71
    0x15003007401d4400c46091340c1e18410052116003410b4051180030000d130781c5034821099000050112800e0450001c0440d08550700c9420546660303626440c05459460651b07243d5080410500080c480d000b4a04003080c030303a008514044e2240403406402400e030749045d60106288a030020250f5039059960500d0324040c88901000c0301c202c010b181c0c00491001c0c0140030700c01e03040805000301d51904454610b44460101c2c3d0600040c41c90500b000700c80a6007400c249044882c500c1070b11045201d0034078080c2107141106500700d04081c90304050822010510070351140fa40540241046070702d0313544040001c0d03090701c004035042c015208003060b01050703002301c03002a00640b4003d45250346c00d911840c480c0540d020204215202040082006000041c0c28a00d40700404030105800f64030565074502c4601c081c10300d100e07405203904020584442d211407580c0016500700060025002c1d0f0308004e035000b051122540076000c11007170b00040b884030481c0300b5070458542842605005440c0c0d40c4404982d0349540c001d440c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 558343381 1250 558342131 558342137
    0x16140a02060d0b01031b020d11010b030304090e060a090206040311131505010219020607060e0a150213050103020c1005060111060124050a0f080703090b070801030b01081f2c0d 77
    0x41c42c40d1489608441400d400900350004c068080c6203008c1201d031a0000143c0c40703c99501c1303044120254800700060805019800408100e00c014400128a0a10001c003d13094090900000d04c2c05138a403d0100c8040e070741c00c520800c0100d0070280100d0359410080d20142009403500724510f2002c00d5298040084d100d09034250341c00e1080c51002c40401410300704010f54812420405030000508941c03020406111701001c1d58880c030344e43c0c2c481300c5590544001070001c10703030001b074800c9610041d610307288060442400c04505083c050300e5000c1d0340d103074081409a0000d960741c0100700c06d46c2c090301d91020200c5d070350422a80190b0b11840102a00719000c5020142c9400705140b0500396030048094404903000765a8400701a45038081c01c4480100c007408800c2815603c403011004200e444903a584146801e454150081d4135500e0883e40080050b407080003150400f2120424095003a007913001082c6180501181d0000c8803041c151900356000c4014400d00c0e2450600c0d00700c1800030400f060300e000742c0d031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 558344631 1250 558343381 558343391
    0xf1c14061501080c0d15060206160306080c040504020301060915050418050d0c020a1203170105042003190e06090f1b0d0512030c0408070b16140a02060d0b0103 70
    0x101c4141040100e06049030124a45200280840b1903c2c0c014000c01003002e400401c0b9110707003100918408540750070180041c4c1114003040110081051107031003144151408101040c903105050b504c03803c40c040c0c81d522650b103c070003240c103640d401d402180181012050420040e90030032408014010766104403409141030200d00156421400d140ea03401070b800601500c451a1181c00445185092140499205a1510703011684c40807407030040031068400e803194046080c511140c03030404101607101612a504004904d078103880c4220145a0003c5004510f136180c0d11603142903a60390080700100d6070a90f18004014035030f0074000072001d014000000a446100404a03029621094134034191303201034040319017100b6507003010344100303046a00940a4980010001c0d90060095106691580c1402d801080900c10303100184100401041c0c451030541c42d01e03400074107140c52407000e942c0180000c5155134400f540c42c8024000d001e003155005241c2e941c1c4a008240240c02003240701c1c4400c0c0064642 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 558345881 1250 558344631 558344641
    0x204120204060510140304050106210317040210030c1e05030105092412100e010e0705090f060f030313061d0405060f0631031716020f1c1406 62
    0x10b1004c0411040d59601c4074401c0c00140c154a01d42e1024008840ca9903030303500000bc901191041101800c040000510b0302006e0380d041c010148501550b809a02e901e065041c040140d03501864030711101d0301350401284207014903000b0b46003565150003940104010600042c41c10307030b01c880214140c440c216084805a190503917400c081203210440e43d01004605100004e443c03805198211854103214104c0d0302103141e03154041300781c40d4000320030300050b919085000c10780c40c8103100f440060013041da41100035282c04101090040320140401d0b020fa016045800c2d89034a0030300031a26100028005208002d036540b000500c14001341c0103461050f4515407100140d0301e8076015150056200501c1844004441010407556511080c409126140f0382000c00e241070749000300c18000000c2d00c03401c1681007403560400c002e4501e50980c8404100c1170800030b01da007089211500340c91040d01178910f1110381d80c2c01e00c042544a208072101840d009005c8021204006655103100c1031400071400b503480c00d440b8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 558347131 1250 558345881 558345889
    0x1030b07051903050a0605120d080901020a1b020d05060906071b0b0a0b011b140606030a0f030c030215011403070e061e0f0d050a030912080406030c02010b0402041202040605 76
    0x924040d00030410504202c0140182c442d81203250803940c150000241155600e001400e8044c1005454041d034200c02d4194007640d401141041c0e001601c90f000358500514004010420b401911410340740280f00d40c09202907440d820590020154810b04550311420040c84503070744c500c4129149000102d90f104003070319803c103d0701c04403203d0303910105808403600c0b01d040010242c0b440020003030401c510074025025200300d103500e01c6c4030240500410440c442064626030b0a140b002040036000e9804410580d002030704180d803111625030140743c010203000461030100c2c100911100d40d03001a5019000120f8030569440b844d00c14840201c044a00040c1e64000300c0c0107400302102c00e0f50340300c0041c0c141180c20340c80080101049100080441e00c0c402000c80000301618007880080e607007030380a58003640402d608507140c2005001c0007101e400160301c0b00e42d51400d161140307025140806490b2900c284041c2e000350403803259018010015511a40c549049403441050b9840580c461030a1420009803820 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 558348381 1250 558347131 558347137
    0x3060e0d0503161103130617010506030708090f01050414100e0304120602041502010b090901020306090c070203100c08070201230c0703090801020f04030c0e070206072007080601030b0705 82
    0xd12a16080e0943e0f82e01c2504074019414507408806100a07102c0c1c144240d8028002800c018106031401010b490a2090050000c078118a8400c0d100041c0001803015540d180140d0758460440d28100c2925526480d68a090480c80d1422503900d40c02d10342440704120f001102c5541c41700b0300c0030841c2c00302c4005510a5088d90040300d480c40b01c0380c1041000b800860084656110f24600a80b40585000d58400b4502c6030044100790260040c1d45d107400391800c5151600310503070000e002000a504600b00030300095107401c1c000d04800ca0003500081d84404544040c4041c0c0440d0032950010814051755510140007032500300c880c2e500651070004902424220301100400c058041c0c2c0042e100c80d80d8481d60500b080c1e114407000e60a020700694001a040030034001000100c90010803ea01d035861442d0450f60310302c5682000000380414003c009020b90300040b0340303911150500d800880040c0f00f8000540b11072982019040f41d014030303440840c00340c0c00000e0440c1280e1180501c60b0407030b40c0d040c2040303070b20740 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 558349631 1250 558348381 558348403
    0x100501030509060f07030c0504180507020c01110d0c0c1d01090507170112030507120903060b060a121e14060906090c04093c050f06180c0904140103060e 67
    0x3011401103840d0301c0c0302e0750101c402420242008d500d0540c641c0c08800c0300d0316038080c8508056440d0410007250b20b1303043c84441040813080c24a480041c10001c1000c3e11195442d030024100091041c00707206001240d11180002c08007c4040e4080c240f04000590302504240200d10415061002140d44507110b218600b21500b030300c038400c0417185d0078840145c120040f035540c2642000f505100c0e0340c000c21300036068806050065100c01c5111440d5190010079200414040c0380305560074010740e103415410019010006010310000142200310360142541940d030404e031034449929000220841c00c0c020b68120b8010721044424004503a100c10812a26444c1100e0314041c4850601042022180766004a0944c40c42c5030305400890002450310890940072003401c08240d0302000480c010341c40140f00b4150030210441c454041490802d000c2800e08440200c4869410f285000003901301260740d05507071542400500900104080d81100c0031142c1081c001503c0c0b00303250040b502e400740e074005a080703141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 558350881 1250 558349631 558349651
    0x6091003020a171501032423034b031312033c051908010b0307110c040203070c050d0302090d02090601030921030608010e0a12140310050103050906 65
    0x2584404c00110003030807401c0c09152000f074136280c0e510349400c02c1201e03401c043c3c032180301043c007142032170704440c0188110400c4203402500320070450881900e41c0c0b000700034140d0b19a024003000c80400c2001480d5120311100341c4c01c2c90b220300701c1141c000c02008002030008903400d59035a44082e8642c8044081e103010f0020080c0814403182064605541c1d1a09401c0441801c0800c5c4075034540441042408034400d00c0c450300000ca0003c0e40944803000c038001d1a8400c044c91410070001c2d03050503140b207990301c07010b0000e04c140180c000d01c03510111010015029124030240c030940d2681000305000d0306180b0000d800b11500c1c05440c140501e194070a109403654958010400000c0000d55003d00000700340181c80301e410152940c0103000814078041d0a047e6560501c400c00c10541c1001b10000d04440843d003010885905202010101c03c0c0001004c9400540000841540d280d03c3c2d0003e445e01564032502c1d80401d2004010824040b40030500d16044070000c2c0c0b010f000d29070f1582c2506840d080221818294 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 558352131 1250 558350881 558350911
    0x4050306040b13060603030e10020c09010506031305010e060711190609020a0e07120f0c1202030c0c0f1015120f050c1e0307170303010902030606091003020a17 70
    0x22440392140e043e003100100c21420401c0d031580d02c5040130346465400507404241481070242c4c1074241200000a400c0c0340e0305c0a040942c0840300001c0601e0010300c80d2901c60f680c04400300f011700301d00f800a888040d50040003046212403101416441e2042181d90f072002c1210403d40d10b085690120303008440000440c2950002041a910b4030000d01c0400c0c0c05031380140b000000841d5510410f4569405040d003610340c02c0102606840801c250341d182c00c2c0c1e04d28400d003402c0b441a031554118140c80ca0a802c1540050380300c1c6d4032240070350051f02070741000c9411072207540340c081445400825100c03101c4d2402a82480742d02d40e2441142400b036181d100d40600f50305400e402c2001f00300d100e08990b80c014803a4090b074035016071183c0029404600d9444043c0e155040d60300c035130503d180030400d440c0207101d24080c0381c140d017501201c40c0d41c036404144500d0084580010011b011541c030b1800311001000001c0548500080b0703500003c0013034114071000004100118022038008200100d50740c410102ca1851082c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 558353381 1250 558352131 558352133
    0x1e0c0a05150313050a02180a1d1f091e0b09010b060901180510090905060a030b07112d190804060e040204030204060806070f05030702060103320705150405030604 71
    0x3003169280c03c015a0580100209640142e0700c4400d43c50952800c2a601c04641c10800c2c0c0da40200d4490294282d00f40900100e0083c0c05100402d01d921541c00900d007542c4545d015031241000350041000040c400f511000300d48200c644451660350680340141d07442c3c1c6843c1d841200c40d40c2222040c107038495200074207000780d220541c030541c1400d40c3e07031600d03008215005a540c40423031003d4003440603400c045062038100384140041e80c401d45500c0081112428400d40c50340e01c4003110f4040c0a04000208680c003c008403545000b04402c1340ca8441c0a500c510741711100030038103800310420b51001d005c1401207030185404100b101c2c86416090360800d9415251600d0650255015281d04141e0b58205030203000000141e6298400c6100800ca1741b00502054507041034002e200800030040f09003070042c11300a11030000d60000781c03241503039030101480410f940b51040070326216004c04110b801401f2104259040303108041528012200151402c00d00100346041c0e000319401030307015203501680010000f074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 558354631 1250 558353381 558353401
    0x140a02070e040f06290103060f05060309070b0f03070f020606010210150f1409072d030902130f05010b0a27080a060209031b0906040e1e0c0a051503 65
    0x550803d228007034180200800fa80d40c02e0030341d01d0b2692600c00515032010040655030f9440d110080e80c1d103003486d0421150b8140340c00540d007280240102402084080001a900e41d01081442e01070a10045070544915036040d4110450340112000000640340000c00f520940c00003403018001c1c80c0580207444404003100b1040b0040c0b0440d5003103182072030880400518071310110b6240018100d012807190098120340103100d8008405056103041101c003203d45030304191200c20350342c501207500320303111940c9914004c01c40151800b0240a503120f0302005070b90ba88800c4a0380b04503036007940d094050010340e98a40e601041c07801000700311400700b0500d003200c68002568480d0f400f6442e00c180d0780801c18580300c1c403905280640d40701d804c0301c00c194005414000c03441e0801021081001c811142802c101c107040201c0c0440001400d8540103680b103090400c0c942500340300c20b050480740484101c40324041121006e640d0041410468050503200c00081041c0c14018405038018503d4045071b85542c5908103c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 558355881 1250 558354631 558354659
    0x1b05040e06130521030108120301050d0f021f080f0709050315100e0f1819030e013005010e0603151305060711060702010e07140409050304080d140a0207 67
    0x844090040391601c5500c0e8000080c2c0d4004c1c070042243e010b840b503042002540c07502034000b168407003813202030004103c0d56a4100c541e4540725441001c80b801407400f840894180e50402c20b1042d0032079240c102d004080c5a00c00786192040700c001d0780c82c2e0a1030300e44010640e1501c005000d45509600100b1250440038068280160041c0e00c1d1002c0004117555040c0c19407000d0419030301102d04010703410070b110070344920302d018410200080c4040c261040c1e042c14141c3c030140040c44000d090006c11512003003607078020f1030345540040181d04080300b8031502107580c0122101c0040c46000e880d02e400008100451100d4000303100707a6026006100e02007101d0021100820024098100c187c00030004c040015010302c04a80a414580c864442500c1d03010784440c2000d200424001c11a0314280780c0302001140040d82d035046504240c4031101010002000c58090001074030003800b10b20000400168142c0c00286500310009150303a86005c00800704400b000610500310300b83c0050b400400d040c84084404414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 558357131 1250 558355881 558355883
    0x53010e1b09040513020909010612060507030e0601140102010e03070c0915030512030f07050c2104170a06060b1c0b040b10032f030c0c07030804031b05040e0613 70
    0xd041c2001e84441c0041d00342c8070300f00d44810708240c01c0c0b070f400390840c140a048a40c020030914000e00a0504240d0942d8000305c20010191100d512600800c1e08903009030b00100394200a44107440d000d6865200a041001040c00200d0042d880c00024040661010058a5800354001e210120744d40c6424520300181c51041009001c0183c8610b001001039820445500c080001c000d06c0703500c914159484c820a544000c2058003404401c1140306203a000110301c117140420031030342c84004e20380084804440c9010326000240032822910510104900005818450b02e200700d00910040f40c44400303003030017801000200da00440059030440745001c619084041c2452001d000050780040e0b4000041c0000d00100d40c04010aa840c59090304101c0401e1060004500c001582d005048440313641d400c0c4c0744002000310a00340000325862521744800d2044074021500a080c850f1656120700744000011200c140d200100031580e0340000d054200b5004456442c050034000d4007855544070102d141c00306a00c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 558358381 1250 558357131 558357181
    0x41a1b04050d1b03110306010f050303070209220c0f080307020102030a030f0f05010323030c030a0c08090303040f1e0b09010c0204061707031406090a020153010e 71
    0x440c0640c201c0d0342003c020085009664610141d01d45d00300b41410840103820000014040c44070600c26a00c0c0002114811a4181c5910701c01da52155103202440400b910803600b0b100c18210302c031007070014403d00c03207040d112a4416040c9503503a03601d065589125090000f07002d0703003042c001006070034002d52050902c034100050100380000030401490445200340c05c1140c071410842c1c0f4030482c220146060200c2e40c600d0100441c6410111842c4075074900a040b0980f080103201c030589410050b03124252508000003508917500d4030b071141080c1c81d260100c2c0c01450311500c100100c1c11044d01e01a050344003121900c1982c01d2500b58224011a001050f008090740c20640716040040d0f503004200048282c2241e1002a101c014210700d00028200d0212400c603000368001d405001c0c0300080403030038452065090030711101201e2483d03004d4a0362200080901c80715901d441d104e19200c40030108002403040c0c101c04015000003807852600340341c102801000744480d1104001000141c40c116004004c2141c26 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 558359631 1250 558358381 558358403
    0xf32061c050c041e050a091e1e030305040314040b071103034308030f07120207051e0115090e0a020307080307021f1b02010e09041a1b04050d 62
    0x14041000c0d540a4807400300400845408071324040000d10810f504840d030b40f001800900400e403118602100d00100280f041844110a4020015245407101c1c000e4007250100e20744c0569424090002e0008550581c0460b40d01440640704011041c21102a1600d1034801400c00600340ca07a420380c0c11440b42c803e034241c07008200302003101e400f20b1105070008511036052003c51406042000b000b04c10110300103401814a8040310001d00312034252980004000030842141d91070100417244218a0007420244510000d82c0c0302c248031011070714130300340495910120364045043d00800d00700c40610710421b0040112a10a21041295812245440c10500b00301c0d4610700950b00002c2c204041d40d840101a5400010b11702c0842c18000c4003840e450f4001c20000390301111040700a06441d610800040d81c0e030a142d2001c0b821a802507894402d0224080c010100501d003030725016080c8444039007480c840114140004010328000f115600700c401180065908061400050242410301a4005c90382e48001d0307 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 558360881 1250 558359631 558359653
    0xa020a30211a0d061e060b04030206070c0506030a0c0f0e130c27051311030406022d03091002031005122b0905100903020d05010f32061c05 61
    0x80c400f0a07140502641c00040c0b01c685040642d81540b0000300c00d40c511a04001c0300304540c0440c54169421a60166143e9076100c50f58908011212081d40155900840110511140386403d034004602d02c90740d51906001c603080071000780c4406032000880d0b03500c0800c0018010b41020103802000c1b428009003000c12621006d20441c0c5400c0ac2074074200f03088400114800c000354035000c94000c46508000704100a1a0780c00c1e1030200080c40020400380800d500080e240180e0141d00700ba440680003081c0c6501a5141d18040c4050294401e80e81c02c840c9210380c58003001650028821a4017500e940000d00074618a030400740151012010010381640c0200d488000b01d810f4980c104148a03025a0500c0d40f900c022044080e18019043d00000c1c0262406450b8042c025000b20b1a54140c0350102c030001010789941c40c3c0b59000d81504e03040d40300e41d141011440c107403d2a081c16900020381880080b400804003480b45480a040d0444545a00241c081942c2c600b807004603482d02e82c5680a14150ba04131000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 558362131 1250 558360881 558360889
    0x1d01031e0c0b0a050904050c07050a0b15030a030807030c0801050609100c02090a0b0a120b07050c0a05011109120109020303030c03130b190c1704080a020a30211a 71
    0x840700f41030700825000281140c203440c0c18812183e01110b42c9000c10704101e030325211281c0d28810050000c200111050100e40200807198104880c0c25000701161600201850014502c0405a0703099000c41e00b0306c60001c45032800761003003c0c1030ba00c01405090030908000108040020403601040038007541c842410701680301c0c2445140701c0d07044142c003c5035507070b04c030703001e00031810619802034015083ca84060b0740064040080c07560400030502c0e1050710f03500d00020441c00c26051107002002503203084401e00c0c0903030302c200c041c000c00c1c02c080382c3d400313128000300300311500f07a4904420096068004100150302c043d60b44010396000703020300d9160030540300d6076a290b0071001402d40d0f203034001d04c25407940c1c00124130f0203008400d6840c1240c0fa0148040c07282d030603070519200014000400c6140c0c0800c071203054620030030020300080e400c0b607654941681405000c2801d803042d0007461003e01b44103408595114001d50650401e007200800180e04085036004e070b507005214501c2c00d40a405441e240c681d04d02d41da = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 558363381 1250 558362131 558362137
    0x30a021f2106060e030a0803060f060d1e1b0509150405030f0307021903120806060f130f06030b0a06141b060601021006060f030e01020409151d01031e0c0b 68
    0x10207010014009040242c0600040800000c1511035840f4400b483e0006444100741c9411a40070360318501c0307020f0b6040014283c0d0081072010060981742015141403e5804008940440c100c0c0108014030400303440e0002603002801e50344c1c00455801c00c003400c464100002c0300309101c00240302d1581401c2d02c40380081e050031076282d000210b41e40f011800200b503140407285000c01c1c4241c00500c1da100e030f16503070b00c580405044104800c2030106103000034541c1d49410f8101c9880e081c201808655404401420800401e0980107505001c0c0d9221000300b44280244200243c10400030701c2e14207402e00d000c0080341c1225030b01a465004800900030704028040e041c41e00e07101c0f1203059014180030300d401c030700080c54040b605900160700b5040040400005401c185c80c180344545a140104040c002d42011a01a21560344901c50103482d000c00c251181c0700b01c0101d10161070b031550380c051a0b1601d00d0781340080ca04013800050f00e4aa6804140740c0010920507404a105100c0c00c40400ba19580351407200140e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 558364631 1250 558363381 558363437
    0x50c03040308120703110304020d0605090f010c020d021002031b0304050109060c05070615050109060302090d120f0801150917190309360b0a0b0a05070b0105030a021f 73
    0x2070410244a00c1c141c0600421603041b10b0b49103803030300310300e066000545143c2d02e200e006400240c0d5500032032114030042c8641c2c00c0b854840d81c028010540c5040b0000e64905000c040100140551615004100618001c40b4000e03e44c00dd1580380201018062000725070001d442201d056503250350540014070b00c0d00035206000b400c0d8407213a895800b02c0c01e00009840008c0060401c00d00b98010600440c1e80000030740f41a10300c0c0d0f00e030050b142d505903004202c00c0c0b040030b04080e118140360440c22900580c41041c80c5540510382c1d072448500d9030384ac213640803140b02d614000c0010a0510f034060202409031040c0000030042d07030080324400f07800301708481c000304104002a000110111010300c6107031103c160003403245404034220715016074440003509140800c0e440c0d8040d003c1d140c031118203003035a80281c0003000e800002c0d14a40e407020302d81c0014149a0064904403140030040e0000103141c40c02082030002c0750b8020f8199010364407450207251842c01000c42c00c1c800d0100348220743c00d4060103103d00040d04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 558365881 1250 558364631 558364657
    0x12021903080a050114030718150b031f030c06081b0c0a03110d050d05060a05060a050a09050a0b1903020c010c050705060901091a15040515100f090303050c03040308 72
    0x203810320ba030740c92007601c905800c015041414403084034520f8030001511000c68a81107280500220910f0205020b001c400101801c010703d001004505941d85c100114042c00c10340c4ca090b950b891000f0080c01d942c00041c40044c02d88000047e00300417182c003d102c002e40c048071700c014100c0c03003101c8560054642e800007060280701e035204104100400d604101560450342c8254010b28000c0fa60740c0c8020861b200c5e9040741101030751600e0101d619030b1242081c1e8005001c0003404c007500d544030070304003d001d0303005102c02400003804000002428100a1602c0054600302d0309228600207030b04c1d21120020300d05002c400105503007008070440b140002e200f030f4100851660b03909581d07000281003070741c5040c1d13002e440c120b042e0345413615003030000e078820b410200002d484a500c000140e0310721400c0e0b20220110700d80350340c12a00300420001c1c0341244010300b00c06903408940700700701500c01d400211074003001c070701c00040881c20313142060010034051009440749003811070849103400d0701c0b59103040198014400c52810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 558367131 1250 558365881 558365897
    0x2003090c21070b160803010803030f0a05010b04090e1617060117060711160e0a0c090612020c0a140102030103030206070f0e04050a0f060f0f120f12021903 68
    0x14a241240d0060900d1032038001d0300e410720801d00c503040c0e220035080c4501d1031082d00004122443c900320070440e0458a0304004015103a681d104100c07500c070740c4103d501d02d01c61001c0744001101c01d501d501c00c40d4180c5030a0f02c85103051a0500340108010b0001e03010114040c8142441c5401c584050442580985600983d058451311001e06881c94114181c01a0502d541401c0c200c0001e808000ba42943c004002e180c4182c280c040c42c0031a0f03041100940900c1d0060100c2000810415002211103015410482c020441880c81d5801110030007080e0041c040010f590f075002040641d0143c01601c81225540151190116641c0d140f01c0d0f0401000c0e01044030380d4000c00104241601800101d42c0f0900c0350504500b0940343c100020304040c05c91881e01e01c42c41c1e45d84c000c601c2003103250344030041030785c0000380c01c004603515042440c0d240c0c0740a00c5100d10b0f140b44020003007a40c000c1c00f84010030b2241e004000e0b40c040310903a607611046009510100e4118891552010400c0624065000d4601e0081c4c9400788 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 558368381 1250 558367131 558367153
    0x70c0c150e01030e1b012601060905193f02010201150305060c0304150f0f050c1314010201090b0a0c08010506070201230c0a032a02060706200309 64
    0x100000209007031505043ca819142015000080740c000d09085400e080c0035000b107811303070060701d0580740140d402811040750001c07940c2011b400e1040038140c850548035512000d42c0c0b40100401c1c0d24940081c2124050500f000b04000c0390340f0300c2e10400f40f6034411b2012542c86a1820a0f20300b030404000900620b41c9100160400e558080c820841c000c0c0c0a103081e00c003024210b48900d030355004003420202035940c000001800340200d001560051215012041c001c2c09004100180942513208611142e00c2c13404002c550021004411110f011104141042c06145400d0314003041840101c9214150b5407121503e00c00281421492482400c07803074000288080e09420050a1520580050340150340c2084040c0250f0303004200403110900703800b52400c0f49020f2038001c00300c42c0550020081d0a1146903c090100364010250458807000701c1c0011007009008140d003180c0190725440a50008170402010300418045d40010307914045c0d0f07034a00640729400106042869008130b910071025041244518 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 558369631 1250 558368381 558368387
    0x3030e13060b161a0130170702040501061d0402070c0504052802030c0702060717040909050c0a030f0b1e04060b040f0b0a2102030102030903030106090b0708030609070c0c15 76
    0x1e0443d500744d4595024541c103040408000711811504182d950040140d10681c04104a50f0b001d030103a4003440250003061422210460b913040031008030b200e01c0c18080041004c61080086150440294044814809004007844002c1d40b2501098600d034401040c0400c41e0f8a80c2d00a05000e02281821101d594840300203e84040e912041103483c842d0040041c4108292020281d60707032240c04460301c0b5038442c6549407002c5c089109801404102a01040006050030f0580c84621920300950949020329406802c20292004a000c0200b52001e280004d80c0424001121260321200000c203070307040041c10321114581c0e01422542155030945600000103070b03042034002c90054116514050041d444101e000408500042c000c0450a02e10200b45031141030b41209658081e036000340c0215541c3c10548034a44e20ba03803007401500040341440b0000038511a03c0801c9540c010742049416055807a69010040ca100001c2c0200c3c08100c441000e034404183c02c2000c010041009010395050800f00c11009 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 558370881 1250 558369631 558369653
    0xd020a050a020f010b060a081f030b061c0209070804030203120c0a0e031506040509010f2301080a0305030718080d030903180503060103060506060f040f0302150403030e13060b16 78
    0x2203c003590400000090341d40780d0000303642c0481c50a040203012555510894800904800b42008220703403200400000d0050801c2024058902034595400040c842e000120b00f4902c02c41c0d0094110200e403000402681c4907603c01d5030005d11900c19280307800c50030606a020380100fa030704030b6240c01e400070300d0706c25680c0c114180700c1070204107a02070300380e050204020107030400b401400517006544440024500c01c4c000c1d4007d81d0120851182080f070740021010005581800400d908403040103038002155a0100041c452500c82e0305039a00c40c80c40c0d454140440b0b0115090400b05001c89041c1000b080000c2e0501640f03000d04455940002c01c2c040c40d00340100308000a1100c1c000749000b001041c8282e40b800308100d0305480e0041000705a036115030010420610034a606400b107200f000c42c01181c114003100308241100c1c02201c09005070745511003101c00a108070f1000902060100801c130060b402c3c100d00c440040c026800c800102265036901151b001e40c0140e003100000440070045408000400c941d0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 558372131 1250 558370881 558370903
    0x11040e031e0706064a07180b0f0d0501170a0f050c0a06120c030c0c06110d02070807030e1507060507020a021216090c020a080f0c0d0309030e030d02061501050d020a050a02 75
    0x122031703c840110022201032407000e0312a4041264072420000b048480f05071a0005241ca90341299403010302c030340508115003128080301040d07410b0400000e0040648140b0301c111a41100241c00c240d200ca5588e080100104a01100c10b40104a801d4407196500403903100100815161031980c003c00300712003130485002e664820141460964011241640100200c582591042d0300003451074020083c00000d0040d0807030016218000a075100070840f0740d5015059443c0722742c480d010303007030150f40401031110a08003a14280700e000380603e00c0401c0840e00407a4100009005aa00c4902c083d004102e00c0f10044500b0342300c80d0321142c400010150260080401040502400c101603003c16000a45480d401007014000d0a00411030050040320541100c0d141c005038012240300610300c50020b8042c01d0070320b034143d01080076100812602c0c203000c00c0180c08011241e020306032a030303108081d480e40001c071203020904003e414400ba043d80d42c25413008001d901415141c041d165007120400a280007200301c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 558373381 1250 558372131 558372239
    0xe01020a03050910051207050a08160e0f04020909070806100e03030d110f0a020d03051f210b010915050a030c0b07020409080711040e031e070606 64
    0x3104404294031a0541d500800708442c0c841d184800310304202c1d070a00843e0302d5414a090600c0611148a412000515281c5103a840d030386100c0d511440e0030507a1844000b40f500100710b50a801c002c452900120104903c1401880142044030702004110366400482d084408600d0300c0085c00ba0624108441420701c5070320380f8000c0304c0c4e0403c01d004240c4900507181d80a030665165111603150803045e1095440076440f040c0b001d510f42da9444002561a85c80340c2c2c40a0100740360001285c640744101504949441c40c411581140d41e28040301c40c2c6586003401c607a45862001400302c070f00064000080c841c02400e180038003084110504240e0600c110880d03221902c103100c0c10b0300400001300c2000d4003008407000c408140382c0310521800458003404640e1402000b0b0800041c0307100800c06020700b06030400c182981c040029200200c0070642d284603d004070500c8034003e503064004a00500c00070600d042c4141000700d6101d50720180014000030b040b40802481c00c0048459024002c02c100389040850342003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 558374631 1250 558373381 558373393
    0x204090b0f04021e031c02070302030d03051905071e03021e07120c0c03140a0f03020d081605090d1407030510050603071202060a020f070807050102011a03280b0f070e0102 75
    0x4c00025920000c0388440d403980c3e08082d8452078035a00900441005640280a64201c0c1e050303641c004004003003c45001040e0078100c03c0003801d500360ba00c21240700e24115201c1901c080d5000e01191000100d8020010800d50200103c6a68880041158080002c0c40000f241c6980ca20701c1c0801e1180742440c05c20f410800c00c13242070f50202d0b80d00840329046a40103481d00c0b0a0320025601d40742400c180d00302c0a000d6540749621841056030010369023480443c6a0755040183c1c0b121902000380003401c065a0000507000d00c54040b4500c0d02d0340c20b049086201d07060818044803800c1007981004030a074825609500010020940d00c0c105000342c6030b000030110041c4c20340500380209809003002e1114081e000c0c120118103408018000c109030040f100c078000445003041e0359030919541c0c3d1704803805500c4c019424110003a6019106510304840c200703004000d404150404c000707401f051109010250364421507000d107400420b11032164240178020941a21a85107080d500181103101c1d000c014038110f501013 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 558375881 1250 558374631 558374689
    0x7140a0803031005130b03010c050c0c0108070221071b03030f030203010b0706020c0f0f010501170a120c150903050901030e030309151009110c1606021002070204090b0f0402 76
    0xc448600241c840485d440001201242d10507001002000c1c445900b640c07030a10300b035209503003010240c04c0700034682040310035002c3d06600445541d8002c1c2d80d81c0c00964040c1c421174103154640d120200031040c1c00b070011810450991603900a0303c0d030f0709803800802020010207105159001803482c1514201e41130135440c2d5490308814158500c9001e0002d0040c544c00300d00d0800d40403041c8800d803240a00c40c4c0842d030f0303902140c1c0f8045000309804e110b407120309503248000d51080c44001c140030b600d031500405104282e034000740f015507500001107801c940320304010401e000070b040d40c0c2c0310304070b0f034140207948da50303100c0e0401c800240031512588140324003603000b0f00800140400020360a19002c000220780d00540e103855945500c43c1c2155040a090241001c036000c1d102c8060102404e8049100700841c0c800b0130807428800d1005546024080050308200082810401c2a80017010818030103000003e500b8060b4484c1103130203000740c80c80c81c81d401c40b040910040d454103104010310f041c0c4441e24080200c40b4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 558377131 1250 558375881 558375901
    0x6060a060203180a030602030a06051c0f1e050f0c090a09050d0e0f031002270306181f05060102070605030108150a0b1f1d06070f060e07140a080303 65
    0x10707200c081480034005001010f081d403290364a02e4011a440031040d03441e0b043c031900301c2c6c0250003103000b85400b803000c20101b066110f2605085500c8103810a000e8040e105441e103c1c1180c51413010130407101a046c2c1c45407040010800c112001d8000400006851444180c0c1d007000a848000740002080074180400c02000c9000490140c840510b5420400f04a80c2078002040704075240f1002d643d41030080107181001042c080d0002d10781c081540401d4510302504200121654481d00c51541c2c05501c500006042c8042e40d0755040c4030140e00d40112600c4480c4000c104103694001e15030600ca071074654040c0189540c0401c480e41c09003c42d401c0c002c0c203540c10085e265544840c00007100184811001c01700f82442039039031001c0d8424030082c150804400001448001c0301d030203803503650b0014002500420100d000c107a01481070070303c02407255142020548490104070740d501d42c15544240e49071540281e0302c4040006600800c504100001001603800410200c500d46600c503150342d810420800c20704110b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 558378381 1250 558377131 558377137
    0x60906090a020c120a03150b07080f2b0603110109061d0f04150501090f030b010510050903150108121602150c071e06020f0c09070c02150c06060a060203 67
    0x11201c800180c644550310421490811503041005040f100080c00d0f800981e415003008581e0140400c4003060255a4004038450b845038810140c601035041c070004444440800080030403c000381c10821507895440e4003504c201c00204003217042c20b07a40703d508208019100d000012041c5d0b090a00e01c1100340f500c82c003c5c164402500d8100150455400b41c070030b15a0741e000041c11030101c054070070010310001683c01d42c6003c0c1e03180107040c0070031002c510028203042c03000009000d42ea40b014581d002a4640410310202488140101040c0a000e200003034044e03c04100c1041303214111540c00c150727940b5003544c040c2069803007994080c429200b01b003070101d80350f2001c1c0c0310f88125905540072025160035440701d6507140a43c0c84071401d01d0246010025400c038501d10700d894502412034440c11110f80d240c60503a51542440018080340d00038404500c000e2510100c11035002d0070350300340300300b50507540e5000600c400803154040764180004035000c034884908001d841d901c01c40955003506800d0402102a503030b80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 558379631 1250 558378381 558378391
    0x3030708060d0f1b0816080c061e070305070807030c030e0a0e1314100501090c05030402131a0a091b090303090e07020705090901021801030b0f090402060c06090a0b06090609 76
    0x19880c0c6240c600c0c1084d913150000200300c514140c6003400120b14140110192602c19900d0520560144a45071b1819030700303c4442510084002e800115072005000381c540041c5025020b2101c14805840420950002010b4503031207507903804038443e954075000c0e05a800903c8942e0180030115410300c490400300c0c00f00f40d006520010b181000c07d017145800c01c0600034102e800703e42800f42040b051050503180d0402c0b8143c401c100c800b400000120b400458081c0001c8801030351050343c560700301405405903072203144a000061448580c1e40742000c049800f0b80656845004ca032aa504045100c12050701000f110700034281c50a6a461b610f59240204804121300803819140d1503200030544542c02004004024000503083c01d074540340185901e030007504080e4034401d003c2800400317071001d9032007841038200c0300e00c0082202c61401144403d000c00c01100070002c0741c00010070011703034041a4040060b14865038540004081010a41ca480b074180040600300e50b006040b01c01c00d1008607500e94903000d40c0320b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 558380881 1250 558379631 558379643
    0x302040f03021509030a0f140d08070c02150415030e030f0307050f1e071a01150f020a050a080301080d0906020a0305030a14160207120203030708130b0c03030708060d0f 74
    0xc050711004000a1340300c2c903d1040d90610452003040c00b0440ca145191003850301410f82c542003003030070701a900d859480000791140050300e007100040070280161450b042040c00a010030f907645000100c1090039a11070340000000915081c0c1c0c0e000002e030f05024000218810802860400ca01e1080482d01ca0002400c100d09119001c149181407010440c2a160401c03106800113400c6c001c4410440840d034032519041c0c541d03030f21800c0c0ca50f08081c513140760941210f8030351960105c40100c41d0307070840303686ca040541c2e40b0440c003a00c0010070200380308203c014040c83c012244035544e5490301c17507600d28203100980c3d140140061030404100044e0082202c10090381c05042056599407659100c90082050034003280030340486806015042c07520100494a0004580890b07155030b4941360480c1039446ca40200031740c90f920401240001071104800340ca885040402182100ca4980a45244540154144640c507030300100403c00002d511400464220030300b41e8802c505901142c0b101850165030340400392036 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 558382131 1250 558380881 558380899
    0x21b06031e010603020409050a051e0c0f0c011a01020a0803040308040812130501050a060f17010b090a02070201090e1905040206090607050a05060603060c0a0f0302040302060a120c0302040f0302 85
    0x30701d240218011140c1d40d4031003015156581c441c03030050300940041c021840414034101c006000241a80301d018014000c0e0b180d00c41c007000e90500318074455400102035000c100c1051007040f0501224030090031684003c8000895212130b6002c0107070210591020590440d4411607150011462aa0840f40c1180d01441c24210b42e940ba400c001a0900c43c04c0e45004541181d1404c014500a413540a101900d00c104024400c1e070702c03001d280c0700075201c96005204411201842c204400349141444400d40d408510020170402102d2002070044101241e60300340c1940c000070000b00315a0300040d444050056400da48002d42803640e00100d4440010006505850360b401c007140c2591350707110a4031904a4000c2041f40d481c0d42c14a0025118002c680c001c031554403030b250124003949004114181726051079842c0500301100440c1c100c40a400c80445c41040c50340c01c200c08805600c1b124020403030386207603485d0180b0245000f4104011902603241c1d46082600c1488140182031000b18400212070301103962035a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 558383381 1250 558382131 558382141
    0x70503040507030c0303020c090a0b0f27070203190203030f070c030e0306011e09110306010513050603010905150a24021e1507020d0c03110f010504050309030706021b0603 75
    0x115007242608090701100b14684c00008055001440d500e071040c040c1d89a1003641c0721208020191044001c1d0658464076000350301049003000c554001c10340031100340080301400901d400c0c02e4103100940f102d00040c0c10002c0d04e548408130242a1145c2107040d40300652552500368116604000003030701707040800c65002511010701d440b030701c2390400c1c07005e0082c19121607580d9401c00d150300d8107448840e400c541aa1071000a8090418802c13003003004114101c403880d59540c000111080c1d404901d241d100340c0340c107a5010419840710400340d4040c08244d140080d250130709250020184241500c114406c50f851101030100e8103043c0c03240810403640b0403d0400981c0c62040903030501e03035007058145032031070004074103a0301c0c1c7c10000b030700c00d43ea51007004d40382d43c00d8407075000490311101c4000b1401f01090307909408400185c491070a8080b00ea401c0000c0c0e901c00d1155030766580c02e4034000c2d2001d039010751020030000d42c149070502c1000002c1001c2c3c00203145080c6281c1c03801460780c81d41d41d4401e204400c003000183c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 558384631 1250 558383381 558383383
    0xf070c050a05120a020f160603050613050c0a110d140d0b09040f020109051806060d06030614070e01110703080a110709050912030103112b03110607020102120705030405 74
    0x10307001e1a40407060701c0c1040481d191401035030f0008104403005104410800e007881c83c01083c2c6814400d409074101d1035150030071009070080e1030083e00c2190000307803220f01c03901284078512a0900410341c685441d5503030307020031000404440c4800c2200205ea0400340e00c07410703c035400c115035041418014540a403194001020103004105c41100769402c00301ca80c00b0002002142c0e1008130707034107100362134114145031144244400c0c1080740184402d000a2200421050301e03160020300401ca4500038041040c946903039407502503440700c50003402480602004d00480c1504003200b41c1401001303180038110000c2c0102e42c5555659540f101810b20400003800303507900d6100c0e00420000c070f4421011158102c2c1c0c1c40310309000900044030188180d02800040404179110303079003164126138101c51071000d50302103041040300700041e45120f42d82114082c1e44600e819841680401000d0b4040c1d21362401c5030003401051130070004003c0022045900c10040911603c548122941c0c01003401d00d00300d901c0c0c7d81c481ca003603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 558385881 1250 558384631 558384643
    0x609060b120a0606080f07090e16090905060105010503061503040203010e070e01150219112202180d050312101a03180a02010207060e0d02060408070e0c030f070c05 72
    0x3103400800762010140c0728640050400c5030301c1d2003080100324169450105c291600480104401d041c0c100a90400000b06503400a440006006042e00e600c0c0c1c0301d6028084111036035604c6403040f0394a90040308103000c024070500e4010102820072902e14500400068101041c02d408031400b12300c080045002d54809504c90038090300030008990b0399a894103400c13204d2400074413611105000040080003c54404210f0005141210301d1702d0300c00e03580a0351504500c07403c190110b41c1050b1140c0070b081100448a05005904841110050f9100034100c0303900c0548503001031140c011031240c442b500010b000001121080075050070603440a0f143d0071960790318450f195103d0010481e140080c0042c450140c07004500441c00f410f030121120210803241030b00c4d41c4161a000e4090780228000b0820325014019174042c02400401000901000f540010300e540c0040d04091280e0b880414140120342900f055aa009088100c0c4507085180406210f514004000d06440801c040344403207008004c010011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 558387131 1250 558385881 558385901
    0x6040b0414240d060e060a0b03030702090403120912030e03040f030602070c08061504060611060115020a170d050606070b04120c08030f0403090504021201050607021f032016060906 79
    0x1100943e8000c034100a0040c0455418051042c011000402d0411415100e20401e010010f4080c0d1b06000d400d07001c005808000034800da0070712140c07000380b0030390507060301c1503814883c41002c042d000e0061400004003107403c040052012640100b100b4040d011140c85c5d020b045070740c0102c001d65212454540691606080d5006169504c510000d00808500382800307a6600036081d5410400c0d40c0d903c00303048603060010710045400b604608014400384202041c100001e5015004031421106581c0e5000034180c84100391032010704001c2070040802070b82c0e002d400e400c0f440c111109410b1a03400c0d110802c81e00c0b00a0801000010400da003040d16078010f441c8503c200341c10a041c1d9840b881d0054600c82c2414045608a00060500e900480c1038a842d100352080c5100d55640c01446d0703824102401030940c4000304c03d9902003014081d16a12001d804002c044034012a540420424089220082150340c10f8105c0c1303000180c03d01c0241008082081c0100c0b07496000368010901800301d00f0880e00034100aa5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 558388381 1250 558387131 558387139
    0xe03090a1415042c01050603040f02040b060f031608040818010207090e0307060c110a0605060d121107050102010b012f1009020315010e0f100803030f06040b041424 72
    0x2400091404001804601150700c2e0000c00004d5200c104a000380c58100b400b445070701c81414004107010807903420b00d600c2d1440c0701801c00159600b402c0005a210340026038141d104940c00020400744c1e18004402d0510343d90310781807005141c20156190101c2d802003000e0310b200800f0b500c0f144030303040e8420000d070001480c0c0343e04100201004691a01c0d00d991050402340d90460401d0640e4003414400c4010342141e0f80c3e014060300e680c1e02e05a0b14132010b0480a410b03140c0c8411900e10080204a034840144000c2c006515401020810909440c6c00d062a0f50300050559141000d00140b80e44c03c00e801159885401d070260002a1107441244861141c3e48121405c5125036141c138200d9203c194820065180214125200700d51404141004000c00b40180d225200d0420046135100f00c5074540f190300f202d094401140d00684542c000341c80c6800444002500b100c03c0350501c941810148907518004800703030b5080c4100d42c00110340d4030305142c003c1e04600050345030259010300800080116443e02c02c0041c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 558389631 1250 558388381 558388387
    0x60103021f020c13090b07080c0d0e030d020c010203222d0606030305090112112d030a060f0801091109101e0608060913030f0905031f0e03090a1415 65
    0x184907013005060108048420a801c2e0001c91540c074050750352544210012102c06140645031740c3c841d03018102258640600348004d12202a002440d80080d00303060b411180016120700d0035500c100c115a402500003000041c0d5005c50354045000c03801d40303018024515404443e00e032002103280280101c080d101900651a041c00807041540c050014035198600741d0714441c1521b0400c60800456520303540c40070500c1000c0140700ea85514101110f8401440041020b090501c10050000c0301d13401290081c081d0303170303940e28180103205070300b10a2005040313904001c02c0200c1690b9514078a03189800412485483d1040000320001d40d20380c5c00b140500181704035203520054860644003404424099003003c01c10000000303c0c14202051130300e11689900d42000e2218180381c40036681601028058001c00016980104841d03c00704480f8000c4881d0700130125101c041807400345e0886054207580340894204010f03406199683d0801d02d415140340c08180103407168200009031074584544410304000c1004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 558390881 1250 558389631 558389659
    0xe06030f0a050a1a090a09020a03060204050a1202010206070c1e03031514010507150f05010b09010210020a02150c0d0606050705160608180c0406090c0908060103021f020c 75
    0x42503a01c0c001c1c10340800a1200d500c4910700e0005445450700981c000c2c28401c03081c50300c28a8800070740d030b40141c04810300080c41c074019004a684442160015100700380c00190402680c18200580802898058140482110180e000035150380c00608036808011141c1405400c1c0300e103202600c03006141c0035480042c192442e19000d000780ca41c0200c49080742c9110840061107034000005ca40f00c00780d0581d505031a0110a90301c0c4400348607904542c010440e610381d84070080f41c0e0750307120f014060308580d47ca19480708400c1000a15282041000c2a100b0b80140103140d00c0c01e400041c400301c85030300000202ca803540ca585909a450081c0d4030b14031810380c142580003d00f16000402048039902a80c1a9142404124520002010740d07101d0700000401000004070b4981200420513021482d40040c1c5542041e07000009044d540e0301c0e0044440141d41c2c402d05e0240344c1e0071070701000c0203100050180c9810741c1741d07400040d034210721800c0c80f01c18841c0001200d074100c0e200b403005188142d00142401016000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 558392131 1250 558390881 558390901
    0x904060e010c0f020c06070f0308190221100b0f160f03080906070302070309050d020102030c010906050718150e1f08010302090a0e0a1104020c010504060b090f1e070e0603 75
    0x1d83c1034500b01501501424000070f0408008860307030340707400c00980c50700300c0300aa1b0115503920008100440e5407007104101046060a8001050088064000d41c0102d102c6c61014841440011700321194002681c40204074071406032099a10741d40c0e11615164403442c4d0304542211103900000000c080903501c04460003015004181c69015941150441e2196500d442c0c060b0201e110b41017001e004a050803000f00010303e801c0d140b641c442803040c41542c0c1000342c4000910300303541d007990b000c5801f1511501042031165012025040c110700e41003504120360300d0300d090240540c0b00c05810004200d100d16550019440c1c02d1a000f114041d01d82c0030048404183e100204003d0003030008a20803840e0340c01080d0a982140101807034825028042d054050b6180e07560f95003131031182c20380e5800c1902481225a086020b00c9800d00c50340c00b4100200380c03504c02004004046a0091000d0381c003442d00700611180c880543c8054100f20321a084c80300e4a9121000f0503500d002e40d4564050380100000100400000c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 558393381 1250 558392131 558392147
    0x4021603080609070c11011403091b0103060b19050403080c030c0d0503011511011e0b102a08070b042012120d141312030204050f0904060e010c 63
    0x101950300e003200c0b500c40e5030801004003016112070700050450302d0864041068501030415a1005040c1310000501c076001c42001e40d001220024030a800c04108405419815440b444066209280812240742805440e801900a50244446403409410540d03152409141164040c1d9045210641c581c1c107103030103040c2e4982c0000200c034500c0c0038080d1501d010341e00034026241a9070502c00d0101140800e5001241c1c801600681c12003250348408000c04c15008521500201607a091300103e280300300380702407001140d0050004001c0014003a8410440c1008806540e01001d001e40c0c00000c038042400c01d01c0ca107015806e4058140f4580c0000d000410816042014040503842924040b0f00b00580801950a40c941d20061603600320481910518092400400b943e0002440015448010003401d140c00320084810a07060000802301e641488200c00410f1400c001074a025440e1606280200e000c3c403510006040c0140b59001c081420400035400580229442c2c40c000c0010341c00c03100e0003e14101e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 558394631 1250 558393381 558393383
    0x1d0103030e0a05060307030f090b01120b0f07170403020307060510052806050d0608070b1c02030106020714131a040c020102040509070c0519030207090b03031602040b040605040216 79
    0x18034141d40a070840c00e240c040d07602100e50082c4082d09664501c1016405800e10131030081c030b0143d03641e081c100003500c10b8044601a061501105241115a28181c1780002c40a0842107002c001581000445940711042c00b000c1d020201c4240040d461318a410b0f4558014014014134450030202080340007003401491008685044420382900344080c88004011f4440d0781102006c4002420140401d07402003000340207003a0a441c2c00618540d44c0c108550401c03403c1d030006001c1c0d02001400c1540f44038041c040f26980c241080701140713994075142019640302c40511070283c0481001021101c2030366261002040c1044523102403082d41c0840303044c0d410060007417a02c1845285002c030340d007406510510940b801c0e82c4000c0c000305540d4071894001d5606000d8580221024070540310328000b01c200a030030741d0040c00c1c441d8000341600c0b8200f40c040401e43c1c01601c5590b0203035100303001d4040761120314007601c80d24036010340300010700c10450000704000e0036450b007003103070000e00000d0064281583c0d0080c400c203003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 558395881 1250 558394631 558394637
    0x1206010c211d0111070302041d03070c0806060907020a02090414190201091409010e0c090a0b0a1e051605030d111e090604030611040e0403020c15040b0406050d061d010303 75
    0x80c042d06005440522490a0b8001c0592101c01d040c8014141607005401e0300e0039603224510704a0001070118690382c03080741c0459803041104030030040030790304100040d0400d10450b82c0150a14005a000b55555451030001e44070360446001320b000d2180c6c2004100003295100143c41100038001d41005140b034803600c049000a40c1c000740002c241c0403c40170f04a6030800103001c3e00290b480c0402c02d100c0300c807000e004111a10010040c80c0d18582c0c0390f09501000b0702c180c0d50100d844081d08000582043c00d044c02002e140002c9080c40b03003150b9800b208485808034961840500401641885072860050855440d42c651030402c040d0002513004d80a8180440301d11050601106a4041454940540c0301c0190700558148801d00004030103410120040700104000f504080d035801c0b51b42d10000e4280c6050b40540c01280c03158055083c070030340707015190a000b07441d1860a0701d450180301c0d040c45588695020840d01103413103071128005400c40f10041560b011076620303031a00060030324a43c032800c4c8800c83c04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 558397131 1250 558395881 558395927
    0x50a05070602071119291b07031106030613020c0c100903050f07050102060105011419050c0607110c041d0a0c170c0d12030902180a0f021206010c21 65
    0x10099545c01e031400e85054290029010918034421040486280f03081c0d60521000c5c054071000c4024074102c40e415825640c01040c1d094914101602c85418610382030f40180070800400c55141c8441c005142c00100142005a40d034042640c8203041050316015070f58003480c802c501280b030300e5021324400c0c29a030017801030301c0f992001c840078282d035104e0a20400b8050307008030004202940c0202c50105400d420070b000c1030700d003104901118402d020b840e4054004610040f0f43e0030ba4850307080124035400400e5040c01002102a0422180c3e20845602841c2c80b454842c0398203415818450320214141c0f004100b102d1145d54a86400918078025016078550786040a408000c1c03241d00140d4140c010b00090100e00d800d0740035843e40808071110450b02c0e410b26417503034114401a20f808018642c0408429008038050404000d880e06440754051140c5480d030051000020003000210741070f400110900f4220320440315450040e44900038600302c01c0b0940551100c401602d900220300f10701d906640c64807098 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 558398381 1250 558397131 558397159
    0xc1c050a0506011103040302090403050f04080d0503100611060613020c010203011410090f0608040812070f0f0e06190207030812060906151210080f0109060c0c12050a050706020711 79
    0x60381b405a40b00203588141a24040b0b00443e00a100900c0b805442002079490143c4450315645020b103248a20300005500004000d600708202c004d07240641018600b41440703503640c4008569503031001d4000c1e440f8a07a0210540b084004175812500a030580b00c009540300d41c0d403240c5001c0c451a01a110740e00a030360908500e002c0d10f10aa46903015602c0c1081d100c2200d6042c000c00711401c00700107000303c40302d00080152501100316103110750b102c0c920783e5441c5109407845a80090800450580c0b0205210045007120742c15540c06054441ca200d00301c04c18840c0c8522014200e10f0030840f80d00190000314001401e5072003941e01c40b0b4541c85000d00f51180703801c0340c4400e4207000c1c0003001340c0c10303e404600c0d003400141540765404e2441c94028101d0181c0820b0305450748100c034113010300496440c0c0729a640d91030080800205000c4c480c0c3d14112402c01e0700140c41c00703071145006441414a030340108400001c1d26000180654142d41c0500d0b040354003151111804c0c5409418000d02820235407003400c0e801d403115 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 558399631 1250 558398381 558398383
    0x1203091403030c060a1a09042f2404120c080c090103170a020c0306090706030b151c0f0906090b0f07020c0f0a050d06021209070e0c1c050a05060111 65
    0x28000300d210000422040c2c3d01c21042d90f00900d0700146c6000a046001c021102030340e2200300036801a0b004041e507600c5448072808000000c1070a041c00012403807080d20907501c41d03840944030a5004d010422b0750318074003418002c2c40c5e02c601c2290007904d61000b40355040414048440080d05c01c0d24400c0b804c13100340c80008400c0091500091000401200c9020088503071103940c20b0141045c240e0360300445180010542c0000d082100840d100015584002810003005906026440704440c042c1e44a0007540030fa140c0007500717840303091400000080c40c0481d44003154010350142000450601c0b081108511a141800242c0b003002400d540d83c1c08200c021458581d0b521100a000cbe20541c0c0041c03a0003100c0c10140031483c07415080c5030340d0015105000264580360f22404c1280a031083c100140d031494401c0d10f07852503081c080c10034801035001684c10301c14170700c50301c6040e031b04030705401e510076200c0420442d40c20340c0440c4c00c14a01c801b07a041005000c10490309030003e034041e4030262203811407812501007403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 558400881 1250 558399631 558399637
    0x9060302031b03030405060c190b0702160e04061d01150609080607231b16060503130b0a09021002010c020c01051c0f0e0a0c181e15120309140303 64
    0x2d98503800c200301c200130f6450500003d03d488000003050300c1c110340003c105c404003a03070000c00680f00385086908025015a050101205110880c1070030700555003401d0155084a41c000c2c8024001030356940c1076919072000c101c100c050072450500234020444c4d01880034007003a45900c20100032071003034240810300801c04030f1001d204250b1907680e04503001518480440980c0e20381207180c0e4000d001c200d440f0000c45000001c1c41c2d10030100d001410810710400106000010507071001e8204402070042c401c4c1c5006d5083d00c0105186c01c0051465651145004080100910140203612a59840c1c010400d03d4041d0001f0034511550b80903a14003681d04401500d542c401d0821122400e82c00344e4100d011f1411aa10200012400300400180a1000130105103000c00a030010f441d004100002081540b11989a04813064031b036500a000241c4010030100c0180420315600001c2038895140061100001d41c5120060a141c040c0f4000c20119003000317402e0b410a405071110740030743d0a0110001741400022 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 558402131 1250 558400881 558400933
    0x6050a02060f090d0e0f0a03140d03060308070b07202407020d030e031303050a110103020f0306010c02030f060106050c1011030f04110604180509010e0c0d02040f02040906030203 78
    0x2404d640f5184d08001c9943c150000d0070f6a42c0b2605515200c1401d40302c5000403000765100e0140580000d190151551424211000c0700e030406042c99010f01c00a05403a050b2680300303601194001403038440f408203588180f40c070203001c07521030f02c21040160b40c4c00300010265601c03140800310f07080042a080d05c4a4468030304858403405648070340c85000d840d521952200502400800659060500001d44852400ba4542c0f0686a0f07900100c5e00d201405070032010348140e00000d08086107480b50f044108141404024003242c1440040c2076a0b4055403014045451090f82d4841030391840e60f150480a42141c01412012a203445141449110b2402c1172107a1300e102160b001e0414190364540d8085260050300030004c0b03403d002c9800c0321250544544005d4009414540e854406041d100f04074002260001041c01c0e509a0414a4444003408007148001c40c46d102550403165400007800440c0141282141b0004043d00c0090009101c00c0d041d030001b0142d80c82101940c0303910108882007610403d044c1c0d5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 558403381 1250 558402131 558402133
    0x907120321110a39020a080c010c060c022103070e190b03100902040f030b0708161409031e0f03180f012a03031107110405060609090106050a02060f09 66
    0x2d000b0064010700245000f0100089134691a003220000c48540340d910021340244d901c080010031313085207001c0e01ca0f4809403060600401c10100341c00c000034000d0070044000b5000c1d0340d5440001104920910001c41d0085030304848100c480000d10004165500c00c64100c000244131076158807051802003011906440c1e01000d12181074103014601e001948050205c08010160704d800003803065281c00508010326000301240c052501c2c41c1008000610b00501007000c0001000800c41c2000703030380300b040b03e00000500d080005008102c0070a5040d115103c20564107201d2b0314245111409083d01c0201039511030310075121281e00001010340da9010b00489104094003a150550301d038103003810591200760051600451b01000101d802004850307145d2004491100d51880605154060080441303c600c2080290310307200d880d0b02c400c0a03001110034550b12403510394011548960700c813816186407039801021040696510a009409980800c4c0d149006d03000e40000120121082d02411380b00741c203904 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 558404631 1250 558403381 558403387
    0x406030807080a03090b01080a0302070b0f0a030504030504050402042301020c090a0c02190503030601090b0a09091104270c03060e0411130c0e0f040b0d0b090712032111 74
    0x7030b8072280c16801202d8082c1c10107580e501d1070004101c103008614001e000d401c0c09055206600c0c14000d0610f0b8060300201200c84003008035501003124241103d11854051030000751075191450304503080c0c070403035221651041c00840d0119259440c8626401a400342c041e1a05c9250502c100581e02d80c7d100071001580702011000103403a50762070350012050a403013413060f1a035800110b112007489442c118010340392036001208000d0b69581040c1c000707004c4c2a410110a003060349402000f8076032030841c0202450b0b10303298081c04002120403001c1d0f0380034006040c0811903814410900499101a03555558022400d00080a0700355010b07103d40410b44104000304010b960b83c5460705400c03080c01c85007641d08421140000101c4131104e00c5540600c00682d6194010750f600041000368500e0119000d501ca1460301ea40c0d102c450b039600c03403201d403200d034054401c2c51990380da440810300b008074a501041e02145d101c0402004c0560040246950809803842c0c00400c9a107422203200311180b0303000750403080b2010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 558405881 1250 558404631 558404633
    0x3010504380708010504051027061a030f0a140109020a1707020106141f080c040315060f120b0705030c0c0a0b010f06050c03041503091a150406030807 66
    0x514a21600200301181061000d03001185004600a0403a0b04000280e8082d0044c0203900d0035001c2c00b5082400c1042c0482c200d070801001c201d91101118682d1100b0241e0301c41d81c13643e4041500450024440040300409003486408031a08942c0f041381c40d004402c040400203004408544500c03c955800c004180500707a082042300c100035400400c0480078004801482d02c400307220352003000e108501f02d070300202d100340c03800146034004c2c0c1c680c0444a201c0c4100030481c2480e00b9a00c3c1d001010720005103006202903d440c180300d0454400c9400143c01500d02e0501c075041d42e80306400240454500c0b0403232202c1c442da10102950350304840f41c0000c1070710901101107082c40e40324801030360b00b00781000152407600c0e03e601e0040745070500080c1d02304d640c4e1800304010000c0c1914205000014207583c00c015103030030024000544c89204a0040102070520840110b50542c401d07400742d40090b500101d104801948802c0e502c03401c49081f909030804ca00d18182c0d420f03103810b00e4007526048135800201e013410a846 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 558407131 1250 558405881 558405923
    0x90609120f0913060305010f0b09160c12020721050a0f02040b030115080c0f030d0804060f060e09010c180303030207020d0605070f08150d0212010e0318010e03010504 73
    0x714003007403030840c0e50a0005440750781e11403603600e00880c440f49000070380070724600d40b040c25180c51440c40c4641c249494070b60341c2c20352075440210b03900601d003990030040c480c5e82c1101956080c081d084040d10040d0002c02200c0090b4001843e00c3c02e503016968050410411a42c20480e2410341c03644c0201a60800c1e440f001c00101c000104c2081c440c401080030400040700b130b0100303003108c91040c91005054203103041005065001c1c008070742031580607903100f54040920310103e9940c241601d00541000204000107007031008540c0424104c1c0d030a84800e100d407543d240c1e080a00650241d17170003c000c0d407030101d204070364a01071900c48035202c1501990344100d17407841c0c034150001d401c5030b0402d030f0b00144001103003c000740d1148603040c410801c54079034203010110b0580007001c0040003000f0b003603104217014040305541d640b445994007090381210903c4482d002c05403840d000d0414803505d16100d10001c00e034885000720506c035041420200380e03200c14240f041141050700741d035002d8501134106a803041024410003c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 558408381 1250 558407131 558407137
    0xf080c150f131b1a0703030b090f010312121d0c0901081e15010308120a0204030201020a1e050111040603230115021c08040b0c03190e0a170d0509060912 67
    0x902c8203500000541c3e00c0c0c8803038500250320b0304e07410084c01c000142d00082540601c9078a03a040c0e0b040d03c0031000c03807910480d03c0402c04418013001d48102203803030001e82030b5440780030307004401401d00a0900c05941ca6040910491148001c410a940601400185181400203c590403921014028008501c555829400c005202d4040c816603001e0943d00140044d40d0041c645d000714890181e050b924400039401c90180c00000c0c1162406a004100800250707a00284c84081c5136081443d044000ca1880c20000d106410b4800082065080251800900d0042c0000c2d01c11902c0b580c9052021480310690603071480c101110380510302d9203c00050080740313008901d81d14643c80a004a8007a040c1195010011a4000b8002c41c001800f6800300410402284003e5411840240041d4114100524100303400911800501d140030782e2181c42d00303c00b0804004031070000750000180c15101403010700740809503100c2d1629006003410500455184800041c01902c1040744c0d80c0500080e050160b48011030358 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 558409631 1250 558408381 558408413
    0xe060f040b1003020604030c080607090807060509281530021b01020304060c05040b0901110102040f03030804051501060f050d0b0a061d01030203070c0f0f080c150f13 73
    0x3102d01c100120050700d0b880020301c05180908283e0404500d006502403070b041c0010001410004800d004212b882c400103524401d4541c0c50a00700d0b22003140b5000720f440c544030b40402288500140c007015003118090702541781642c0210701c00900c000300c110010b4070440f40486c0440032860360000808a40d54984014405d0461200307000b5250250380c250010060303c400007a004141d6001090004200c170920402841c1180ca09049003414902a0001894011100514140700c045070720603505200c29811680540300800707030300441035140d0900a12303c80044804880d9445080e01e40d402c8491314008190403100a540d401200403000d0310121440e40100e210440c0b000c2d01c81240f002c455948003030190107080103a4440103040224180c811099038010f803124107051040040c803581c84d0f40081841081d54100180030860b1551b40381c4041c0c03075185400040c0043d00081502d02c0ba001c00450030380d084944201070b00c50603895051a183c031100080e2080721203001e1564401f40042d020381e011100309 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 558410881 1250 558409631 558409651
    0x150201050c030618252a0c0603050a09060609020706060504200a0e030d0c02030d03140619080d091502030415110c0d080415020f1b1c050c040e060f040b 67
    0x269550082c840e00d0398020700c4070310300401c040000b810786900d1010b04012186c80c0c030000e10009000c00352241500c0c50800e02030142090f4890300007608000300c5410001c10564401b80c00c0260f075546920703440c000d410130070301101d07481e0605100140318500390080c0303d030220f48240201034a100e100e0034a10309901802d1984d09001c40c22070441c0c1b490f81c082c413008008910b213031610580407100340f040508003041c200c00e002c1858640580c1d0f01c440c22500e07070b0603a072240c416510100c1d944a40c40c40b040c0c840099901862a5106011880e00903a170b01c00b00b04021a1100381900070310002c44003081c0d0312401107010b00c03514984200040300d0400c1c40713041405504070f4004150307002403034038038080b650450341500300703aa103960005810803600658000d540f504081c4c4e0302c06018003402401c0c6041d02c036000d10301081600f240c0d5842681883e600d2210300c0f441400d002c805c003d002025450400d0301c0d65420300c0342c50300c03c524050b0040b10400c40420050300c14411403d4540c0c50780d42d19078451003000340180c00f903014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 558412131 1250 558410881 558410911
    0x7051009360e01060e071106040b09071a09030f07060503060f0409050a050d020c0a1a0309070b03101a03010b0304231501090605030706050304110105090406150201050c030618 77
    0x7400710244a104968680c4100102e544c6040488101c001d94000d81b030402048136184092a04402c0454455042588400c4220158480ba40094074002c1c65400416104074140c10005c28400d0100007031440303a00682c242e56a020440800300e0715061729200300c0000c00c0c000c10008050345000a0140c03202c1030000c0002900400f5511110307d00304000c403045a00e64084580000000d404114010400c00c08030381d04c034425420881c000114128140690b140c0e500080040351000005000d045c0103018001e41864592420107000500c10107588180d4141240803603c116130b1208641c04c9034180e6030005401480c5486650310171030b44101c001003000b8040b00510240803a45e03c00c0c03026021001810122142c5035042c03005000455045522241c403940c0a0101005266004400c4e03c3e80150400312800c0b41ca003c400050321644541c2140c1980103203413000100304e41d2506640d88900015a41c000c2002d59a0b03045004010f2206543d41c96200d5441c50001103280340d801442a07000080c8080c03050713 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 558413381 1250 558412131 558412229
    0x100b0304230a0812040b0a06060f0302030901240e0a0614010e0a03170c0c04050106440f130302030405060f0d060909260a0807020307021207051009 65
    0x64113400c070b40b500f0640081850180010320260010094100001d000c0411080c1c0c9017107001340901c15100001c0003890307008000a9a820740a61156205503144d44241221035481c41c0e0001c405032131802185022a0400042440b1840a1107924281d80c1c01080b0b510407030b4425401900c3c00c80384406023a901044102010000603c45809a4031390800201110784030b50100c40700c41d040406211006000307030b00d04001040300c1644040010449888007080840300c03e2144200c51092071904141030006480468842d8101c4262514a1043d0000350701400540c031040300400d4808a84070001e001030b48103210030320141c98000001e15400c0d10f06a01326152402d0108028107940c080e600410403155901c0c130312018844c2d070806161101e40100c1d40400c41c6800c044403448240194600c02d400c116216001070b841a0007041126181a0010868807000701c1d28a10f05580d142075005050081c50048880b665103030040300360b2002c2c0e03030103880d00340da4215055200d40310400b400200102c950f010707100d050fa = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 558414631 1250 558413381 558413393
    0x1140703090b07050f10020a0e040902091815091b040b0a06050d0f0608030c0601050a1211061b0a020a050102030c030d0509030708070b01060f0c020303070b1b12100b0304230a 77
    0x550300344204100907840720a50b00340927045240c1e40c541d6900480c100802c845c01030340c51a0b0020b620045020301030703406144001030329107010318507260000e00c103c00c00180302c01001e001032140801019140403080401a00f0180002d80b06841600740d000b802d0400c040c8042c0d400b81c0054030070b0780300c4502c0000303007100c1441f40312098481c203510421240c0c0000a111542d2041405580c0c0903020542e0b00c403403503e2500d045c2403003440f03442d54080d00350000701c03003444d005645101c210b4002e50000c004042d041505a61020b48a4180120492040c2c1410a00050550012096601c0080781c507015604000c261244600544030007071003080c6e14002049508005416071014224490080d400e0b18295810582c0190999031818004420b000c600b025120050794000100c3d661305520025040150300c940070507650400d1080004c850f29200440c00024171084003207840e120b480b0010056070803540d1100000002e100c01d46c0c01070130358000000b0605551660b40b141048200c1c041f0700304c4100c4900f5840311 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 558415881 1250 558414631 558414643
    0x1501020f1902030d03020406080a0c090315050f070807020a03050702150f0309010f200702150d0915020306030717070504090b06040509010b06091903020a031101140703090b07050f 79
    0x5265024441c51000303055042c10000503a4000440c2030031460541003000c0030b0032400b802040e01d0390168486402003152440b40c03d10400070340e8031a5001d8010001c0e119200050002194642c68507604440061b080d40d02c40d50700f4a006124507006401c034800307035443c12125917006a00980c0c101a01240340100080c0280c01449400807404030140c4038140f200400c3c1c2502c03840f6014100e90703800d11881101720304007034003602c100c0c104001c4000e80e503044510120b500d480c0820b0081d048030001084210102c000b07500f06810240c419000c441000101842e82c0f8128002610314030703010340c051482072109031006000002800f0008088601455688001809503481c1000450f807403650070083c04250b0500340a10741d044211400240108001c00001c90624007555840511440d12801070b60740b000320041c0301030051364001d0032845242d5200d0910301034241c40b101c40c50b800a41000c00b4008030041c01c03019202e000e54544d0761305456034941080544903412120040ea06401182000d0641d00002c0000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 558417131 1250 558415881 558415903
    0xc0f050f0705070f09050414150f041e05010b0a080115051203040909030903140f062e031a1e010b03040215070606030309050301060e1f0b07030309020f0a0501081501020f 75
    0xc106c1e4900340c980302c0403c0340006401c0382140d00c04610f42011080182d013603540070710b8403000c41a01e684d841c00c0400f1101c80c90340a401c14068a03840040034408190050200c43c401079540c00207a0f940c880446088035000c0d4030486c0c054090510520852402012401000b004d000c1124181501d038481a4101c07080c16100300c020030307108070081080160441d400c801413a00740c130140650350b116000094135084010301490401a03800e02d24020500407e840e036850b50414203159488581764500300800c80511741c0d69070311440340c4000103001007503015464020600248803000c40e507481c0000c109a42d070400750040b6403182e92131a074a9841040c0c0c1d8090800385000316804141d0602d9820083c010b5411070b040303076010f42d04150050120050b00c00000f90405050100b0a85556884401e0342c4c603042c45801c4003502150020b02d80091650540202e41d49500031130780186840322010070006940078a01c01d00780802c10750000990708091850398004410810f0059507016000e184010b801c02c00e04e244 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 558418381 1250 558417131 558417149
    0x31603150b0d0f050c1b01110a0c05060a0618090609060f0c0e010e03070e060d05160f050303040609060c17040602010e06090109020a12050106030602030c0d0c0f050f0705070f 77
    0x765031a440c80e941d0143c0c80f814250340d00704104900346404040968840c1c0c440a0054841000800308214001d40c0f101a001d40c6642060b91280e05c0b03480c0043c080d104c034902c00d48291040c00d01252504403288602c01c201e5005801d20051148a0380041000c2e00b1114800e40e0b80590302c800f2500411414050b44030030205120000451404060000d44480030080b54035040281d02e0300f461049840001d00242540d0324610030351829903070f01001824002d44880000c0241c05909811107100910880c100b058429511035035040e10784410905549010758403840740080c941080030440140201c1e283e440395130164154100c200358007050002d880c1e105500010051395650403441100005002c99904280c40c20000d010006071a0005880c0300c20fa40108103d11102ca030f1602d08000c0d003540044011907200001b99120700d813041408580f500b0520310720381403a0401c40c444c40300611079207140c6140401502c074103050410b81c0d080e0402c0b0f500b000c0d01c111164401d044022030150b10002040004003070960b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 558419631 1250 558418381 558418387
    0x1b0f1503060f0f060f0e011d270f0c0903150601020316260301033219021002030c060a0209010306030506090a0201031107031707030605041a03070812031603150b 71
    0x4054000002d029010001b9a040d03190031607a02964030140140d200a20804c20725045002607480b418500480d9400741c89404060300503031484860a210340f035405181074071a9204e81241645104035259a54190841394009080710300006080c2d40120341841141c0c20f00c00c2c1885424030903c520b0100307442100345030000394010300c012040011500c2181c6003050035945503907240e40f02c80c0301850036031400c107000d50a54104413940303005013210717029040300300d41507243c0d004d0200000301d040c01001d034091200d8048001215000001f03d690607030030040140310607902c0c4802c034002908402640790402d5218140003011510401074a406104108041c01e60040c840c4009000c6695070b81440000c032405001d40004641c100c3c8104411888440e1400f100741d0700c1440c200c0041c40c15400903a4030500d000d400c5d0142544210743c0c06c500800913011a0441d54544c01996a1f5500400034004070641c02c1000512107814810340c031503d40e955080c00b00790580c2c810660030225049030800f00080f0404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 558420881 1250 558419631 558419639
    0x2503120606050a02030403110609090f01090c0e09040b1801020c07080106051c0b13080705010509010b03010608070b091807081605070201051206031c020a1b0f1503060f0f 75
    0x1442403000030102820040d150036103e4074003070346a0085100c09020f51004100030403140d16400c04481c525403008010a2061520a00d8420001028000c85c41b01901d0300f4440d4040900074082000c4074140280828019602c90f641c400f0001c000905d0740420310b04061442a00482c24000b9200030424100a000d2203803c15003900d00b101c500d9800300d4402d40e10a1900080e0030742000303050980704d070404450314032a610640300080c0c0c05550440100300c4880010f69005001c4198000e600825035080280000340002c0101403e0b07800c24014412190826142041290b1840000340154040540040c00076000c12403e40c4200c0000c03144000403491003420416500700c82c40d0240e00c05815070800509140590300000d01278003a00c11400d2101800340041074050b40c0402c94444001d80540c0c8803512050059002500d032000101701305c40c400c00c424104a28900c040301c4c140e0644180420070041701c0c1c9001129401500b00540020a15945003004641110007a007014003400700c00d8482d0039005c0c54 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 558422131 1250 558420881 558420917
    0xe100908011a0f060301050603041403160c060e090907060e0d08030106080103121d010c06020903160f140d060b01113a02060c0d18110f01020607020c01052503 70
    0x1c08000c1e1213110308000601c000c3e9078020559402c9500140c0f06080072010280d40d52451241d00640007c480804214000b041a8a409101500c0c442d83d00d0f054507000380d005010481344165070400306034000e00301c1800380c20f105100c0070b43c5203a40104907000c03840d000e0701c07480060b60007070300548005608440180140002c1c4603200906001c0e81c03821030003d070b107070301c458400c410018904103041010740440d003024030200d134064810b000001011b542c01c0040401e40401140070782e111b40d0f064618000000250010000d40b500d0710301030050b05107910302145955400044c800d22220505001d000101511103490800c40840302500142c085c0c4408208071500014020209214800031400e8140c4144115400714070b0a4109803103a104948809940c0d040001522114075084500c00348910030109204107001c00c08034010065450746854041e83c4012a03e071075003106c4540240e8010340e444892541f00c1c2008080c1161031307044a13000402c0c5500c9111101c0342410044c3d0000c0d001c2080c1c9281441 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 558423381 1250 558422131 558422149
    0x30a0b0d03020337020c0a050f0619090b030705210603190312020a080105120102040f030b04020d0206070f02010e0f0109090504140109030f0306060509010e100908011a 74
    0x803100e00d440c4000654009540c1d1240d0501d50624101c481c8400000b181a40c109032074490009020b0982d1510f030b100004e41d1404c0c0d0b820017034407425180340001154142090003400010029020303500d03110406c01d5601c1d00440c048101c1c404c1000350302001a081e041c200c0518001c40a907500ca41c1e803845020301d1012100301486402c040812003c0521844d43e500041c0d4411798000313000075a09007412414250f03004075454085a6180f070000805080066205215078180c8008913440c020a1080b00705240c00c074042d0340112003080c0030103141840400c04246405038450700c001e00e44036800d1180d80c00700f03410f034001d603d089032001d80c0480c03007000b1036030400510b04520f142990303040c0d2004980d00c00245071001c1445040f400c603a80350040b4042c442030210084805459000030710088186160050040c02140c403a030000910302200491264480d100711103007840c0582d154011500d00404000020007007212010034400c031100700041101d402c0c0100c03038001c0d0600a071400c4910346201840840781d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 558424631 1250 558423381 558423401
    0x1090507050f03060409050c09270d0e1e030703080d0e0609060c0702210f0709050610030f0f14090c04052e030c03050d11010207020109031e1502030a 66
    0x20005002101c5041040b8050700c0c0e20480440e40070812054908101d41041e201d000c0c000d8001407048104035040c59040180824400310102c40c40724903000e4282541c45024008420b00000ca0084080c181b910306420f40d03c0bc0c400301144003099520201c400240341108590040300c1c0218042401c0008651901c68005503841c104040c168900d005e14200303484d01c400910545200380d0100301c820a544515660300500c0b0800e0078444001c070500c1480c156504503c4450803680e04c910140461200a80c0c050540110300240030500c000000c2c5800398081c000b07410b1500c1900c2e90b1200c44070a6411140114900070302002400346079030801c451051705100625501500031390600c02485041e2061001003140c0800f00b02c1c1440448138100d04c820f168610030380c4081c0403803030b020380301200780440465668141d03009900d440b01030b808a03d90342d83c20f130300a950001e408070b52922010000f10b0781c4e1000400c0c5004000311034051410b925645c4011041d4145a01e5012550200c108401d1100a12881c41d80c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 558425881 1250 558424631 558424637
    0x50d0e03011406100e190e070203043818150c071202040e070602060f060108060102151504020d06050f1c14071a0c01051501050f090a0506040e01090507 67
    0x344400d8421600302e24409006203010700c22080c4950031443c8244032401700b00c0c8004002564a0320b000d9040c2c0034440d25401168407030b4603000041800140000b04440c01c4074802c1141120441c950b11400c6641381b0402c01c14a241c104104a0b42000c1c0c244400800c0b40d0a025001844480b140c9800d1146440b42e410002c58081400c011101041400103111011a000003048082c959000e201180140c0300001c0003132900e21904001140b95500440c029100700301d0380800e125142e6400e80110745100d8143c643d10702507000305240030840940d8100c943c0d8045c000c2007401c901305840d038002c10100c0c0d0081801c200081c1e600e050912013441d00003081c1c03a2802040701d81d401448516400601d4100b40024010442140c4009a4203140e50030f02a00c001015140a14450b0180c000f1003508554050070400c0519464030b800101c00001c040c4480002180680d100c506154150100e84110380c405501a40e00c80c040f0030700002c0a44c1c0e1040144040c008010300a285d42d40360810100c2078510141c018028 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 558427131 1250 558425881 558425891
    0x6070806220906020405040c0203030103150209060406200f0a0c080601060206010b13030203010908030f130818030a050706020313150507110409021f110a150b1903050d0e0301 77
    0x40309584020900380300801d1100040450303440c0b03001402446135501c026006414625040b80307042d0044040c5040f6401000d0500381908082c00e104c0c224400d5000030b07a031211042c017043c014540f04000f0b06141c0030785840c0006243c1465441c19140c04102207c989d0380307500c2405e0040400008408010050009030700a100a50400e0406501caa0b0140901000c480c00802e85102248015208000540e0081d000b00900101420045080d80c0100c400e02125200715000c02c1c40c003e80e00b02c2c150003540e0841d8041e4202220f1000d001201243c01001c640d1512424000c4000303d8000d00c0300c140100341c1034002b16643c403078036401548501041d0740002c4c08010250340e1640b00540041c201c4603215400b03c0400031640710800007038010300c0a0032020390400c018444101c100d0010710b2030112128090340340c46480040b003206407a5541000c24004040d21840c00c40e103801e40045070407090780110020815150001c0c840b800030380c0c01070b003035005844982c425001e12542d65001a000c10440c041a002481 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 558428381 1250 558427131 558427159
    0x4051006020d180303052b060302010306060f0e0603090109150f1b02030f03191d06151e0325140a050108040b0702030408070308041806030b042009010806070806 71
    0xf0201c02030321004e01031001c0028009103210418118044880c4c1902000f20364680c00c2e03118200034496030208902092600c28042011070148040d400350800320b80d105040904100b05000440d0000382a0020642d01c0704c4400b00000c000c4e003c01e00310034094600014100c040650580107440105807a40402880003a49060a0f58080103ca101400405059070344c2c0d101c02c0301100c0c264a0796880012090300d405440801c403901418030b800b65500040c11585161600e1003c401035001040e049548405c11000f8080c2c3e05a40f01079900000302c008040d2041c6209a0100d0022811202c041560850a000b01401400c0302c1d00807100c00401c007130f224920040d041800180ca1840040c00140144014900243c4003e100300700300c41c09040094140d480c1d5540e40d15218220340c00070702808401400c10781041c4030005180c8148403c503a046544c581c1c85407155125200d0301c0c8040f20100c401152108508203d50b1961003002c0d00902d2424002c242518222000401c3c258020304101c2c4a20740d044034080b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 558429631 1250 558428381 558428417
    0xc011e091509032a0309090203010510030f09021011010f0c08060904020f0a080a03270513060504110c010b09042003030408060a05071107050306010e0c0904051006020d 74
    0x14039101641c0c0c0002540090a00303040d11603000c180205004004007982e0703806820007440050381e5140c42901e031001c00c103881e405280141d010034081c0c150070404801c0041c0c009482a000f140c1e00c00d0110f50005558082a0045200d40d051076100d800440d030075451040690009103e80d100542c1420800c11404181000c0101f80b840701404680c464010350f00414255501c401c85440c2c80c0b81c1c002e04d10048180d56901994446040702001e07000302d41c560052480c0c24048071001042d00c00720b2505d0b02c0105003030104001c02280315007404003902e03a1b07800000c01c654649200c2d080c8003411f011b88068547c071024000e00c0c20f480101c0f0b8118041d61064090000107102c10364040b08801542850386070094440001c00c0c0766002d6030b03011403500e00c2000e060002071906a44001e0042e44203694540b0000c1140a15070345e1035642e440782c0ba4141c0c0c41100104044440707035443c513402044040581e1b1501c5000000601928015248003118844c9c007101048001d80400260150030301d1030510590007406e0350865 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 558430881 1250 558429631 558429653
    0x30d08070804020d29160c17030417030a0914010b0112020901020a0512070b060a0303121d010c020714040603080d0203180303011706010e0919170c011e09 68
    0x83c01284086044d5080001c0d00c035040700310882100701020440511304107015030680907142e14918001c518078000ba00b0744158200400180c01100e01001e0070031007070b0101260390000340151100c190144009100c03d45460040d13000700d00424001c0350070b158506025a44489051040d00c2c1c80e80761484460450341c101c0e140740380b4422110301c0180c9405d06078005074103000c448800105075029020b11071540c028150050301020380150038115a55940c06e06000c0c21081c60301018001c40c100d206159070f82070352600880121580e034611040000300c1c07040c2440c2540d610040d464056040644244050280c100b42c580500d1402c07503080c4905851600c41c02024030502902c01c024980001c00a02c140110030b4076040000c0780c030340c2202c0d603070741e500ca100c044140d02c00040240540268000007031640302c1d5202907030040c081680903042d1111100002040d01100c01022104441c00a00b4240703040c0b1443c0c05004d07081c00a60000c14064566640d80549205d50345066205610745145000403850318603072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 558432131 1250 558430881 558430883
    0xe0a060509031c1110150504020f07120215070f0e03060709140d0f1202120a0e01030903090801020301140f060406090e0c07080a030603050f0705090c0703030f0614030d08070804 78
    0x180411681049504542c015001d1310020b4013480f909002e00d4620700c46500800c180348010f40320381e800a407140100710582c4030f295410524210244002e0b80801c4c0c032004c8804d003080b19401102d20080c2c9080c81059180740859200d0080b9081d19440c1c1982c0382c108010ba152054101e01500140c41c3c04d51005e0414034450059004508281c110301400d0748132000030004403908284044900000c61401c4e000c4504200e01035070040c000d00c000c101ca0030145070143c900c0030885031074039070030b00040c03d004500410244000b5810800c4221000030107070000e1000394041d003911301d0301509144040d0140050300362080c04181c0280c000b0001006815409090074055500700d50300d00b40c090303d40340c80c0c5a510340500c1c840581181c000190000703a1a81503404042128403072429030380b034280074055041e100d451350b1280d15044642e200001d510901903600501c902e074861f0800044094550401e0300880ba4142c0000466103100d40c1c080314186410480311000c4980362400070f12518180da4014450a00500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 558433381 1250 558432131 558432163
    0x3032a23010e070b0924030a0f0207020909010e010c0203070c1e090204080606040501061b060e161d060604080d1d0303190305091207021905100e0a06050903 69
    0x10200305812020b42258500501607011101400d86442644c1d00e242c2c002c0c103a89101c1c0441d0135802040c06442880b95406c005410f440c00d086907a6120040080c0c4030b8500300112080d0700308060307001030340d802040600030300e075220001404a51105c0601d0031100300086500030b540c000c0c4072403400283d0946030342c0c05840707407400012424081d11030084045181c581006103958004240890b0903007000910b2031142204540a000c0b590b82c0e413800b900d075074020210340c000003601d455104c40490610b400c00c603600703411031007207441d01c007090083c4884061080d0440d052002c250b4809040040211461710741083c8200c603c3c516061501058a541d4202c468040d82840440c82c00003500c1c44c80305010142401b005000d90b03035240e03401d10040406008038188540803c0c903081c081000c5000000f1403418451000806925200701e640802c02c03c080303512101e06000142d00000300300c98842607246d0080403019200d00000080400070400c86145582006c0204841400114619500056011160705a01c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 558434631 1250 558433381 558433433
    0x618300c0312311101180b0715020715090201050d180209070302030c07140703060905030307110708070303050310090c090305062d06190b0706060914010302091f03032a 74
    0xf40140c0b280c203180061070204121b0040c0002d51508890300512406220301e8038181180e0a800300c0000703d0140c22001b92100c0e1110142e200000030f00d1380711540c401d0050410341c1c11700d100200448182c0754a0324401540e002d00c0507122046040a01c14250000143c0c00d095007503141c401005e2905000380e2a02030301c03901e503216422864200c24000c40b03003e1500400284296401c2d070070035503540da009a404200103007a209250b401c030600840c1c1502070701c4801020b44038552440d1800c03101c0b9000900542c03115a0034480001c0d0190384c900c03c841006003152101c074001481c50800e6070805000408061108000d0700c15003510444004802c0ba100c0940684600c4545500000c500220f01d4825459206040c2c1038020603880d100d5009000080e12440c1c0074065a03885030800030580394440706945c06070440030014030040c41c00b0b0030303040d42c404103003a00981c202c3c581048400b003290160340300760040b91504540700200702045c00540301d100c100202c0c0303824140117a82d54034072001c40c1c40399403094a103c035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 558435881 1250 558434631 558434663
    0x20011506080a0621080706020a050c19051e010615180914040b1e15030c010c080301150c120f0e03010911060f09040603050618300c031231 61
    0x7542500c80070b42c1c0119003192114402c82c00072b4207a6000381c2101c000ca2180810b50007940b4801c000c04420725521101500002e08541a0314540f850081d50500350b0b552900c00228102c800b51080a0090300035546410f8a0b42102200c408401c1140c0c02442105090041881c0f0009140c0039440e00140c0c00f017101c240c550b4a40203d10396002d20140c44c0105c0201140c1030000a082ca102c0c0c0c1c02100404070251154600e102c4015501c440200c503004000b40c0b07050004001606440c00713200c6071424982004550b02642c1c4d9102d0a010100641c1440130841801e400001e860744013240c40c182401c1a00200a080c1040c2c888414071642e90b005148101000108502c0e0340d01d8410030f550038410098800d0100c507803070789070968591000302c40c52424404d0b016a5000d040c28005441045034002602c4500081010074042c031036201d01503039440b101c2804000f20140c03d003040009040ea0450701624081500381408100b824035a00e00784110f184950140400c034140700c61591814590740320301c4445100000e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 558437131 1250 558435881 558435893
    0xb070c120c03090b030405160815060d0f050d020102120709030f0b0601050c010609050a0e070f0b0f12090313061d010e030705090c0315150a20011506080a0621 70
    0x1603070004c84031048040b080c401008000104106400844603490100c55160740340c25985803580c83c0700540e400e440b240421141c1c01e01e175050007001c0780542104030401c2040c0c1c0340c1c2c9240040788004040140e600007002483d60000158454101f00149019003916207552500c030b0344030707900303c42c043d0060a601d008a500caa00035411900508800d500032722980b41c2e42c0108400400080351a40051820a000009513020106195040e51400d0080c02255418080148800d400c01001c840c40700e441000000c00300001d403ea45407040020030b005507660400b0a403c0404040903501c40018880c425000400000780d54007140e803509001c1c6090256070009200003868034680d40d00042c1c10030b44640a21051013207403001180700704000b01c0500001040b00040c083c0c003044004458141d81d0041c440190214882c0d510280d503811581d10340d1003015086082c044c00c4442040e00120003448034072042000c5a003240606030300240000c0c0070005103203081f030000744406401d0402940140550707424005c02c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 558438381 1250 558437131 558437147
    0x2070608011503200c01050606030f071b200120031b0c1009031b0f090f0b04050f07030c03020408071e080307061406030a0f0210031d0303040b070c120c03 68
    0x700301000a001501c40d02c4c0044180c0c1c040c3c2c00743d00c03240d400e200020710f40c6d046c402c1c00c49000d00400e000060881c2da078403200720380c42d100c03070105070003801044c46004001c1b8020100e1142091000c0c54030418070480c440000d080e21000d518011049d5060180741c01c2c0d401004825100710982d00c88451510800010710541030032242c442041e4011001130000710b44a80c0801c2c000d09a0b84203e003030900000105160702014903007031041c80d0410144110900070460142c210340c0e03070390800110100e501007007c000541554000c50b51140180300c0c04007000640c0e58903014080d44242603090440c0b503d402c20b0300907a1500c50f18043e41c5600c45d42039140c20201724181a002000f8142a0b043d603481d034004d8902640500b0b92804406000f401c14804038503031b4034011600541d07565200c050310030602c0c0d4031f500f8130840c9041480403d06143c1e459148044c20a52140a0b10a01d9000005142d13245010b140044c098100030348440c0400604031408000629105d0344030005000508040e940b100140c41e040320360300707 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 558439631 1250 558438381 558438401
    0x50a0b090a0e070f300b04150906141501050405090c071b080c01020705100203030a0f060b0d0506091806010306150b040324020a0e0d05190506040c0602070608011503 73
    0x1c008504006803601752a01801c8011141c12003071805d9008004806908044070130001c2c1050381307180041800528009280848100150b402040140458031020229240740a21403400075038142005100c00110550342d10520090a01c5402c090070b01001c40d00e4074000074040c148110000900009000804d00c41100203a00e6585015070300d0b0715a54000d840340a42c81409005d0b1003401c40110703030781c98052003200c400c4000e40d0080d41940d851000750000b501b0341e041c050007042d599400201d08840d505000f0000382c0d01d1141d011542c2c0c00d20600380b11a0040c010030b581c1002402c000664084000891500c0c11290882c00115540d0450540b45090144581c80614100c1000400000304181044200b0052071111101510541e40d00d5446081c0e100f00701031500011152050701c0720354a401d490659085008604a4a42c55140100c0701207810a4800550365507000504100c10001042041800740050348050588645003540c081d01480c018040c1007514040c03150084900c0b03204e9489500d2036 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 558440881 1250 558439631 558439649
    0x60905010507020a1502072d0803010f061814010c140105340e04020f040332030f120411150c1501031101080702120301031203050a0b090a0e07 63
    0xb424070344006540c07042405000c82d00400b1400440c4d0074842c0501c04c0d40d0441750418280096035104414100c80d0105001498051003c01c060358408106500061030180044c1500b204c20181045005440490104100000008004001e11070981402c120351f058690a08100c0c091801d1450820800f031050b02e05624107610f09400c1110b200f81c403000a244480c1074410b100106803a144010490100245002c004507055511400c110708042c1e005010521641c01002d080c41c1e200e686030602d0362030214281c0c521840300c060b80103001c100641d140070103a00d113000031450400e21120307846460007020040d03a1800c401d0130005003070120389072413130091030401007131101c8514180801c958150803000040c5154860414010342c4c2c1d00166504a0590b030300945c0480b2908400c1c401101c0c00c0d10001c140504500078070010450081d04540a03502841c8528066060b401c103149004003107500041c2103c003800c0c10071a15044070317190314000c55008081c103c40411051003a90069241282950111405e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 558442131 1250 558440881 558440891
    0x3120a030522050a14030901020a1104140109060501020c0612012108070b040c050324040c05030d030b010212270a150522032409060627050903120406090501 69
    0x20000042035404d039203480740350743e10400c58014901c070707542e03010b041d00850150744072030381c0d00010405200c5108903c2d1001030000c5150800b400d005400180300380c0c00281040c1d2101c800703011030b6030140010040000b060300c00714105060302501c05480342040c403520004080c4c1103042846002119100d00415820065541d52131585207400c502842c41240d0554015020032004104c61801040b507a09a418040d50030150100765915650020b2016000710391401c0a6100003403580c0b814003001c0c4000c205e070f4400041c200c08000c00a4107140f200383e043c0c0241001001a029506a4251048951200054405002640c00c000f14010f8040364102000d0203019169070009542c0c004010810104c51181c52000030508100014610949000040c401c52014226141403120324201860711032070b803000400d403542c19840e80801c482c2030b904291503004d414184190044d81680c03080c0d894540202d41008945040f082e140c0c0c80f80101442080120040700110f401c0c0440780d0001c000054116000b008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 558443381 1250 558442131 558442133
    0x3060308040e040b0a050112060b0a1505040f08150114030c1507050c0409050a1506030b0109020d0c090510110102070c141f05030a051906090c030b03120a030522 71
    0x524108980c1160032501c1c50000170303050552801040d04943da807030307010202c81c10103aa9503005004121a01a0050094000041c0d40700041000c0c950841e82d03034864503961818450395441518060f000f080e815484401402020144040018115201c0002d4030701011000d0700028144031203183c0d455800480104072116502c417241c01805414440c2040718040c400c1c08080c80140e4000117800b40681d040521408041100c0610490583d100b560002941d02d071640e0b00c09880304404c3c0c0220000c698040b6030404c00d064607200c1c030011318649092100d0114500b80000354881c3c5442d150b80200070f140c0b4007644441c6803d405a40b10903500281e40c280c45030b01d5640f0f800b0740c82c00300309074248100c90f41c40d40b00c00f02c90201c0e084410000e456941d51031035545c0c0c818400c005000003070106026004200c10000c400c07000c0341b007488081c00205030041844a210500142034981c40d405452003500280d00e1920340349805401c9610b200502d05011507550f03540820803050303c0d004e190600070f180701890400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 558444631 1250 558443381 558443399
    0x103020c060f090d1404030204050c040e0a05040c061706060c031309020a03060b1305090709080109140d3207050a050705010f030902030c041e06060810050405160f0306030804 77
    0xb91141c40e03210101c0f07010304580c150450b154801d1169001e0758540400091016050640005901100c8002e0851505648d07292068000e1000c4901088407076844050004004204001c1c500030500352806c0d441448161100280894019260600c50b400004001c140c0040510540d03d02103044403080d440644c2c1c0d078402d040a5400401c0d4100040d02d0600c0100d02001c60806440d007210404441540c000d0a050a000e0b06200244c00e400a00501b200002120301e4240980510544142d0000c001c41040d01981e0b482c00794600308070420b018003010030400c1c0040740301c901c228a200342c000c104c0d45071400300c0103440d651150310400740450003040440e50a00500150000460780d00781d0304d20b40b500c40301000481c110b41d0038110003036040c1c015100003082032825400904011302d40ea4140301c19401e00c5400441214011790128011030884c004001c0c2008040c0082030007090265420310442c0b91644622844c643e13a8511041409007491000c01c10303030711070782c810310140d60702c51001769031191203034126 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 558445881 1250 558444631 558444661
    0x3b0406090c0e12060903041404020f030a09020a0e0712021b0f0d1202040b0a030b0102072601050112080a0f020a02090a0b12010614060708090a0e1b0c1203060103020c06 74
    0x5016100c40c50f10302c030b0720500c00a2407511501001c0055420700c0e044c00442c85214601c400001d500c41d40900c400e0200602c604015809034004a100013200c100c188148041c20130154403400718901c030142002f54886c1c00c245010420608280d00594400c1540c86021003a102c061006101e48112101403861002c0000e4016106903e5150507606c1044010707108140d1003035000710301c4903030424401d2106082c040d8000c210000f41c140181c1d0080364a9103004c41c400003d050070b4030303c0022030101d10b05a1a1081c841c041c09041c091b0b0b159040301c8460741310b03500981311f80c48001d404c004c81c264150500d6442401200f110f40d50080000d500781c2084401800603098055400d4071130900060001d100d410305110340011550082800384d607201c0a4410800075803c9a14241d584440c200612121a5a281204009047e141d01141000d081016504031002001d944e6683c014808100344403074110005440e401106205078078a0341c954031500120301a0099080382c2c1c03070520a0718180000e0342d05100c03074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 558447131 1250 558445881 558445907
    0x5160503210907080a03121d0c04061208190c06020a090303080f07020d36060201060605040807050904060216060902150a05040b030901060308040e0402013b0406090c 73
    0x1c4070060780c6a9040c101d031503840ca4421800658400a011030000b4001c0e040451000c242840001d4404180040716004400741015660b941c0c002c0070341c8015910b881e2003401e02400141c03825402c440e2455541400038443c102c1c1002c811084120343d40b40b80b0b44a0045203c401e03500007010f64584141d46000307820b00c0c1050104401107001c030f8002415444039400c0040c418400d0754001c0080e8290940c090301c0004002202004803040314540288164006820502c1e0284003840701d420b46140c06802403c4a506400c81d00c10480d0400c410407500c080081c080c0250f030300850f00803005403180d18181c0e0091003850b19000400440e840d900e414412158080c1d00301c0c0d0b0090302c040f0781001b4142e04a032050311811180e000400c2c4107010034451304900501950b8420710fa6000010142d440c0c0d01d8a2119030803aa00160896500004000440d6032104038500d02c038440b1214401c490020316103a210358000c4045801d8245005140540150b0303460300590300a0801c08010400040e110340001d0010080780c039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 558448381 1250 558447131 558447187
    0x906050105061810030e0307030207140a05030a03030b0a12061e0527031b0f120702090c031b04170105060a030b130f1b0302030f0c06040605160503 65
    0x1064248003044070352050310080f00035810880c40b0300300310300c0c8680c0d110803104241d40c811610314248400c00c01400d4030f900980040c01c56518141180701001d203a821694002c0004103002c000d941c070005121041d290785401c001c258008007101144400a495200e2100fa08800010724103100a9070301003090002250b412901e0220f8210662094500c00d8981d903420030480c42c211900030142c02c0c412048002e40100b6603103800c5071541c040ba00303010310205406403a042004541040c081c1001683c4006010300c0b81c2a0030300d6000d030002100365100802030030340d5190010000d81c2080501c06e98040b61511209105d440310749421110380c0060105c25032103899071038207021481a02c1c0002d01541281d03407140c0c041007d50354a01d5a0a00d490a002c000c4a00d45046071148000880c031201b504444584e900403541e070540b440c0105032801d005420b480b0100c1e0066022004035850b40780c03c80313054520340c0c208195611542d00941000e4030f5040300c05402c601010802038010710160352642c2113180c14507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 558449631 1250 558448381 558448391
    0x603060302040507080f011502071212110c030706030b040f1505010f0806150c0a0f03021b090f010b09030a020a0b0d1104080706031802040c02070503100c0c021306030f03030906 78
    0x1610140000e0f46d00d03410a803202401000007000540c01004100414815030f4241e6540344003060340c04082000482c1d112591400b048506a801030900c11034088a80003004031042c80808070fa2150312784e0141d4000c164072580b00c01d8241d100e541294003880c0c4000d504114449006041c0c800390b8615000700380c00207407c10b420b005841d100320705050041c04020602c2d23400c0c41c1e9000040c100380c0e03c80d60619403640280c40d40200403503075040698409601a0f009000d240c0512040c44072100020000c041c801d8101100f0322422002641d4424195100060041e9a450721840020720301000003070029407100c002100810240d501c40040d0015400c03600051044060004009400d401140a0100950300060040010512981000c20504540c54100c00c0854454022600b655001150400560701c51401000942800c011003080002c0c100010441e00d01d40700e100410200300c03007202a00c20400c2050601d94400280d0003d03009540c40041c07401c00560342c0c603024002e0203505a081d5101c81ca05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 558450881 1250 558449631 558449641
    0x10e0603072a0312020307090f080616050f09090c13031a01050a081903030914060f070203090f010c080c0613170304020604090f090c120507080106081c110706030603020405 76
    0x2006800b81a207605803246103c01e145902010001d400c024200e40400c0386481d800036800c43c10110200184c0405009480146040030356090011003200c0f4071020000c0c10401c1c002c125558100b51144004211205a8941c0310a0707034001442c001d00c8940d180040ca4170b4400000c00c40c07198000d50062609102804040ea03070740b0b007040811030481c0700d0f1484039008007442c03c02900d0307040801e440c154428180010b03140d1442d1100361905110b00b1310350b0400e030302200620040140c3d00c055240e2000051006601e0040b400010402d14102d0280040c10702010240c004104041203054032219182101100d440e458880c000e00c04250031440c046e1091094110480500389504084038441c98000d04018600391509009000401910014860302a0341c2c030803010028249030040c100a187c0c00103220006482c80c02c0160a002c20340e40b015015078900384007000b000c100403c5490000f003254601314400900d00300190740301844070907100007500407a900800c80540651002054034025941080701e5a10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 558452131 1250 558450881 558450947
    0xd09150c0e012a03050c07031a091905100e0a121808070b1e071502090f09060a1208040e1603141014120303011415070b0a0902010e060307 61
    0x41e20f00310283c000d098445000220340520010b100301180501141c05c9560b90f5140c1c12031181a031084101c13003103100317070a11441c110304020280182c2000f0030074607070303d59181d40c0d2a40d6076a41100744810032a05c40d8100424010f060240302c0c11f00750451070104040a40d62002014100524040744417581104404280d00c036000403101c00303451203500d000c0c0ca0485092950a07040004000a042c51031041145400246410054181c245c64400000d610744952008001441002c031000c1401107402d04200902c80c4e0b140c0c0c140d60121800c0300718640301b4820500303051645100319080500b00d0900201031002400010420070045e112969042002c20700400310100350040558803018000515542400100900031303d00910910081000c0c0c0039000004519095401c00d0703111807641a486c0d001c200c0c1609251102d030140c400c0d1800c101e4544003850740c0c1c22040314005000c4100030344ea960218411640900d80348205900c00400030340c3c6034508020000d003600007041140108402d030401e0b0240305c0b81 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 558453237 1106 558452131 558452177
    0x15083702120d0f02012d0b150304061104080c010e0613090501050f010203070f0321090f0203010e0706143103060e030a050d09150c0e01 60
    0x1c140c00a8000d4400e1400c0f02c0a59040c802ca403c0d03281c140b00c2140107103240304244060340e24440c281303800080c1201c0a285401909a150701104440315034095449248180418002013580c010102040e025034810707503407142d0085e0300e0342a00350300aa1700c004036500301805142c00d0001200c04c00603035100a501031a25a07940b240103002c0ea0030403800c0030780c401c0406c1c0029441e102d201c2d620404090000180a41000005030801080301d660a68480390100701000910507511706080150a08240343d108a1281d071030f00c007034041c5404010460404640d4142c035200c007165510078441002d40c0c8001655100000c00f071078000c20b007607030105004038080307008a4180d010905501c0c08070f08a410781c44c901815640144504115541c7c041c04603002e188036a0800f00e00c01031035182c41e030002401c80321902c1205040080c44103446034040b142000381e1034240daa4640001c0c20708800d20b2598 = true := by decide +kernel

theorem cover : BRFrame.Cov 558273381 558453237 := by
  have h0 := BRFrame.cov_init 558273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 558273381 ≤ n) (h2 : n < 558453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
