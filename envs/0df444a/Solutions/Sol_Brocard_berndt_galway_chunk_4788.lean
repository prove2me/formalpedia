-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4788
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:43:49.493027+00:00
-- url     : https://prove2.me/submissions/580d5963-333c-4433-be1f-0f05c8480008

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 860971223 ≤ n < 861151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 860972473 1250 860971223 860971261
    0x917121b04060c0312020c0712120f08010918060f09060506310209030a06090b0703050f06190306110a02060708091c023918161103070b 60
    0x10340080005224880e0b00c41242c8944943c076050000b2250864280d0794082d00808071303650101c2c85041c40000300c41c01410700402c805405606c90340c00300900502c0803240501d424514001140d090750042022403000d501c0b0040300038039003106124100007170390703444240c1d014611420111070300e4181041c18404a48900d44d008581141c401c0030328403801103149845107400a01410032219290010318071411174044502c810401419103c8038401464000c008000c1510140d860300c0181000842c50790080c07050074010450b01840c09440c0c0c2c0c807401040303001926031030010b07032458010000000042d41d50041003042e842e0308030075a413035160800e0000e00e0f0101c0281040304000b2010240400407c0c04501d0b9248420840c0039096840ca4103803090745010b0034040d1080008030750b02036210141c60145510320007070703000702c4219021000050400c00201584030151a002100c44d01142410303443d1019100c410303a513401c20f00342c120302141800f400c5400001c030585032603005070200700c5100c0e0305198030380b24 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 860973723 1250 860972473 860972521
    0x30e0a090b0a170f0a0c0e010e07020c0f030703020334180203060a1503050118020c070e061c05030304020312390a0309150e13091712 59
    0x2503101200042d4450200d22a25101c1e041040320500003001c1480b5100941c0e01c0b00003211440e01540c41c3c02040c03050203201d0300c10000d40300720020611103070f020b0b0410300818059004010a01e4110704201c0c1c040180b00c01e4550505c10700000100584051000c04550420803696561004220043c0344010856012050429241c070b4030a100c024031804400100407030800c00180c40e90b481c000032680b84403140d00403021403205000046503031641604002d05940c43c81041c00c0c0c00c18406103898050b80541400c8181e1500407c5040c40205000340c001a80510018a2110310140444030848200301e41032050320303d50000004c010550a08000c12310f5511801e40e01245881260040f0482003116000c160000500024142e050700c8502e0445d20207925281c3d0a41d140048a803402400c0c2014511801040d046103002188000340260034407038041030007504490b441885052084000c0850b0b0034203c620301c084403011601000004046d050a07a0494000c54403030422034180840d803c80902c110701 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 860974973 1250 860973723 860973731
    0x71e0c020a15020d0309020a0914060109050a2610022d0702011202090424060305060d02060a11071203050c0c090103331b1403070e06091804030e0a09 66
    0x2c46540090f0b04c03480708003540340c00181c14215100240e040c508035800552000c0c00c22203400c203800044031184c0e0041c1c1e4246c03521854540d0ba50f041c000101038601c0395081c031031504140d2000c00b6404200e02001c2440c1c6005490801c80c1c40c000030000c0b41c100350200d4200a50583d45da10540202190135411201004801424030130f891b40001c2034180245901320342d00380c002c40e0265480e265034001400c01c1889141215031412200c00359000010984141c400281c1004003044444c100320000115072600a4041c1e031910042d2001070b40c085041c541c059607240310f6101b0029890b072500700d007149924420356030b040d178409a40414a1a049205501601c582e44080042002808040d1070f01d0f16242c0b0448130b080d28145515a0005140e03000100b864014144480c20007a003104c418a80d0312244a9180c4c3c020b8080c00c03060480c00c1c0d01044482c240030920100302e05034186804005022108402442c0c0c1031428801040301d5081001070707400f1404507107a120300c80300380c3c94030030b808802074440c0c02c1d4104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 860976223 1250 860974973 860975009
    0x606030d05120c0733060b03010b0315030f030c0336150403021908190506040204200711011d03060f070c020307080307051e0a0b071e0c020a 62
    0xe24240c1000d40b10083c0c410300050b150702040300c0c3c05180907000c44100607040c051405101c211854211452140504a1400b24081801c60411040d00d060304c90040315103013180d988100c9040581d190804c00c1e50305108443c3c03040c550311410030081a00084550155844035002c4034141d0601240398604880a44924241daa01e18244c02c4041480d0030219000380d00c4071400710705840c0174071031900040d4003c046107101a82c0c07880ba070100789040f80c1020080740d61441701403000144086942d180106141c02100120340903145c240c011100105100301d03000d450601c04145100c090b8801e41c02141c146440c074001090035070f0004003c20140c603090012001000380c482c0081e445440c0280160b0003030348610080f0b03a003c0d1142d600c01c041558081c085a42d9662501a40381d504d030400301c4105e0341485804802c40042d200102010019a1170b00300625542c880e0356a400010200101103a0401c1058401045085811044802d14142c9900e40a2a0807042d006000b4510596001981c41ca54019801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 860977473 1250 860976223 860976247
    0x807050d03090f061a04060b0c0d0306030f110604181a0312041e03020406080604050c04060509070309020f030601091515090501050a03140412120501081209010516050606030d05 78
    0x150505652240c000284009a01810840324020964013500245000e00102c0c2400170a002400b111149c0400c80d9104080e014044043c0d070403e0100402c007451303409401000a1103070207241d05224006080508064441c0d00210705001d40844600c0e110740c80b00510300300407484c3e8005040b140300c20b034007a15868080c400300010501c00d51207252405460f10b030886480021100b03e6002540d402001842426510505641e03103d00030346068030107000d08966010f451900d84102c4040703480203000340f8680d5076010350941c01001500b20507138000380303400f801d500e01d03540900c5441e0181010381d1001981948401950480f042c07d6005101e07840343c07450040c102141c20010000c12070310300346085131303844400305000c8000d00606010910114904014001084000c030003a1070604025901d190340102481d130100c05855082c402d20140340c1118007481004d18400c001000d8104040c10100c0c601000c0c10318002c12616001002d03165034021005000c00e9250501000c901d020031fa14180e824040c442400f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 860978723 1250 860977473 860977493
    0x80f092a220f20130b0706050f0112050c01050309030d0f0515040b03032b0207061409033f0103110117011a03131b0501030c09030b0a02030c1201030807050d0309 71
    0xb071246000000c0340d91510410b007410f8180180068130b6025440701e00c2c615014000c0d10342680c0040c003040d5109c0010a07840341c20904004280c3d0440c00608005001380c0041daa143c2c0043c240d14824081003110308031480b0a030040900309000380c0800540c6107010040d00010307a131000012032003103040c03684849095400005417006280c2ea01c49081c11900007240540018100c4400c004245001007030305000d1140651001103182080b014001c41c0d80d99030084540c80348101d4000e003100d00d0503c000140b01c19a82441072001c280840000d001c484080c2ca86a894450240d00456030b07002604002085941c0c048101003010122078918403103941428038800d1900304440140840302c0c8080005101c4c080750500600c0788035048058851021030010101d10120304a015550200713040848181407288620f01010480e500402c01041c19116400c0c0341020b94406819500580f200b4004080c001901320b004034021445030785015a502c52a150003814000c200c658001410725160442d0040fa00c0288 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 860979973 1250 860978723 860978771
    0x30f0f071a0421020d06021306050921121305030c0103020f030a0c05090402070b0f060111100f0908040602150c03010f03110d12020d080f092a220f 65
    0x154541c8500d442d1012090043d00d050042d501000182c808401d000300e903030090404003114080c0c40360094903000181c607a4410621029040303172154910141280304143c14140448609003a210b54520321051140301e9003002c0b0f441842000907002c04c0010345020494602d40900a003004e40c1040f41020616080b4040140003005035901c656618442500c61000c0310002c01d00100119120300b114104699049800c8a181201e0045180403608545c090400d001c80800d0900c002c01083c46015140d01c0070304032500300151181d440d0500c800000300c101e0040c1015000ea50b00421186000080c1c442900002514410b0b00c0c86007000140582c1c1003503a854010349070030070340d83d911801460000c03501c0c0400180300546503003414075108180d241d011030a00340840c100c6c0c0e01c0e11000c0d200d0041c0d040c9800c01c1980c01c2c18013a4003001c101c510590305224078400a210001c3d005402598803c0452032444101c000015520b0004001c4080304202d03103d01d004c5603607155070420440c1455110b111900c04514 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 860981223 1250 860979973 860979989
    0x1090f0803040c03210206060904080a1404030f03020f06010b0a140f0d0e010507020c010815090c0c100f0c0e1809071a0a0f020a05150411030f0f071a04 67
    0x1401e000d03c0494540003541d1008404c1358070440c1c066200f0072200300c0d25610703005004080c0030446902c0c007803400c640034540000344280350411141c002c1d11594404c40b49001101c1e030600000000c5101c0500a440c15406a0003405070f06806180311801c0080503040000c918501740074454a0680c041c43e0808415013080909560301c008252002042c01425a01c481c0b85040481e540704900e01074018600411041c0c0880f113030441c45030015140180d0858401c9455650346e01111074901c1c08454840d0070102400e01180f40650030041c0900789850340c03072195040b6880b641c040040031418840c12104295620f0b001c5040c6120000082c04c2110380041c0a51034180100412380ba00c0b0705014000c000c0150707009a440160480700405079a8100a910b00045824051203a1039140080342c0580702c0e03035124002d010b2446a062420200341000ba20607264191034481c02c501c03d89081001034903030b0760300c50010b12415480d5240d40d440c0090940004195404104118000349550340076901624010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 860982473 1250 860981223 860981227
    0x180d0305070908010f0f11090d0b130503040e2505091905030a03180f0812030a0b040e25050a061101020c0607090801110406050f0c0a1203060e0901090f08 68
    0x100c1c808032911803081d0482402c40d440c01d0290036142040d54024403020500b21010700264141308041c07181c2d405004800350704500841400e00001c6c402420050340403801140d4040d140145803a8140b854109800c442c0c0f1084c9482c05000c41c3c4a44016003485024002d041c4203085454044000c0440c020341d10020302829580f140f4012071842c0818010103004050111103171000941130080c070b0900c054030b26104021a11002041200100070721a0966007100d000b00f40600d0030551000f61940020310b060101c1d951056800c101e0b6655000b924003544e15000106580007510442001f4120411040744406100f00010000b0303444e054403207001c40c0c0290404440c82821190014064883c0c8aa402d03038034050074042280d030941101d0194180c5819400821402841e14002c0d1540d20aa00800010a50600011f810717114a13400402c0d13141601400d503449512160703642c01087c1100362501c00803c0c0c5600303040c070500158562041d07222990900034021513019440f08440046d810070f02421080b00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 860983723 1250 860982473 860982481
    0x230403020118080f010218030703050c220606120e0105061012020f0a0f0f0c0809040504060f050f061309021f05040f0b0a08010e0403090509070210050f060306180d0305 74
    0x21442c1040e0003030040505540704185100b10440c000d40c0711203203641e003000d03075120040310b0b41c00c3c002400400d0700d03481f80040280395041390401294078580b11400d00d08030041d0419490382041401600c2c014110f42e1140946c2c0805140c4600030b03640f05505145050380760104200c02d9984508801504007020300b015011191141c3d5803102a105032071102e100440005800394010341d200b14090701c400c1e003650728006401c00b5040b04036910742c02d00b100034012100c18426041986440e074000d60300548500b10008000a07100540b00c1902c034200d40d22103e1807042401c110090411891203010394000f903004201003c2154006901d900b001c0020410000207401c0c1c42160900840c1103501510744c1c000003000e6280e640c03494103034552002502c5e50000c1c45d90000001c04518545d0001e014071703031540b074014240b0b04100a01007d8403004183d4011481100085914200203100d440e00500d03504c0c0c4000140e01c0c202c814107180090107000000b01d10b152011800100ca0007103070120320001d2038503005c942c0342c079 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 860984973 1250 860983723 860983757
    0x324090b130e0c0306091203010605090a050d050d0e0301090302030301120c051207050102010606141905160825210207030b07080f0105041b112104062304030201 71
    0x82144140701c1407407925039202c4000310002680842020110105d400303d98a07460b0071615064101e404844928003840180495801480035015102026020320213260752200003503a0710b038525000792069041089850b04460744078165031400c03071301940240400d10050360002d682c3d220501ca040a50685050707807408006a0780300c0c0c0c00003400c004010380004807003a4035943e280d41d000c1c411180598039001c40000d2003070041c0c0c1040030b140340c9000d443e410000b032010403070744880c004080750081150410113455403c0c1c40c0c100c90130b03845000302107140d25007031704628888040c2e49540501020349260003540d8005440c1000303800210401c00d84a0711500f8043c8070617403800d281c47c4c1000780403200c031008110a0662180c68240b10303170001541d087c007590f43e800501003224510083c80130600000030030301c21064000c01001d005030402804603142614016051160b240070001e5203110b4610000e0108940e66011100c68822000000d140070350281d030b44ea48a000e84583e10000303052010310464005840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 860986223 1250 860984973 860984989
    0x706090c0e0c0c0f06010f0b09040f1d0106051912060e190308070c05030a030e030d060303170702031813180311070b0c0a06020309030d090f030324090b 67
    0x3214140e6101c450800100310361032500202001d0900e44600000201880000507890f8121400d11506040c2d45080400d201c01c1c1d40d20a003182908642c03510290002c80c0020320424030201e0001d0307850b1b0f180c0c030001c4000c682590900d500c10f62050f10f1a2211040d00c04040518a0459002146004240d5a9840d00b00054004119000481c1c010b10302100e0040040140d412401032203560303001030942d1240000d0300c1c100c100450141442e4401d000402010303020364860803001049078110303814072610642d00002e440941c5c1048002400c12640001c0450b005444144c104010380007850500300303900d41c130a041141c0d00900c40c3c03090110751880308010710f941d80901c260f030864125500340716007941405031100740700402101c16449003140024101d00d40c007080d07440014a14018050046c00c607105e4401039040509041d115000421051508990302e20a07482d901d88030f00008510f4031041d00b0090206d4001312150420084c1185e4101c0801030041407580c29aa4a00000103041000401150001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 860987473 1250 860986223 860986229
    0xf01020f100c110a030e1e030f03070302240c07060e03030a1a0d0819021c020d0930060f09050709180c060e130617010f110706090c 58
    0x1c0c0108550380d010151a038112412054140e102c0500d1940da49101542e1030042150150005034a038880000301d24003202d0454096034000c0340301c411110321100207420f120204a43c1c2502e82d1000400d0410190141705240780900201d41b1b40040303e0300c46004010b18400245042043d00d4002617500c10056503900500f40540b1044c00c90780c481c40c01ca42c0003401407841c0381ca0b8142c03000390032a03240090f103095184407205c0e41d84802090b05149910440030624908188401c0c194014581c5040042d85119079801005410f94000d14182070070840151551800e0b403c0510b6091014444922601c0c80d1400003c03007188800c2a84c1e00e002d0241843e90082080d40b220310340741402c000026040c000c00150450544505403002c2001c1c5a01e41c60003001f1542d4500001d20880300000304100c094000c200d8800d049130041c044a2211008081c0031003120001d800044000c0094140ca0809010903c2100103210701c04500308020b00450000d28683d0050307400046c041c6440c1c81783d40b401c0040e00e00d003003001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 860988723 1250 860987473 860987503
    0x9150301080105060102100b01091202060f0724050403171512030d150e1306061503090501380409080f0406020d090f12051504200a0807050f0102 64
    0x4a5071546441c81c0039240c2569150b00600c075080d000d0010780d03107512030611200c1c2c0586542e82c80314030f4441030709420340407401d05a0381301d0018850988605407140080405900c02c0c2c8041d04585c4403407000c907080c112041ca4882006107010100400240c002d40380d40740d0703031400c1403e103141e41c0c1d41c41c901401c200e0003105200c0e0b0403200750f41d00101150300c0003020b0300d008441040d00788098100c178005950110440d01c10b9184400c800c401107402c0c0144150000313419801518049070054a50b40d0751000c3d01d904031550346c002946d41043c003007400028171410140000280e88441790040b6980c1114207440c481d008503001e4030181c580d03007040b41c0c0c856101d27003512a80102001c2c0c0740c5144030400c2859410074450030b000740c010000f145012900c07441003c019290494010380000e4280030543c0881c0a00d00d8048520344100182d480e407000c00706080310300c124800c0008580500c1450011302904d02441045030103115401740a00c4078000c08600e40040d5441503401d41e6850900701700403460038000941ca205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 860989973 1250 860988723 860988727
    0x8030301231f230f07060b12160e0708040b040210020f0604050f010e030c030d090f020d05011e0207020306060423010618060f171005150706140f010b0915 68
    0x4016800a0a018200000f802101410721485a103030034544191210300343d20744010030080000415540c8800c01c4100d01410742c080a829401301503151102c1464140900f005d030072810002e0300381084006d035101246140c050014200342d6502c1c513425a0141009200f0801041c0c2c14400301d10810260400601d0a001c8074018145410725988a40d4a002c41100301d508080c60702c6070701e0100008a904600049005600d0481403031800760040090480072114081c15802c81005a601e0200d040042c80c080c0e40005848411506141c10038200304031406c1c00e440c010700c18040580e4010810645c090402c1c0e0740820103400c4202d1684522844411044001d101d003000800d149601c80520580350940c0350042d608962144000d84000a5165803040043c5111a0101840105d20b07882c603003081f90040d1020105403240d000070600d081d1f030865040c0c1c030075004c22440c0501449000e05040d550050824216506003011050040300c0305000ba14410301000404081360b40724a4134200000420041c299 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 860991223 1250 860989973 860990029
    0x604050a15030f1104090f08030417030901021309050606090d0f02061c060b0f034c0e0115050313050114010e1819020406030506130308010803030123 66
    0xa0303c0b0001d00c44064988401d01c0241e03000a080900c10010150b0f0498020500743c20540d44020b25075100a00c00c66080d0302208864504800c1640603600446518002588941e4140d00c01c6400d1503c40e07000003a010b09040078464241c07030700c50032111110740503100e0f080a900a4200368142c2182090000c0d000040000d03811046507401c0d051900d000c400c14814402155146001800c46c00358142c4562400c1c400c0000c220420820100c03041c001d002c01c19050100310001c82001c207140c000420000c0420b01441800c401a176810903d04003404a002c4034000d5941041000b4150350b41d0f0040010a010000010503240c0c00200040c94030075a0110080c44003004020311221822000e2040303c100c0601000454240b5000c0700c00142905082801000b9501041074403030070301c0a07589404d030380095440b00c2c04070202e2003d02000d48282b400c3c00e02e000c040c8241d40390080250034164000c900c0c1e500188011300410000083d0422600318007038511202c1c0f4050000220501c405200c50021032011440c10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 860992473 1250 860991223 860991233
    0x311031005030d0c1505041a0c251203020a02101e1b120513020a030602040501110d23040b0a033813020f220f0e0604050a1503 56
    0x400c040d91000c0d000d03900030811445098818a0310b03658010a148021984c03403c0c180210340c4a03aa200b401075010035213400031103400d0650150251042240d40400050000c800c002000d0b00c1c6000ca8100141105100c41039141c1c0c840c4001166843d40416400103401d110840c8200000c00d0781c28880e007002c114000000111f01e0b41c00c0340031611890500d043c801c101e0058210440f0303040780c4901d142c65079003410341e05889000041c14000c01002c3c00f00d0071985520050f8a5010103000614403030702d030040e40c407810600050304020ba40d00304080241c0c00a105000075651203062400090101d89a4038040c01241700d2000f00d6018680146407404000700788041c00f5503158005051000f4142034111040c031980700301d2180e420403000c41c1d20703c01c204079aa25003181000c405400e010811040018144180708030b00d44403a9012201000350071920380c20720040c1c14038010b4840d00400c14890401402840c0000080012a00505552043e940c6500181c42c1503400d800420031104000c82c00301c901070300c071303d45 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 860993723 1250 860992473 860992501
    0xf16060c121416020a090225050120130e01032d02060a080a05060a080d0c0203030f03011e05010314010e06030703020306090a03110a080715020409090b09060a0b01140a031103 77
    0x1060344102c604c805c00082e1307200c5510880c1c105210b45142840801e500000c0503000700542c5000300e80c4c40d0740e0746a0110108140a0880411003408008542c0d9040003e1410403214255084000140b8210004100094072079500140224071003450b450b01890402500a60740d1803042d000c2c1d0007503800107070910707030300c0d1b11804a03449420802d074104180e8076100280b1a1102003400740404a03800351118010441c0651621210503100804492509a80901000c001d030420f03401010038040181c44400c0030380144807214043c00e020b10781001011442d95454107c00d00610440e0b440c82c0740c04004c680e05450600c900d034081c0d5000b50840308181080264960380385100c401c00d030001206006241c0c1130000c04140c2c1c0d02e80704c0e0414a21810300010b034551443c4a01c071215030320140d035400c0000052010050080710025030045041d4001407070881c41d0075040039001048210034601d40f130f0107104107a0b000800100400d034040c041c0c2da01c40c41a510f042c0e0040c49008030b07101c1140004000c0213040d1a81d010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 860994973 1250 860993723 860993767
    0x9221703090d0207140d050709090804050310140708060f1002070807140a03240e0a020906060705120307120e0304080106080a1e080405060c0f16060c1214 68
    0x104031802c440c0c04001c01c903110301d00c901907504244240d500c0c4000e01d25040e01c100005034021f40980e001c1c283e40f141c2180480703070404000c440841c0c0118007007201c0d24041c00301002c08294040103001000c4c505018041c18040100404184480040440c0c035949440c0c00101d0081c2c0c0c0030700340520101d0600000303551164a031144150600c1882e03800306d5400700034140e150609002401e4211250300f0f50ba5012125030300081c40b004041645c41c0300250341c2e020f502441c0181007454014051601940c010300200c404001d020a000340c60810a50300050f0300061310050620340500d002d503d0f40c894000884079104039030003c1500f581402c1280010300c0300400140202e882100080103440c0e41d54840d01d0700c0740602c650141c810403540c03456404005004a00c0c640c1680b1a10720030703203800d0300c7e100050025008520340b90010b6000d107425080010040000d00c503c0785942c0503051159103006801080340070541d4004240403a0450640103003030017400d90100c08401403080e41c0d00c44072084c07641030712803a00103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 860996223 1250 860994973 860994991
    0x409050f0108010605100909020307180b0315090118050a181a0a09030503010e25170c191b020301090b0a20220b13030209090c09221703 60
    0x18900103190302d4007014012003c046e41d2120a032851405014800039000285900e06106041542c850300307030005400f410150a203000241e4607424004005044031200d140e00501916503040144604d1480504003000994100b8011034039644050800700500041041c9a0782c03524034850303203400c01214003000c150201d580840d10004d56074107040807064507141c02e00640401e104200500c001e45404030031030341c0405038043d10041d03400300c202151580c0103c2c18100001a41d0440320900f489084440c2540040002c1a2181800c009102c240c010210802d1100d09110f809070540c0d161103141c1c0c01c00038a40f500100200b0501c0080d06040300301002c1254408240c5180426055080c840045041c1d08035408400c19400c0403c6040d110044080166048035a40071304900011903210a071f0042903499200f040c10090240740d4418090900b601070542c280700e130040b181040884c1c40303040ca1164040004411004503585d00030020500c22520003010307003411480010f00000e0349541c00210b00450a030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 860997473 1250 860996223 860996231
    0x3170d0e0303060f0d08040305030f0d0c031a010c02012a0b18072c0702010213120203030306061309020313020f18070302030703020408030705070614070b0112080409050f010801 78
    0x181039010348074403080b80c0d620740c800c400c03a66086003820140c1d05402d240d80708a03589842c0a469407140b03803031038204145081d500500014106c0d003140003401002010403031ba05040c820800c000104014a04901180c2070410080341400c1096a104074150030b181c140400d40280c3c403c5103240320441d050f00d50702c42511280050740100302084900c140c00080071342c4450151068500307007110000b561401b4103909070109619002605541c0c8258242030040c421a00010303515000401c107542c0c103144903401046043c00c0d01344c4000250714007004407a8031840444a440d034403c011484019502c0144d04001d00c210310105c2040030080030305001c8034509000302c80d904864001c0c0010448940d40310101000e20307c0707000300412040c50098001d50740041c00f0b810b002d07003441c2d12202700c42d1840d00950820341d00c9034040c80c0204030050304141c034059941e0468852031315140454491518069040c82100304108100c0c0f00307a028070040c0b9064801074420040c05100c41d041c46040e00599840071300030300501c0d52038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 860998723 1250 860997473 860997491
    0x60f0a3521070615030b0106020a080f0c01090c06030605130c020c0405100801090b1b040602030301061209020405010303030506040b01050a0c02040504020a0803070c090f05150405070903170d 84
    0xe104011000961020040200940301240340e6841c100c04a800c104450701881800d000070b655002d0031541c5007408081507400743c81c5040141d002c14041c0c1c0305600f5504581d0703861000ca014081103400101c00740c0c003c15035a6085034011401011102000b0b40480b0031044045001c507032541020b402c035030703040307071480e40001c1e18000407400c03100c48107a0030001d40c1c0560180521800d043d00400e9002001491415007180c0d01d0300312a003525020901190420540004c00415031b800713102d40e0341e88482d02c030f03049820326017881c070701030340e40e20060007007100b84282072085200d52001070300528030082c1c1c00b0b0030a000e036507580d140146c0a00300545000703105500305120b007102540b244055490410079513031000c42044080c2c007407000074080030340260303002102a10f01040580c0104010851148180403c1c001c55103082811012561100f00c000c000500b4801030000c0c000b1402c01022000c0800c981c0010340741c44803031050750311513000ea000501201038880b40b0305200e00e098010b0040703800c50703050a0102600c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 860999973 1250 860998723 860998799
    0xa0b090f10110414040b060414011106090a0201360302030f060403120b04090c06020c090906011d07020f07060918110f0306120111042c0708060f0a 65
    0xc00c2c1128165058401d00c82000f0000803072548024030310010348006220102a0045807450740b00c0e030442d121059001001c1c3c030003540c0c45158001c0d800000d038060801414810829a104c05104502034100024950a10600b103400c00c41d042c404007a10200308100342c40728106001d07001e01d03031000b079120703011b80703400e8500604010032424030855050342e03407424501608160788018940c5202d401d4101d0303600d11207800002c400d02040b9000c0c002c3c41e00240301c1c4d028502c0401c034403030b0341c01480004141c006078010003480303400c4640d030180c5558145400f590303547c030000120700e008207d0311011440d118100001032501d401c9841c40d8291004003d01082d0f0405000c2c0e1101552a0480b400c0d1280348200016400040e084c000355400a1005240108100b84084083c0c299103170843d901c01d0110000808006007035403d6111344680207002994907214030100c01402440d100241441c0c140310b488000568580d440303900b5042e040c1001010b4203c07080c3c0311030081480300c0500c0100f240c10080c05025159900d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 861001223 1250 860999973 860999981
    0x70606051503071e090e01030c091104060f0806011b0b0106090b12040204020a0e030d110634030608030a02010e0d080108030706020f0d020304050307060b0105210402030a0b090f10 79
    0x2c103040c0c880081441303806003103d018040022000e81003105040b40407540003a2100c01600031401403800c501d58078240301000040302c01111201c002d83c49c003000b0400280350400d0130304e142e00d6000d003043c4030559034510050750b01245280629504c454461011410031001204aa040e80c0e803030394610900a803150080c00c860f2140f003800c0076182662200081c018a080d4000b8410a050740c98040803904140c404a4940315a0b04c0c404004140c1d0316690310000c00b02013103200c3d03000d46500301a076448424201d0010128800c589000022142c0c50081000c45009801a038021319590742100d540d1048035100a009000305080e0501500031080c03000000e80c40f0716440c0d07051b26180c8024600e070000a5464500940c401042e01030400c4003030010210107501403001d1446240101e0182d9500c0505182642c12101961110346c10b00805010036040e09164010301c0800c15580c240c000f0305611103000081ca020a541c0008101c000840108a14900003055401201d808942110354600e1440e01c00d00640b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 861002473 1250 861001223 861001231
    0x2180901110306030c13020d18151b030b0307031707030206060d030504060507060608071205160b030604020a1211040f0e04080a0f110124050105160b0c0f070606051503 74
    0x16610042c160001403609031145d055441040c08014600023890040105a0300040301e00c071400001000c5007400d2246940d2aa031120703403804c00030032646603d807203400701d80c0204070241d20800d80d440080040c15141084800b01858010300280d84090006901a850f40d1101608800500801021500038100604104661a4180c580a00305030904000b11003607001201c060340ca0a488003030000d03905030140b01003805401c01051003920143c103030a21074a490400301492000101114003009000d00c4d1005803500854101e40159076511040003c0b03a02c108200f010055241c03508100d1040307481d065000340222603006600c00b89550b900d01c1d107045484800c40d4050300d004410404120414420070a848885030130303080078503582c01e52401071403c444001d100741c005502a9618100a02a903000c820010034091904070324100403801041d0442c0300044c00204440030520206901e007036210117482d001a0b00342103030354481e8810705180003e0905446114011000c0d400c465614000c6101120300c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 861003723 1250 861002473 861002479
    0x30e03060a02090109090221220c1a09091501050c060a0f1107110d0614090d09140f04090f0213050103060f1107020d051f06080606030307030f08060d02180901110306 73
    0x54010000e0706901248c03c02000d03001020040880c0f8940c44a400c08548095402800c0c07840489007401580d03405e41c0381b10841c80382d256405008403922a03652100c000d500c101d005a10703520134403650006a4040c041e11840801074001c10080007421285e0b54410f140050100e2001c2c402601806950140e502c02c90001a110320b00c1e00c5444030707903401c4c80540c9241980c810b00000a445454600c41c3c0321091090341c4c40c54441d0030103101240c040d030f0302007000d1010300599140904210803460000d40c0d00b0709030440345409a5150b29421041c4144001100d8289030080d01c00e4804601541e02c0f80c006003024001122140d00e018184041a4002e1040000301c140f10a01c0318034043c4107030200094440b40c508111303403c2c81500000b100503c2c003860286901403240304046170305800c04a8103420b00c0310007441030780a40e105000840210340d1107444602a00d2090500f40070300e4884001040c1180c0308020042e403c00c201912080d04101f036205501d00c51407207100200100081e08552075840d03c0b080d91940e074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 861004973 1250 861003723 861003757
    0xc0503040c030b10240306090c021f1103040f120203073513050108010e060a17030c070e0a180206091302160501051008061b0304030e03060a020901090902 68
    0x80094016603c031900081d45001464010b03507030701120018103116581052403055011415601c0c160103000760809091004001c2c4040046240c0c001c0d42e85640c0ca180005200c0708100041c1081060391215012211000c1e013180d0b0391900d41000c003803404000100721290b1011614401050f48040242d41d250b0750301400080318a10840c140e820400302880640300034400c81c3c1c1c0035000f00c03c02c0400500b800541d09580c0c010a91030034002501121059000e10b030003007043d90411100d40e4500b0704000c00d5603040b507042e000800a04030700c24910b0103450700307914061140f0b543c0402e03527024000909101b4502e40320140031444a61150b01c1e1401004e040080d0414028801c0390b4891510f6610183c0c000342e5503c0041c1801a6030005603503280d550343c42555103943d160309106020802c508d0400240510700300410560402c2000e01000440c55406460211404004101003521403160380c540101c0c01011114242445000c00b0001d601c40005680410002a00000c00151a00980d440500d48120401c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 861006223 1250 861004973 861004979
    0x3150c040b1c15081b0904030305090a120201020711040c020d0302030723070209070c05060a110c03030411130c081302010e030a2109150e0112020d0f0c0503040c 71
    0x100300d82c0c0200041841906050001440c0485a441221900c06018042403907003842c000c4001d0a10307040d1780d40c2942c010324646451805898403040160455814580060b24ad560b4810150820444108c01415101e440580041036941500074020140c01040300d64020500c1c2e000300402c841000e0040d4025801040d0403050b054000e9000c2d541c0010399040400300d509040ca6050b0344210400d40d0124503560100e0340d082942003201019501402504004103100b03200d0311816503c610003032081506c42e440d010105007059102064901040d4200c0c22179032607040c80d181001840740c1590b0f01a0007486031403a03a210004d4030303000c0c401c0c0c041c41d6629000810b4a40c42c00d80001108282d07005e905005070500550043c0d05e04110b64000c16000d200042c1d035940c60308900241d0484080c03003203801c000201806010b002042155801040f20604121b2205541840143d0b001d031030054240c00d40610103d864200e400c11500000044120f8502c100b203807000d82c00702540c0d40d0009481c050010b5000300d40c18 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 861007473 1250 861006223 861006239
    0x702130e100c1e020102070b07090501050f0c0c180601020d321905030a0b01090b0a0c0201350906010e010e0a0f0c2705010e1003180b0603150c04 64
    0x41d00488107031400041d040a00001036202a0080700443c005070360000c1d90409100b0325500349604407810349030854500d07140c400000c1180c040d81ba81c0c40c805060018800040703001c10001702000300c1000d01101004080300c03d0042030800c0c2203901c0da000d40261080e95030128400d4801c03001d5480c014914603031004907960b502d041818110a000c6014204008074500100c60241744600d008050740c400c0c1d601d01c1d00003201400e89050050603414001c03500c00900c00345104200303440da008440c0c0380c0054022072a0004030341001141c02d030ba842c030707645213a08a12101400600000d11020241080700a81c482c0080140e454000744200d039040441d85006101882269401c00e412200e40c040101e021500c5800c254101e41840169038045070040e00014003140d10300c881d246001200c890250140c0d4a01400070f80031081c1c5c1581640720b40078802c00540040e002e5400380714910311f03000c0c213880d0340c4e1113910744049141c1042d121184288038100109280d44055800305101e01c1460341c005080514003501c1e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 861008723 1250 861007473 861007481
    0x905090a080c0c150d0f29030106050a0e0405101e020906070c0305010b040c17060d0503070501020c2a0f131409030a14031506090a03120801060e03010204061b0503070b07050702130e10 81
    0x907e652554070f50340b000a06565400d8020040c101040c4006010305141c5840351420688528000310390b4100031140c207120001103400000c400c50414007598408941001401a10a1140041981000f03503408802d109056116802004003501c0c1003102440c00e46d426940c00c1151004400c034031b024800000ca541c00c0040d00c0c10040b0340300741c00b180e0a02c0c505070707140d90985c0c0003594895001d5000c146030b40aa10402041350f010407490301480141c940040c00814444ca80070705400c1d0080d070040380002810b8045900c10350790110754540c28441400c0191180e84c036a400204042d0004040c070703000c8500c0c038004404503801101e000e408040c640a40105012803a00202d1049500c60356280b00000800c883c0c03130030721150303800030b9980103120740c1400ca01810282003040017034002da00c1840180603494000b840c800c45140c0d1141c0c40100c00b51145001480c0d4130954400410820180d001d00940035040406084082c2c03003251071a00003514540610b00f25507111190040551146800a03000715071a40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 861009973 1250 861008723 861008801
    0x140909060f010912060902012312190c08150603060307062a05151b0d0f020403050106060f110c0d02061b0d05070c0905090a080c0c150d0f 61
    0x1850303103c844d503401884120348080d40080d2001e03a142d1180c1030856902011041c1200c000300c1c1c0d0601d07800301f20741d0305000c1030103000307500c0d045444c4020110300004103c3d1202f00f920302400c4000e210300505000020400d02c0c0c01c1d00d116059140c91100d85600d80b9110003174902c0350354050000c0851625000084861070300c1c1080c1203a54034030644403c0983c4031542c45c440b940e24001c400400042c0c02c0801c844980b00c000402d0428401c041c1d200b01c2031a08410821940d906991040c0420440002080c510082c4140e42c0000c18070340c0391190000d107a54000d840f10300c0c0700905850340d00ca0070110481c016203035000c20060661200352040302c0300041c038082014000c0c07140c0c80080c8454a03403406101524102c0040080c20100d00b022403400c04214000d1181005400c5410060026003402e0020795652204082d004000400105032900f038010100031120112000511480c12034421091000c0745602480824047c00c0c1030404549020603540034041105454a480000075003443c0130352500105850 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 861011223 1250 861009973 861009977
    0x2705090a0f0f021509010e150406031a060c0f060a0b010203070314091908010b060c070608090a0503040f180203040f02091905090d0e01110706081b0c0d140909060f01 73
    0x140b503507005038903180c2d451003040d046000c0155a40202c0c0c0c0001d0146042607010a12803010b00e0308070460401c0c00350a40741203d1b86030030081800c00d0f8802c4601c85962021201d1784c5c004002280e5040c00000010304c03036a0f1802e590707066941c41c1d00c0d0780700c40324162500c4ea101540964020045000028403c0710340a4201c0c40c09240745080172000c200044a07800d1030310203a02d0360340350344205118909007031156800d6490112122460401307900341c2c0310784550051140c0000e201410000549a00044c004101e1480d4810142ea45c3c4588610710700081d05c48038090440c6200300c244c00f07411040302c41d208582c011604417000d100a00c0050b0f007080110701d401018110007070300781c2c4028200640c0d07500410340640150341c00780000040c000001491241308100d03650400000c02d48503420702e40d020480805454a501d0b00c118155100d1415422201c100e1700144914440003502010640c000300c0c01d01401d4256030b584480a441254100d140c2d40203420b14142c0c40495a000b10b22240340021009501003018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 861012473 1250 861011223 861011243
    0x405070b1308030d201e09030f03210604020406051e09030a11120307030801090905011b05030f240d060e01061d0a0606081503162705090a0f 62
    0x16a0300c0c9800c54014200304c2004036241e65038452100444998560100140720340103042c110491094645020302140c4900140c400017011025038070213000c0c8004010900d000c8907a600c0c20311009284500b09031a44407023102651001c940d0b00d203024001c407004c560090f0744280c03c0c1b8405442500850b461188094000c940401140c41203440900c500e0078041d0055030300100003040c03001400a8075030888101d003c0d541041000c2400650460002d90543c0c1c0302102c0050705c0c0c002850120300601105080341c080c8604948000c162a5000009500c54400c0710080003090b00d03150740801a40340505441002d188018811000320306010198142050290b640032a1075410000044d007111000c0e082a407105c1414143c111015a0188500c3e821a001c0001000124034000e0300078410b850180504206e5089840c07000040d603410410481d8032000031380d03481c00d070560b6a4815140130092001000208002010b014204039840c800d161080115202914003c4001d948a420340b6440f20f2040b01d602c0b5075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 861013723 1250 861012473 861012479
    0xd1401061d09280e01020a03061e06140717040302100801061b080d1104060f0206040c050607081c1a04090b0c0a090b0d060f14010e1e0603130b0f0405070b13 69
    0x10350069103220080e207000141c2c1c070301d0070031001815188140c110b500103980402c2d480e606103042b10030300401c88030f0303610381000041e4113415207002610510101401540000b070086c03c071914514001c0084a208845c40020b19040720800d0320a001d0912035100410041c0c0181c2d03850441c0f96202008492150110790700d492810381c2014215507443c0300c0c1f00b00248001c00c1c24405982c104101c084104124001480d4a140654038a20700d60102d00031140540004a007240c10080c8880a99282c040b25031903011b0a441c101d0650300080403202007610000c0b89000b210318040c18644581411941c018000e10364990314812803d655510000ca00c108003c000320780011016502d2020b0a040505902c003c55000e10300280c0c2c07504c00c0f426030400044202c5120308804d940c0e0700031915011400e000ea43d4119035248201407030110b05580881660020304c00020000076209481000b01d245108002034191910b6960b0641c1d0456000c03100104a5484818284240c240782c002a00300c40207810348079101591 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 861014973 1250 861013723 861013801
    0x5150a0306180606090c080108070b0d09022707030b0420071a040f05010c09120318050a0e090d030506130f150603021b030307020a15020d1401061d09 66
    0x40a07500402c0003d80e070390811b8004550080b081401481100000d01440781080f0b1031070924480d030120b0007422591651402e0454072400045007005111200546090704c0d014004405501c1c100c4064002030b2a059101c1c00510f031078419010169a06200c200507005169040c581c03950100100751005410072842e10746580c00c0e140c0311481144101301c4820301c811315207401c50a48024010076800d005110300c00740102d44940b46900100e82e01843c040404140750380d50049049210740100d5080001e0000100c3c0340011404607a0288155104032000800c4141045040b5142640c0d00e651011088050070300700820750b008030000302000f01000449000403600d0b148140d2230f543c400d0000c01e4000c50600c60000800000f00c0c0d00142140c042c40c610320344101c009440340c440100040001d2008000342407200404c1c2e0540360140d54040701000042c440c00302d0010305040c02d01c0341000041e82e00d2445a803452110001245002c1c0291aa410b641c4034680145099883d000031156600089501946262 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 861016223 1250 861014973 861014981
    0x27030909060a0302060301272334110a020d0b090f0109030e24091e09010f051c021305070309021f0e01110d05310905150a03061806 58
    0xf11580750050100b41e140a01d051080e501e5061102034a410301e44401c80ca500381303280034050611300c0091126503c042c140c0080303002018101c02c070301c1403078ac640c54660040360507400e002c0e010725210641c0c40e0750303505e03d015942c81400200a411044521007034000a00022400303821200355410f4918820815044600310390b422102540052144a6250b48030b041500c00a1040c507203a50100044032030002410485200d0383c000da038051310240039640c0501051a84500300c1e100010103034401543d642c07a80410b10149401501d10424107041c1c600c1013040550381d00c0385000c1c0d001d0f00821520920030504001040d0040081c0d043c0f54441c00c0c1100103030f6980c5159000d000028000317440c000e1100500a25902001140d18140310346041a00400b003c00600d02c003001d00145070169859610501180c80404059013501012401c0c040c1c07100c1101141d0240e10588100600821280e07881d000c03189405490010301a400c0b003a40c00041c000f06d602c5401005140d11540003255002d082035071448111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 861017473 1250 861016223 861016229
    0x90619020d030608150412020f1c0201140709030602090105070f0b09060709060203070b092b080a020313150b0607050304030b01050111100b130e0627030909060a0302060301 76
    0x40c1c00c045481291260503100e414081d1070103000901c0841c22461000303002d01c8004c0c00240034000c0d15841529201d108118500c9100b0302c0388240ca0900034500811205400e0b00d201c00c8000d94204035000c2d5a4840034034040e882404640c0c1e07040c483e180f854441070003e50102180c0d80c104401089074201145441d000d005140d40b04c0d8150260611300032090604044c00584090200241750b041041165400070035034181c50b800c440013525541312450010b20b0500e080030040708008003000a09103d640e0510707415026101e5482e0012190f41d1009400101e110407100260b000126610000c08501440e901d0f00800700c00150000d031721200c2c94001081600007105c111740da82c2c00018280b00300180300642600518084c02c0002203100550081034039504ca100340818000e030b88803011031140e42c564505030040e082c900e070100010b00c00400d0060711198100c840440402012039004c000b0614840840301809400015606048203801040005100500129405002d400300070016a850314015802 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 861018723 1250 861017473 861017477
    0x10f080702340e01120305090406170313050a060917010e010e100e16032405040309090c02120d0b0d020a0f030213020f04050f010338090108030f090619 67
    0x7281c2c00c0a0407151101d4016001400c03103c6120004102d55845421a00b0016615052a585403419900410000e0449074011001243c915000d03050b800c0c0007000a10208075151130100c0120340b68802d110000c0703841d00c1107000145030b0040810025041500c0030204106c1c21b8000315440499030100c600791800b01503209890f410421a94020360804d20480c4010592170000d40700c41d011094109103004260300c80580340d02c0c8500390382001c0815014402c480041121001c203c00c3c18030341001000100c3d2400f605480318501303007000c0c1c851030002500044450103400400d02d00b0b031003654020080e21040100c5500411070080010059490b50a804041e001e0340070709440c01e500e180100b09110a180d140808201c1c410006a55280c006100310760136140b0039200b0707140800c2c445004900400c1207100c07003040100c06902403101c40c0d0030038a0441c1a1a120b408940003041b5180c1007043c8043d007031103103010507841000081c91040008dc094000c100000f0308540c01c1010302c0300c680600030340d11300c00200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 861019973 1250 861018723 861018793
    0x111061f0e1501110708010609020304020f06120a0e1603122a02011b080c161509030609030912030201060906140f04050a111209010b0f010f080702 65
    0x244081040d009100200504070003281c1c103041401d60000b80e021421401d50400a10140030a403114007045000000c1008400070841c060381e07208600020740050320120701c15030104844940f64a040d4060b07600101841d46210f030152100c19902005050034544042c3c140115101c01e41c0d80a00c0468100045001c0d02c858203e010a02c10010007081c041c00120340003040f000c000030740b031114011100034410350a08084214030341385410115041c2c0c0d0040700500d41c800c000360781596250701184100304506c05045054a540c0c903404000402d821710280400000c8140c01308001003110303900140201d5004c3d08280900300e8031155404617607502130f2003e50150391a100c6c1080105003d11480300180b803181d1403000d1901500300062201c0c500c3c070700c5282c4203d482d0300200b1101c0900d640030b090620300f0303414400d54074111800031002d08072040b208107d5552a000001003036080040c072131108038a0507540c050b1000059041900e01c2c0c10050309000840c4030303412110400c01ca8240e04c920b6000c1c418441c1c42 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 861021223 1250 861019973 861020011
    0x1425062a050c1e2e030f0f090f03090e06011d0607080c1b06120403050d110412050106091b08150d0f0210140a0302160206030a1d01090302030315011106 67
    0x204030600d403040d00820401103201303103443e209400d00f0158400b10185c80c0100d8403804401c1810060440510702c84c48142c40c0054400c20040524003046060380319494090040d45e55980c8400448002c80b00940401c0030303524450491024414141044580148520b00b8001c050304ea0407055004145003101e01c0d444650f201390b125001094034903003114100d44551815110200d0401d41c0100a0002400d002001c5007650207407050b81c00c800c0550b040e9070429512030356618120b6a216405c042c0075500c95107090320100313054480c1d0080040c4c2240401141d80c400302c00070011601980020040c2031319002082c00b000380c0d541c40d00c0c00e210340a401000011034043e801c0c0100700039019114600c50a210038040c68140c44030200e41a00c02d22010f9003001601e81111007041000c0e80710700301000b50b11800000410001c0c3c81581d001145c4080400c0c00d00d11a43c110041440c2220404100540035034420310008101000d1518200301050040c036111040d4107244008a10300801558800005813201d0752034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 861022473 1250 861021223 861021229
    0x80712020c012f040510031d0a0c090c020309060403120c0b010e040b06030c090a050702070306020c030d0e0313120f060507030c0206060f0a0e041425062a050c1e 71
    0x851030f40743e14140a602c0c09240000081c01e120301c20658005068981c40745100802090000ca04240443c0d000e0b2590b56000c0d1410b5034071400503000300d040c5289400ca0070307001c0c148000261000000c02501e154036040c2907484012203a000300c85204100040c021102001075282900c0500074080002410401c0c1418508140f4410006103814000d602030080d04629694207212950014000f81000881e41c540000c00c0f401d11a407904041c0c00540001650910020000014400d0501034a000c121640805403010344034403444042800c80c40d002c0e60b050002030002a4240300040c4920940b04110645580c1d64080d55003c40c2c05001203a6a5203001c0a0a60140480d40d4020411604102440c28401c0001c8141a40c0c0c09481c40d0008240002420041c00c040200c47c0c020110b001c03034006038030000c442e402c5209095500e040e904c1000c040000d0309402030004003402c2a980311401908002c1e6100d80b00f407150640d40688140c895840e01c8046a1264282810f05002c020090380001d8140018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 861023723 1250 861022473 861022541
    0x3060b011211120c0f070c0807050a03120f0e040e030711090112140307020306041214070c0501050901120216020a120b0f070509090c03010302100807080712020c01 72
    0x7042200c941000e00c5074000307103111012103c0401190002d1003541e140c5048200d900e0140c814401800200040c4c100d080c0194a52402e0403200f82e00c007110596600c030b1341400149005d07440000c0a148079508100e414902070070110344011418644030304070490120009007035030000d9420581c160000203208052001050080c204941c0c00e030356405855141c810321203400b82501c200030b0848044154406402c100074021104056002001c07181541490b0800307407820f00d44400803c01159a0301c580200c0000d200f03080d50070494003e21002c160500d03200064603168840e039501c0d4104408180085a07110a9101410000003845070000e5030310418810310034104d1040d00310302c0e481d0900c0040f81001891481c0c0d02c07039100c1c001c1d0782d51410076240c440082d5514010300c0d0183c2d44c440c21050030086503020750006903040700c1c02244d00d80002180e0840a0354042d405560031400101840005120603006228880c00203001240061810704010344481c2120247c5103010040c10059403030134851209d03004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 861024973 1250 861023723 861023747
    0x507030c090c0f120b0d0209040c05090f071b02010e0a03061b1806140d020a020a03080f0f060f030f010608031801020d05160f0210030c030f0614040504080f0403060b01 74
    0x9010151000d0f00101800f10060039540d40c0c0c44503110203420029403500a0440d4440303602800740b03a1581421300c2d00c1c00e040e009030301480d0b00448a07200018807040540301060b00800854941940035209200a101e681d4150103060b8140b1521558100c001c3d216105018000c600411000a08158401111203440916105d0350100700b9442d000802011031150744804841490401640e4000c260140c10340d9400740d14648034000380b0206610746441d8000c9400c003a454826030b6440d82642d10f914a4001100c1d080d01c904011600308070008901e404c0a041000076040020121400000d51070a03032400d5415503004a1280d410201d03580d41420207643c088050000d090002e082d01807031090000303000d8000d54142015a0320001c001c08180400c0343e941d00701403900078045d49095010b07840082c01504041c1c40110020303140040400c0d1001e001d100b210300369044152120b089203000c1003048080c14000d04181c80f1601c0030041200020a5070000b8402140301d103601044600c1401c00140402c500e4007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 861026223 1250 861024973 861024977
    0x10b0102150f090109080703020303040c060804050d0e031e071502010606120c0c080307051305040b010504050405190513050f0105060d061e060b0d0501050301020918130507030c090c 80
    0x42491080104400a075842280c0364031400362030f66410340b07050151408500240850100040c004281940400150701c0740340a001100d040d00c0d5150f8084801e03480031500a0500c3e0829054903510601c200030800d29070000504560701d00031007094842048051a040c1d10440c0d2062904008118424460254180e600e0000304216840e101e07000e40708003d103050b075024850f9241c142c0425a4000d035485000c254100a4140e124900400702070140d40c000d10205e0358010003420001441d1410f8043c00c282d09030706a648505103850b15040c0806081c0203842c4007002a480c1c9448403142c00309100341407252111a0504ea08003072036003070072400c0c2175040c4001032803a410721003082801e45845a0303040e41994802000034003ca1034610800c0450340302c8000b40180350400c840058104404406040300c074003160401c0200303982e0340081508030b02c940e4a01580001402c00d030010820040855181c0c2704d007e0006480c6d0080b84e6aa806081c61555041118a01c1010038244201c840340e10442585440c14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 861027473 1250 861026223 861026233
    0x10c0318050a020904050313140f0a0f051309080c010b130b1503060112050c03091b0d260316090e070c140106090e03072f06091c14010b0102 62
    0x154565a0b1582c140d0200039010343c6660010030304124042080710503148a0441040038a0707100e0100c560310018a600042c803e40090005901c0703494420544421070301c2c0721405101c0549010b051204030840b0700d0f460280c1c60350314143c2c207003c00d01d200010024444041c1c00001c28a0208041107001c014440b03940c02110700e0140f130748442c0e460305020402c05400e8001080c1c0c582c3e03140c3c40103c80342407010359610041400c084c180901041a68080d5002e0b006882c15108001d400c080308484207001209460391001c4041d50400100f01040095005094981c101100f1803d01400189032584242c1b0700e0b07080ca603101440040d03200c0d8002c0340c400c0908030640c4445110304000d10000e02e40404688060800100030f5215860541c0940c440d000400384a003052140c0d401039003485403260040f000981d0341e06038594042d440155030090303060520040c0d011141e2641c501c441489000c0d00075101031500310002080d004000c2c242d201807002807a205101460391a00d0381030219082d114402d1010f8155801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 861028723 1250 861027473 861027521
    0xc02030f13050405010b1204080f091c140a08031504111603180303020a0204050921092812050a0c090902041104140d0f021002061501080c0f2a010c03 66
    0x1d1130454a4220303030008403692300c0307400f180d0074242c1500c141040c1d5a48440740041181781102d43c0c0754080b0f10903000701c5a4dc0c1c03200704c0140c0d04d944c4400c02000000c042034ae08000191283c1c003012120098001c000e000003520015014010f44141e1013a0aa002c0616503801c41c0002c040d4410000d440c90324018804a11b91031552350041c0d13450b140c10740c0086c0700d25240c10010300030304000c1204000d02404e004200d402021494081e014940c00225554003078030400c9100c40203400e01e100c080e4000001440c41e4901c0525040103040c2c041c000034001c907401d003d00035003c00070400320407001c00640b511080c0040c140c0c4807481008211424403078102403045061204001c1c81c040070b07040c41d2220700709592481800489203006441d202c1c035032100035031080c4034048421340c0650021340355210b5800700721b001c540141c848005580e1000100c4440e8180d0904128654900095601501596a60510300032303d2001e81d8004441c0c240084a24030000e039902c02513064071a5240c0210300088208105940038aa0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 861029973 1250 861028723 861028747
    0x506100509040906110301091a090702070b030405010908120610030b13090510050903070c080703051c1107090e0705040203010f0e04020607060c080103141504060c02030f13050405010b 81
    0x1c5160007031060ba565228241800440d4000400201042940d1540d0f90b03159008000186000e1055a01c0301c001c42a10704101c1c109000d103140a41c01c1c81d0006d20700c05240c0400726249500090049500355281c140e1034000078005005400c07245a122102241e0b031410409201125982c80d4000c8205820180c0302011500c8404104d4100540b48001040e43d024a00344145440b500801028034180b5040c10021601d8010001d0014907115000c1081c0c910351b00d109056580f1100d00000e4003940121078580c0c154000114841341c04552400d05034050040c903141e15050401503400a00b10329220103915000a20a20420f0b0240204517801c41c02d55040110b8075100703550342c1c00b607207602140400100f010343d501c950681d021294041c100744590318803070700018a0712400b0f1104880b0350400480d440c01d40301c0003055551042581c00005181d40d078490f2140009401c2020703c040560000300458407024036000300030a20140e5481c40c800303030b15103002c0900c011520160b0150086042c2071240c000035038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 861031223 1250 861029973 861029977
    0x21603110a111005160b0406140114010e0d0b0f0f1602030f090d1704030209061c03080a1104060207030c050103020703020a030815060c0c09071806260f090105061005 73
    0x5054806404410b0f0307030a025500c51203000e00700341c0288894080141001074082c122032141e071140c5028803000e0740c04d010414104000f07000708408070300d5141122a05501c10982c0c0051160000c1c2100d10306e041c10788840d80c04031015101503000442c09020403021a50b000a52500b00000d10341010070106c001600940300d01940680a2902c1070000304140ba80e42c44528200041d5004007402990402400c0b1094903030740103110803409041078100186080c40c0c0b0012a684080c01100311388d542140b2a0313000c0b180c1400040984001aa0300c2003070303001c2091040081d101404007600103204d103070f0545c1041c02c004004c2d54400740c1058010846000084e40c08a600c1025941c035003010102911582c9084544101554455404c140017051940182c1c10000e141c1c051894251240e5145032103404046503120f404c801d0740104081724180411481c0d1058038150003003445004c80d0400400011041c1d0030010b0140d62031464680d4602c2800382c0300360207109040d00004115450780420481020240040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 861032473 1250 861031223 861031253
    0xf0c091b0918090d020d03200c07080304080c0f121207110d060903030b030a0c180e0d08011a090108010e0a0f1d073312021603110a 58
    0x884046490400368403039001145050708010422102c510380380c512541d1315150b00e522540144196540070341c0c0540a44154100b521606d0242d02800c2c40075001051103610108101500e849003030000140c0e01d105101900c0130b844003030054201c4403220f400700080202030000c9144144500b912190750001c0c0041e400d600440d50050b403d40701d81490414100440c4900300c00d54000d0300c80e81c812000c20506600038006144240c604102c182c4006060690b0b5507215100101038441e201018840b0004500f100003501036001d60114544010200c00d45c10a40103041d01c03000304c0d0081c4018402000c000481c46200072091206505080e19240001c0a08a06100d2100409449000318a801095400860038944012030a0202140101d4400d0f44200c248907620403a0003a4600881d801d01c5000301031520401800100c100408030071018440103603d0b20380c039070900624800d0ba044005c0140068080e11500c800e03500ba96401509014112880310903008a00e07400407240b800c0080c0e20500401c00c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 861033723 1250 861032473 861032521
    0x30b06180105060909061c030206190509060c090613121101050c03030c0310120c150c051c020c150a031812030e0c040e1b03010606020703320f0c09 65
    0x261b00c50902090344003010040724441489000100801e05400140345802000300f58100000c078000d040107401101e00a41e513200391500b180000c135000303000780c030043c00c0f0261005000c80d01d40754402010710107583d182d80c810785080c1c201e40d4088051164038402c0b04a601400e09000703203010705143c6a5074403484001c00b40e4088900210204140d00d08500349a009007007648050094403403142014584034902c4e208100c100008030719101800d501c107240044881c0c0d03000d03008014500850079002c016003802c980781d004510822b1001001a50f82c82503c05840c001c041000703550f050415001400d80d110103140c140c040101003c0c0380000360f11540c440c88400c1883c980082c41c0d413a07100031030742000410250300b0b61040c00e03d0461040c5003408901104000709041c0f80d00d9014500c1d005040c01e0303e656215803405a004000200086041011007850015410340e03001b00a0700c50005d003060000343da00900041d5413252071090080c1d0410011310718070b050b040f1008501c5242858a0030b9280d00341d2900004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 861034973 1250 861033723 861033739
    0xc03010b0d0f0c0c060608011b0503041a240109060801031401060b0c0304140a0609030321090303050f0709050a05040f020d05010801090515092a0307030b061801050609 74
    0xc8400e01a409400641e50580c0c052000300d100c80303801409410241001c0d17031a00c1c5080d000062124051084480003490003803880b842c0c2d140c00390280d4030364100510035900e0441e01c00d13088213109507141d1071a210324000e41d0b0001e00e44902c12240c00c1e034400002c515034107000100c0c6007445280c2c0c0008440e4110380d8130031031943c022020081200d015160035401981180c10100b45410040b4002c0041d00076500c548000103a034a18a104201242c440d92180300c0105a46000c2400441d100b05000030090305c02c54084500d10703000c62001b9084805544c0103a00180d51001480300c07600a07c800f4941000542c5000a145801c11000511f00885072041c85d00c5159110f035042103002454050320b80480d10520304100b03d41c1c1d2100010b002e023008800845103405210300c480e0000c8013031040d05001e1181c0341d0052001400c00c1c000b400380000c008420326044130800b0f8100710300b96810001500650310450520349141050418414070b4403581d00848010784c1208010700403170b101c00307080ea01e10100481d202d00d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 861036223 1250 861034973 861034987
    0xf011701021c05090118020906010503042301020d060b09010f18030f0b090f0a05030307081012031e0306140d06020c0a030c110a05031f1b21050c03010b 67
    0xa80240300304201c0580712994540c90220101da1030b480140300700b080e04000c3c801180c2e0083c40c440300340044800250310600303a030041071065101da0059a401807080c140002e840c1900914504800324040040c1c461307030340000d4140d04d40c8040b802204000c050b861010b41c101481c910029040c00e100c0d404010030002010514030069042c0c071095001140c1007a0400d20700c25150030b06105004003207a1130700c1c40707110f5a0202440c400300010040c01654000000d5800c6407100c400032250710801425005000941c1440070030003040341400e001080d8402d0716442440c2038200d20424907501150a050141880c0c9441000750486101c256a842c000407503442c0003010716442d2a02c028004d00d030346c8109501c00d01c0144002c25800c0201e120f0740601502102101440d02070400201642030300500340c041d000b001c54044c45154080c01c170f006030b44140303402280c2c201c0584c902c0d2480c010b03400e055500203503090310200c1d110341d2495030200070822002402d0005151005450000744010b108048140800003451 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 861037473 1250 861036223 861036269
    0x50618070203041517070203070c030803040201020a060c0315080c18060d1a04110f060f160210020c0f0d03052d0f031e040b070f1101060f0303080702060f01 69
    0x1200541401090b100c90f0b0580d224001342114040caa180745403541e03171408190158000401d54240b0b9522030105206241950b950440303c0c0c2010300100d042d8418907000100044240c01211134141c202c0c2d40c0003403c10003c900550100d811503000c1c8a00d42c11013103c0741c1564503201284900003800b900d204100c2d4888a020070f0703220716148005030600d00940301422460b2070000c0310034081d6004114000c103000d41803040101c907621001c1c803076622404c00c01031034601e00c401ea1f01510307900c41442d030240b40415064010440d0654940650390058000c4181c17003c0a14004020610158040d50560781c1420b25940103040342c4524450f40d00c4106c4142c0311409281d81c25011020125144800c654440100e04200012604255140700c010008080805d010420412005d44580e4110301c2c0481c0d191200502640c10702c0010829400b00a16601400c10400e424041e05009000c00c0d152038414a1650400074104840a032281045400450074425292012501c03281512003414441c04a28406001c2c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 861038723 1250 861037473 861037477
    0x1d09150409020f100f02101a01111006090e0f010e1b030307060c0207170109050607120f0204171c09060f052203112d120613020a09050618070203 64
    0x2110b548910100c1c600181136900448220601c0c4d50358088a26240f030304056007040d1000329203c01d098030120b0144290a611680540402803558010b072243c09400c00a200c05441c025080010f01d2a1182038955500608000d07507510b0f150301c0c000030800da000c000c0526441d0142a19900304409440b00502a40c0e0317014812103510035404001005030a1403694003944230f03440c51240c040d07032003242c10100903082d60600032000d034143e110707011f84083d81e20054203035183c00c00c501030182ca036070760b4080c070040002c411b00c000e1019040c0d100740e549100c40c05407851031410300c0d058404019807000b480025406500300c1c0e48402501d2a03230070a204408070484007110180100e455a5030a45480c01400000745000c1040b00240d031b004581140e8424030420903c48050b40c2c01044813446d07690803a280e02900d41c680c01e0b012130440001c0c040d000080303180380807030b00e440ea0554401d41089d00038850402185025260400103000c00941840030385859000240101c030455821100300110b440040d1030b007442401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 861039973 1250 861038723 861038749
    0xc0a0c27020702031e1b0913060e070b0705010501151404032d030c120203040609170f03072d0b0106182102010305010b090f0607080f0a1d0915040902 66
    0xb04070340c54907103005c24160389114003140c001c0059001484210142850701201d40b08070b00c21182e0b13540d2604075035111001440d021002110b00c0c024402c000c1071030f401d01e01c020048140100008201e5505003802c1c2050b164004030203a003031000d0b00241502491850064904481d0880380701100031f10a0601546400940c40501c500c3c0140381a091040640000d5200d407201c0c081c10071070a80400c01c5c80143c0c4c1d6071042c1c2c0a0324012824103002000444042c4070804281e011190555a14070794980e4a140340d0303008442c0803110f10322003291100042000700035a402c4000504d81d100b0b80d80005440b248044d61042c0074820170000c844804803884807504051700b00400c00c0203550b00c0e1020103940c610003a080c0d080382c100c0c00203081c10000201c0c440500306031105001e0007440c411070201c44000b000036a502c03018084401c2401400824414402400540704020035511013460140c01c101080e03102c8400010454401c0282106002c1084441c0719060415001a600025401c646000007060000408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 861041223 1250 861039973 861040003
    0x1f02030708040f2606130c0b04030c18110313020f1206180705032d010e0a0309050d03020d0513080303150405180307080706110c0a0c2702070203 64
    0x50300189000811242e0021100c13405602048001d0045003071280a102c4c0f850035406501402c0400d000c1005010701041e80c40c03062045840c402c3d0740b0f04071524190030981c0181c44400c1030300c2080004100354003040301301c184c1192003000700b101e01020750081030001511399203d2014448004086455401c2c94549042000f441011541e00d10b410560342c5013000c6504982e421010341013040944000030b82482620320003030140c1451680301420159010305c1007015004403000322031000520b202031058140000c4160040c048040c1c5502340a06041281d50046004080300040c0c580070907800305030726080786a9842d105903143c1000c14500e03000406904291114040007050041c00301d40ca0159a45074003058038240129650140e41e47d050340594008075106400c100b20b0340001420701401410001c0c402e5000044206400c8444034081d004285001c8040d40f0103180c01e001d000044000000400e9035040c140010b889000007119000ba041c40c40022b5150007050102c115503007400080e184000403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 861042473 1250 861041223 861041227
    0x30a09031112030c01090c0618090e16080a0203060f0420060c010e0105150604030506150d170915130504020c0703060507050301140f061b07030503191b021f02030708 73
    0x1300c054000d241307801c0101c80d800e466a40004915018020f01c0e40401d080e510440c0e03d8900d4682c0c500080d115010140181d805643c0e6138529203055401c081e4044e01400d80100001d0500f0700c1030500e00403024040c03000341100d030020000000c0000c604808504607601c0c2000100e0240c3e00841c08500400e8001e0045508111604641050550016200d0b010712800d040000c2040707001d000140c070440c00301034280d070004000104c15041d0204000c1c00c444e00a09100f600c50b49540710b603000921000002079030141c00190000651800c080d81050301054400071a11f03001000c5a001031f4003506100d003a01594010602c1045d9410074040840150340000c0140240c0c985200010080e510034040c09060f910020b00049650603d094068018040945100e14200000c0340441680000b0380e01c0c10594800e5503004800034600b480508242e040f180c01402d980340900e44040d1050040c09940c5840c4100c000000340943d6591510b9440200107900d41d9081c4071405500b02d003148200f5038060180900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 861043723 1250 861042473 861042487
    0x1c020a03050f031201090b091f050303030106030615090f060e12104a0a02030d0f031d120c1510050f010f0e040c051e0a11030a0903111203 61
    0x40f00401e102c0d440c2d00c44c2180b280e0780700d00807802201c89482d0450f030041009000152805d21462402e4032100501030390300c0c54a41d503040003c0c91340c1e00980158001030740f11581000758143c003074440003c400c1c1c0f0741400b4503074030b04080c0d24203003a185500c114401c000c5509203103003094a031108a10f0340716175441c0503030f16080c2c402600040504a05031900c02c0180c40041e001c0d01d20f0255040d040b03155220344024a055091450008041d250b000100715154000c2802c0040180d03010016070385038211075100c004100c0000341d405022140411030031012a80f41c4040425840e00104000310507265401c0e000f5181c03095203c0a500d08401300c0000d0603d5141e880900c03100b0494a1407000031558201e4070000f054560200450710802d000100c0400300e0305a00d5442c0702854a40c00080401c0060302d40103003040130101410305604270352401c40520b03038400600b00c031200e41e0000040b011030600c40c0080d4a45844060000c169200901c0060305030030b0494141030080e541e2066810b43d01c7c403401e04032521610 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 861044973 1250 861043723 861043753
    0x9010b0711062b1a03060108210d0911190501090302330d1a06091e03120c0706050c150402011407060f1a060d050c07140604050601141c020a0305 64
    0x40030303844c40519110350350350340b098030f180c00504181030700c44031800b503c85003500c42000903610188540751003000c04284070305400d5050520604400d20f020300e428101d8045050248101080481c0340180c5681c6a075900384082c1c1d03000060030302125070544960580e51030741d224449542070701c405590f40705281c0b03100c81d4000004800c00303491004c00507901013216000d500050182e25040b511440c0c0c002d0300500084140c1d2415115250484240503000e10b41c50303420000190030b013041010a0301940c100403800403a0401c1c00c11070807005c1d020f10b0078103520304010309003495540c0318440101c2400c076541c100003c0442e40300ea000e0070354011240c41d4450f03c404e02c42c0741c25005091195001e001c198a0b2201a5151480c40031405148003c0504041d1401845501100140100030709240f82c0000c00c200140000f0791403500160700c1f0214901400c1c00d0b0420349481c03428854180c3c419604000b1401c41e0000e25a40d075125a61100c0b883c0b451750003030802c14800b085003007070310364000f6045005111060807501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 861046223 1250 861044973 861044981
    0x80c0d111203031003060b19031101031407030f0b0609030705120c04020318160e06060c01061a0405150703080f130b160e03060405070e1009090501060509010b0711062b 74
    0xe116a0044c40395241a0062203104034040c101c0700603103023101ca800c002240c1c0d51194000e40c09018174001c255590500704016042c5029101940000e64404411140b11024841d40c92010310488030b4610702865000027a68a0400340503d80c070901c80202e801020307020403c171152103d00084c0c0103548a140450320900f108070380c100c4044540c080e068181c5202509440e501040d154004074910082c0c075040c2c240480e603041101e43c804c486d9a108000325a100d000904809486450300c11107030342c0c0c1d042000f032140c5050600b000b191101c10030300650001a4001c01d0065000c84241c190240c0d646d03911003054803829541c600a0301342c80e20351051102100f81e140644540085540307400c10f241520700185030359008201d401810a4020240601000c0a0f405005401184034400e21a0198580c07500904548203000d084500ea907484d8410403040c01e040c01034600400078894036034240000d030303124103031655007451545101c1e040000750b2034040c0262240c910342c00e000740003084080c0c0e0b10144420f4014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 861047473 1250 861046223 861046229
    0xd02031003050105070f030e010506010c0b0c070b0903030115020712081e120108010b0f061b1f0905061005030d03050c0f04170f0105101217030718080c0d1112030310 73
    0x641480e08d0030b84020414041e071307409201c041c1c0d1a0046d400b030341d0302c0750321180c2c4020b09484404007080200340007160130f030704d241809034082c031010b56965498802d044500c405151541001d40d0040300042001c021010b40764003503e40c21103100c55441d02c0710320b4407121034070801180c01c800810100e0843e40046410842d0b80c103841d1400003c2010f003a6400800a4240003480115400344003002002c08000b4066030401d83c0c01c004004030343c40c118035416029031146c030100400da0296903e807100424810100700c01e0f40c001c8600c4446003030040c107000c0800d0721131a4200400c0d05140e112004547d90142d9401141c80b448100403242e5100d54440d0308400e030b460052840c865203441217200300183c480041c0300c1c1a00030004220f000d448640740900740a500d20000c0c406031008501e80c95034841c40308024000b148181c2d8145d1710005520210110751400d230085822100f11a4415a080c2d0b01030345525042514094010040300e2408441d28002000d541d444007034602180000b10078000c0b034103200e150620917 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 861048723 1250 861047473 861047477
    0x120a020c0f040605030c151315080109050c040533042c0103170c1506010815091807171f02030c03060405040303020d05090c0109080703080d02031003050105070f 71
    0x9202010802c000565841d8002d2580c16080b0344c0c1d20203ca8a090f9002100ca00c106903071550600341d6002d0040005d51544e030007040c03084060900c00210b0360340840400d000d080482030810290800d0f0f401c840e0f00d80520b001e0540128501262220142030810019079186500c4043c040c0c1c141c02c011000d8210340007442104a0485060050700300070310340020146558500b0b00111605030300e551550011144119050072511404100040e14120103205025055030003207001441810300c10001840400000c1076107400d040320b04003801039550f45880480c0c0042d0204483c0d8080070b0346082150901c0da0690115400c8400300a001100000114002081c02400b5070344040e00d01d038001c2c5002c103a01c01102d00780012001040007900070b01d8681e20140d081402403900600b0880230415401c100c54068480d19004d600c08406005c4a40c1d1018200018104810141c2155461903442500300e02548921090054000c0001540e08212250000045400c00c0090110741407900000c0c0200a0900070040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 861049973 1250 861048723 861048739
    0xe06010201090b01151706100f0903150504021516060b03010e030d0c030b010908070506030a110c0c090604020a050d1d0313080105060604030b07031e1a0f011701030305030405120a020c 81
    0x1a000b929804820f00c0788201a1118854085623142103510141140c05142070140b00f08010000c144003070025110030a80a40000341428240100700b007030011000e95003100038041200240e00c04060030100001c652025000c99181000000a80900840c0408032141c0c440861703441450540c0e40c21441902c0981d460070040411140011660071009014040e41d9906c400c1c2e04225a0801c04000c5a000d0b0100a00050215566401461907070080000d03a500340c0c80404001218500708120f80d4010030111002c501e00011500064164001c040203100442c0d44c0303100015121240044c454002c840711001c0e00c4c1d8445800d0310201300c4000d14041c02c81c90b0b619160000e003940c14950115070030b80b41c1046640c111641c0d005000c401030901c0b004200070300c0c05865503606a01406000303081158141c480e0350350340c1480c0d840c144001c06d060a0705150400907184400220200c0640c03003641900e40611b400c5030741e42d0ba5030030080c3c41c0040900300d941c41c100e0001000700700340d540800c24494405045910700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 861051223 1250 861049973 861049997
    0x80c010c0228050303070507061b1701050402041413020403051c091514091f02030403110405040803061201180b01050316030510020d0f06090902011115010e06010201090b0115 77
    0x1064503420b801d0b00412039802040401e00c1c00340160040c000c081c2c81442c0210300d041d0701405881d4081d900100c3d84001c9404140e0306400070311380441180c00b41900340d03411420f0904d000d000343ca04440c03240c44d85014080008045200e408190103c8000d580c0003030480e20301040f506a0a141354900c0c890079000512000404542d10100605110203915281e0b104030064104145d401c0140d4040d48045500c20300c0c0c503c0d149105104d000346015100d43e650055a01c07540f443c02c0c5411a00f20030044544910f141600308400074004409030b9403c040c1c2031711102d18143c280c080b040c1c01405803444002c010f11140c9031410400801c00d0394181a1242034095505c100307104000300503448002e01004040e50070007a0703440844121503014182b03030f0305d100f5004070707a94070b420341c907032084a0342a0031204846845850910955800c20031503003008690078000d160814405e4900019820f060188280640d00350008c40c41581c0700350050707030a198001d900c0e1102569940100c550071203042e4540c8012540c400b03010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 861052473 1250 861051223 861051283
    0x921080103051b0102100f1401030605070f02070f090b030a08030103081801030c090e0910061706060a14090601030b2e0309030801051c0b0711070b071e080c010c02 72
    0x503004103c0c1030f0024080f2695220303409000e400b20820b03100c034080c2d0721398540c041c2031520f040b098000c5019000016007400e1840d00244440c0700d103c541000e55000d0042002084884108001250f400e000700003a0b00400b0350010f07040c8400c0300302c041d000d11310200c000f0080c0320500340105041c9d10f03856000394080803034000540c191085504580c021940703c0b5020010a12108280e40d8482c15a10503100c100e10b224002c1301c229aa2600000481c0d688201d480c829000f0400c03696802c60001c41e003142c0e030140f4000051506840c883e8501e80502c01040100d80d16034080d40000050580040c104103100310841030b00340f40c1400d1003140060781d008070345940c881c50380240319043c84580c0541e214074081e8207050074050003900e01d210042207030351688040e00203d041031440601452240e6141c103c800078901c0010328007010740c1c0048960030030421004000a180ea80848041009840c3c0a9075142d07050074505c0c0e0300e000f400010301c050f5007070140020050741e004c541c00c2c61503203502e4000704c0d03203070044006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 861053723 1250 861052473 861052513
    0x9050a0501170406050604110d06080c06070807121b030e030c12030d1a0d0b070e090f01120215030705120c0403080403030c050703170703200709092108010305 70
    0x688080d0000c03140410041801178005650184d030140c0045003e010b403158a180c83d911a0400b6152203685034400d0008402c02d03c100303a12600704039150f5081c1681d40d00e4100303040c0f2802034000d00203d0f402101c4a801e038040c0d1080b205400c00c103545c5074a004d1079807d014001d5448804464400c1c040d050748208640f600c1c880130001168503034001c1d8145901103c2020040080d00c0b1040c82d0100d03500c9101405580c0d42e0171200c0d80d1441040c091070305d03041c9248003a04842507948403501c100e0101040142d45070803c185141100c0707a21410b511070303d0680c004140300000f1000d00280c102c1e400001c200f2582d4100c0000c2c12641180951140e06543d1501409440e015138080100b44410410040012900c04c004141c0a1750044050b150740d140d690760b46e50400e0101c00140c000000001c21441c06041c0c00034185071000400b6801060401d0140070390a07100d071041d00400700529600c0305114144501160301c10410103880120302c4859456070b00103000c01c242448115020301c503165041804401b8110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 861054973 1250 861053723 861053747
    0x71e061b020619020d110d020c071502030334200102070b0f10120b31080a03020d020d0515060406090303081504090311160302090109050912070309050a0501 69
    0x4480418041008820000381d4400921719180d5500c420b05518283e0412004200300807010b98016a203901c03e41440c5c3c24622070b540714514844214020110064001c01100e6110650844145543c49190329012001c14a100103201412440100c07040403504000001614201c03041110440c0110420a41c283d100303094005194041c0e200200d140382800340002900592410110b802c019112061805949107450781650100c2d03400c024003003421249a41c600d040c08260003000ca0328000031003140c0e0f40c42c00840c001041e0510010b0400304091090b0f06803050385102000555440820028140242c03005482828040c801014000260315101c0110f0341241c55544440d0f200500d561070981d51190028460443d00403242155180c5076038034428101e401c0c1c829100e010401102c8210300d4039000b0315610314500d0300700710b640a0001d6502c010815045a0042c0808aa80d0341d5444840e82007400c403100d071503000da0020580c58105900080c0c04010794000f5030b494000d440d030302c00044074507110545c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 861056223 1250 861054973 861054991
    0xa0b0c0a0203040312051c2f0313050102090a0e0603070807061d0105040f03030309140c1819090c09050c040b1902120307050d06120201020c06071e061b0206 69
    0x441040000c03141610b44101038034a003405424481c031010800e02c03207039102200240082d82c580c084008c2d04042000007101c040080c0b400880e8001d0148180d019100180521031141d10446002c410460250115884a10041e0480304055650021130323901c43c5060701c20034444d005200c00445d8001e00041c188044810b61382d15888415000703424203d080d03c0e03c182190400c4410000031418090701c948480c01075109550000d40505c00d0308100240c0c0d00200014210b41d0006800849507a035070315202e4610750340c0071071130307801c02d0f101e0040b0030f1030341d4140030040c02101d400d102c80801409000011542254849441408959a141031080d0306103d94003078100103240034070404039010340180d4021b403c00e4180c0110b6540007000101010103070001c903130320710004800181c1d0082c10301d0107004140c01402212410b0b0340031551079001039151005510f0f5180a09008a4448184030b2514205022420b5000c0d50540000c95420b1410140c082c1c0e452944010319140b601351382503840081c00c0b61082c4030f06 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 861057473 1250 861056223 861056227
    0x180c090e0a0b060c0a0524010515120411010806040e121813060501080a0c02070605090310060f180b03072c010303051b06090a080c0312010906030b0f0408030c0f0412050a0b0c0a0203 80
    0xc00b0030820348440303429803203407008000d00c900bc0c1e424031058034041c084d0380180410044070300128001403c1c801d0040200d801281040e00c0b4055035100011600a1481c1e01008151070703802d000c54203e08d140001d031038654400c10210f1540100883d50b0300402c281d900030703079030318445980c3c48904e981640c000042c4000160302132181005258480c1001e440300403c02400d4031035154014000b0f1080e16956008146028800c000400500c509600c8090940740d1942061200300512070010b6103c20a61040b500c2480601542a20b03e0119204200070b50601044031549540c403801d008000380c00200300d401e4200540200708c00c030761000040880c803440c1c0b503000510f03040c2d503d5070321880d080d0000c100d00b0400784000e200d0304003554907200750310340641a04107002481c540b56046c00c001110015041c6502603011a041c403001c180c07001c044030f50291850612691b1442e805030301030307a80d02c910380c08051003c5800002104000c13022034407081050043c401d8205540721400e41103030742d100e480d02d1034000d44c0c42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 861058723 1250 861057473 861057479
    0x31b060709150e0d0b0a0b0907030603110f0409050f0303040606091e0c030e011e1109030a120210180b060907020c010315030b010807180c090e0a0b060c0a052401 71
    0x8501c00f81c1005078005040300703030380c41d015075201c0b20711320340c190703402c07465541c4801c0c190506007030503902c0c0ca50202c014139041c00610703d103480c1c40c500ea1245003100d50240c10078040101c00781c0c45036045400126844411110380703580c02107040342c985d001501c0483e81d0505109001030f81700502d024071540d100d0702070030546844a40024141c0100004041281496203038600700b0207401e401c0c480c801d0110765004003942c0040120160030308861a459050f08000418082c4803065100040e4842c80c29074800c003445c0010007071103401d0b40b0b8203015198041c921810089001000c0245003003c809980c45008440c100e5180d03001000401d4000315440801607000c4105103002d0340c0b103a0030041400101c40c000f0103019840e51a10107252400b600130141c01d612100c000c12241409480b9501a4480300700200120240824020420704645c400d01c0c0c00c03074400f000403928072580350b4040390201d98006d0566a8400c40380310400d88481105006032a1805902c42a000a40b82e98148030010003910880080c0d5a007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 861059973 1250 861058723 861058727
    0x11b080a021c1a03010f1b1107030618050f010509030306010e0f0d060207030f0e06030106110f0106060207060f0804080301050402130b03040f0209070e03061503010e031b06070915 79
    0x188000e20480503505200c0c0d20741c0c50051107124200340b41040c2003010392403140c0c10b041c06c0d654102d0b51010054a0f00c60070700000c45860559603040b901a02e03040d00e5001c103c0030524601071103034201505051501e0391035100079150000d000c1c3c590303115800380c8d02c080721815000c07422a041200c1c0b00380c0b55081000003641d80d61086c0781c5e280345000d00525910021035104c011445400509004070b506503800039204041c982c001403103c0c0d07030a02520b08100c02d034920b880414030601061060301c09010320180107510a0340300b030000c1080d0b030715801c6c02080042d81d241d000070769035113462040300301207580c0854040c07040b4443e003109481241c00059191030b5034605014071009600880c0750743c400c01c00e5034102080c4a51075400a6004501415000c140011107004106001e02c003d072450090200c0040b000d03002d500c010554a91200c29a2a201d00065103180801d000d04400c0f034844160f0f0100040d60107800c0b42b01c01c030030070540c0302d100115400c2d6500c05000345c81402d150301409015184210b4000b600038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 861061223 1250 861059973 861059977
    0x90e16080a0c11011e0b03061504050a0605030118030906020c010c080a02030c1b040b060a211b033e0304021306151707090614130e0108011b080a02 65
    0x20182d458107008180143c5041821101110800105044800c0c0121040c0605014924642008401802c5030342028070200c0201821990032600440e140c00005140c0d0145a01040c01864081c0007400607121510801580808200003100840c02c6140c0100fa10b81c030010300030751001c9041c1c40b159440356442c0c540021980240021608501c020803440611450900c1014070f240800e4001c4408442c0c00c82c04c020030741c2d45400c100c0b0b014250500414802c19448007841010b156a41402d001000400001e100036205c04490750041d06d100b80806080301d5455480398014800d12000800c01d074024001301c0900d4140d001020001e0b088800e12804041c80a20045070424801404110003129041c203407010340e1b80551000800080758612503000c41c0d000040b40f66405e2034500e406941e07280081c400b4041d90403a000c1d9408000e01d8611644156606c2021190080c000c0c410212016980c0ca03600d37030000c00309001b030100390750a081c245807605820001c0c01002c0d0030261580d4841d995400100c800035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 861062473 1250 861061223 861061241
    0x303160f140f0f0462190b0a050609010b030a0209090a020a021c05040b0d0b040e030a0f02030c1f0b040906020a090b090303030403030c0c0602030106090e16080a 71
    0x42c0e0010880725900b40c03042c41c020070080c1441d090b860003c0c19401c40280000090f0602820801700035603580100d10815404522500c0c44120616000480071038400b5080d0007504d10040c5d45d1041181c2c161090024601406410344a2160403c03140d031129644404e4500a8800a810003100300041c0301850300d95001c0d5500204000d8018100505200011350061007555202e5040b5400132f107501d00203605020080041d2541c008060b04451000c000819070304c070b0b510842425200100341c0501c82034041c2c00078101060010401d2203a000d1418840ea140d80c4030219000100d0181c08980c400340380040141c0310511242c50150100f062900c04a00482a82e03101c40100f0640c0d03003800c41c4081c0d56034401c8151160285d40016101c6071580c5000d0045030280d000103011001c288041c0106a50010442e1b6001d40e140c9408603000340503510a03140c050301c032400203008030300110000c2030b0769a00008a2045400b0041d80780c5603900c44028106202161104240c0051203010000d000d071015500041c001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 861063723 1250 861062473 861062497
    0xb040807060c18090209220b04020d060e091504020f0d02090f070e04020403110d0812130203012909060a08070b0415110607030f020d0204080303160f14 67
    0x2900c551039440300c04884014040d40041051440c03400810b0f000003c5180143c050010110328040c1030070001001c2005030070300c444100c2d496a24410f184820354200383c9900501500564842080808d000007906050042505144101001a403040f07800649441c6400800c00e9040054940e5000d218003007000c8008140c214035440720300d41c016201d00701e88500c1030102504400c4141048140180003000800e103151180d4018007040c0007081520041803064202214050802c03505850042d5150180c0000e41030015400d0040002e100b40521408140c944218020486000240b0f180e0080040740c5201d86900c841c0290300d043c16081464800b0b4000f0030007004a032049548040144c40e204043c0c01c8040a00c4021604000028081000203404207440c100301c68089110f4031240d0742c4d41300041042040685600314821490500d030304490541c0b540540c190358a079250036031a941c903031054550140b066100c050b00c1030710911800d14419805241e80e00c0c2c0e0000410040c6802290300038030f5140e05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 861064973 1250 861063723 861063727
    0xa0b0a12031d0a0603020304061a010f081806040c0e1f03020609120102030903091219031b0f2d11150f1b06012705090118030324050a030b0408 63
    0x452543c80a41c220020141564050307900c1c82d1a203800750030342c0c8450305108440458000450700c2a07030085188200320105261074052a51a0352450501d0310030640080c1d4235028403018001844080010a015942c80340c514450075200d410320b400172400d0314020354112040740d0030148014500f007002000c40c21001001e60030b40c01c802942c11422680140d07220314440d40300040c00c000c5420b128508200704402300c2c001c0e00309240d900c40d0345e01000a200400030200007482c9242c80507820981f544240458220700782d01003220a51500da00d11415880d050711711000b042001c1d990b00340700303401c1910000f940207400420801c200310500040c4103001004216184050001c81a01d980004c05030100c01210312010030107070f451003d414107011040e084139a134504007100d80c9030307907008008c0d420000c51000000003840390b440080719401030140c1c028184041c4008a025030030302d541034000b006881d0804000c08e030003c0550240c2c41e00180f0301c2c421940c100781d03070903004c2000c90b4411840aa206002e004454 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 861066223 1250 861064973 861065027
    0x40b09030309090f090c0402030411010e01360e04021008060112090b04020420090d0c0e04030206060307120c0e0414030304210306120f060f02040e0a0b0a1203 70
    0x1452400d4110303085848201300c001002000c24082004042600c005d8038110b20718100307030300d034100c074050850700b41f606004002240003200d9205240c0c89410190641d510003407484560038082084181c0859521404420728010409000da0381910340500d6009100e00e00d001642e013020b1b101403500901c1e40d8180160103c44000035505806a510098410611070305140b600348104030444402106080c88080070929000c4406880e004440d0300220490350030a9943c1c451070042c85103409038014003441008042130004054000545a0013a038044083e100134513103400100c40e002181040280403280640000c00000c0141030340309400070301402c00072000c2d0b4200020710349107038001c1e40e045400744558440c102e0f0310007008204400c03050441c43c081c4026403801d202c01060701d054400c00b0700003018580400003004440d61140325000d282400654444c1d65035100200d007132400722140c00b0020708000c040c40c2c0d10302d40b2000c3c441c160381c1150001480d4460f40d844c111001c04039030407040c00c08940454a0303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 861067473 1250 861066223 861066229
    0xd0813032703050f01050903090d0f060b060d020d050606030c0703030e0a12080103030221040b0901120501080703140106060203030c03040c09090f02040b2e090f060c0506010f0b040b09030309 84
    0x14001c0e6003d00003c0041d81c0c210502a403c42c1d030014000c182c0d94001303111108160380ca1040e19407400390045101c4070030b0f824504003c00140200b1040d60361010b00016070001500709a00500741180749040200074642d02c54041c0051880116030301c80481508009050009009500c085203d1707188404aa130b03171f441241c1e50907994110351a00e02c008185040010410154104a070026641c104505140301c2e101e5084070483e280660f00886000500128003400b20340d10038100c50340d1100f84084140500c2d6900c00302c5c152900302c40d00081d50b500c8401c2c1d081011000f41405407408840c901e43c000c51030f503911200c650b0850740000d082140d02507505140020550224041d40c440349008072050012000148104400c549041405070702503072140405822810500e1000e0022011100e0810310400400b507084440000d241c01510b40f1316085880841e074254080c940d100c1c3c4501c114100e07101a6210b05c11961411140d10480c00745000412017881406450009840da041d0046e08490401e00a9000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 861068723 1250 861067473 861067547
    0xa030216020604030501150906050d0f02061201090e100b030604030e011b05010c1101090c0e0a0e0703060c020d110d0507062c07060c0c0911090307030809030d081303 73
    0x802d139482c0c0c1d11021a40d218050513002170005043c8078070100a00c2b4641800300c0c1c0001d124403000b803d8075056100c4413003591030b2141203071500c002c000c0c0d01c0b43c0300e5038442c4ca1040041146582d114000e00c0340c440302d00d055030030034850180d40c803100400070030141c0e60301c0d5000c40b4080807401c90f050400a1056842d8031001907080d0b2490194855000410720180302d810050000c3c0a0070b45540260313040228480110f009059000250b07242682e102015980d15170128014100102c2080018440da0100106200030303a80812503000440d400d45890340308029007140e00519a02188100e90054141000d65a004000400ea942d101d500003080030400c100c1d442c030303a441c4083d10321881c122145c00c680301041c50521812028180e03d05261020181903120380342d0302102d9000702404d00d6504d481164281805000340c03000c048004080340c0710161a894103800039008514400c1c081d200d01c81a01d8101400350034018454040080b50a501010607101114800428030966803001529040708418403a0808 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 861069973 1250 861068723 861068729
    0x105120c16121e05031b16060f110c0d05090d120f17090d200a03050a030e0a020108040b0a09050106080708120a080606070302010605190e06150a030216020604 70
    0x10304a04009a642e4015040c02000151038400040d001d520401da07a4100080d0f80e0090340c41c0c1d510f100140c4802d40a51418414003010798400c0300d00e8104641000401d0b004540b081211100600681074010144131007800b0343c507403100305a04091085144c1a101e60050007001000801007035a82c1d0745030721001d01e039001c0b00e1110f00015000d541c18644494200b000c40700e80c0d0710305c07402c036140070310308079084985a0018071402402c000f0b0244d00400c000b030043e18108003102540b41030301c03880b110500d4090155480240380f000071074103241c0050017406001c103034506a1901030b101c100b140e545513620703261040e000a14058042c2d5850084e03002040c070034800d110103448110001c1c5007150a0248a500d4005052801c0701c40900030000c05a0b07040d0b01407004c90304108140e6103a03440709242d15080c4c0c054000c0c1d41140e5000509414000300c2c4103002d0341000120b6500301c001054984541c0c00740284a50002001842403c08000300c5000d94400d600810303541400300b0310000030328001d6000030032551041d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 861071223 1250 861069973 861069983
    0x1020d05040f0308130804060c051c02010203060a080a0203101107061a0f0405040f0803061f092408070e0a03050f01020903010b0a06120f0b092e050105120c16 70
    0x40d09500403d500101402d8104502c8030a40907510721035614040030788118080d1104000c5280c80002c100541000040d0550036075070b10001543e585035100a00039007080314150f101d2030700c02000040840c03000c1400c4c811640c01034041c000c0e8000710112030002d4114000000c1a00d6030400c03424001c10303210302c5000110703490304040c0e00e04c80e003200c42005640c0c0c4902d05800d01c100c1c40e040500001901c0400544807083d44900c203142c495407800c00103412502405c0ea40781d600b4503010b0312034007166440484c0805482c10a06203407a560152400a0b10300c1c0452a00180460080c102146002c0d000d92060000104002c18074141c0c661039641e0750f801c02c07030040e084201030fa401080c540d905280c01e0042483ca01c600740c5900500c82d250240042a0845821041b202642d40704010076405a036508050307881d0401a040e82c0d002c0c2041e02c1c1604808030007400c0103244c051410034001e5814a408a9141200c005942d001c3c01d10030348003540d80105001034050051b4400802601e00540ca002c0c0301034104500039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 861072473 1250 861071223 861071243
    0x60b0a120c20072c0f071107141008040308060d020301110c0109060e1203070f052703060a060b040314070e13120302040521070308041203030b090903091201020d0504 73
    0x1a00d143c8020b003800209511051003c0040304c40700c0d4220000300c0e4065501d0401a400d03031170b00d15003075070005d01c0c8240020190090340c601003109003603c41e0000c80c200c01034030000500d4100d41c0d003c8624410603900100001c80d1207001c210946000c1400b0503460780024000501c864004107041c503554040407092070283d44505851050108521948044100c5d000180a0361030140341c05c10342c01d01c0010820001c2c000e2210340315030402c0c0303e0010f0b68901c210507010881c00355004521580144035914800d8030034422100001c2c0c00c00b4240c088c000c2114102d014050519045d07a6884000c20074115107041c90340b085040006441030010b4401d8002d5120b0071207014244900d0078011130f101c64050044040c5401080108082e49a1071030640d6850980d00c100451218081c002904141a9600142c03c2141c04980450010034a0103415482c5101e9241049070f040c20009001e8210320444180440342c0090004913114100701250b03800300030450000504e0310112500b19400c40700195001d0303ca417058 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 861073723 1250 861072473 861072479
    0xf0f0602070b040e07050a0311030f06090619050d02030a120c0c0608010e040b060f030d0f1b02100c1505040614010b090a09020f04030501140a060b0a120c2007 70
    0x5110388070242c4100d52076907251600340a4070740c07503828015141604010000a0a0401600c2540440502851000e2096503401c001d1326008840b04156401403240f8180e42c04140c9524103030b00720038100300000e0050703038030140b40c2010080c2413443c4101c24ac0e01030180d080300b10f00040100480d42039490385600c403204004014208420385000e280c001c90700780a003d01c0140b281c0041218070907807140c3c6c49072008015988010100c0c3c44408403004186c0c1500c168507800b0030564000071440c00c000f105544400c00b01402c680d01d00c18989440c078020303400c00d403d00d00e036903880c521802e03141e40600c2c00b40300030041101074040102c2c1100c40841d0141c403907641d1201c0d460f0301e6031503480106004150200001e800d21036180d001030004115440740a00d00d90380000c8130404007400700f05880081d42c201008000281d4111a0b0b0103600c401202c2e5001c01c07501d00940812124003640981d86104803e40c1c0b0a004101e404081c50010b180e051000e00c03d20401c40c11408035100318104060124904174050024546 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 861074973 1250 861073723 861073727
    0x90c09101a2b09051c120c1b03031409160f080d0f180603060317070f03050a020a15202502130e030c120f0405190f0f06 53
    0x41000381071040c46400c200c1c042c032031054116401c001d00050080603500b02d084112000040c280c5030070050107801140403e240c8402e50707603a50440c8007410b44580756006803584070002200c0c404075a10020442c6030b190b05800450310302509220a02c41e00300054504284070b0510101030080b01c00a5041e4440c0c0103e04500c0a158948401861200000441300b0700340540036403135603c5000b22400b0424a00e00460b000c40c0f04140700070200a04041381104151901c00c000c016104900047d10210301038a0362507403802254007140c41e2a504000b02e8540c44101c2d503001c6503d40d00a180800440c8a54068040454500030b8a20200c2081041c0001d0340c0c602071401000b0704121524281c80c1c2c4505000c020030041c1c1000e0903101803482101d0840640c0c800b440083c1c00c452116044414961030610345002c9441c00000034061009074504469103441038140c288003920580b54880003402c6d0601c000c110606180d074501d00c1180314181c0034007490362120f01100708003e1507030101c111500c0c48142001425 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 861076223 1250 861074973 861074999
    0x1407031209030b010b07030207030c12020114120c070c1a0d0c022808040b0c010608071509050d1511090414092d16090501050103051e090c0910 63
    0x140c5080034038a940c074540754512a81014407441200800c00500e0008052090110402850340403280080c0c50b5100c160700c0300300001155080740031440100420005000c0312055500000341c01d000d0488541e203002c0454a2038120003030840744150301c0b200109000002103e0302c074517210507500142d140c0a4045200d81070b80c5e080c8000005542081d005a0303102040342c004600741000800342007003880c00c11326004c2c03880d01c1158000c06049401107401074060300306400c1501221440e804a4003484d44032521701b841c0700c0100c3e9a20300803885180d810011030801d00444c5240741c1c09000c200031100802482541520884041020020000200001035180c607104401c00008001e140b0196072500403c0340340d81c9e41000321001c004041e0b4400201c03541034034a1655551000840940d40005401c1910700110040350203070641c00c50802c0c0000c1980d52191242074030400724001415000c50340000072410305000542995258020031403602c1c020f4884064640c001c0c0089903000148a1270711a03000920 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 861077473 1250 861076223 861076253
    0x21e060411222c0604050120030a0f09050109030e1e030c190503070906080105070e181f0305060a0501080102130303260a0203190c120b0607140703 65
    0x3011000c0d01511403510b10440c40005480704540010f032902c1002600c1050b8403074070400040a8520150f001c02c1180c0810098011803180f40203008200d04041c1c030342d0340a90000f00d04024100e0900024000d50002e070003a0f00c1c80f03c80e040c000034542d1b08548513242034814021040e80400c500c2d002185250401d900910a00c00d208070700c280782000600f00203034460803d400da6900c0b40220010011518215400d004001c2c80000c01b20307140301c1e0342c45c10424041c003103901c500340c0395520381b100043c0030b0341c0620385200000c080148017540820100084400028000e0520500b20b91100e0342020054000c54444014500442c0184450303d410a42101550016001407143c0d900610052100520326440f01d4150307540f42c200505070f01c111400d0054454a9800c020312581404024003207004e166a00a5000703102680e040c11690001c0c0c5101d9082da5180d06e444000948021000420380201707500418140c040100100c4c0740c41103d0f107420b03a1042d10140507040c40d40102e02d00b081000100200c0d03088d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 861078723 1250 861077473 861077479
    0x10b07120e030d0c08040512161203091214010f020c0723090a02090405070f020c0111071404020c0304031218050d0f02010e100e01020c01080f011203021e060411 71
    0x1148803603101007900d0301c1c03d9004510900c031402d038400f410415510140c402500d0040c00042003107640003007566962042240e1681c00044a81c004a226070100c4000551150151506d400491030542c2104c4441180e607070668001c2c030110301086585400f07024035a1b4601d0740540c0903843d640c65014a5081c50307502d5201440d420040c4080052402d920840d1f1a80c404040303690000d0350f601e2194800281c800c0c3c00f50168800d2400e41080405074000d849200d035000e486d400c645048040c5801507900605c600c60482040c0d001d658100490301141010010714400608054140581c00d9080ea146421503001228002d03000420703404200d40c8a0034001c040e40711100d05c10006407604d000704241080004d80540f01600020813071082d03902500202001003405800e80c2e41c0d00a40d101c000700000c10015080303005000b09403204d80d680d032107042e501d03001d90141d00200d8007691070030003007105000d164041101540100168002c140c01c44125802a00c0d210750003407c03951910307143c1212540c15031014184 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 861079973 1250 861078723 861078737
    0x103021507060e251d161b150e0c3307050a11100509090a060e0a0911030318100e090a0c1e021f110705010b0f0103053705010b0712 58
    0x61601052569400401d00c3c0350b803110211806e541200d240d000380030521102031a03a000c007002c0288209101d9003000e00341c04200040868283c2654507141e40c1004168007840c04052500945000101c1100d4140b807513560450031418495482c0050300001e50507a074070f800001140003800008480491402400c41e005071807000c41100181071802a824200c0c081c01594000441c0050300381d1016015008664080d0b02500e4a00c0b1900050020301c441101c22440024170a26541000025103200c0c40380c2d100c15004140803030060060031000c0a02480800c0211017046000d51070700c421941c01184526004a0f041c0c052800103030920803460740300064800440404c5441550200f205102c0c030400b80310182a0409011401020700b41c00361034401d04030400112402048015808150090000c4e68130344001304030480150226581200e0070005c0166040d02300d0700c035981040205403034004440565000001d03820440c1c0c1240d5098009003500d00000520b00203002909998a8100000b454a19 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 861081223 1250 861079973 861080009
    0x60303050316051b0d02010c02010218040f0b1c03030e0c06071218080f060a0509070323030307110606041b0f1421010902030103021507060e25 63
    0x100144401818810840d01010440b1203081c0300d0f204030341c2e05183c6000d01400c0d01d1824031402da20303501840d00c604095807800000d403040b28010700903148a41c0751043c4071a00c2020329002d11002e00740c1c07008084644d643c0c4142070344103980e60f0107050343c1202d81d0032005007004030b151402400f21480c13031140680c2c0398007407001d440d15980c8400c120780b41d1652000d5484407a110443e02a00c0900c8c880d222510030560f42c11010501560000c0d0f582e0b00f0504000c11116240c503211111011264169018a95030f0041c0c1013f00200d81080d410a4041d10f514a040c44002d49880d0711600303542050302c00c030340000c00040d06440b417010b00b0000690040400c80c2d0400130a01d0071350029841c1c0901208400c00d00c1840400100c5281c042d407680140e5130f800348150340e55a1032001c600035504e00c41b511004a0f14205400118428102d80300b500d05030790340038000105058601148a070140c11801c012142c41d91242c0440248a10522001d10310f00c06140c81ca692081e4001454001c2c894a50403042d82548100001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 861082473 1250 861081223 861081227
    0x6050910150507020f0a03050f1b030706050c0a08041410081e0903160c080f070614070c05030a060506030c01051e28020307020a090b0d0204050901020c240109060303 73
    0x281c8248050304101e59204098808a801294480c500542c080307249100001806404500071040c18100c1c0d040e141041c0348074041c1c0604200300704a05400d0743c441c810a104680c000c0c00285100c0d030411089030010006503503500e120b507001b41c0090038140c01d2141607184d1810141c00c02c0c182d1400d21300700303105540b609011790600c113000350103690841070540010800c204002e00c2103614a0310f041055a80c03815850070041e02e00811845040594820607940304184840450302c08150340d09941c0d5802e6010007407810402030f4028030410b032000b440c200c1000542c3d607020000c1e50b50043c4216008642450080101802d01c1c84502909040c001704001c103040140c0040c2450044040308089152200340024002180b9500c50342c1401c0d40340c002c0c10120019640010180450358801c41e02c1401903034540512400b5a8400c10100e500b00148519490041c601500401da000c0b0340b01000505040c9501d60681c0fa0030302b80d0710100003201ca0840c0d600008034124006501400d941794061080510755600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 861083723 1250 861082473 861082499
    0x1a09090f13023a051501031a0c0405061611011e031a0a061701080a11090912030a0902010809030f0417010e010c170a0608190c030204020d06050910 65
    0x2d00c030b0707200e8800d8074641410840e401480c15929240d00e603525200c00c4800c83c5400503840003520184100e0101d90b0042c201945064180c0c0c0d0300c0385d09a44008201521a008858081d1000d6400002808085000c0d100c1c0c1d0081e100000c01105010f00008090034041c406908070004141040304680700d10303a803200346034401c9a0a400900d40010441042c0c07040c410082c454010035a400200c0d10b40006115501490300c44441c1d401c500d1445890f41d907015040e41e140075030500202070038a40d004529161a20071011603100344201d054801401031240318800d84c1d4011140c00d03c600e6561040d030302c25541d0090250354000c8540000310700d401c00b450705000b81402035102d58003079070703182c0c10049001d4070007900880060b44614000b4071498a188001402104c110b06415030b107019200000b81490906014640071600702070048c00b40144143d0701e108900600b0700003070342c44032100000000103842e11b2004151900c00c140c00041c00c0d9003010300708088003a01400c40c80740109080d81c24489620b0b1001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 861084973 1250 861083723 861083761
    0x5040309060c050102042610020a080106081f060801060e06040b03010b091507030503011a0a270305030d15080610060509040b0d05010504020a0f0b040e101a09090f 72
    0x80c09414102c0500d8803901900c03940d00800251581001c8000040051030b40318070200b280f04c2d040d0307055413000c084400d0403401801800c800040c405001044046e006814194100b00300407040711001140d564900449039045e400540001d4007107004103c02da52007807030002c99590441c0c0461805190102d040307036600040c058406020000a00c207005580c0d5043c40000d120503048043d40c540c4050f04000d4440d420901c5429102d444283e1003d000c3c071110b10849440e2021501c500b4200803e000c0c480316002101400c010380a1010344012010a408002078080d00a0a0704007003240c25207501030101c26038403a800721031580d00c0103003440748141c1400c0401c4140c41d01460800e480303000c1a0000b401520305460700702c3d0098400c603042c2c0305114064100c00e12860007130b5024900c040e0b407010107810a40d8248a040b41805040c841070058000c03034003a050304034815450f0710007881e8a0301c0141c2c15000e040b0840c030541010000e000320f0700e418580f109030b6120002980c052050b291080f84c0b0360880d81c00c80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 861086223 1250 861084973 861084977
    0xa1506090311010912050c0316030503030a0b01024b06010b0a140406020d1d060403020607020a05090718092034061b0e06071110030609050603010504030906 69
    0x10b5001e460f640b0403041319004014070302c00c07103540307907010b0802070b0b1292501041180640200681c218040c0140348454003200c0d40100210318680c5e80b00361410050081008442c114060481341c400142e10019a1280d181000c45035400c00f00c0c1d2180f00c0031240301a0910354080304581c00105000400042507250440314190b40b02581d072007081d0f03400c80f4120246030411407502c0d4040b602064240d40021500f0b2030000544070b14490000d40000401410881c05000764050700400041c00142008005001031501c00b80c42055200c0c3c49000103004180116042d10000700e80c81c8181c8000221a01d03000000c226040003080b0f00707942c3d91a03461201d0015034202c43c1c500000154544640010041d281c900e280c281c0301d008010b2500034400a1700d180c2c510042e59200e042c030305990a0020004140115202680c80b4158034880c0301c0148440e80d0401d91055440152a0118210395210318040700301e907000a5030001205810a002c0d90100c40020300480e0090385001c0801c400242c12500d9041512424 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 861087473 1250 861086223 861086243
    0x405072106060b0429030112140a060c080708040506010e0c1207120b01110c090c040f0602060a18020d03080a060f032102150411060c0609060a15060903 67
    0x1042400e850011000c00201500d1a041e00040d00820300405441900c0e40281d60252001807809110000e00010b081400702c44820001002202140314111406611941c03100300e40d01c2c80d8410302414002d40c4c4009507011502e900101411550000216074801d1003801c0114040c10700e902c80655074581402000340300592800820302e600c09140503580c01e281e0002000c2000d10740840010300f81844920405807050506108519560080520091900380d40c0e008054075800c030020081100400b50607031944078010000412035049003640d500191030700b50020540e908105000708115183c208511110852b449100710051f030300c400c09000703a035400d85402244c980741c011442004101950251000c000ca00e1170000411400000c2451110715154001c0d0044d481c500041c0d844958491751700c204c0590fa580020001005444200d400480241019041040d20300301c0504c0c2010656404155600c500c0420114003c1030083c440b01c5c00380b044145908500e0100d011b03010480b03a000090005102c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 861088723 1250 861087473 861087509
    0xf090903110604030201060e09030a140a0302040b04080102030f0a0c050d09110a0303120c020304080607030216081b0106060302040b0f0c19080304031d0f040b0a030605090f15040507 80
    0x1c0384000101c403840020aaa8503030500e8076019000707000714403030440003a40311f00003e400340b440170040e5652101c0646940b901e2103580c80d482c640030381c8092042014517900f40000b10b803401403c80500045c045140c001652410090300c41c00703100c00010143c3d0300c0582403614000406501100307840400b80313503000204901030179140500301f4500f81c070351541e08000110360010a05038411110300711003517264402c0100f0f0394050300888c0c0b41e10030b5010b014840d520101c04136000620030760041400310402c4640c40780a02080e624181c142d846000c042c0c0282e800c1c0042c8618640c800c0c400d8000412031030a00310315080c50140f00c1c281c14050b444200744102400301d8212800d140038807420920849a0780030044d10103031840c104070b46030429501503000562160100c05d42c600e5020051010100040410320342c0b100b03500402c00601504061150484506600000001c0e858001c3d20300402941015056400c040f0404d00e00d48229903445142c81e01c0040240004100c1c00b14070300080d90820050f1152040b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 861089973 1250 861088723 861088727
    0x90f020a050712030f0c2c0a030f0f080d020301060e01020f0601210503030406021201090c0503010e040516141c0c03022e08182a04061a0d0507090f090903 68
    0x3d80c3c6005d80d8009400c0840d8503694952000720201c90456101151000140c00d10701c0444808400c10311340d421000d00a414000b140081002d800d0442c03003244014a00306940d940c1a049800c20403004065903008401400215001380c020744003a40b082c4014000549500710580d903844061040110420b500890300003c0301c400840d803107060b5009821607503a41054609040203601c81060004052158800031130719004900641c1c0c0030340e84942e246130960342480c1c8000590349000d4811980b84c41401c5082082050b42c0140c68014009013004502c590204004d00c180c020024441025004201120350001031141c411241500d40550f01d821540318030101181e96a040c819078880d06440f40891404440da0200c60383e4491580803501424580c1c00102d03c95681e01c155801c2c07580c80140c010020458180c9140c41d00e0241d8000b40003041060755196800207008507400d05060f406400074003040e040f200c0f40520f0760401071034504440410300e030014403040c04446d80688103010333895420040a040c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 861091223 1250 861089973 861089981
    0x50606070b010b07060506060304030806090c091011010e0312040f02010309022d0906030616030b100528090e1306050f0610050306010e1c1b090f020a05071203 70
    0x190702842950895860b604400c010743c016880858181d03003004001040d90900c001524025a17154881d040f0546800040242d103040081c48240941414803101c40c4681c4c0e80b40400100c03210a4441c0c061010f618903045084d41d00c01201507605a2003000704120b1207140c511a42c0d03000c0c1c1c000f016050164a10300c0124090880c031304001e9402080c40c8034054901407907030244c1d03c017294840380101a5030300d0b0307100740701e09150100c40c4a41d064010707000244081058200b07480c070714051407038000381228031400020a040004103079000010703804110180070307401d0a611030a1595200411001081190307000501440705401001c1c0300e860901d000c035441e0150980c449400c642d00600070722282c03405859100403c0412107000f44940341c4100c0d140e840e0ad0041c8102c90190106070340745076820401e01c0900803042200103003640c4d0001020011004503d042080c001c500c03541c1500100f40b2490903030203800b51403c1550103000548100001850070fa0884226409640c0c009000c1180b2440f02070168024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 861092473 1250 861091223 861091237
    0x120f05030d0509030a0207060e0a030602090f0928090206091009240206060d0804140f13050609250e13141902070c06030e030c0d0903030905031f050606 67
    0x741d030800c4240020001c020014115100780c940c00c540c2660303902e000c11640015032803d002d030803951201c01480492010380050106c5600900f84894803800700021804803101140c280501c0c1d000408180110300d9207481c500d004600b8840c003400300b00110b4000070b640d4410b41c05205e201d040b0310144044002d00800b4204014800614480d421480441040f20100303001400c000040c051030001884c3c0345008180542e800742c00011442c101030805200a120000007c140c540c4086801c26660345076481c10690480940e09840204a07818074100740542004003505141d95200101c994150058140000d800e14189515001d080d0410001c04030754807461240f05803040a05008000492003e1506120f015010b00d8103250080f0b041100004100e0060460090080208400c1000307114402d40121a101e5400010740e89080c0000d21300a12b4090f01780391040100c0d04641c4104145900141c2040040c00150301a1001a1104d00c480300b203c104102d000384240e5854001c0f8025032030ba402501d0395 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 861093723 1250 861092473 861092497
    0x3150f030f12070c06020d0905061e1c060b03040312090f1b060e0105040302060d05071404030501060810050601271d01080105060102010b06072004020f031906120f0503 74
    0x101d9a282c52200746560300c40c0380e05841e040150031000900a05c0040c9440170380e0402c0d17a60840090600c41002000c0c1d200c01003484081e20194001841c0080f198014803220f40c4500d002e80780101421081e00964000394020501d2000c10710800000c690000d202900201c521040004c41d06092328001c040820800030103050782d1412400310f5400c0304141411015610301d602c902841107211130044035184078600009401a000384a1046962010b4002d2900318980b41803401090420b1980e01280b90095801540da613034407280d041140032803d1004c041c1e4940c00301070070710852821200103044900343da11358824100c030703081d4890625000f0b1052900034023030001d4a005070401000c000a8252000c0c010b201840d483d280c00b007203a540c0148205003001801a0840303060060320348500601c010b031000d1280715107803482d9540030560384510013040301201882005480f400c1144101144141000781030416901d000320a00c001d07030b86000c0ca00700041c0d11986030f0030310f0a5036103841d03419030040344e61a0070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 861094973 1250 861093723 861093733
    0x3010305010203061206010503030d0f022b050601260604090b0709060219050d08150d03050d0b0d050309040b0f04050a0e0d081b0a0c0f1209080303150f030f 69
    0x1000350640056020f83e0007199075440c507403020800070351110000e200307203070385075200f00802c40418a451304410401030040c4801410042005941c1760800e00d02d120a418010403112100180b20243c032039141c10860a107803182c44c204144220f6100314002801502100110f00002981983c50350001603885a00808500003828440f6010b45994400c0c0180310140c012a060310389040d2a0080b030301c0a894110008102040160005890302400a8400700300750707120765030b40741c05a04c03452010807410744241d6450740d6484584a4100850751a06080c2d4860310500e070f03400011900000590f04a150701b110006280c0c40b4140c00101d01824040c1d1032504203042008004404155a0003031344055100b01c11b0300c141c45940c3e0f40c2216824004c42d41da0400e54404003d8014001050f0044d08000a0313a092440003041c060311164100001404102c030000f44034a40c643c2400c0d4071001c03101c02070450000440c110f007806116240b0482ca401030590149500c0502507201e5a0f04000c46ca00b400101d0081c0d40d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 861096223 1250 861094973 861094979
    0x120303070e21012f031501180f0b0a09080f100e0a0212031209060c07110a03080c0c150717030c0415120b010e0d021522050a08030a140d020f0301 64
    0x210030300340e042450718202401e02d82c4c554410050042103d1060000174199200185c02800545d881c5070803165a25060120752000328505600380e130000c2c040d0076001d400b5a103a8510100c0101966083d400080d0660041d40c10f00c0215540041ca0300b0024540010100703200103030321301c45032030204904000380d40504401d122100c02c0e100400100410581510684c01c5540c4011080d03944203016142400440410007026012880191903c4000440144402c80c010740c3e9403200d02d0380781c0181c210040b141c1c1110350340c02041c1c44c281c20800402c0720401d4009040450076103070703072540003803040c000c01e10f020002002451000007003048a02804002090f806803401042004040901886400f0911482c051840b00c05600605041c0d01c4c1c0117004100e0310300e00e4119800e1002c4044084841002c0440600200208986803000702a40700707590008103401c0b0386042c08119003460281d021900c0b6400402507400101da100500348125100007440d580d0342c50700008110028452002615000340003c4004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 861097473 1250 861096223 861096251
    0x30a0c030210180c060e15160803040503091036080d08011503051302042d0915020c030301060503180601060e0117090319020f0a050705120303070e2101 67
    0x75040f600410800e4031141d2180c1054950b1041d4641080e40309141c200c01d10000d401c81300081081643c03c64200c1e003403441c1551802c80d03d405c2550201c40a0b040413800341910b0501c12025070701b5131454940040e280350302c0303814411549066070b40311036a00351345d168076081d003421002c0c003000a100035400c07601c100610b054000e000c00c60078082c51654440d0000320345403070b80c400e0107624000e05860417601440710103a420440184070030392114021400314400e111004110078070006018111420104075145039180921041400380d10032448544107120040c4c46240000c19a41560714a00b0015030300d442d011064500c0001401801806126902c0040b031255400354641094480a80740d4000b1091040c4160105510882d070804051b03000b44041352007190f03160040074107482c150050361810403607000a5402c00d0316030f180581d8103a00c120802c202900701092078080710710065000d1400d500b4080c134006e000e00106402035124450100d11303041d006184412a154540c1d10b0380080010080403060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 861098723 1250 861097473 861097511
    0xf080a0305040c090902060a03020306040f0501150210090b010311130e1612030e010e0604051306050111070303090605030a0f02030a0504121409091b0a05031017030a0c030210 77
    0x40380d07103500c0c641c0006000d131014082d401840d035000b4080781c2440a404070460003500002c0016902588035444070900f00c0f40b030700ca80c6000e40030300d00d881950004050006403816112141c03a2500c1880e00c101365020a03403806045065a034880f1708803002c2e02d0140001030940074514001c0481c030b80b4080c41080c0c03207580007070a030044a805001c035810349655a141135009030a0b03418068045600071000e01403941c498441030310807580c0109680d0034181c032140800c1326400078070007102d0010341d501000d220540c2c00105d0350306030105c03030700040c1102070865400412400f2188180000d105003c00441d20145503030f000720b098100d07114030031922071426184150240006990545441002c000340003115442619009aa03070341401d0400d2810462400780848510010030f904e00440030f40c9140c610410351b603c020400c601c800c3e910140c0f42d080ca41c0c000d1000104a52141c282101412b0144070192404030544000402a0404016856060030142d0908205680d80314045140032100c51101d407801003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 861099973 1250 861098723 861098731
    0xa020a0e12060601030507140a0e060d11071a010f031101170717010605031b0702120109150501120b010320150a1806050304140312010303120524010c0f080a0305 71
    0x17800b40000e071114201580c03034184003860340350f9141381001618682402196000700440d8081c202600e00b00c10000c642c802c64141107108520000000342c0c4d45c0a000d5110382d4541d290a8005140429500d8001442d1003503030240b01c014803104400c440c0070091780c002d051017140e00d404480a1403e604d400380703004000f135400341400b80000030344400118190344524282e9100e00349228402d610400c00e5280c440582d04801c00490b03120220300b1400e0000c0700300380a2079519a100758201141070340301e40c141c4d00503100160040c981020810110102003000408000d044036002044684800c103207508803521241c0703000404c0d8100030a180480001c600100007040190800d556101c0151f03049188810650744507c5000f0014009002080200e82824000c2045131880c2084914000651880390a1032409034019808124514010300c000552406900c0d8017058042c0c079040411400200c401c400201c80015074108200d040c81c2204000489083d200c1c45500000d90a131594a6000018081c1404407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 861101223 1250 861099973 861099977
    0x81801030e0a050606040e0a0c0e01050307090c0c03080712050c0315030102040f150504170d0909050f011e05030a0b04020103060e04050d122d0c090605030a020a0e12060601 76
    0x18680703a4000c0408a00d11404503440009404a503c07120700300405080c022203112903502505050400042c000c24440008050b030076500309103585048109402e0030601e42c4403030f2842e070620180008403a0f01030340c0218902d0741800c21080a40f82c12608803888c12004045087d124901000e1002d2006084003562040c914021512a00001c24084c14285d01441c03082c0c44e8824405401802821800005948080050328140b800d09943c3c0d2802c514401c00001110320030b0300310f039010010a0303a1140c0300b0005409070720021b100f80d050500d48100350800c14071402c600241222101c40a0300820302850f001031000400b01c030740d5004030b800c102000c89400d9074101d000c01e18185d000034880b41c91100003849140c00c08007809101d4000302c030545800780d0b50900c0705081982c0d4002e0100c2ca44099240c0c1c5445030713150103800080f0b4400032010080b1241100100107008018404110705030303200741107a42c0906403074000758a0340055241621a1450341180c141d02c400c0d40902c4030420440014881d114500907 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 861102473 1250 861101223 861101231
    0x120501050921040b07050c0a09090c0b2a1e0717010605090a0903030213061e05030105130b0301060302060301180c09060f08092b0206100b1207090308180103 69
    0x101030000100c20314001422880b00140410042c0e80344100241440500540c15180d04028a0700040d16443c865000756803102e075500d403070f013052140304541003010780041003055103403045246010b40c1c06698041e03601c2442c030200d4044060040c084c410307480c04018422252348851146c1d0003480e211046070258030319040118a40c10407112050040004031040680400c18685508410b0000b81c10a504203a0901d9020404102c110340d0901440e4001e003056a200710842c182400c103282c50017102c8a6910422505100510460383d178101043c0e80821020f0000440103c00c0011a0240141d0381c030180d48034201000008440c0524940c19a100c11440c0301006001d001400542e2126620700410001130300028040303c8041c003c506998011161604540440030036400c41400540070500307c100c1301c0b556480301e80880f90100400c0790001c0d0240c130b030100542d0600c0c502e0f00b52030017480e4100f0301001c503000118000c18051041e00c4040c58224a41503602c2584003c648011b452550300780b40020b2074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 861103723 1250 861102473 861102493
    0x6020f010e120708031f0609080606010206060a06120e122a0a02010c0204020d0e1b180402090403050c0a06290d0b07030f14010f1d070f05041205010509 67
    0x202003103102c1d0101080328010304104840d20f5111a50308020070001040700c07065003002905a035600d0610040802d696200d544034103041850f401c044010b4405819903212900b40101c540e203020300a416030b116442c2c02558030b1007140c401d030b016040c000527190031400b0709800c60000c006604000d00d030b02882043c810b04031032039400c00203107202c43d00e0b654400d50b60091281e16005611032091903148500040026082120580c4908100d840303000c00b00849511641c2c00c4001d401c804032000d001517000b103412502e6075401a02e060030080d00100b00902c80d01d403040010381050702580940c0d080005520450b04100c0c42ca240450042c111400d00c102d0034a860801200c6030f040d444000c1078003240c040c00301c400121003541c4400c40303880041c1101040c561207416621110740700d440b6080c00940750160803801d9501d440da031450542215084408a55071003064941280c0c8007400a64105940f0720703112051081c0e80108890f00c1c043c0b904038040c41d0940d543d0190034407105400c5980283c02400c1074441ca029 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 861104973 1250 861103723 861103751
    0x310020705010b120a050c0409020d0b240301020901120908043809011b03030b190e062407061e050714092101060e180106080a020a15090504050106020f01 68
    0x50310500810b158451500c82c072150508e90444880301d48050300606100d0840e5590300e400312005c40f44041d01200c00e503460030b00008080314131203840c20305130000c42c542881c1c200001d0000850310180510b8a440701200810400030008036002024903a44014104500040d80c124101d0090064050b50b92428110444609a6030480701c04000c1619880d5003e26030b40d11500e4441328464055092541d1200d440c4540d4480d80101c80c48031040d0580c0c0442e040c1060010703455900c0151105000300c1c1d00a600008010b6144803540300105221405a1181e0241c40e1080c0a4800929000c00d2107640030380c0550301d007440340c0005000b81081c0e00c48100c0608050301565081c0070b03216060340d002d044600307500003115007100725074102051140046002500c82014441140d41070395469005000c043e5181c240c15000e01c00c080261408001811400205400251400e0200c0c040d00540c1044000c6c80f02c26030b401880d070b1100030040544103000c0b541e550f110180d00c46c04911030101e9194242107070144048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 861106223 1250 861104973 861104983
    0x20c0f0111190f170709080f0102090a03020d08040306060b0a031a030606040e0111040b070528080325120c081b091302040e420310020705010b12 64
    0x1200c040e601d044800100601295072030f060042030000d0021820904035203454220075503208074200d07111900014988052245441b012035000d43d44c0780d20500001c00196228071100080780e0301114010082c01847c02d00260300e01c2903900041000380390460000c2d07040624409090344c144642c0f002c1205902d03070351080c012803042c0416294190840343c0081c00340c2c035159120b84000002040005080c0340102d400c503200ea4840d412204500501203001c0003001820071112150207680c81c0c0c01303140d00d07005104400150303081c060020195840070001500e0020380e40d00f003c3c43d03480b100400c40e40011000c00301524014040048151807828540041080c070f01a500c0740707000728081c0007075005c41181c241108003960003071400383c1e50042c0d0005165a4111080c0054000b810701c030302041c500360521424040074110340758480b01a103003200c02035461000e450b10728181e4108215802c0c1e440840030000003800c04410700d0903084110304c04200001400b805510071322400d481075038006503448441d00420f41d12 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 861107473 1250 861106223 861106237
    0x1150803090f060c0a020415030512040e13021203030f040b07050c0312090f100609050f0c12040c091a0a170607030903020c0d061a04150608041401020c0f0111 70
    0x16000340070b06103860400701c00604001c9010015034031001566400581501d0f00c040181507004172188061041c0a41030000c100b00d003101c0c0e603800b4a0140751540f4811003c000816540c0703030703080c0e6040110642d160302c00302814459542d410340f40c1d039140c0b040840300f0480c407ea509442c82501321000501450107070040390743d1410640300842c1000d41c1550404d8291800410f84121406400f410711800c1c00101701c00040c1741c04840000c5801c1c0d041ca1007001c11290001d003103a83d5000101d040c04130820610045031071804d0204024403142d52941424050036489903c1542101c1c50315010101c1410b01e411151810a403c5800211443c1d071036010884000b07010200e103845412603000302d04014003d070f22059413144070380180c0c1c82c00c00842000888546161409490301500d4114142898150b00c07101c101d08a402c503001c004c01c59181d80c20b400e0400b4035001c0e41c014020724101003010310910310380d8000c0201d00e480080d5601c1c0650000991111030102d5042071940c2071480551141c0700041c1580d0b11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 861108723 1250 861107473 861107479
    0x15081e01050d1e0b0708220c09020a0e03030c070810140f04030e04020711010201140c1c0f020c25050f01030209011e0f020d020109120e060d05090115080309 69
    0x8402d00a0711820003c9106120190500d0203803110900041c00051809118a8440e240c40980d8a00340b10002d0108024606404040c00f0032200340300040c8804039144261501c2020058030703132030082d0381940c0d0455030301c0382258944000320f888401c3d040300140c94410740d80c8000075100c00c150500c80d020b0a541101c1814014071a0701030010303d0170401c180800d58014080e1070840d03d400220b40c0032600b01e070b0020b901683c0c5040c010b0400b52655809000f441d080c0440344800004070b00d0004040f0050380608230016032071185484280d074040c203e80d04418100111840d0441d600c90442001d00c2d0345945005040940c0d01090b0300882d409088403102808a8001a002600100d03510b40110000d51003951b03141e060100c1c14003803c1c1c0c0d0009100b002d4403090b1300b41d20340307100c900c940200c040e1822803042c00308002c581c1400c096000140103142d660444140741e0802c17100c1982c10400140b0300b4081d400055501307038a024108052000c05400c1503031401850381d1285001e41d120034100b901e80c4560340600da0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 861109973 1250 861108723 861108739
    0x1403010b0904020a02030d0f060911070b0402060306010c02090f1f06020a0204090f0f0c060318150e0a051b0109060306081507090f0602030309161208030702030415081e0105 76
    0x20b06064000f0078004540340b0549107450f07041084801180c1c03140c40841c0070140d8461041c800009548641030140c80b440800e5420215136a0301c401c081000200002d0040e031012020807581d034043d2500d003c0f00c1c0d50044c541d00180c580000d82c04d84554088030000034640c1c0c10080150b60107071a148010a0300c020ba406801003000e59000e2002402d9000341c1101c140a65034140404110214882d9803c188140106142039103402002810b45500821014100a81341000c000090340c0e003030113000747e85941101258540c13200d0300c1c0d682800014040038040b1b0051000411031440d07541c0301507680035401d8032519051a1600c0c0d044041711180c1c043ca46580c1d00044a0704003104280e140f4a0388a0a9803800301d81c290f40310342122841c58260741c40200540c0c0040180264490140b0500b40b594040e50782c8482120300d820484401d030748401c03070040c05c140000004510103074824001c60300a071804448640b00052506c01c02400303603200301c402700303000e011402c03005007030180b181400c40c12210b004100039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 861111223 1250 861109973 861109987
    0xb0303030a1a0d08090a080c060d150b0f040e0f010e0a0b040905070801090c21030f14070b010305061003120513170a170c0a11011b121403010b 63
    0x1038010000d00210b940340800c0d0300c10000881c1c2d500720703844801511418060b5140c9400070207104580640d5041542c00340c0082000420031f884420564201a4614a0219042c1c5c0982c12680c4481ca41d0b8010350444200001c50910a4910a0080044400c00742104c00c050742d80602c0b03814028030a01504100b6961680030075840c445a4111603400079005000146002d925a10707c1d28000140d8400382080c0d440304034100a0210690004008090301d107190711030907440030030031080100c42c0d850003030610201071811402c4034842c8081c5203480004181c05540d0701d140303080803000c2040901c01103c60707214900002d2050030403d5005004c4a40c00703443d00818001e00702041e034268019032a0031a100008510000707441c604283d444100c0d141840c00307003040d100581011012503c82a4030880d003c50100300d80350145d140010340d201260b0f0082044442c1c82c4ca00341c01200e80c007141d890340c4140e14140c000c1c842c0034400d1843c401d00e0b9001c41d6032600e11426001c548280ca80340400d00c52080c4209003400b40c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 861112473 1250 861111223 861111241
    0xf0311011d0306071214090309010810030f0503091f12110c0a0c140102030a020c01120b040e0c01120911090406151e090b0603070e12030a021b040b030303 68
    0x200c8a0910719030000056008070100740b8104080741c4910004034458080c004074941e9110318004824101b494580074a01180700ca5540d00c60021068100481e102c0007504040041c04944d001d5644016001001c100314100130b503407600429141445988000b00328000300f1802e040c501550441c03900c4003800c4060790503024005080040d22180c60344020040350b0742e030000c240126181e0a2180c824510081d0078040941d840341e0700e0700e5109040d907008000012500c1d40004800258080034a4803c1c0900803100100014161070004d1982107401c0018000c1d5450010800070b015030703030030381c2c03880714003051080304c00140c42400c6005020840c0044070030003141031040724654000e0244c10080f5441404100d0a90131a005611005c000f85c10902100401c1406e02c0c45440100411b100c00d0040b1001d00b03001030164031024112805102c030440c1420426110002515010a40d110036a5203521003001d010352503141d684994000c0000c0c0750300c022034918091040014032100070340103600319a100106 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 861113723 1250 861112473 861112487
    0xc100806040902031e07031106030606030109020a0c060f05070e0901120809030f0a05060f0a0c051606110c1509010e0c011202070507061e03050106050a030b0105270a0f031101 77
    0x1050760035010710517290000c1c60004c45101d0304c0350141402005013a145052515403441c2104a4510920303081060040030359407581070303d0540c0c8a1000050780c03103910702b100395032844c018080149900d080465020110341c055002d903203c0c040d50307200c04100540e85420070180b04400d006100540300300b8141d5a0100b802f0070084c0004103005821030307801801c801400c40c5031150701607007221241d0205040007400c40d100c4103043c0c2c1003940c0c0030060040000b05400682507000351f150740580316034822803800c103005c01a004407819010b5000c00c0e66913110301d02c8001e40c0b100742c102030203054002e046010580702c0405101d030340c000b4000c000140c02122810001150700844106030214066000e10180700403560038400d05004205988540d003840b901300c0409040b45881c101d03140181441c003001004900e03000700880f0125402031500240d00e801040041c0d401d03008180b050105070301d00c0342800c5090000d20340001c0001c402124044211980c442a1101c541d00c0d9000041c180f4080307450f20b0344c580d40126a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 861114973 1250 861113723 861113741
    0xb04060e0106063204091e020c0304030b06180901020d0b010c0b0a0504030504030c1d06100206070813150509070e280902040507171f0b0304060b1002010e0c10080604 73
    0x80c0030f00c4d562081450040881d00160084194550b0342c98042c024581503403280301c010154041c055060080c10104240c0302d020342d00c8003800c1104150000345903982c0e65000c85048200d080d200719450300b00f6042040c000e41021040051040c43c00303440c03220540c00303041c1d841807065202400b00d500d44c0d108010100501406801141488010300011000408086004018294002c40240c46c800b000031901040c078800b405541c054075200813410700581d40410050b520000908200d03115803a0740464049019840d88040e02404103012605409c0d50f0a03007185000385100ba00300da44007601c1707a0742d40043d024281c0d1800d249a54500b5000240700b40f407c0d4100c0d082c030741d07000001003507081ea8010405070340b42280c010001882c080c0b05410b089104401c1c0d1904442c18056180107660232400b80200401c840c00b41c48000e1401200007000c126990700260032094001d0141c08210740758080290207007480058680305c501581900c1c0150341070007844c0c02d40340c009031b079500e05854a50300180401440030308 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 861116223 1250 861114973 861115037
    0x7082b2702032503020a06020f01060b0405031c050c0a0b1906061b210c021206150f0d060624030b06090409060635030c062d040b04060e010606 63
    0x544000056543c2c10940b00050842307801910030040c0c0c15501e542117a8440d040500258410f200900c440d407000030f030240300c450310107c21002440f200c0e1070984440c0204401d2003080c1c410f00c100801001020000300d8083c0713800c03501a1601c00d50002c0c1e07000030355625020707080018405104034161420700001d11090640141040c1d0441c10b00180e00c59a500c0300c040300d000c081410103030300908504101c182c4005012260020b0070090601c225283e041d5000440694412444103070550400ea40d02040b60340c0c4e01d40d11520400c6000d56801c90703006c0003001c0d401011204024110b4500c5000d019007c0d1001d01c20005004500c4c2c9100c110402004109001c020340d0050381d10400440c002d41d60031005109811940c0c0806c450106a81c91556003a810440d010030f5900140000051280001004c0d44c00005010244604165a5406008554011942010603100e090034003003032201c5880b449006034014030302400750601c001590303401da42c0280b0400c1c00040c5081100c0c140f04003568a5100c0400d000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 861117473 1250 861116223 861116293
    0xc0902090f19090203040303051f061d12010207050f12090f1002011508060105030705010c26070c0b0a1b03020601090510090f020d0501050307030807082b270203 71
    0x748071483c00302c0e041201c049002c66916002c0c030101004111350b80c8030b580e0901424411050130f1080090100c046039032081801d20301e0f00e006070005d07541da0004007050034004000310744420850070165510821401d540b001303402104031841028411400301c40c030015001d0304014400d003905061102d183c9200310307640215561041300f010001d02c080c1c280d40c01410810700030038080d4185030401d030924150741d03c918188104515104002401a44203280700301e10304000e8100f40300810b8000040d8070900e01c004010030914140841e6078003058002d807162414a03504c0706000580442043e1140d420307084050090b80c48600100710304c0e551500402d910110502c0100a11030b651501282a140040d81051242ea00030038910784a5170700744129401402c0c110000d080e40d9281d03845548907440340e101c000d09100c40001700b80000d4100c0001c1c403950f244c11010310303070003400301d16403090010300b1141043c082801090082103840803402c4080100b1710707002800303090307180141c5100048000442541d00400c41c0a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 861118723 1250 861117473 861117479
    0x5100c110d0609140705010f0906020613050c0a0b0301030308060604060806090604060812030405012004170309131a0604051c020301060308121e0c0f1c050a090c0902090f19 76
    0x88451203402c403004d0f000042420760304280014200340f040c00040380c10000d440c070007000b200d980010200d4000b0307104000c04000f40400e0800604003021211b03621f40100301a0400100cac21580c4006504030f81c02590303907540a0300e40c0020004144518451000041d040e20045441707460400b080300d41001c0020000140c2d240e0720302c3c3e020304021069040fa81440d40120421084c8102802900c112039440410001140811218080d40d402180101048803443e0301c034421709150200b040301c4090100505e4081140441c01d03001c001f602c00319481025036443d0300c10340c450600b080c030300361000d840006012041e421021401512641c14208099038150b40380c402c0003003c03601810040c000104500c0c04844103242112401102c8400c0448401030b100e040e6042040420851003520b40740a510703100280ea0740814100d01240c010b0040844804904d0300080c459900142e6020b000c41d10301c9410340600305980c45c1d40c02801c034020040030981184826141407501c0c949280f104a0841070074140e010000e407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 861119973 1250 861118723 861118733
    0x18020108060a081902120f06070c0804320f0a090e070902040306020909091603150e060a0c030c02060606070b060117160311070c0905090a02031605100c110d0609 71
    0x54040504110301405941350043d414025503c2c01c4200454000f00f404c02c2d9250101c55507030301c00903c0d2104011041c6021010000d13294101c900818407001d48040210700d02d120110440b20482c00354860400a803156032980c10102d0b2001c0304804000c0540f240c492500720f6000280c403c88180e429180549503002c41e0b6801e052001d4406140685001a2515441c00030311007103032809401c1ca02242d2040881102c0240030b10340c508182d0fa80589a90264400084070780098101d0039000300882c001c0d6010411107492561011090071307400d07a400c1c4400c40c41d40e00f082ea01c0319820303110a9002442040650089000a40d009400c54410b261444000600c45204150510240d0b080828003040102082242d42d050184803111400c466400e450140c00e91303a9840340103c3c5101c1c07100d100c1c0c1c4440020751a854140888000342c1c1d005800d60701714031028240c080c24100c141c040d661080f0500034410440340d100d25001d50351280c0c0403804e2503c02040740c00700186054409800c0307520680794001180040c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 861121223 1250 861119973 861119983
    0x20c010603150506090925170d2a080711090a020c070b041805041b030302070305010612050d0509030304051201020903060a0b030d260103030f030f18020108060a08 72
    0x5000700c0312159038250464561083e140d000d002c2c1803003000c0c040144003801c180401ca0b818007403040402010002e00d0040010448009584040709186140005501240011402800d00c1400349d4900403500c012003561900c010300016000005001c0400e0800094045801081c03a03038040c4010314041c401450014078215400c03500426501c1d00400c5081240c80308010000252611403803003403d050603d01a03894210040140010090b00d420100e014030047c2045240007800c0d90240c29112522400c001e5030f038038032910045a41e0741c40c207980051140d91546c20303820314030f510801500780c0700c0307520030b007104c5982000a24540c5070208000c001140c3c0d4603404141c1499281c2c000142e2150391020415080c094004c00200469091102810850342d000ca1115040c0b1407a081482170310756030400b620000c03001e444402291504000000c014550003120034055022181d034140254200d008203213080e2030840d0200944481000302610041d070103803c049901000151414962541c0c42400510b01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 861122473 1250 861121223 861121229
    0xc0f1815020a05121602090613181a090705010f1403130521030105040c0908010e010615050f0a0503090a0204060303180608010b0f16120201230f0a02030703020c0106 73
    0x742c1c0c42010716204116090001c10000c000310242542000440100c08100d04601c1000901c580c80100000b880c55448900d86010203040d90030400403001d0302d000300131089643c400d06503801e0902640c500302040101a003280300d00019005842d48038908030041d030340c9442e22904c4000b070040008c511800c4051440184d44240031085d0284100156070070b0542c01c1c0498181400c040803540340d002c0101e403042c0c0d42224112202a640042c0c0038070308000444100e03003941c11400295080c000300861840e01500500152444c200206411004c810002d5600348151190a011100b040c040180b24030f001d10055035010aa040544144080c035500040071603c1c0d0360411004581c1050780c2d105606151100c450190080e4207001c0366035410301000da0b0301800b031660181e0200781d0010340c5000320510342d05074942099012001d40c2c045014240040d003c2c02020104464940142001f0303807030702e810390301c41c40e0094503c00100e84a98a400344d010f0082c2d07000030840000e16408016032080703c40f00340704000003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 861123723 1250 861122473 861122477
    0x30a0507020303070f0b10140a030311030706050c0310210312110c150a091e020f1f14070f030c0c080307060510080a020603010e1e09100b03010c0f1815 67
    0xf43c3c50080000031a8400230b400c10f907044043c180c41c580310358450342d0307160007a242c250424010740c0ea00000070038514417a00c44001c04450410041c03155980040e001745010386040104030114507200c0c41c400c4c50101307041c0201c11020482d007a20710042402802c03004950122401d0100c1ca818403205110620350000c12011210303400301d00000710403007c0410a41d0400301300d1405002c80042c0d40c5a40c2d0f022900c840c20303a0643e01540511804560743e9540c22013030644042c0141da2182000c4911329030861a1303c9052001c03d820242c42403481c1c2d00d03d030840b60b06a922410702c80c9a100c0c2610111010300314400c040350f01c2802c40c000403c034140204064905140306003004905840c100c002d000001c07403190300800d03d5a0082084200517690101a01d06607118030f1218a03495480740f40b42c01c02d43c014565200e40e86450702c02841840d84000c101c1c0450f44c81d0400d001d00001071b440007031600700d4003441c40300300c00244c040c0b520300e000f548200000b4180b4164001c440404a0311381c2d412240010714005401c1c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 861124973 1250 861123723 861123743
    0x60204030f230c010e190515040618031a09071a180307060206240a0f03020f19092c010510061e0c1a01030c05040b060408030a0507020303070f 63
    0x10400b15550340a080401c50102030030b4061807440010344075100036200d880c8183c0790a80d0501c003683e02e070706000e401004001d020301c07100942c042c609441e540c880d010303a0b0002000380010310380300c020400c04a800c481d0b004c41d011720900302c24120441001405084402d10f4004c1200028000e05040c00c0380c58402190040d441d92100c480d1030580030280e0100380103010b904614000c002194000c949e01e40e1100107805001c410003941007d0700c0d1441010416103512864042011501490500005c001d03644283d401c00200c288840400c0b110701081d00c0b082e425a51690000c0c05458541d80003002019040b280d00c9080c0e003818000468440501007a000c102ea44d10401c00c11000e544c80d0b8079800134140b5081c42e107800d1442d100410300c1500c0c0c0c0e000040601581c145040100002c03000c400741e498240720000b12155850345032a0800104c00d11075941f045003800d481d0082031070003a084400f190301c07503c0118a40386100c00c081d522030b0091101a41e06000500415001c10000048400300c81c0c0700d11405d207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 861126223 1250 861124973 861125003
    0xe100e010608010902030d030e12030403021507051804020c03121303030b01050c030316120c0f090501020106050618310522020d06020c010e0304031703091207060204030f 75
    0xa800c444041c2d0200000d40c3c14401e4040c0540c0b4042080c42d076000d07041c44d000c5181020307041d180c1c0c900700c1c006803002e0302060008100001c0c10f41c00300310a407100e50f14820904190712509821107043c0a0441d501d140342c500c0014a80e01d03458164010501c0700c503d0010f40303040404400005902601c1240c00c80901c05290940804040d8180b003480481c0009007802e17030400751000300c810303564000203001c2d00c05620020b0500c2d0007140201220b69024440d80b20038808404614030042003030300d0086d8a0004107880d074501080545c01805240150350000e0500c034148140c003070710000031002c1018440d8020080030320b1000f019080c07403628032045180450201d080180008140200e030801400056000e000b10441d02d40e1203983d1800041c010b4045030750440c411400c1c100080203105d00e00d16818170b580b8107042c404400d007011001d407003228043c440c11084204141403242e510b110403208038504e60840135083c03495a5140c0041e145590190744014285a1266518000c998448200341c0d09040b40d800c00c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 861127473 1250 861126223 861126251
    0x110403020f0303031003110607023c010c030311070c0b0a0806190909050c0316080705190b0a05040902042d0503061503100921080108030405060d0e10 66
    0x7900040c1c100394021403075468070320b408426955a41c0801000600a690010129a915020b0740c6090341c0003082150055504a041c501e105180200c800302c4003500740000009142440c2280b41619068513910407420b0283c0e403c50040c48081c04021130f82505114880101e448601802c0160a07104007203030b42d81800c92409402100002d1506110307045072441c14a11802d604c441e007084a640c14008107180342a85030007401e10300301c0035620fa0144204000528a9000455000121610070094421203070300d94041c0203030b0f550003040001d0003408c12401040001e0485006001e10142840e001e400c00780c58001c404140d81c000d603c4031003000310250000e88081d608589844030310358a1282d01854600d440042525250010408640d9080728041c445458034103000048451100d03102c10044010689001001d000e00d0540305112940040b0f00b05141c41d00846072981a1150a40190b042524090030441184d00038103500c0c2803941c42c4c4003030020b003000c2000382901c42d01100201040c208091140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 861128723 1250 861127473 861127489
    0x10050714100c02390d0f0506180a021e150d15120507030206090f09090106080f0a0302150a0e030d0b120a15020d1d1b150a0315050411040302 62
    0x4080000030301c148020080d641e11a5500b00034400b80c0d8250361859010300005e0420005840c0608003040c880c01e06d404000010494510800800b0011044800050786281e500c400041d4000d402ca0000798900c4032245150030089242c42d4018511410724201814920032900841c007140500c41c3c0f01c01440c90100210040c032000307040c0d102ea1b06002180140ca801e540c079040d030311010f80102c5000640481c142c032030320780f04c0d807030346030050014880c90030314000c01c5009000c10b10550b0320a00909268071204070010401c1444103800d40d0080040c0c6203400c00307580301d181e0060034601d140c0d540c1e03403000e0f0000041800038182c41a03809000080b521385040a000942d2140c00d04102282c01c801d04000001c0c46000032500d240c80c40510060322400302c44441c90060205c0300038241c1940d0b60000520722a8070020300a1200e0344001d50f0101401d208c1c1080c400c80300900803601104d03120502c11f20745041d103c1d03404640761901c056a0a1301c8a6070b02da001c9011102d045a00d03070b0800310000f50070720940c03c00b100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 861129973 1250 861128723 861128743
    0x10021303020933010212070206180604050d14010b01080c0a031a091302030709021c0213170a060b04110301050d03090f0602032115132405030607030b10050714100c02 73
    0x21000340380201f0760340050b02030310800c8240c403c880c800c0c90b07411155858040a0b5000707043c0c05005050900b040b400c060140d071040d14840e01c002c1d030808944400552240c02c0b024043c0b040103807075504110580b82d00b0780140852000101481d1000803007035051f5542e0301c0c9414010380c102241800c20030202c1c014141040e80641140c20042e00400446c020703800c1c1380210070f04180121900580b644140302042400c00c080780c0c4000b13600458030003120080c00b8082071a003030707080c89298200304802883d010b2109403034003c40140102042840104020f05000860810086c800d20f448041280c031000c1d0355902d40b280e500103400680c00415401803403810b070b4000b149680080c40d04c1031407a2402ea0444d0300c4600500d042180142d1a1030ba11903502c2c00c9603001410784428030781d1507049694100e0080002c056031481020b1007131148801040d00a4001d02c50301017080d0010b80790080041d4040820344083d40b000d00704a03241070902c144c2c2e0441031410b0202020503840440c0102e11000071030340003843e00c0c0c0562 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 861131223 1250 861129973 861130003
    0x201030e0604030504090b01020a1a07110a030504030227040305030a0b191e0815060a060e01121104090203040f12140a1d04050403020c03100213030209330102 70
    0x741440042900315040d90101c80d00800b02144900705039004034100084441e00400b003030343c2c540c0f5180c0000355441301d80d803140d600c81d540c0b01d210540701440b00340d50b05111900a40416000c002c2403015007010348503041c0c3c0c0d20403080c00161003582a000c41c8112502140c0030750002c1c00100900c201c98286006401c90581c1c01c90364840002d003034588007008d018440c4180800300021115034005404c10044010040c008001034480f204824608503401c0c3d10100c03051480f0b4410407502040550140d8000d04003100d06a5410100a0025603010020300c00b000d00d6104940c010310001401d1a0300b40019803060780326040120744015a131500800d891001849103042c001c5200700c051740c2e0041d980035569145420b00e419242e00c0302c84a503400c1c90190034000c403504203060500308400e06800149881d414a01a411100f0510b5025a84400c07809001c10001415003940001c101501d807640c12590040400c008a203161400342509201c0300c4441c08041c0b040f4580c1c1c10310040690b80510041c00c408841d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 861132473 1250 861131223 861131233
    0x103051305030d0c020c1017060402030c120c0405060406021f140f06010513030b040210090f0b211f06020a0201080f07020a0c120b0a06060c0215091306030201030e 72
    0x340c1e5001d8036030141d149040459950303690a111034620800010501d0507020f440300000c0d0a50080090890415803c2010f0b54690140410354500709803085a2040001003103d42c10458841200c203c0150094000341a87c001404041115076400c4001e000410807500140f0f90011042207581500c20a0540c184400f0710709512003015006116441e5400003005000307860a13950400161201e000d000400c4101500300d52001c42000601034031140514000c6608400340b41c0c0c0c24030216080820350141c0241400c0e1020100644c01c0001c2c040c0550448840104442d04007201460104d2031741154a4901400d6118a040304003080e41c2d40d00700035040600c05000304090503000070300360150140c0b2024400f0303140c10004076054824448013060541c00052440c0d2150707a8400d41c50202901c602c151503905407180071500c140041d2148604885980d100d200d200b8115800b0001c0402e9410080e41c0c0159080017868003e5542080992082c1e100e20400103005085000040072a52908450b944075400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 861133723 1250 861132473 861132511
    0x150a03200c0a080a090801091416230a0305010c030203100e0405193e0d020d0f05071206020a0914010804080a03090b0f07020f0601061706010c1a06010305 68
    0x402d480c840503800050640d61144840700c219000c50041d40072050952030400c44404108003402c0215400f004001254030314911000260b84c0c81c2003a1040440031140d02c1244d13001c080012a42d200c12000050545030274554075200c85003076480d01c0d114100020350002c100514003880b040114042c11215001e15044d1070a6581d0344d942e10b65091400344c910201258001c2007080c03491005100903101002982c04092604540c103136450340c800c41000002c01d40114000740e003413004031010050740050203040200ca040d1202042c3c1d10f40c502040c1c030f550285070000b2588a5080440d0310881d8418840140e40303040c003810040403d2010f41003841c224a03070705e61021240e80e101070320a4015401c0450300d542e500d01e00038180c0007444a250020100304290b0100010b452103250014070460540c3c003a42d403403071881001c0700c0e145e941c240545004540d0343d41c0407500380c01240300b0701d55104206040024403042551104003500032051203040007818031504000d03842d68140211504a006100b81070364101d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 861134973 1250 861133723 861133747
    0x1020f16290904050408040b07060c080105060c06010306020304050705120d1205010605030402011101060504110909060a1203180b0301030501020c0c010305010605040e101707030501051b0a0c02150a0320 89
    0xb091402e141d104544840c040303024041210111002807190343c580035581c41c0c02740b40c0700f80688040f0000e0300115000100000d12410701e00100c60303052040718050081c903800d40d0b480780002e4101500666030b501c90310902003440e4441c51011003800b951070000300900030800100410340380345070550345022401c1000412039a50402c094a4200f90309007401810700100c0b1250500418042c3d00c0190b1080c10301e12a0189a89440f00810504030b0966090341e07a0f9958078184682d0350828401d885003540034002031383c0428403450a0347c1281902c1c40ea00c0c040e103695031315054000c0d002a0000d54040e54005604244683c04100720501c8030401e003001c1c41150701d8004040e01600035449008460b0034280000368590859135004d101030800e0180c00381d1488404a040c40e44ca02c07050108840c00c1d880c100109001c2400803d10240e80e0341a0701c02d6a00e0424100e908558805100008030380145030b03400700e2100200118003a00909225540c00103216805600c0712004103541c1030319050b140420880368120072 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 861136223 1250 861134973 861134977
    0xc030209090415090501110409110c070303080a09060f021c0c091a1216140306060d1109090f100b030103231908370e01020f1629 57
    0x40d403c42c1c3d154180100c0b402402d80a0700140d10014025480d041c00c0000051800020707105403250074000700a002071004c074120701480741d1080a81c07168025142000020310810341d00e5440b1032001c0d80480c050803182c0c0e0b01c0040d11003085014a90503004070380b41981c10612941e0200c9100303025003d0100c0812008040d0208695014200c030921081800341c000c0c5140c28112044109289011000c81c50310b0000e8103a182c3e041140c190006621b120183d22450b1203500b07072401958002c040c81d03e01403142c542c5d50007c20040c083c00880c04000e200b03200b900c0d960206803900c541c00c04215840e0515140101c521018603a811425040c0c03020320040c03001c183c9075100c020380d26480e015910b02904000013000c0c5070440881e000740a01500c07410240030030684034080c0080703840c5120440d000e15000740000c0150701c020300300c15450b424400045070f580c0d40f040c8a4440e8485041c0165244005540b100d00d0402c1100920745012601b456001c00600386070301400c000145115144801107030650b45003072240c1c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 861137473 1250 861136223 861136231
    0x80409051902030f0103082116081b180103061d0907060f08060906011815030c03020c19060f090b0f0601080702030a0c030e093315180a0609090c03020909 68
    0x20100171a02041c8d0840d05040d50035403200340b400300f820b1458907100201c0c01e00d5003484400d0000d0509008195004a0700941c02004909042100e007070803090000a10500080680030b4105500c0d4040085d0140b000a1240d082d9444655030312598523103400c1413850200154012010841603103400f40c03041d03501840154004100700e03152600354860b10012604c0741c001c00a0f1042046070050001803044007601e00000104154134140504a60780304194124003902180700f00541084650030700d1200040c1c42c210505200340000104d1000301c4034141c04503a0100011a542c1d0180e01c01e10000007520030095900c0720702441c0c445118035019070020340b03d004d02d6800e0310502941005260406000d021040c00d002c4c0080d0000340703180380040b0800c8401032001c00c1051103000480c160304040e01080005107280c14043c14816003286c3c207010216065010610141e02072401180c80011a5a00b40d05440201166624401000c1c203050400b011100e0140300c0205140c81001403014603181c8010303241e84 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 861138723 1250 861137473 861137483
    0xe070e03010b0a1505030a0212010b130f1503020739051c080a0c122c220b1c120302040e0601050318011506090e0103170702010507080409051902030f0103 68
    0x181d44400c40c07c400a80035102c111a5140c01d40320000c0f9460038003078080e0038481341403041c1f4110141e4810001c5140415130003510044160082c0c004241c40c025001000c49078490a508400801c01c8003460704247d110b90b00421075400c64600342c0001e107101541000181000b19400007991a205a90344003020000300024150310000c10703003001c618000c215851201e81c001c03c02c520310201c440310050103206455614200c0c00080c06080b910480d070950b01480b420300240ca068054100021300844212420070441712054130f46400700085d440d0949415100310342d02c01082c6090701d003480c04032100550a000c2d0420903106010411103a96100c2d071b100c0e0030120a080050380ca4541d004c20700360020f00d500003c50258240320f4011100b4001c82a040215002651155a0203403150603c0510420a100180450110040704251613411078000c20f444ca02c1414500d24000980e56512019009640036130072032a40e8404001101803094248007211a102d07000b1482c41c500707030300c0180380c20f581030001401c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 861139973 1250 861138723 861138727
    0x19061e06140306241c1b0e01110c270f0408071104060b13080c180a18051b0102120a020a060b06090411090f0402040305070e040c0e070e03010b0a1505 66
    0x1a0402c90b08083d4801c40c403610010030341e603102c0c0c0409680da10000078100c5e92250f103040c42d4141d450409100c01d0b4074210050766030348061049640112611202625145510f00420341011000c0c2c0c1c91143d5045040d0386000b505160a070350845920b07401200400f14480c00c0030480400001555920460300314640c03060311101007501303c0020600030820350300942c2419000240076040da42c2d902c10200200c400c0c02c81102e0fa649444005c0c01501e00c2031a0464a0010410000c04d01090154008038030590003280d44801554040d200e0518004250121160281038030300519810750f4180000e000c07868584524038608808150000d40d110f072800340c050030960ba0751104917a203a480b03e04032014844000c00900010480045000c5158000000244109000d00e0360b400c060a20b03001b50f40072203411001500b0010302d415034040400000410886500b603e80c840454404510f09005004824a0341d400840b80c80035414107007102c942a030703600d11400426504100c0240000750b02c044041c000d15040d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 861141223 1250 861139973 861139999
    0x813030201020f160b10121419030504090e030405090f07020109050717160f030f1b1202120a0b01050402070503090d0f0b012301030519061e06140306 66
    0xd0080c040c0c0b00ca400078a030342c0001d41c1e13408402d1900680701001d00401000c2050f454907580092100140e114500c503480c680049070740441c9014501411802d0050291038180e00c0c4003503150014170130182d040380840c1c80401d050040c0703000da201e521140b09003100290b203803e00304400506038020091407012440200d1f00040c607080c0c400e41080202903404002c2b00c45c07aa0b02c503403828449510320154011135110381241c030010210500840c078126128520300c0c2c418941180c5400490740380d020402e44012000180110800c10000c1c1e61b1030040c082007060508619581c8100440ea4551a007005407980c0f0502c00d610104604001d02c9045503000c032001a0343d0a1070b0b1510605500130718904c9030380301908a5400003130042064003a100c841c82241070300c00c541c0e21021032800c09216618902104c5c410f621510b00a94045c1e44082d8010400080059140011a900a095800941105c20140d0a170104007107040380c00130402020381a02e05180700749020f0a04114000e01004104911811340d1140c2c1c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 861142473 1250 861141223 861141227
    0x6060d0c03150605190c17030c2203110906010f0806010c0c08010e1c020a1e120f030e1515180106021606300f020a030911090106081303 60
    0x2142c0e9540d00055070034501aa220b002900a8101c4a41d48101407408009200c40d94818560a01001c5c0e00080100d90004540c0102456030002010142c42000c204040b4a250183c0000c2083d140b40b0034100359103070350940c40d01486480e00e000d2034070301901d800020f00c241a0380002c00503003000c5891802c12941c0d5103140040340c00c80301c40000500044451180031404503819040001c1d05141d000441e01c2816000f6002000e1240c01c80c2c072000160040780c9103030000380b10072550140707810300554005000e2005440310031100010300ea1050110754510f0000c1500b41d0980182034880c2c00303400c09440b00303454900403d01c00401c01403415400e680e40740d505400360307540c0c20480e601045d41217404100325a125000a03603114075002c40c81c0e080d804c1c045c000245a030b110720040c0c0a0500c0303080030840182e203540304400c7d423116000300c1505c01d2074503410b01c410030310141c0c80a0800390b0350310365006c190194141031209030741e0516100c0c5030060300d090005001e000d42002080360011200701415850800328101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 861143723 1250 861142473 861142481
    0x60d0302210904050705031611160e09060a021602040b04020c031303030905040920040905030a052d040b0c16030f050d020f120a02010e010501091b0806060d0c03 71
    0x9003041444014041c4910140340c8002e095101d009036004c0090b500c1e41e000640d11030104807404184000709008040f450b910a003800031000d02100200d40311204c2405180100c2c40480d0031940341078090408120741101c04008650300003079002c40441c075091a42840110000c010711010b4003640d01c44002c0f50154a9960460f014040c1071401d40b6100c40d11038085924803043d910060700050300c1a40082143d00e80b03407140410060f8000c0d00c4000b042080004a1100100746298035032103980c412800c400301c0c00900c010a10921690f903030f0307039454258500101820070083d140b51081103044101c400fa41c07220b01d0886080c0d456850b40c40f5281c1003580c01c524600190035400c0100220046800810001d00c1580d482c8036601c035005442c214640e400040341c0c1c1d00d08480200e00031340d014001901e112040c2070000c0000040e644008034030700c01ca040752542590f0081c2e0001c030010741ea80c4041014000c40070f105800080b090b04d4040b14074106580000d0203805420842824956189502c0c5a0700d8081d0340 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 861144973 1250 861143723 861143743
    0x402130306060f060207080c0d030f1209032f150417070302010507030e010b0a03141e0606150f070b1509070c03020d030938010f0602070f0e060d0302 66
    0x1e02440360302d442d01d4802d4094960ba20400b030142c8541080401c003c0c0c00844c2401c8040c0015003240d01490031500d0407100390003035005070800e1200503141d1001401c40c5000e01c25200e80a07883d1200142e407452181108161400d04014100c086010f813205074030004030b030b8050504c0c5190441e00c21f41d01c8a041450a14103640d0000c421210002411310406406411031071240070240c0301009061200c82c242030070303145010309056003c41c0b904e0091000400c0301c2c0600c0f070003c119404035100300d000142c1760f02017582d18400d54400c642c4624100101072400c0100e020584404014080c203160440246040300e000f13000300249940032107070001f011000e5004200e500c0800c002d00e200d01d141840300d40504031134002d017405d8005025192064984c24000d004e1351118075400042c07500000e02c2290509c01c0310f1300c043c580c804040d0191408411a0850300049800303000000740110120b0310300800607140290990006c0010741c55950308101c0300641ea8111035012909655000241846240c1203042801940b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 861146223 1250 861144973 861144983
    0x80f060c03060621040c060e0d032d0c110d1505060d060c03051b0306012f1203090708160603020702030a050d110118051905011814010c030902060904021303 69
    0x3001044100d242d100382c078005d50080c03240144654456100710742c2503941860460700301000844c4200020f01c9040c00303500300141c440c200640b507150030241201e221456480140001c0f00d1a0b00308050004d541c01c03800d2080300c125004106411150b03145006203040a03800301c1620f0307840c400503031603848240205810fa640715030308211291724040064001e2605130f0b04a400c00082665881e1607800b6507085034002c80050311100600d03c240d40c07620704582d5022100724400b02c816001c8001c1018100107120214010b00b00460f100c1c5004040c40d4540740b03c2d5800841d140d40030030328090031024941d81d82001d8440790b29000d0380c1d5481c01d0000c0303803601c62560740051851040305074188850383c0c008000c0500c0391842d0028800761517507241d0014801e10550300505250080c4032440c992944003915040d0017489200040382642185110b03a1800542a1040e140c01640034a540a116428860211600b4050504101c0103000e50081481402800702c0c1070b005507800110380894400300140c190045600c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 861147473 1250 861146223 861146257
    0x3040b070f0e100503160f1b02060403020901260a020108070f11060108030a09050105040b0a03053d120b01050402030709080313090507140d15210507080f060c030606 73
    0xf003803009007590701c01c4506201d030710450840700c01d0342403040126141c0f1007099a45d01900c0703500b80301d00b4034015243c0e0030205d80c0102c04100000050f01d43c1d0044074000c0c6900c15240402030042e50101090f88e509038143d502c240c002e407080c0b60041c0c1e0800803040d0420f0b1540380200c5844000e140544205840160080c40c41c41520000103442c2000401000700c8001c542d40c00f1314559641005490354007850060384003016090014851003480380e8000f6501c40703803004046c81500703c010402c8202d0024110460505003c3c404510500c001d003100a02c0140300c00c072a40d00701c416141d12082203403801801010305c03407034000000c90600b92050203400045c01c0c0b03003400c0d07070350302c980c5902007109083c2e4030712406d100300381464000f4400600601121174490505000c1340d1601080c10b6440c002000c01520480340480300320400f107503d441c1c118030800c014914030003900524003903003011458144030f81d000032a151f214440074841042d000c21081c4d0852454140749480740c070b0308000200b107401107080c0410a8108 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 861148723 1250 861147473 861147499
    0x736050c0906031f06020307051b0105040b0307180e0103051009141f110309030414040f091b0e1b0903011d1605011d090402012a020109050603040b070f0e 68
    0xc0b4102d11400740d11000b0304113040315601d10003a1b8a134020601c01a05e83d0b0450003015041c600c280b40c0b8600c0c40c440514040d403810f42c40d0240c41455030019150000010032914202c52080071640c082401b5042a000c61a01e540c591740d509641d0b40f0b9042d0b40d0011681c0c4441a0b00c00300b040007502002e081100e0b02c1a0f580010700542c00031070b210315152245a21074181200300c500d09500c001101c0c00351003010b001d036207060304151900300c080d111b01c0a20b54201e503071001d210341070380103d20031b5500f11403007031540148200c0800b2080000c50415081a003002c6800001d21114100300c0b82c2055a200780203d00c81e8484800400203801401c01051580c0d003203680120800c0c840d600451000622406c840300341d040320b80c45d030004440742d034a940e00c418180305c003c8140401c0c925100f500390360b00500c1454005a404a00c0b0003c00208030802c48910400340c1d1031442000b150f03001201d540c0503120503161b0509600e040d45170103003c0c64000d032402040c4120307002c001421b24410340507465041c07000b426020110350 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 861149973 1250 861148723 861148741
    0x403121701060c0b060d050604080309121204061b0504120203011107230606010c081c0f06080c040b0a090c050403050d0e040e1504060b0d0f050736050c090603 70
    0x505400131220824100001000c0b07240000061a0043c1c2020045c90680e860342c0c0c400410ba40081c1468815210301c44102c45d440341c051009000300c0c0c3d0407002c3c5d00c500c0c0c141890000207039600480842c8441c0d40e21b003207282e407182d0b02009407001c0700d514100d810801000b500100e401000c104845000b4000e0001c0d40906001c20b00081c03500300c1c00d04d034421042030641081480d403200c9082c2c8007140050340b04003140c1c01040c10a0060401c1d20491003c4580d14880c8030303958012104002c030703508500d5845060030005e01d6828400800800c105681c2880b21852480016170403062a000f2003104d84d61b91542a8001d52280e004e49001d507030700c101203600880946001030811000c0b00360162045082c484026003844010a0481c0d03011452829041a170711030b0340c1c48002400300c416400390031001050f1080045041d40c12290580e07806040940b0a0340e050505440300548008107a04210b1030400d2a0307800a4001000c00e070f680308004900043d40c0d01c0717044c03c1100b0361050810a5500030804818003042d16 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 861151079 1106 861149973 861149987
    0xa0804030e09040b1008070b03190902090c03040605060d0b06040c030b130e060f010803070f051f0e0f16050f12030307110120040312170106 62
    0x7095200031851444040310305884810700103050007040d89500c0101e42c06441c0c0a80507200720f40c2800c14811207440040c10030000114240500f40501305654003900145034010074100c000c0c107100d40781c544260000d50f81540c3c9649080e000c6903062170b2000f981e115090303000742c14107200c1c4d42d54010000185420303941c50003415184c10518106580c1d803102d406080441c00b000245807280c2003151761421390000c003001c904a440d00018403c00c0000000e440c15140c0c0480364400c1c1c0442d520b0500e0810140100c0022103201c00048010400c44681100325900030200460f015801180d4546035a42d02c00e610035520f040c5000c400344828204407a032071030a408003400a00c12400a0b0144c9031456204503140c8000820140000d19806800e00072000207416810410010040c1061400c0342403141d440010003500c03048805800c1180107141480d002c20300c0401020440d03035200009060a = true := by decide +kernel

theorem cover : BRFrame.Cov 860971223 861151079 := by
  have h0 := BRFrame.cov_init 860971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 860971223 ≤ n) (h2 : n < 861151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
