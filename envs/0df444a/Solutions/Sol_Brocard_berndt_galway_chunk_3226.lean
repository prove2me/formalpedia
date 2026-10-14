-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3226
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:02:27.289713+00:00
-- url     : https://prove2.me/submissions/423730ca-1efe-4b1a-8e26-1f0b86be1b95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 580035971 ≤ n < 580215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 580037221 1250 580035971 580035983
    0x106080a05100b07082802031308071a071515140405061c0f0203011b031d030f090a030b010801050403020d051218031c05090120031503070819 63
    0x8081005041d41c0740864088400c58034015144c80c405a584513002e410038072045140191613083c00003054415180e103040702d0300a03400307565614050b54603054480e426410081c030507808841d007407000a034002d207000304070314441c0c0400da20399440c0d1415000b40c0c041a8540c4602505100e0b0050507040865080810390780d0200014030042c419a060004459007226003a0f48110ba04140030200101c0d01003100c0414010480504048850b40100e400d40744240c0700f002c089603114a1a40c01103525105102c400d5444203a02c0c04c14520415060783da078018112a40ea80c001c2c0010b90442e41d9803000c0b421402140d000610300b0f483d61b13503181010300a080441d01074025015507a103000c42c03288604100c8440c038071620042009911442115440800e00d0842580c01c0d200820820744840da00c5503905440752111080801e01c0d00d0a1083c040c00e46d040700b0401054280250022850303007024000b56940982061306a81d4218030302400a0320305038841d8002e203c14000d03204d00b40c0403500c9401c06d14041030b000e44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 580038471 1250 580037221 580037231
    0x3120c13080f010b0105071505041e0b0106030b010513060e01030608011103010f05011107150c020405090a03181a090103330b04060804060b03030c07080609060906090709090305070b0106080a 84
    0x1500d0907c038003240104007406024144400d00001da10185d0020701440d440300407078440b0005d440000f05025025165152000010007007203034103000d694141e02007031038a0303070506068600c11030050380203029200621010190403400d50b48030340e2040c002085030f60020300c103807606c00341140c0090384207004914400c0d40c10726010409500648a0342c0c1312107003901c0108540303031404640d054807101c03c130303e0743d420000ca41c5010005640c07207000d03840c05840008003402090080749005402c58448009050601010072020400c12292265a040d00502040301c40e60320126200103d000b03108900030b1490780d10070310b101d881d404000a03e100c100d804041c1d00f816080780d1a00010300d0355004601c41d01001400b05400600040c00c150001000f030350780602143d0410700544101da0400643da00039044503481041003100c902c00400426421004d1100502070500305502c0041d00c0310850300401100075280c00c02c0000f0103108108803408a40c00c0341a0b2111541c440000038003c20045d86c040250900b00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 580039721 1250 580038471 580038491
    0x2101080c0112050a090b041b060e060d240f0e0106210902131b021005040f0201050c1f020c15070905130b0a080a0219060203120c13080f01 61
    0x154003122140503110100c2e01200756010300094440101400c040c0c43e01c40e80c040c0002249000f00710b000341d1003160707500349108101d421030340152480c1d800702081205208403400c054442c10100e60700c0d4100141d003c100300784a002c00c00200080d1041c2101b5801c9071400018008507444040410744441c000452210703682e030201203411964a5000020110000c5285080d43e03080f5030212040311320140c041450b4000d0b10300c0b110100c1d00c20019082c0e080b070424024810301c0ba41884000f01001102c5c4082207142800d4850102e40070800d0002414010300007032098806030b080200501110038030180c031035040d1090145501035045418101c019102d0301b14130f40740002d4000075940c0304001660382d869903030740381c5010403a40f013201421a0b15010b907111090005900d035200720324080c00c2550018000d01205105201c900250382e038009201c1407144e002480f90702d03070100448a001c80b0300004915142c42d07400080440303120701314045040150304000041c0e80480881d013000e8889a41c3c00801c101021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 580040971 1250 580039721 580039723
    0x605010207170303010603020c190803071b050c0919022206020d0e06030a140f06310c050c0f0d02070902040609030f0311060c0c06070e090601030f11210108 69
    0x11040c07150380309420600040c00f80d03e10a48c0034002c0320300d25400311000f01a80c094031403560f0150010550b0001c2d000000c010445412020b90b061942c004040129070700303610f482c2c0f641c5803001c440f0340c5481482d845010541100020b158103200611210045590f41000c071443c0c03102c48010404c54402c01e401000004d240e60020903158100c0400346c90f8035000c201c0d4003040000d5a80010041200706039291501c29508098038902c1d0701c034a000404615250a042081004a09110b0030f0f2028054008904424542d03c42c4580d403000c804014001c28004901d00060b9084e00602030301c00c05502ca280d007030301c8511200050b13611400d05550242d0301000e4548907800103900c182d025080c00300d1003a103000c200051a904400406034000d01e00025a40c0f1040e1500781485820341f1038641703480f0b0200710322201e0076041c030031035070010031a041045840c280e01c0301181d030303842c801014641410381e44d010030000300300d0b0707034100c00d03c40707000048a166108015010390782041d0f40701414121800c0144004254000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 580042221 1250 580040971 580040999
    0x20714010203030f09162d05030a080703090308030a05190b010c1103030c01050709080106080d08063d0323010302061c06060302040503010f060605160c0503030d0605010207 76
    0xa069000d9450340d0b961400100014001034003800451151540c03142c0c00f04144510400680790086403001c0e445051081a21100c420360240b41e044040c612040040da0340c00603603122061b074010300980e11103841c0c0c24251115996644064050744000041010b210030b69480584140d8010f1040c94040000b03080c01b81c200d82105c4005408a002442c03000041031005000408100300142249d00c1c0c4070030641c070b640c207480e001c0d1035031804101000e901340f243d02001e000311405011342d40010014035000c401c0052a00c0c501519841c003400c40c44507001202e240d03050fa005030b69a4420f0216100d401017000305c013200d503030f041c21010020b0729169600708518071300108240e40c1c00b850124007855908580800030540c4c01204800d5680c7d05080040050030360318022200242082c0d01d00580300c516040c2070500f900d000340e440449070342c40d00b8014407240c0c0c2c00c04151084141d0410852504a996251010240c0c109401c40c0c2e50501c404900c8241482558100300c0c203a410030b03030aa07960309a6800c00548611 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 580043471 1250 580042221 580042259
    0x19050a080f040209130f1e0203060c072001052101051c020f1512131529030304080601030b062418270a2409180209010b03070207 57
    0x183e800004661701c442c1240b580790710755006101280091076540d4914000c40300410901c0c2040075250085400e5160900405a11640041c04c05241c14400d0f039424a0714840064130103101e60000702c1c0d0342c00f282d01c141c043d01c02119960b83c078440e40d040d50b6050300302c3d40030007440b4151250703000e4540460070050001101c0b00866000d4501e111064a207410000d90b102d01840f1401c07000c80c28440e030049902070f0a400750040507901d1240d100301e840e504240b1112a02184900c1c603050400f10300113000c0300c258211403080e0b103807043d59400119000002134110b1003240e0040c00144110400401031112030010300c0c0c0a413004440c04c442440704003e00014141c054a080a03204d4002d10202540380d0b52109103c050b103070001c1c0600c0360b80d1501c6011031240455040c1001c404d4500380108401511030b440f50403150181e40301847c1c0403100d007070340b805d04080450080721003140c0c40e0028a10741000003036041854560090030f10b4215a111030146120703803c100e60303500c014131030760b80000b64000560740d2501e0a8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 580044721 1250 580043471 580043479
    0x705060c06150111070909050118021e030111040e01080d1806050d1407050706050f13030c050f0708030c0606060f0306240d02090307051903140319050a080f0402 71
    0x954490208860311a0002c000340d06100b03100841c2e40d4904001d104030b00191080d240001100f103010f050540c00c6409000d00540040c601c000356101580e00c2e26207211030120b8804003200421090f00129000d848081000880403a0204001c40e101c51450030f42070594401c0e90441d800c0c2c031900383c0c04036003050500c0c0d034055650b0713440b90051000c079100c0c00c002c2001441502c004203c508080c6c0400701e811a003143c0001c00110301007407203401c0040070700441d50086201c02040406003090340f0219260700c00307210000d01b80084500d8503020013400b889032a80f0041e1440550f00d0140c0c2d1494000d49a83c004d00440c001c41c0186d03000104149400300903204650052101c0c1d60450355000c0901c03030810000905168482c9024030546190b403202002003241d890b080e000940c82d1482c407006e1610b040c48039000340c4d100300c500d449030741c4107903c032440b0910032243c0013100c407041c81f8030740540319045100b80d5002102101d00c0c210340b01c80480c2c00600130242c0031101d40d40d4480540c0c54003544041c0c04801c1c0e60003540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 580045971 1250 580044721 580044733
    0x80318010c0f1202131e05030a0c2103080601030f0608070b0304170f030408091c11190302090621030d02030417130608060f060c01050108060906132d03110705060c 72
    0x312041075140314100b000701c0080300d41c6d002c0d11400000d01c0c0c01c0301d03c001212080d15010081c0409a001f0940b121031603100d9034060a4800e04e80d8018080041c000e04040c10140c2d66821444c002d4400c0d000b61000305030020550301e5198440011030000e6200301c506503075540c54003209090b038141c018211590210903200850554841c0d55800c40f607a400f120440d640f18203488400c59500d030703805550100c0f95214819002d0225002700a00541c1150081d41d0a0300c0903400d4000c10158aa180419a006031304036841c902e80400311700d084c0c0b00da000790342418030310f407001003400181807078640d00a50007180190404820010907040d0704e1918420504031640303e00c5a51020081140100003250300010000c0c1900000180300f070100d01c081d00994115080740e0345a10040146150500020b50031000b840043c21042c607000003043c41c500d44a40d8010030340080180b03440740844001d0700390150424000b03400303181d9a49a04008001042c1007041341c0d0503010340b01c400501c0b807a00380c044500ca0002503002d060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 580047221 1250 580045971 580045979
    0x5070c12020109090e1f06060804060f09120f1e0509120118050c0f010c0c0e06040908120406050c03160e040204050d0506070306120f080318010c0f120213 68
    0x104000038800100d0500601c01c902040316142e80c080c148008480074010984d140c000c540282070f40301341d00450406035241c07980c180003569003d142541c0c0260440b001003141c00c40042c480300102070981c005020402c400980f0025290311000340d200b819029903d800c074040804040f0301141d8040000c40340811410840001c5c1802d00084c40319090b00118000074140d504041202c43d0f000414800300c900b50090310001d02640f40106840402000a03e030281c2020800e0b91401c108c0e85441c0518050800484001740750b0b6600ca41000b00070603402010207807245050001c203100100d00365012150942044006a0804014015240b151500c03031503021100641440a0300d103844100c0209403c070f07400b0000410182c403201c01403202584603400900151801e842d004048503540d421243d1003000c10500c00307021030100c2d0070741e00c01d094000c3c100d90b9580d12180b01c0c04107031007142c2d02c20101d40d50910745085030b5103811071140c1c510868951540e40101c50300c0d0340e904089205445440394078000800f001c1c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 580048471 1250 580047221 580047239
    0x12010302120a02040e0703021905031908160f050d0212031314031b070e04030f0e031932060a110c01020304080a0905041b0302030a090c0f050301050705070c 69
    0x105400356001c0c0c030303001891500801d050f00c040800300c3d180313581b08100800450810b00c054020141c178074a1003210301828980025224805c050a0303141600d1401c0c1e14806010044084034841d10113842e600844501d18a42401d14031224041520180030300d0380380501080c00840c2940089c03240c0c002d1280303142e6811440044d0074034021000e4640c001c225640300a0701d2010001040300c100940c40f00088031076040e4000c0d1801143d40c0000101005982c00d1200103604003004003d40000303410b00310055003d0710302280c43d2280314203500c11030400b8400c3c80000e00c803003081d00d445e00e0034102c1c1004400c2d0040d21341c0b50a54030840400340030789501090015004242c0343e0300650960190084d25480c08019122031402da81050350240e41070030002840342900c0c0e8100c403012004103000e88051040781d80303424054204121158010080c56000400520050942d42c409501e0035440800b01c1c5405440f0296082d04072200c1c01424001e40ca401c0c04038036481d000300192060f0321b52005141241a007408040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 580049721 1250 580048471 580048489
    0x207050a09150506250503070b01081203190209060a0f0207090b180702070e1005040510050915131401030204110c030f0903011103010909170a051813091a010b12010302 74
    0x1076000808103070b050070540d654400c145c0720382d1805000290f03120041400c00745902c0b681a4031078404c90b40300004800707010352230354181d0741d1005248040c1f070855000c0b90302d150042c3c412402425402040007440070034985c2c0040550809040c0c0394226284c0549424410b400c8494140782c0551004004808000302c1c00400d24280e406601b6105581c3e40716510341d50300c1d080c40f406440c254808407814a0600203824070340304041e40f00f40020f131541e0900d0710b403401090281501401220301102182c1090b00c2a1721030614100b01e0317007145001040391401c078480e40646000d003800224030a41c14141800d907200f041c0c0f01502c03051035003400691f140041c054024980c680c4400e440640654960000c581300801c900013450003001c0751003012420301820301e090400c61404c00d145449158050002c50200340c0d0050685101c40100d00c43c44000301c10311000580400f02e070214000f2441d040c540d1700f404205400309100c0c0030712030001c44003240da6260464403543d4010302d0714240407903000000400c0586002041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 580050971 1250 580049721 580049737
    0x61107030908210715060f08060a05040b0708070c051009050c0306090c09090a0b010906090506010c0c061b0524070207080c0f0121020301140f090403050a021005070207050a09150506 80
    0xc09041907403450045d003c5d0782447e07200405000c1100700401200d08240071840c1d105100c01c80c104110320302a070b5554040c95014086404101005000502080c02001c501004a030050202e881c040c101000742000303025403810842e101c0c0a01c880b909164100012043d001b0b00c1244040d00b40b400d0341005000c030001000740444e401c0d100e003010020220304618400d5010b405980d4020601d182090035081c180c4d400a80554100603101c0701c0d000208440e80e40110583d00503140200d064800261803500404241d50050705a000d46240100322003207465001c0c1c0201300000f2505182d903507200050f600c9001e18844d00c01309404c00394134844541740c003003143c8803040e01c141010780c1242000da0045d900e082c0e0402800007025030010061140b000b40c28111030442c80304844170310b841e00b544400314a00b803201078030040a02a01007415510140240007989000182d66001c00452909a5009641c0d203880d10071a8050202c4100101d207241c0140107186600c14103400e40b500316032400090103642c0d807114007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 580052221 1250 580050971 580050983
    0x1d0105010f050d090302030a030c05090f061803010f0c0206010503070e0106030518030d0c08060f13090f02100804030e040e0d0f0315030c140d0c06080c070611070309082107 76
    0x81000e50f48007040c0316510184c0e009078021521940154070240071184503498130014000b051014080f585d9510a00000515066400c241c48260520120420300e108800b403544c19402d02c0000e842c010600e5101c035200d80b4103582200e4580c0d903254203042d20385415001b401444960000107208050190308051b401c95107410345000c96101d60990305045400c80d10b8030003589d90300d50300e18500040c1e1040c00310303400103000c0f501081c1020940c000a450850440c942c0108184c6812007134045c00f0f002911701c54480c0e005000038120300c09003e0018891f440807a4100c012620300e244901e8981064030580000c550b03001b008080070800c191095403043c4594182e0420036840303500b2150000c1d40c450040000758482c00d41c8030b40090170181020401d4050b851b405000341382c50b001d0034002c11041030a5070102c0b01c460170640e1540e2518002810b852050800c0680711500305007000c194504000001c1980c1c0c0d01a40c0c481c01988d0310303240035503119810800440d900074403407200100f4840081000344103980c0318513 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 580053471 1250 580052221 580052227
    0xf0e1207110d051507020f0c0f030a060203040f1406041a1b04180f02070c1a040803030403120e01050603120d02120108010902150a090306020c161e1d0105010f05 71
    0xc40024080d518154040302d86130080c00d094500040452601c03070704603103680060304008a01440040c0d544e24803d5000d440b94074038a01040e120f80b4140160216503030441d0082d5528905820015030111860304207c0c0d490000046032004158041080d50046501a071040e040e100703003117408011508007802d041c410031059214401803440c90f000810007400040328100d0031100503080407040b540c4030704111440318010803c0d00000b4035019600400e80c0c4501100f044028010318002109004a400800307440c8000800d101c01e00d81c005900302841040c00743c0030700496405030381d41401d03543c00341c840d20f42540c016104200041d2003440a8a41525101c10050074540308915149080300c1c05e0b480614a40d540720450b0055041000e12000f14507907800000d440c051074a000204800007910001e00040e5020400088840c400d1151340ca0000307c0c2c1d01d040c40344036200e041c0f06600541018035908650180c91001550703812075004803404c240c10071701c4c0f115180c0c684001952a1501901290100301c010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 580054721 1250 580053471 580053503
    0x739030b04020f120601050f09040f0b0907150c0b07180308030c0c0703141c0509010503060a051f2a1b030f030807021605031902012606040f0e1207 65
    0x4d8610f4008004544004006951610003844240016004114082d031108030400c404509000c12603201d8990003018002c0d5941d560000604006960304200525900340d1903542d2960751260004140c280118244205919520400e44942c100e916094030b02ca480c0d1181040842c800310007540e40403203100c503418071700760707001c2c81c0c0303505041c0d4a4100f03c400d4046a4001c403c000c02c108034401c980d81c600072583d800910321030303000741550055520b150b041000000000b10b454580e114071500900e4081c06c60700008100b402903001c2c1c1d402c10700e01c1c1400941444651074111141000c80030300074110320100d0004042c2c07600d9104940c02503441d082c809289200001000a0140e00b100005038084d6a42d9500f6003007c0c4002800d00b85441a01164040c00c103100780142d90700411402810605440e071844074034014801607403481d484001e074ad400c078000001d500400c401c0c040100c6219070012a0304001c0713080360315900801c40d105090420020342c400241440d1048008005200f034902800c601c1c0d03101a80c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 580055971 1250 580054721 580054729
    0xf02240c011a010c020904062c0c03060601051c1802090709061205010e07180b2209150314012a021504020f01030915020739030b04020f 60
    0x8016000c8455a540d96215080c144900701503000b001c10034a0100182d1815400050030b12402070806044a66520f0800512030703400c4032041c04001d140d40c500f44580781c3c4010503a481d120700c00c2c0c2440c007d0107060300182107503118030101c0307a440c0c510802c814607501000520400a080c1c018030300102501aa1007840565681c440103442003080f81d48180440c1e003014801802004d16183c900c800c01d017014018007503c41001860790f406002c0e89007042c004901c0304d0180c0800b641c41d5108880503400001d9500e0380c03e0001a051141c01609810000d480d43c0e0b0341d0100d41240c002c40d84015039070622010138000150f813452200e00c0200c0d210000b1440d060a002c440a607000612540d04910b5191040018010b4041c084010701824801c0410b00a18240c0c020684160018400b541015640c1c01c1120800c045202154604420903204540310034840ca0200c624805901c1e480c2c25200a40e400420309148111011607581d003208413810380c80380745607112806154040c000b00c2c2c4c45851079010010a8032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 580057221 1250 580055971 580055977
    0x203070f0c0302031b06040b1c0509010b011106040b011202130c03020304020a050418020f1305010b0a141c090c0905310b0c090a0f0815130f0224 64
    0x80500103126190b0324500c101440c0c920301026007103c60504503107482441d82ca1000742d5003200c0d4550485035940d0b01c8043d1034498106540c0c0d800320341c41c3c03030030742800540c0c0c40552040c03010140a8039010103904100250030760b501c80071500240f0070350104006000c1c0c2101004d0021090744090403100a0380642c10307aa4040e00c10341840034001079404020042585030061811004201c1a2006c01650145119030381079541d25120103405540080701c80c04107a00c0f50114925507090900c2c0403c0156100c81011a80b5070111700ba0000143c2c01d03645183c45200b5120844142202c1d8401d4003aa20502c1c09804c0050090100190351140000400040d19215401942e1242441c0c00c5d18241c1c2440c0041c000b07107001222160516860803503180c0d24001882480e2a50300922401400d17030701d440004001420704240c54100340c41120f070300d820001e51554000b4100713200070700b0380007d003407944d45880d00100b00c48450800580024400c144d2200035007440e00c0c0810806085d88040c644810000d03444d8001a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 580058471 1250 580057221 580057223
    0xe10110d24081c0519140c0a050f010b0a050109060f030204031203200412030305060d0f081213030509011107090204060c0213060e010509090f011119090e0106030b010203070f 77
    0x1400c22480d050302c3d6503400106040c00c06050900909010400460644016aa114943c24081c00c103100743c10b154504004e5512150000c4222000d4443c00d20b422621001803410000d202e600346030410000c0c0c90202400c400359001a034620040d04e1610324110341c15030141d081030003455420440400820f5054010ba8080d454985000c80c50042c070001c482d1102c030b480c580c6100c0200003030006000008000d80c0f4510744a41524010820351100d400040150110740e1004002d0b900040400080000000c041c056159031686501104ea4444820300403161440f880100050003c204500442d80a6042c14402c2012413040f0b507541034642d804402240d00a400480100e0f40759042c0400f1464405200d00d503d4086c524180070240c60300e07544030480e840600444e445480c0b40c0d4001141e0503001c00011000c0780d6007000030322076030215000174034555121300c40c0166060b0041130040355981c00380185908a03140c52a00750140d03841d00f83c2c11002081c1a017030550450000f080b030100445c81003600c1c100380c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 580059721 1250 580058471 580058473
    0x204030f03080f0907060f030b13060617010303020a0b0c07051e071e030f050a0c0f05100f0c0b151810080a03050415050403150e10110d2408 62
    0x9145800d0103001d001c0c2c0144212001054642000b41e1154041443c1085407050b06100c418696621001ea000d05200f80e04550443e8028036094101109038000c0e000310345082d02d8200400c82d91100d901c181c0c072800d01015015038030003460381c00002c0d0080c00341580910390740c0c0c0680c200911030f40c0f00741c102000e170307406009614140000e55000c04002d00c03140d0006c110032262040202c11580710803500c2c42180c0b001070604102030514000303101050120283e40d690160003011407503119140920034240a002c1c1030f02640e1070452048100380079111a60440146417142a06820b06075600c400f8100014140039442c600403a894140f42c58110b491405112601e81d01c10003842c080300400d904100341ea100f090a544025422070229801008071419500c005401c45c07849407010105a03418400d42e030004201c050301c0354410742c001416a00210f81e40341c06909854103100c0c03070807004003039500b0321300c45400c0220b0030005507020344181d034082401c000b0b0080c4002118040c440900c030459585a1012541e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 580060971 1250 580059721 580059743
    0x91c030f0e040b030601140a21060c1119060209040c0e0405090a02090103032303040501140106050901141308061807273908220b1306020403 62
    0x15040d0001d5120030703680703001c0d2420080c10700082c00082c2e48a406100790740010303640d9820751034a80c4803180d000c1d0240c482c004294080e001040e03071f41c044007248510196606803402d07000301c0d107541c4100280c2c6018100349008000c1e2800822024005483d440707001c41d4010781c20402e0008545a074024959400d031a42c84481e0bc6228000c02d010580f003004164500d9504218210401a9980e8600f541542d0301031604250b4440302c407494514510a4075503c40359a00048200020000150420b1120b54950141003ea0b40d030703036920a54641c0258a2210f011401c181c12a614240c2a074000e1300ba500c00c011007900b00990707078582e010304103070043d12020003491312011b100c8004603003000031030000c080e18a2980d101d44c2005681e0081c410f01c0104c444032190302c0319503010451440018001090482099000c030742c140114040243c1c01d0b144003002c01081214002031031905608403881c0c1444030411412551000b2036850180e82200101502e0a0540e101040340100340307103101400165200b4158854 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 580062221 1250 580060971 580060997
    0x90c060906080c0306030703080f1314040e06070906112d12120a0f091a07030b0a12110303040306090b06040b120c01030b06091806040c090e0408091c03 67
    0x1200b40020203440e400241041400030340c1d100022088101ca80280c0465103800c000001c001c80741c0700c0c00203400f4050030402004203603110b030f200009504610865041100250440b0801c0c1c40e1101120840045001c842d0100201409151768044900e010b205442c43d00009010341c640000100325880751441c000407003004821420010029441c403d1480039081446030300165091b8100103104008103901d601c0c120801c1a0b00750403045040b58880c2000d06407243d141030420984804440000002e800c240c8003140604200322030000380d03403440010260a4800752140c0c0494500714a031035030141700c10000000800c0c3c10b8070907030404520401c2491074a082c41070400041da5400340321039108502007003c24103070400005400e181c0d4402030a0118610400e0f030f00081c1d00713000f4803030300c25002030032011855030b007240f200e2a0343c1c421030080b1410040104040f0040703c0392141030040c2501e09401502040c00705030b07070074003420b05520000d19000300800d003a04400b498008180c800c8021486d02c040303c038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 580063471 1250 580062221 580062227
    0xc08060103021804080702130209030a2d020a03081305120304030501052226070302010608070b072013020a0302210606040303030b030c0607050604050c1f050a0201090c060906 77
    0x6a0085141543c41c409828140c440784028456400020702c1504042c0c880c940c030240540517520710050060030340c1c0b03098045040c0408418540404c0c044842d034001042c01e8080c4643c41c0c41c824168010700007540081c29542c461110341d010211414188804120001d0711b44e4030150303000e019039a49009180c80c0c1e0703d145401f50035504043c0000c03440f000726800c070f02c020310b40c88405503040c07a4004050940b01038030190301402a009801c006c407400800003440105054054000c5412180804121104030366140c6420880d8090140000e050100203000901200c2d100d452440e20480001d00540c000c030344038902c0c003041b0780c0054044000700307401141d0300890303030102260354011000000c4444210300c0d00c00001900c1c2d125500000f414580d0b10640240f080c0c5040011038000c0300054603050343c0d54440c0c14050b40d502c00403101260076105204907411181440b43c558604400308205065680040c40381c15140c0b0381040915004642d6154090310109900e80301d8440184100d40302c440485041403001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 580064721 1250 580063471 580063489
    0x4090c0602070b1603121b0c0b0a050402090f070201060b030420041e090812040602031b12060111150109020309070602031c2703030606110604020a060f05070c0806010302 75
    0x20034645806100d0003a001d404d06404030711440d03052070420702d000d00310700030b600040c0350046128801ca103030040c0c0140313400d4002c80701615540c000d075011016640d0b400100780c241c80d01245c0c0290040509000304001145502203150483c00c0e40c000482d8070760f219550340589d500300b1102070301d640c16480100f1001c480a4088120003807803e940502000004088180741c1995002c6480b000c2c0d40d0300c0b0160010311004909840d8407031081c0000c00307020709207810000d0113504140c0381a43c6c20202d08100310003d00c449802c86507030203001d128541440c6c3d41e02005480014010506d4581d5001c0e607090103080038211101a03020341021180103880341490314403075150000d03a4210805544c0f04000f40c11181005815000707200408250201e00704601a581c0c11004000b011440c03080d0420f9142c450801d44c16411a40544000c0d6951004507208000403507903d02c000d03075020350000c50440c070070300c0304601c240402414800c8034101a85003103501c0c0d9940d844d90120f5404415503400c200c00600852404d8400c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 580065971 1250 580064721 580064729
    0x90613020c1f09030e091b0c010e0102031503060f0106090e0403030612200105070c090506041b2a020d02130219170c070314210415050906190e01020904090c060207 72
    0xc0c1d58500d440241c1c1002e0134107d0100d21100580860310240150b025002039108224210080d5160b0400c0b2a000d490074000c0e028180c801e0007a900000c050094400310281200d02503562025403526040d49204d4001b40540700750304261325400c4c0802e112205182c8a40300c0343c8542d8107120200c40036140c007151000100d15180c10000b041080401041c0b003039400501369044114001003c4c4c07660301c0004c00400b20000800364080018101e8050517810581511905207030a000543c02000258010003000601e180254004003012010000d81400b2018109840b0704881c010310b00152121000343c01e051341066a00010142c1e0500076000e0f910890340c43e00008400b11007420301d006030b54041c00b502c19040300600007140205885003005420700510742d00d840380d02c042c001030b802c0906040b0b80f80c065101d801c90100d420310012501c1900b0003c0e80c148078603501c075083d9525a40349041080a4105400038030b4031590203002d2030131b03266200e200b00e0000300d100e001e100b030b240e07407800750064280030807a40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 580067221 1250 580065971 580065979
    0x32307020a0f2d1509080c04050402061b160b04030606080a05030712090306050c2208030a0e0414090c030609011815090b07030e0705090613020c1f09030e 68
    0x202044046401c000f141c0c80d0307026a2aa0054841c003030341e0843d000005130340c010620340200c102c40f02440c030340058045094482c40015540003142803030034030064400549009411100400440c0303051044000f120002034420b42c10b590301c1000b40c034107030482131080e90491380c00b110380003608100304401882200003e044a001619007850240c503607a4407802869000380140384410f00d688030140c8130b681002d0155902100030005404d0408010650342c0020b4101d000c002014030070300c2d101007401503141c000c0750303000001546450001401122264102c04602d904540c503104403500c200307135241200e8400c1d0b0b558002001c210400038201490001c1c05071108003682d06d4601805084240044070f01c03034140e080f5920a0000403443c00100041808050191908030702e901405a00ca605810840d6540000401c0b103035040d4459040100c182020381d8407a5000c5019480d0103825402da401924118040c01d042d207035488a40340c40c1c5102101003410101e1000d50b100c10754408c0540021181c0c1d440d0f40c3c01d807 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 580068471 1250 580067221 580067249
    0x60f0c0601060504171f020309031216090519150c0f050c180c0403061d010c020105040210030c1b1b0b0904182013060305030d0c18030f032307020a 65
    0xc1400200581340446c07003c031b8190004000781c0030100405c01c0701c032000c0448901c00002c0c54000d03000750041250300341807000680011b00024052402c16002a504000801c401c402c9601e010b000c80301511407504001d040c010480b0b90f00300814004141024481c4c020000780c0b01075036000003000040c040c5030500142c0d406c0101d0071300414801d08801c1e602601c2d4000000540c2d0340030fa6445d80101d4180c2d0640c02d41360b608007841c407850140e040d0082c9000f40c0c803d5403201c2d44045015401c2d000d44840e170925038002303441d0316580d14803080c261090401c52402000505540300451540b03483d4401d194000507501c4a000030005658146803045407640d88050038400001002c5540340811008100b02185400d01e15034000880382c1d48800103100b6240e64102c040166541e0792a10946075000460070103c200d2802d5080702c4458000d00000940003c0d8503000301c0c4480c04c40d514400f641203100310581c02c100c80300e070360440c51401c10311200c1e5a611003003d82980306d104620401240040641005001883ca0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 580069721 1250 580068471 580068493
    0x120501020c0111041503090c0e01120c06020102031909080d091a010906060f0807110106060c060e0a05150405120a0804020f1008070509040b0402073e060f0c060106050417 75
    0x8603c010018805e03450f0210711480581080700041c58140c10012030340912000000d00500c1e1a110100000d101e4540440420f5440c1400d9080b8082145c1010400f407450a41c20480007180e880400042d1080031800d06004c07241c10150103ca0074440700300c440b030001004904041e24099040d60062507291000c2c016030b4103029004202d060340c812400d05011740000800e0750203004502c0c4510400740c01d0300030807615070703508801018000210380640f2a6032402d012280d505c1d0000c1614542c09070420010064080900c1c0004541c480081041d100e60145642c211072042230b1b10020494401190b035a000da5041a004100200c0010b069940c0310b554510038000201c2e030004042540001e65060040d154103004c00490098221956016400351000451f50201b02c805910045012410f03075045044440b07506030144030054560100b200410b041541a1183c40e10900070a156400240a542000c003030b02c40782883d04000b80c0201c00801c2c00401d0030320030103030707000c104038044055103000b0102181d038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 580070971 1250 580069721 580069739
    0x90c0f0602100209011209110a050607050705060a120203130c08010c0e0105031e040b1f030804051e03060f07022e0b060405090403030504150501050f04090c120501020c011104 77
    0x341400c80d0725008a0100466030094681100c030f80600d00087c41240340914018099501c54000544240c0c501c080200e05030070250309540b002c0707030f1083c000e00f4001d00f040c08220305900700c0c0700409d00700450a52040c03546881c9001950203024800c0503480a00c000c1e1512410700301e00382d00f0140d01a858400c0702c01025920414000c0c001d034007820425540d8940e09664440103140420700c1812503c4c0c0d81c140810080042c8010780700d8034001d032042d510051401e102d4607806609100191130a04288070510103480c0a40c429034030350440421840300300301c02c040442e04141d000c44050310318400720010031098035014801c030845c00c3e2074842581c51425058880940402d0600c1d11081200c0da211103000c803580303809041b24042c0100605001c035a10301031600501070301c4101c400305c0d007000c01e0311920300c1408a1030141606a6100a00012b0295044801c0c80000c00c0d200700309550202410b01c00007864405025040e41060145001507a5030101c0d450075825201e00e01c4003100c031100c003000108101a5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 580072221 1250 580070971 580070983
    0x4060609090809100908120d0c0507020a0e0c040f03060b03060a0213141912050d0e010c060506040b27010524030703021219050a0605061c140a090c0f0602 68
    0xc3c1143d03000460181c0c00402c549080407901306510302c2c03040d040744610442c56840548000c00901006004059080070101c51600401c08002d401c00d228203801e02205810f40911603100c510b0401c2c81c2c3c03c140d03840221044400c0d060303006460199440b9a0f081080c2400d002082c0e010303030310b0807096180c154400c400000da04154819820307004020b03102e14006c0d80d254110100f540031100e03800e42e80b040d00e440000d184001c50460407101c1d4410b580c4510701c0140920f04020124105031141a0303001c45d540c540300c028020051426074001d6452171a45655178900e46051524a18280305803142412440c2851154006810141c41915005c0d1219443c168007907500b000103400c80b50068413034841180640c0603005255071580301c5000082000460140d50030000880d10641e10700740400e0301c1e20300d1914202c402c00d0054030381140d000c1004004584c1030310042207000b8650030b80000ca9011701040c04400001c240c0700c8a00040d115010b00040c044c100c2c04034406004004804201c071031903c2c0300607507140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 580073471 1250 580072221 580072237
    0x20c1606170c0f0a0309080a0e031014011202041514040b030f0d050a090e2d19150503060406090b0705031927030804060614010c0206031f090203040606090908 70
    0xf02c00011141641c0340702c0c2c0c02c90125075a00010306500e44880001c05412603d01c0c065283c000e105d00158241c80c070780706000f0084c03031085040100d0166424144800311880d1701100aa030029140c201c129101310521030002e000b804401540001c0300094001c02c0249c48004050602c0380d4042c8081031aa0040840d161203501c80c10705055a0340c130000c81056940d0b40043d40803a074214802c008000c1008201d585400c1070220300402c50451b4001d9081c10840d480d002c0c2c0c0c1004600015850903194040c542d40049681010340c142688000d0703980001a02c0d00c43d0407141280c0858507032504004001c001400d140c4c000d0b10714280305040d40341c0342100e00014031071541541026a00c2c3ca0080c00d04070380112a03d0084202d5011800e6040d01508000d011248240c8048801d68600381c0c000070a07041c0e25400e490200c0050b594030040036055000c0021680026104c1111103c6a20461015481c0908990001d105441000d0780324541400c0c1082100c10b503a000d10800ca017030041030000200c1003012110f0300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 580074721 1250 580073471 580073497
    0x2150c0a090815060f0a0825081912020304051003110f0c0a0b091207030c0c0e130614070903120e091f050a0308031801020c1606170c 59
    0x424085100711488101e541c0302042d103000d030340402c1c00403070b1060000710b21464043d10f2001e5082000d50901c011000648507001d5250050b13804c145000c0485007041705541411082030204680b28950359003400c101e41002001b1040d50300b00502002100d034941d040a002d507001075800c0a01c1c0c5800702e81c9414881c0520000c05589103074940d034595400e0203a80001d00006c46894803414166034865551101800944405242e0300c0041d01c2c0c14800640c00d41f1190b0300917509800d0816980c0c055070501c24800044500203030390b4401141d040030f0921300394454400741c1104061421030342400c3d021205440e0881b45202c80c07410801140a40103848881129407100c3c40d0710f40002d8190003100d00c0d5a25540c05a4002211414001c855650f044103804809102182601565440d0200320801a4034070000f0402c000a10005035856880d1802e00d104691140006d8900543e4002c1d0f5414043c0c011200004503000480074414554408a9250030a02d880c00307040180c01c0403001d1440d43d0281e40c0494140e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 580075971 1250 580074721 580074727
    0x307030b0f07050c01060b0a0e0406031104090f0611041503050705070f060902090103080d06060c0f03030c02190506041a061509040b130207211209110907020f0d02150c 74
    0x9440e101c0d00c101c0750798003202d01c006c004a07034940642c01d10591084024100052120303203e982c60340741c544030780c1040703070303400040024100000428070001e031100c030034281c4c0c44481444456021403400d000d040d0403d00c0f03520380d4070340c0da508041583d001400300c400c00e541010301e4a02005401034005044484031a008020340d02e0010061400e6400b500b40d84074001d4202c010040000b080080d80405480004182c0d2014010350303440d10b0044800d844071041c00340c8406400020480071902035882051111954810ba40115000d42d400b840403603480a800c89995000380d081105024004212840491681c0502c980780d040000008450139014183c40c800c440e000100402195510760052260303e00c00740000a1070002080b500300290072159050701c0301d40025054003160190244d03074a40850343e58a0310410540b4030403249e00185400442143c001800a108102c29520540d200e44a1a0a98001d2010302c0503400302034207150f04003000780e065520500c00310084041c01401c45500007000030700c080d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 580077221 1250 580075971 580075981
    0x3030a1506020d200d031a040b03070e0c07020a1d0105151e040f031a090c180712050f0402040615090324060b0d050c0702100305061206150901050307030b0f 69
    0xa000038001851344a01d205042c0d0700c1c04065015000200182c20106418108664900c1400159200a807400394950003404052000b0126400041e80103d5175440980c244082980443c95000c0940c0209408000d25040c106030409159055405404265201e04251100c6540b100403800f40300b6425961082181140c82243c0380b0505550090140442070701c0303201c0d84c030701b8080880b5a01c1201189103d0316200044d140703034000103001d074542d14081c009101c1c01841c120340010200c0058802c0d010012100c1c00c0042d81d454500950b80100e18001c050f44082c10705204000c200d034520360101c410000030904071a80d954121406504880e00040d80b003a003410b094510303000c442d60280c050707541103103010b101040760300141d0041c102000383d0501c00c01c4151242d501840480c05a008000d50090030201c90040e010b05c0b075003055800000180400030740040d1221058140041210801980c89208103178907810724000d19141c3c0100000e8024080550468035890702480004144642105244001c25 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 580078471 1250 580077221 580077257
    0x905120c03060114040f0c0503130507030606030819020606060306040902010306080609010507020706020c030309060a17190c2604020d0f0b011410020c3003030a1506020d 75
    0x20200940081c19510030703684500e400b00c080c2c650360420b10f01817494002010f500310b0407842680f4207054992070321419696035441380c4c208400325003811030300c60040c03403c004009415402000003462044416075200c0c0c07895881c1134020707880c13004039104550000c030a02034641c9a01c4210b0360011026280841c0408441c0010f8002d002c103940070b9400780c03180c5010170114402c1944910b000300011350a80700c01d10780c0c601089a44404202c4010341c90b4004214040961400d003000f000e500d6181d090003582107074003060504201d0760464488c0d5100c10113440d0349101c0095840340f1410808242804040750703040c4003000d6030300d12010b050001311045142c00305007551b5402c3ca5400701182d10803001030350b0000c1494991400b04007803166480d410800001e5042918121009a031034040c264014614070002404009408082c80c01e42d51100e10900400300181c135001c0c010020480f1010000c0d5680d0901628000403903a483c2c0911980752080740040c442c1660105580800c2211807810060138000c041d009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 580079721 1250 580078471 580078483
    0x1b0201120b03120304140c09010608060108071e21021201121103160501080c0405181506120118110a050a120207050d0216061b060e0f0604060b040c090512 68
    0x20030aa00000c4208010840300c900071b4a83c109078007056500c2c220701701e0240180d03c1c40a0041201244440340041c940d5403103611000d0f44510325282000e94544070035050035181035901040400200c40320b008000c01074480000c0203030302450b001f08501c4d00c450a60002400c82c01801445410013400c032000d800d210204072102286c000c0141503858510f480100d10402107550300c1001d010510800c00a62607480c030310182c4003203c402401c02c510442c1e140f901501c2d2031030010305240e01d04081c0c2c0807645142c0c40310f60140003041122001c5041950400a4007102d112143e24084001d90400b203602403001e02c000160b070b4004180c3e00700151075100449064032907480f846000703003040f480441e00070140720f4000381c0740955240603003e03a9418208d0a070500007440c864040e650100d07c111081a4040d8070441c00000c60501841c000946c240303202030300c107081c00644086000c0300e5120005100030b22500b48a95640c02100315810015111140340182514104e403003a18401c4080e601003104014050080d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 580080971 1250 580079721 580079743
    0x5160605070c0605010506030115121b0302070c09020c071811030c04030b0a0e06150105070203030c070501111501060f0e03010f0c020d030504200111060106030501061b0201120b03 79
    0x611052074800001403081c404140159041e900b01800003401c1c0c2840b008403810385070445a520128060300505442d0301c1481c01942010f03545d511000d0035030030701410a02846402da540d0144e540c6c0841d09101d20040000d070030035810540f04000b07500d0013290004500e81100c92440c496006800000030310b400034803035000954841c20000040040d0041c00200410540780314090380c8a40f40c1f150600724044419035a291140d80e40400d000c1503200405201950109034145405485c3c030029501190a68020480308012070b48151401e00c002d43e040840c588041007608010458144030100b000060706040c0309000503c1615071095203054410780d05200048070150091120100e6840c2e541300500b451145440140900100c000c4000e1081c02170038080c507002070310041c5030190000004102d40109200380e060081000d0384e00002c0d00184034084c02071040717480c005442d43c0341060103440d64614141c501442621180094010303a084010360b4264908503100041600300803010900e13140826035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 580082221 1250 580080971 580080983
    0x40c110706031416080406051302040f020c071725030f1a060402040f0b0f13141906200106050d0b061f0c030f0c02041b080c09010507030516 62
    0x100801c4003a0190406000710b40c08001002c560f9544000104c2100301030025100000c0701071000c900030420359004190080a03403e0040740000c240d5000a040b10b00c05600d4584290700890325000c221001d1108200030000301c0c09c4881100d41c8004c40741e4803070042c00a0a043d08040c070b03450514128984540030f0146600058410201c0c0b241c0c24640c1103040090704200340c1100d03070b100103002400c007402950200e03005800311544090502042c1e6802e42c0081c06d03900751500045c410b1411209400102500038451480d8500859800b001408400600002c91030780b55151903a04000c0203500c038404190000d412410601c640340b40300d1000c0e0151001e584415400200c2050504c00d2002c000040390054108032582a403020a021071500811640307862903011442204000340401e01403c0c02184000091500d803030242d1f650ba001608548008008402d42c500382208000f00582151006412000900300982403a1040f0002042440380001c0101008070120b04110300e00d01d8000040c65480e4450 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 580083471 1250 580082221 580082233
    0x7031e0318061d011d0103020705010b0a030807030e060906160c033f081f03060f0902010e092e0905070507051002040524070501050f1f14040c11 64
    0x410300408000e50b0074050030291160070f408291540c043c114101d81000702d940304a80243c40e8000640c001d4202d05001d440075526000d125005036a80c0d14001d0203940b040e00f14a031940800c1c2001030060742001c644602880e020040148d0590310801601c000e0300d50010040d200488a2800e101c62500e117902c002e055000c09a0080040b25610080396110001544001141c042c01c1c600039440c610341d00000804501c00303031301003101c021004501203208028400c42c488150f0303482c0d03141c00071204001002441c10741d40c0d005607000c56078802d00180c0107a008845030059402c1c942d20003840194000040d80200110201e80007441d8025081540100030300c15041103246414180036006510500c0f08441c1c90081e91012100302c995442924244c4801030980d550150f07800050f03921040888e0b08008080300c0038805040014001d0040c144076141001c1c00213600d0a00845e03140b10401402074004ad5000d000c03030144a264103c1710480082c000403100400c0380c41c1140c00503906420740a0020900780030346 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 580084721 1250 580083471 580083479
    0x406051b0316080d0c0c0f030315080304080303070f110c120c130b191d0402041812090b0909040803070302090315040201020d0311070311190c08070807031e0318 71
    0x3200541a131005001c802d20030300b40100b200b2914520b103280d00070900b000702840540464429803007580c00d0310200542d5215162210409803031600150320103840d42d44000108820a9480f0103008540961420a000f4400c250100301c0d4030341100e035004500510481b100c55140410400c140d403140f002c0a454403200a0701e06060300050030034141d11900906400c01203540c0b0090030101842107a000041c0e04140c095610f50b0160302103005001030741d1050303d68040711401314100f01c011444610070580c419074450758150180a0030026402170508400c20701800f0800d403a03403007000741e0103503101c40031680e02c1d81c901c00c2c00c0e402401104241e40d05031046c13400440c50042000c0d05103020318003d030200c0700c1c101c8103c9421401c0e03907017451441881c20805c0c44001f0000740155002d0045006600640e485840000d440d2004548213183c01d0700d824145080c10045070800b844010060b242800140c0205401c644035401c020218444002804840d21302e1603051500c280d03034402d00220f40f20700300d034821651 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 580085971 1250 580084721 580084733
    0x30d0506011b0c0f080d020601030f210201021201050402130b0904020f0705063102091003051b0a0f120b0a020d0c050316091505070305130f0e0a020406051b0316 71
    0x560282e41e619102d01c5001051217500010520f0b10041564007c099580c00c5aa030249c00340c035048421140b02d80030802d420a95076044904140481e00b035800143ca83c0741d02c2a200c00d40d180c069120f6806180b0400002003003504159520701030362100e805085e5075943d6800450020320800c11642451240414140b00300b00d00824442d001d91032001d8114559010790030000590351000312a040190b50f12650540141003a40040c1e0303200000d150542c2150b80e85c1e40300c603400c000304500b41074111102c100c3c450090740b50150989020b00030581035024018285014040113148012020308242075820004007c08066012101d400300703440c1080c443c00c614035070003074125003040d00c080003400d10200341000c40d50300c1050031504a650527110a064000e41c0002500c80d80e04c180b80940c1000f400f0002c0c50150700902d014071005209c2092005801c0d46403028040c00031070f0180100407042d00420081050503070160540e140c0c064040c0c4215201e01080903220300e18420911081ca40c0f40c41100b0b1901401a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 580087221 1250 580085971 580085993
    0x40b0f03040209280f0f0e010c1b0b15060f0c0303060f0303120714040317070b071107061b0f150b01030c05032217030a0c11030d0506011b 61
    0xc0700350f9920407592102c020318070020b03424521500103403e1201014203c904140c11402954900000c00124061254000000e0399042141420300ba13454400d076000143c1d0002c403803149801c00f100084144002c030703558118006009400740811a550102e4a1019540e2200b00c2d0100c0401c0c0786010764440011250b01e842e5003003180c07054031035180c948440c1410b0801000301c503000c01507020034090b42e0f581c81c0c80a444211030048402c200540500c00440003450001402c0600300c200361440b6256840c2d0b11349008080401819501040414021081d5061000a88009964072410304030a0320408031100d50b071549040d00003810405585847d40144004201c8000c014820250148101142c18006406444407020180005141007001503440d5818480b40e800f558100c0030945024040d6132902041102d91016541c81450000188040c4031114422007400300802d0600280404000e000b50307459018030600368503403075291000200f180c4c1c800c80500d00d841d004c402882c2c215100d01e003071405c0281 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 580088471 1250 580087221 580087223
    0xc090603070801091109010503070f03020903070305010209040b0a05092206140a140c090f03030f07030f09120c1e170a050105090111031305030f1602090601140a03020f040b0f0304 79
    0x1407034030f800d00014404445c1111040c5006031070782c80c6151200030040740e0383c1108001500400d0303800c0c810b0107040da90070b219030001980039000158540300003800300710499078000c03807903445400900f0080115896440074560f2007003804509521900c0c201c0d544144402e50a8401030140d85415a02441c0c000ea0210041c0141240c0340d0400030609052181050070100b0b03100b54246550620401d00d81c0e14000e100c03000a07a401400b40c0c0e04142003080d9010298011800450100d06425607505070301d90300000400c000c00f80d444002c1900891a11121039601840c05009030004041c00303240c89102c4071f016024024002c24121400305900003203610f403030b00038a5004039a5075003054080307410381d4414094405010884000c547c40c40d00e40081003103170307030f8038245003207a080c041481600c01722086100a0400c0784800d1070280c501804600c10014000c0000b400f45040c0140c13040340ca00c5500c004010340d80d441c141800c0050362410722020004080c0566800344520990004d490f45101c070b101c01c003640c091 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 580089721 1250 580088471 580088489
    0x40609050d0c0c091508060f010302130b0105040b0705031b06162a15050a0f11030403080411180103060c172e091a13150504050c090603070801 63
    0x40444241203074040740b120700c00380806100e030605210784800c4d540311444000030002e051301c0d010b42e685040ea0030404200d9664640d03503440320040040d4101011005c4010031081020032200304254006007890090707029085440030086a100d041103010800ca840b4020103100315140c0d2010301c071084d60380300030440d44d0021901001d59444803031806104103070b000c214290922481d40b290441c2c0721909076000e01042c1c1d41005910524012003400b0310499018070520140416590f0200d03400071b05a500d101c2d0f039105840740820420011944c4454641d03007095000c0c90400e801020000002d4030002c3d003403108240b07120054000800c000c9075602846801015440b85245c6290702000000a80d0040324400711044011450600c0d6200c41440340710350456104c00211226160b5a4840c21a01071310341556180e10703e03102d150101d2906100703601c1400c41002040c454207034484c443c0c0c04180d0480c4543c030300641c2c964000c90b41800c103440c1507980205001d0102a04c0385400c617801030407400203120b80303104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 580090971 1250 580089721 580089733
    0xa0209130b0f120a17120c0c011503050327060a020a0b09061603050717180f210c0a050d05031b190813020a09020d0f1a06070f080304060905 62
    0xd10f050031030a180302c00d04240c1c05040416010b8694041e554201e002084140c0303c1000720b040c00c081140c003094050b4420012190316a001003810b02e003100d0aa448440e48010300b160200700160000046411228001c01a07220120303d05245d5800c00705800325240d40608045408206aa40000d80c08541d90141410001c661a00d814180c1c5500003945c0d24010407640c2407590084c8d078000d41005030070110b9850700c000c21060000349012000010740e4405422402035483c0e181d004003c200c1046081038000c081e200c0300c0406589060444903134401c4000d040303004039200a05c4c0009101d0002200e800509480428408a00080643c0e10486402070310040ea601c0d0420303840511000e54031001d1130b942c46103a03030703204207207080e41d107034030001e0005807418164040040107032982141d1034000e2480e00303c0541c951543c0074202d4244c4028964410b00c0b1440d0603642d68034100140f0a581e04410706545282d0b0300c036881d04042180c1e134500c8102420140c0f0010070b100c2001140c1d0711034503440c0e0180017550a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 580092221 1250 580090971 580090999
    0x3083c09010914310c110f01290a0509010b03011712090d11130c09080a05030a0e0303070602070c0e0a0216170432030312010306050a0209130b 63
    0x8054900110254210807103440542100d0350b51254008801c1462110381040b038150304144c0c00b0360700141c400c07000049801010241801c0204118003140400f00020302c84030140c02100c4c0400c00840000115808625021112503100d821001000e00030103402d104031582c40300030250f40381d4005c0c82030000070300000c8842003000c500400c010b8589a2000080340c50512004200300c01c104c0400310580d5909580189503049584d07005140503002a607a0002c21000340a13100a4a2036241e80d110800940010891100003100841215044203841c1007000a1007407000200b403440c016030714001c0c1160b100044410234001e5404180c0100e46183d1840d21143d51503540713070f0f0203078000c1c1c200b0142145050a01103001a10350025051045082203506081903595030941d0700c58480481004040f00482102d145554108036003d0720301e101c1070300110320740288681074040f003040521014051030360b03c001056421507650126040c0810061205d11000c0120000c0802094040c54080c414100d0414040d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 580093471 1250 580092221 580092239
    0xe0a0806011514030403091a1b0d0f0f120c140a0e030613080d05040215130e010e0108030301140316060e1008090304031e050102041502060f0103083c090109 69
    0xb920599241d078520401520344445040000304d00e07618040c0243c8144500c4510441d0322880c0807004400309c000b800d05810821001e403440801d6050081002010501e0014060708544d000d10000c101c240e00044030b500a95080791080304400c12844c0058000a4020710290b1000b03000710f00440850a8a00c2902c171060541030b550740c650b0000380001802c1c45161220844c50380304a038001c2c000790060300b100002600e0050b40e64805d201010924521a02c02e002407850005051702510506c500543c965062907001c0766030b804144907220403981c042d4040740080d1014000b003402441e9000e001c0e8129501c070407015016044562005024141c2002100c8a0754800c070003c50007140100003a600e410b003940c0300c0070041105400c0d07650145c1440d1a015000403c240b00402c014455656000d514400d4490002e0403c180a003004110384512070050000c510759000300c40300c0f024034107000f0ba10301070700060310800661004500b100904405941c0c8402d0100c1d03070700501d121361003640c81e05a42c0307488003201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 580094721 1250 580093471 580093477
    0x602070306051608130311031b0f0d05090907020c362202011b080a020601121e0312050a06170312070e0a090e0c0103110304030206070e0a0806011514 66
    0x32000076102c0d400300e04c1e6840345c814821000d5000b80790280007194400802840d541c04001c10034646c80d180e0b61362060f0820b0501068020f00080e0300134209841510b10000e126025040c5001c0c40f814080c2c01080300c8500070031003800518800703062030f131034002e400c1101c0401b0f41198241c0c0010030440c60141240e9442400072602c10b0020b0070010701d0510019100000b06032001c0400c80c140515010070f10300150070b0400f00c49003140b0621003195581c541240013070420700c060b4000c5c01d010a1a02680d40094800d03c04180c0b0030701312090190b600c508509044401919214030b61812034982028040803030f0707180e040030040c0d40c01d0955000780c0000100800760b980c8959140210030368003142c0800c084521407020310241d00401000b8880ca0f9890700c89000c11180d00060172001030788100d10850280d60140250410031a45200381070440c685504c1c0a5160f0100425480c204000255600b207250303241e404101c058000c800c00c8030031568441008008607071a04640302c001c00c0aa001d5020122051021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 580095971 1250 580094721 580094761
    0xc07061e0e0a0905090c0907082a12010909030e011706090408071b05011b050a060f110c01020909070302040302131d07091406040504260403080309060601031401051c080d06060207030605 82
    0xd00c0c0c03c002b00c0030f2004162904800036405600800c10641103100780000050b8060030b406000000c80c0100f40c03402a102d03c07030b41c2481505010219109603403020003050f0075940039a081d5001125503030b035442c2482040c42610f600500c0c00c3c00e0071481c0120a50035000007425244203807a0640c140b11a208190b0039064050001007859100340b00c3c1f030000500d107802186021091400101e4200040210801300f034100b506486040da5001c00c90980501e1303c2580a0b0304a041d90174218681801d5070003181443c558401e00490194903030110f4051560f64020310100d05e0703001c0096408481e1582e1747c01001d008415840495a820038020402510381440b802e4081c2e5885002e4040c000c042d45415211a00c894011b000941c0b03007800000003181107000203521808441008c0c103418035048002508686ca8281c0c0c00e12a415035074010f102d1616001d644040301c001803154200003c4161800d00524030a03032420041c81c0381032810004406800091000030740b03204440c00d100d0b541d01c0352030302e031000410707590 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 580097221 1250 580095971 580095991
    0x51e12010506041a13080607050a021501210507030611070506060303131a1c1b020c060906130315020c10020304170307020a170c07061e0e0a0905090c090708 69
    0x4c1a80704000c3c5000749413441c0111404a4141d94925480b420050102d543c0c1d004101c0000300c802d4602e07410701980d1204070003500115600d50604140344803400c03002c04681286001041c21006012003007164800440d03026600707000d00241d44041c0441a000034000311114850040410060b207004406d441e01d07040c05401d085005480d00c141c84c81803602c219109280c90f20100850415507801d03424045c55400c80060110b100b17500d10200c41a0072400042c080704640146820b0117041da00c0348219071040760200c0f480d90310380ea000840030010807950b40c0020203800c2c0501840c00b9403c11034000d0060b0003140360a1700c91661264407043d041c1e02c0100c03001460b00002118410071203051201440e045034062044480c03900c11540c40444d030350320402c0d954121000101d121200c9100801008000d4501d078508001103030262201d040081c80741d100c090050022555500c03403603803140b403034000c000c04003d00c05000e5420080e4145490780460000319018520000020705030714003814006000b03030300200b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 580098471 1250 580097221 580097249
    0xa090506130b0109030609050715020606180a0b031006030303180b190209190f05150f07061107121d130b0613030b06092a0703051e1201050604 63
    0x2007801d100500c030120225042c0100c00d4004808200148074000e00584981c00510500c0c0c10140000c10700300c1c43c200500d0455110381301700300c03031515031169412094034020014001900d8000c900809012140006600340c8036400010410690755045141283c2c00394800308942944100c803508000380514018149040031004107040c2c80c01e1800d207076001c1191020050403c0c0c0d079000010029070301818a103135811208801801409810101c80b4000e06046901d00f0845401c1003c843c0c42d8020301c4c440300000f40010a2080620110307030002d25150350b0303441c0c21903900d544501d8100405080f8504000010380d4841e05995441c65030140075110b180000d101904203007894980c1c1c00a1308a41115a800010900194542c940308100304c3c0017461240300b01403402d00d807034000d101200500400c0309070300d49804420400704ea01221281900c2541500c4055a03400e0300e403c0c1910f040c0f2401500640e540546011201c242c04041c020b00300e036001082030013210344d9a4400308800c40c02180a00803001405c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 580099721 1250 580098471 580098499
    0xa1e0519020a171b0408010902030f0303130209040f0c08070618050604150306030c080312060307150c081e0405040b030a152c03120919140c15090a090506 68
    0x1603840940e118005000b040c00c81002800a40c50b65005607014000f51fa4641c2400411840e00b401010161041c0c4c81c010740c110300d031500c0e141d810340a82910281c001c110020100b001c0c043c10907010340b80d403070300070700207004060b03564070341c6617032040d241c8104000520301d05003c051031498407c121707007103841c000e00d49820f007400c2c41e8012404002d10a49130040c0b50703455400200264645200340010100e25014503200d01d40c9181003400510010001446908071000c20300a803812040da04961f00340da490701026030f400a280507113041c460844203100203d00d18000c2200c1901302e00042094510a48041c07102c0500e00c818180d40b40d041c0c24000b00032400e0109074000c1c84840b544401400d80850310070204d151441208141080c0c2000910700c2c0c070340c10015000201d0310b00c01013000c0e003000100008007a0500026501143c1d46a120001000259409008245220204800110503000400b00c0301400c2c4100c4c0d0f0f859080e408a401b00d801032800d554005000e6032584242485030310003501c0c0c9a080020303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 580100971 1250 580099721 580099757
    0xc030807051b030901091208032805010306060312020f072306070f0303230a020307030f0e06041203060605040504090804030c0b030f010b03060d03080a1e0519020a 72
    0x40c0040200201880400031444100b92080d9012540a000d16541d003100400188500f0041d003203001f210400b0305560001031800400c4984c050003a208660035400f00403000310b03144655502844246040000110a00840e03902c00b000b100e2207084000c0b40c074000e088050b038440c503101f07a849515030410792003084145414400022502070103c10401d03000034480c002103054001104c2544c0030508034010404058042c0f06500f00c2d009135840369500700708100c3e580c0b800c002000740600081c0d9004404110603c1c0290403002c0d449100403010310480a0580d83ca55840e03004540079194915511000c0c101c05e40a48600c2040d10b00c3c1380c0d2440c2c545800c181c180405400b0038501115100420400003020400e03094510016196400c110341e80c1c1e082c81c5600d212401010b820003000404c0801c20300005a03159030594a060f0ba042c184440243e444080740c0f0010080300070310350341c101108080c0c400d19240701e0303001d24410108407000b6440713104ca20702000304a020b90740c403940c0403c003455a40c21103210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 580102221 1250 580100971 580100987
    0x711100507140d06080d02070302062d0c01020a0e040b1503040515162307021c0c060e031006031106031b1306020d0806090a091104021204051b010c03 66
    0x32060402e400048041c5408010560000240600d0350b5503c400a1140c81c0017071017034003088002031006001480c20b50300059254420620030000402d4401c940c0c203101e4018190302c3c000843c4c2000466200c080060489000c0e6004641c030307030005050340301d030f00c42c0610302403080d1503091901606e04031138003150319007040c01940b0280c01038506100702074500c2c104400c031011031486034034680f20803040010184006050000110105288003041b6050104c0d6030341141e0546400540407145408911f80448805240e5800f0400207031805071003c20100b24260031401e6401460302c00c2d41200c540c0984044040103c0f05d69010061003108c80c080d074100030b450410080e503040640da9207a03030320350118000d07c0d0010748c0c04480d1002500c03202840400c5010b8040c01506074243c294181f00c480b51030072100140c0301d0305c801014041d5241e941c82140040c4035005141e0b420762900a04115602d1488000c0360400d428101e030100d07200d202d500c4907604070403504c50290300001c6040c0c42e0854680300301d0f5010f5840907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 580103471 1250 580102221 580102231
    0x40504111e1f0906170c071a040302010c09090b0f090606040806071e031a01050d02040308130305190506040b0627040b07020d05190302040308030a050f07111005 71
    0x1d0040d20250301030355a05415035042c90300d00a461107140045000140c00900300c3e5000105002c2d103c4101c421a041a1130041c0d80a828500c103241c1d195035501e0501d018034240b2015004001c1c840042108142c0c055020b60700c2c80c47e45440d100c10f11a5200084415540a6400c0c1c1d0741061031005003001908007658881d0300444001e05581c146919034410901d07080c02202c01c1000500c1003002c0c0507100151100c40d521001040c9400c0c000c0d404016860074240aa00c1012410068009483d070007548003581030380c0245034456080b51780c480e14241000001c0129010a4504c2d002c1d0112181e60200c10b001c280c045594401c016100c165229120365030841401130405402c120300d08407801d10404c140111580502d2088107801541c1054104219418001003521081d503110000c20001c0b150007130107941208103000e01d070701c0320310b194803408030080e0150340d00040c200f0328044203000d2a45002e4004c1442840c07090490030160761071101c1201d00800d0150304581c0b9800c0300103c03540103a51038005039448 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 580104721 1250 580103471 580103509
    0x19020a03060921120b1c0f080c1e120304050a060207020f040608010c02060907081905070512031b01090f02091b0c0a020109050a05090118090203031803060604050411 73
    0xc10101d02041d400c1c3e503212440440002c0c20b502c3d4010400040b441080d02c01c40702030b1002d034000100028019050305da82100070f0240c00701003c003041000324880031902584002c90954000c51203c0d581c862901c0d0058034800c7c1c0502980000107100b078405001c2e2131103160444020401d44c501038031240000e6104400680e0007403150101d842580d11036002b503c1c000c05414000250047d0740d014001d040c41d60140442d02c4980000b9801c01c0501c00018004600b001183c20101c003013600c0740b500c1890089a80d0101d60008a03001c20501c8409001c000381045000c03120360710b907452541c141c01500b00d0321003010003050301940c010300703074050b0410180780755020344080108242d0398004030f5101c0f001d030045280d20260b94090700305a011940d00c581590b000748400d44c2e590004905000028101c40e505001c1c1c0e00744d0628514200d804030501d50043c500076900a82540c0d0b469010070400c0c841c10011811050180c8203200c045001400d040c07140c24413813038001c2d15103089032110201f080035a40702d03d10f1201c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 580105971 1250 580104721 580104743
    0xc050304030c0e0711060c030a0e010f1103010503100e0706030c2c0301060905010b12061c06050a0b0105090a14130f0605100507030906030b0a0e09060919020a030609 73
    0x3000141d40b00e018161846040320549006500204024080101c1c1c149a420401c1480303402c4080c101526088000d000b00800c00c00c210f001007600401b4030700f80700d14455080003026181103140380029070603200240c054607080003a804030704040c0d0741c2c0903c030750059602c00c5504210040c401d512003c410003540c0b0b4211a258810490304030780c5a504e44d050511070001d0180c5008620302403040750000e001c0300a090001d9854040b100701c0034050788101002c14100304001461540e0360741c81100e425410703c0e00c40010900d460800030010301c41200c41024062820036270404640c0207109680007120020311a00741310341001c07070300c00d0800b945a920310341080350100d4402d621306150280c0d440b486904100003402034506002c00012054a143c800e007440020070a0350003103a440300031002600c0ca43c5c100407c10b22081008541c5900255202000c0d00a2440c1130190206010401c40d01500202044540741e20b00c00410282c0100d19400080d400002020200005802c540140c00380c107014824807a4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 580107221 1250 580105971 580105973
    0x50105210906010807290c030405031c030f05131407050a0602011505040c0921060c0503100f151103090406030b0a0f090b070e21072909010c05030403 66
    0x21a82606480740d0820b900844010300000000700040c5000b0034840c0010403d1402c1c0031440f016402c2007000829100710300003013000c1011010401c0310000d180240c100d4005c010780c00e04104803160f03a0041c041c0002d041c06c00d84000118140036160003404058032982406020303540d01084000407030500d96182c0140350000443d03584002c01c0000501c0c1c95000400ca0351191254048109a2078108910030391074021b40031169a405210b05046c1c0b004c84511919100b01100402074200340184014003540c101100f1129050b03209019601841201003440003a588a80c00c600080b102402001d2600001c02505449244109184070500b40402c0c1078071f14180041700458151181c0d60000c2e11105008424810040301510900b0070f4a80055810042810b169990401e00d100c0034000000300100c0000320802a40e42d03d02050700843d0541c0320500d405400c031220358a1344442e03ca1500025224529a446c2c625406d0700c841d44c171100c5500c02c81c0703807a40c150015550b540d41040c0c1911581300a00c0040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 580108471 1250 580107221 580107277
    0x40309090501060e01032304030f112a0f0105090d060912050c190312022224081608100b07030207090e0a05302a16050105 54
    0x160107046203984c0c101c0400601d4002406460001c80c6d49521184560303540e68008800c3e00c0000e400690504c8c11740700204c1030240480d0a01d0790065103803d5801a44040c408517030104601c0801450200038a0310098209010420302200041c50385000c1a0104003c050b6803801c2d56181011902c5100e0003e00392860341c940c0d58038508801e0030700c00403850005440b242e41504005a115070320104c4040364101120b41e40082800c4c0305e000390303001c125401161004040c401120304081c0301c014803c080901a80c0c8007a910050040301c00041c001008401c1c020400f10712072142644140e001803400c0c0882c800c000030071140207000905800c000d00c9000c1004c200b803016407005105003030295005040250911088100715403d01400040075406800c907100040d00102d458030385807854581101a015900518004003a503140c0400302c132007000600d15407030301d4032440885c07804d080c4042d09000e00320015001e240d94078827821820049480c444070800180d8403600003030007200c401d4603041c9a501c204080c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 580109721 1250 580108471 580108481
    0x30605040b0f0f0106090506130e070207030b010506040f0e09191101030b0d0f1403041a0c0714030307060b030a0c0305010515040c09170f070e041e080f0304030909 72
    0x1191a48100d81c10300210449110003950000740d0340d407090380d40d549446405403500500380f103614003a41001c2104202810044c401c1001031000390b401c1e040c0e6103898030000f903c444050008a802030703c010004520b60601d1400d0314203850100b10100e2119052a03411210140000c06a0009100324845ca881180c0c054444402c2c4030302c258007803201541d80300005003c2d030362851860307400340940304411004200d03240c1100304455000150340000c50703480704140d41107119640094143c003414030b0841c07020107034010003003480790b510800741d6800685651840b6100000b40c0d0441da45680b041c403050000c10181c3d841015503540040844540380c0e1340340d84885951440d64000c1d40d00340d5503842040a0b0500b04c04d034052203120704842c2044401004038020b4144e085c1e0b030140b40d034000700a032201c8031400000c000100c040c11400c4112440c1d29680c610ba40c0341d4080c00c41d011644000441010010071008695001540d940000002d0030301034055003807043e540004000360108009400001031800e12407141d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 580110971 1250 580109721 580109723
    0x519050d020c0d080114030c0105030f090a080a36030209070c06050406021918063b1c05070306020d090b190e07141002030d140a0606110a031803060504 67
    0x6132801c19803414060002c011107034510f0320b000303070407124400c00c007681d20004492748075503030146840c102e444461060b40340035910400106901ca0009010700303000e40080c1c201002140b5030642001511201302c0c1704d0881c070786030b00d101c0c1664005e22100384011300c0c080c40d525902032000e180240b41584035840e1401a00e00a88040d40e000e6800130300340044c1ca0404580c1c407003080d80c1e81400021044118030040e604401da1050a0810000a001b51508000e100394900001c400f005007640c400000503149201030342c20504d042c40b580c4103d00c0c1c000340352b1038603440142c20380d00034019060482c0382d40c890324007950005101c0e0030180c2d61001a28001510028014000c403044043c40005411314001101150070b85030400744541d10640040004005451030030340c2562040c1c4d45115218034078030041c3d02e5070184c2203c806d01035051110000c420300504c180c85100d440d2040080c03109035902c0e0015601c05005440303103180754024096500c003090085508000c499400301c8109400c039504d880c0e400444200b560 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 580112221 1250 580110971 580110977
    0xf0302100f020702100c1104020310230406060c0c060f140c0a05061f050d02030a08041502070611152805010518090303010e040501090b0f040c060519050d020c0d 71
    0x3d0070340035401e00d990603400002060500d411401410340f00c5421280800341640d100310380000c00101c44110084e03030007009000b581c485c0ca8102030745030850040e203000c180310f00e4081c915200f0001807080c8205e1498010720b8120780101c3c600d50600f0400c90b040c98280c503404003403140c1c0400929aa8150310000c08034442030718041c01121161380f50090034910013038075018482c0083c08483d04000c2c0c64040b000100c0f102201da01031102000d101183c1440707003503103000d00321040104000072103046800703509881c5142c0c0d5081e2078a003a1100001e9a00050b680c0201265500909100c000780310031640c0a904240d020065440710301526400310700c00c5a4643d60140c02c103440e8401008141000c0c000311180c0c555581e00b4014501d0101d05c0660f0308e010510903488401c0c0d071000890f0903c40298040a100b64108a168a0030300d010042803002c2e4005841c101c03881901c1354400a040c0703105500365901406980c030361549030507420604460a0300300381104102c1507420030209080c5001000041480c01041d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 580113471 1250 580112221 580112227
    0x11e090312180506090f0402090406050d08030f060103020a0f110705040501180f0e06220506040605010e090c0306061002032514060c03041e05060f22020901030f0302100f02 76
    0x1140e080704100780b951100e030060f40c1c103200c840c14695426810001442044e1001622000108009005004198081034005100c001c4500a0008a40046100c0d01000c81e20340c1280d203e0310011400c070b01c2a40c1c50840002e00307000c0c00b50f440600c41c000c0d510170140ba00c4200c500301602c80b4009000c9843c2a071015080e44080e50002031000100e00402d40349080c0114100041c40500310702c140c503880b000340729182d8140395026219030321b801c80000480d11a00141100c03034501c0c0c5468220000d1100307008605001d1071410002c2c9803007400003954400b682001d0b000e046036481719000c1c804000c1202007000291301040c4100314a6941e00b11202513403948600c03030b810b40c986507420b020070724150406618619030406c2003046100320750b0740116034000342e0201c0c16040020390005032082003d0741d80c07001001405640288941d580c150100c0c02c1c09004503415000180072005140828441035a03c0203401014003030041010800081c0d03c0750905000780150b80c02866410741c01c1040302c5000300b038100501c0e404 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 580114721 1250 580113471 580113497
    0xf070b07180f03081207020307120206041523060301020d02122a09010f03110c060123010c1b0317210108060604090c0b0a03060302190302011e090312 66
    0xd6501c0c08010244460390100309410343d1590b0b0b01c2480360305211507207800400089007080d8802c004442000307030024091032020041c01c4000392140b81c2914152068048004691182062440703001c501d0f070f69415000b036060b540c5800034840204000d00780c2d545554240401d50034210307180020b000c0e1030a000d94141a903d880c40741000c10100d00c074442486500300854511081e00e40c227040f590503003024249004410403850b0b080303002e1718100e40078203924800803138074040300b1400041050503100070074240b4980354a01035202c001a104030620700d00080000c02d40c0c0c0041444002d0b003000280420a00d03007201d640b03070b495030324100c140107514103006100040c0f5034032400038030342190b001544420342001495260081059075401c02502803440f560b40c44c2514020481200c0c05071006101c403205168036000c909401600402892005030b0151109401c45461802c112140c2001d9a81c161034900c0340c2d207201c052601c4130450110b070b040c09000341c02e80c001c400320359050300150085800740d03601c000e44184 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 580115971 1250 580114721 580114757
    0x6210a0209120f0d080f04060b0a0504090b0601020601060f0504030f0204150312031404020f090a140108010b040f060b030f150a1215090c06050705070905070e10080402150f070b07 79
    0x4034031401420815414203000c80c00c0c40c554071b0a500a030b0807007800702d600014a0b00050071026180c0c0103550251408010782c2c100902a0307060361140c5c00980030342c2c59580c0d0700e000a45031460009688000128100020300c001002e0030441c412840c00a400001c051040c80e20a2000506a82003612418a01d1030381101d1258180210800f4400306101d00e00b040c2821340c0811b44960082405600c5402200006021a00c856004080f190080b2101c041c1d0782d691101c555000309100d00c0c1060150b414104200c400c00043c3c004c02045030129003a1070300c0d40d6119154248040006000500c801c0c0790041d500741e681e907401120a0190140c849039460116403440c0c68080e80303041e09074450300982010440d1003c1502e00d45c400048a010303051640e0340b00403c0c60402d003008000c0e001444213030b152006005440760b0050120905510965aa000c0800307021741c161140390040324020b5000d01c0b2030f1f0812141032005406040b03030f0700b017091740c0303904117840c0c0d039140010f42c58105c0740c2e0790000b0b8421201d01001d0355 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 580117221 1250 580115971 580115983
    0xc0f1410060807170109051c0e0105190507170f12160c0201120b0a15030c0215010915082e060305031909030206070507090b06210a0209120f 62
    0x40681030070400d891074400034039100c690398820544080400f1555818944080d005050700315840025540c42d007911a4070380e202c1880481d000c000003054034244036102e500660454202032100c1d582030b800c81ca0500e008844d1640105001c59044d10581080300301c41c3d001c0c0000c0c1c90302071400e82809880e0007619800c441812001004502280001c03031740615840d400c038250042d910b8081c40e00c00340b1a824080540003810368821030300d1300f00984610009489406030003084600d0800e039814402c079900b0340822070b954580000d4001c0c48042003001003040c40765541c019400c50041001c50b0031815030b102c0350f09080100e110aa04058154400301c151345242c009060030a40060030000c118407410364079620f43d03074051011000d0008100303080400006015001b03010013194028400c50741d844051920030b0716035100d4842e04892a003410302c1e103d0549407080649803425680c07840440e6030340c01c502103400000000b03000700100c2642001072810751384070b43c64100c82c07102c0d141f070081481c0102884414a821 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 580118471 1250 580117221 580117243
    0xa02250302090405030429390a30050306180a0e1c02070b0d060b0a0c05010c0f0e04050415020a0207230a050d06111204051b03100c0c0f14 61
    0x104903080448105809a065682c0c4100c51800307800015083c4071640e40801c9074400d40c0312160400702610300413660000d90038400c10311400e0b281c841d8500302500d075a403040e8a407040305280d0640340e000ac01454401c101540d03228000501004022004180d002c00c6014190b500441640d100c010392038000508001c03480f840700c3e070b44040162a07400b001009469074424058100e05510015000c600d00c0c106801c00005817000010880d85d40c4030b5500c0103800404500003c9406508041005500764000c50509188000640712410000c4100c01003100624009100701d556200d1101c4500d407540d042e10180c880406650002c2100c0c2c0d0900f04000345516211041240702d0340c0359501540551101003c0744125001030300e4240c01c403980e92801c07a001c0d1860403100c1182c1000070501e06610707038102400328040c6000e0002d80c0c05488581e00c1000300c480c00e4140194141c1c3c450a01c00d80d0820a0342c0c0f201c50079020b18505030742c4645556840b010100c64007002079581090f0800c0c80308414405201c070800311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 580119721 1250 580118471 580118519
    0x6030b01020f061b1b030409060617070f1b05010903050901030e01020325021203250507120f02150c03010f050d11060a12020c070905010603020a022503020904050304 73
    0x10300e8a0701d5030004c00c1100070080c244941001c1000040c1c00c00700100c1c505ca4403548001e90b62900e0f00d600102d00141010b03c07c3c0400900048600034650315039980150003404503a55507480c00801d040161600e02003071a10140e010781003052407000c100c0030300c50401001d100396a0941c3e188007010005051754210b03102e1103940d91040052007502009501d008014948601212000704081c85040c0c0c1048800500182d16403400000c002c10100303034080903408500c0e0060600301645103030000315070600402c0b500418051422650304001801800e41035622401c0e03104442d44000008a4220003080580d100c82c20900040014044400501000c00140005079842102d00085464100c01d604003c141640100700c00a0030041481c45160303c00c0341078506c403009664440d40c0c101c8a0342d51320300d035200e1022414a02000410b03228443c2c0201d0301c0f1090507a000389410501201c0841210060609000f110303070400c0c10000c0141c83d09603000e4031175405040134586441c0741c2103a8410a010301030070300c116 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 580120971 1250 580119721 580119733
    0x1801020a0c050d090e151210061d0906060411040801062303010b03030a03020708040530070b0403080d0b03010e0f0706020a20220f0f051315110406030b01020f 70
    0x21180252685540c0718101e1010400d0500c00b06c0003041070a1040030f246007240c012166403041410041d04000200c41d05000d03c0791004106140942100c0301c00e43d1284501d82101c40498418a000d403c0116401c00f00201c1c1c0d8034040e601c1000c01d08440450380500030540d15503a00201100c880d201500c45d0140070b03402800b1105d94000007076124404c081d200c41c2030560100d18241840000c0050b14042c00c0098855506c98004410390000341c83c141100040040104424059031a004208002141c041440300b50900d4290b070313284c414a03002420800380c001d540c0d140d00030560340c090190714440070600d0302070920440708815540c02c00300c05410090a55008070300c8100010025050600710b603038101d19010014500d040010748004500396025000d00d142d0f00008507089855010b088010b12010040154041c4044182d0503990700f150741c1900c0365a011600e40100c3c1c02d482c114a0018200500021180d0940c2c20440c01500305410800000c0c0d070342d1205600d1940c040102201c0391620714020301c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 580122221 1250 580120971 580120979
    0x603050f010608010e040510141f1412010207150e10020903030318150a0c09090618090f080c03030123090103021020030309010518060402091801020a0c050d09 70
    0x441c9041c18170442d039038008240b00090034068140045a40c0038500038007070050608603440c0c1c01e60003a00b81c0e103200d2001c40d103034003060303641980c07542c0d5401300c4020fa4200c0d8001c1c41100c0400c905d19007a1042c4e04d5140d5000c100250004200000d2008145e03112080000c80c109410380941c074050300800c030900100c0c07040000070b049035000400d40b980100514a1880315514003551241000060810480060400d50a0049045007074110170311600240d1754040040e41d8524107041510010711030020048000404030140e40e416400c80c6180d14000c0c0780b1074803a411255940c00c0540c0c801104110982c002200600c103888000da0040911001400301406540d5002c000405aa20610009102c1c0705288180d01069004d101c2030680700100401c140e45d64408003007940e890303600c01c4901011075442e240004002e541004c0300b110490300c034071005040c00c1e03582c0d50034024101d8010f04940610a23607060b945a4618090004182d100040d50360071603403152070325045242c214800e100f9818810000001c2c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 580123471 1250 580122221 580122227
    0x30a0c0e191a1647070504080607021605062a1c03020705011d100b061b0312252312090709090c0905070e0303040603060603050f0106 59
    0x1054804000c82401ca41800030060366892141200c0c03c10b4003180c80401c1014403541088401502c6111422001ca0621442501412682989440c9481503038a030050b401480d00c1d0000e0307680b1543e00e007011803509071100090344c0780500450749180107030300007000c949000071200d410100622040c2c1d041070406080040880c107000d10040e0003640304811060f2200142001c101c005400c1c04c40364241c138070850503c100140654810b50b800c1c0c80542c03c1080303c5148108100349200e00200000c094400507035000701b004007a00310701d20641d90043c2c003802481201850010b910880c1581d4000941e0f50301c10144824000b000010701600d000c01601141440716542c0c0c0440c903003c01d803546005444d0700040780101e000d222030401301014241c40440c0e50b034002c0e070050110f07078052882882192645a0b550343c006043c5d420181000746980c80058080243c0e48090300060740004503030030a142d00c0a10b100c08a0701d1a0060f0b80002c0000ea100c0e034080241c160984552504200c0700403840d9543d6052880103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 580124721 1250 580123471 580123519
    0x30601032306160c0501141311031209100c0c06080103031101050601050906130b160309090e0c040504030210053309070c080706061203080c03150108100308030a0c0e 73
    0x5a4240700344c03102038500700b00080d846100e00395001c0300c43c2139207800d002401507510707818180e080300d801d486026030018501e00002e2600500c1c0601866a190954030800e10103400e00c204840c9040c070190300d0115001542c08100301d0040c10040e0f5034544d03298503604005000d01c000100808017a40360030180a0182da01504031480701109844003541c86100c210541c1422605a0083d00da80c4804074040343c505006150481c3c40741d0081c0c2d10307000015110540c600c05c03154900d415001d654000c2000880c0350900380c000c0c5074454007030300599014521400d0114159201103519003550840c0d884840d0a240505d2801c41060108502c0c503981e04c1660408218004c10240c05c0ca001d2100448900082002007c100c454031980308034280f120343d50300d40c011806122041c00813004207440758000360700ca2100d00705807480740e02030003481d0f0304104109006444404010f8020b4450781d00808000c0f0104070302100031030241449183c0011001c0345a980184941c2440f58214400c1490401d030401001070300a117 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 580125971 1250 580124721 580124761
    0xc0d27020108150303040801150602061e040201110a1101031109010c08090411070c030309210210050c07081b01084321020f0720030601032306 63
    0x710740d0380c03200030200c490740d140443d04a5041c407000901040010042d081003042d500f81d000d12212381625801c040c2d8541c81c085480c840c0d540c01102c510441031101c00321544d0170a0040c10050f01d4881c00c9461141049485242901c480b0b250904140143d6814440d2111608a044440342404101000288210401030f805882c0030301c04038100c001c40d0703900da000410714080e200b82140d8980c024908551510106d02c01540032a940c00c1c4005240c03240c4440041030b10000172100c0311141426800c0210f12000c0c4c40c6d113a03040090501140c0c4100004020070340c042c02c10600100814000488412140750805e107145041000c46814031038115502c5044410398001a410205920111000041031810782c00350440c02030040111421050340080c0c5001c8911901101e000300c412440030a41c050744215680c50450050170000d04001c91383d01002c6c021080d603040704c540c5c1c0e102d402c3c100080c0750080c01e820030b5404d40040c03e000c00c0001c11100005850204400c090704c4149042000a5209002c603d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 580127221 1250 580125971 580125977
    0x4060c020415080313170c0a0b1e03100e06030c010516031b06061811030705090103180317160c022101050a0b030d020a05072c0c0d270201 61
    0x101c2c55100c01c0008690b400600000001c803034844000724100c1c1c14295040c8a000398403401000080002c2c6008100040903250251a0110481c40c1800d240300b5644030318140d040a0b203c2001c0044031903080c60049d8001c581207039102e81c0b0203040118504200f00c0c05840640f00e40c1c80b0303084041060341c00c1416240e601d64000b00c44403d110542c00c1c1920400c018264040039079241090150030080e00ea80201c040c0d80c58081c540c00c0b8952100c40c40c0c2c0407210750800c0c00d001098244001860b0030f20650007000281018034003c02c40c0e40c00f98002010118400000300c01003010507105582e402103403441d5603031100c4043c00c210b62481a02c040580094010307080a4050300000300c00054402160322840e18140444008100900e81204544c0080c20300141d45440b81c0a070380c04043e0312920000d04184156003000c00741c08460300d447c0384003180c4660100f42c924140742c0701e203140c41c442403000401c07841030007828031359070751600242136400480e410f56402001080405001a0104950a00301c0360303520fa0a003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 580128471 1250 580127221 580127231
    0x30809060706050a0c0f0507211101110304050d0903150914100902030706020d0509060304030216060f120509060a0e0c031f110405100f03020f0d09150204060c0204 72
    0x100200d00d051140d18400340040d42000107004046500c1ea2151803100040d946040a4150139801141d2610a903400a001104092424540c503c0070b4030805143c407009080c404c20311000e04850030701f50f500c14012040c1070200801040203000e814030040d01401594a060f503402804c55807416180124a001e60301b2545e914050542000b81100590450001c513004503501c00741e440107040003030507810400324002e008091001951a0000407290b10f142099211300b1b043c0000700081c0300c0c0ae90030007030060702188122404843e6080d281c201500141c40103654901d175400d41c1d084c01800000800c81d41e81a00ca1500d0100140745101051507a00040c41000200d2006002d40a103803404d021041d083d545809500880c003020490707500d841901d078110390000d014820180302c029035a4013442c8921604400c0100b00200d11070311400d14522031040c581030050504418400d00707001d58001c2c200d40600c00381d6034132500c000c4c0102441e56110b80c0b5a015025031030182400f0700100f081205a074000d0046440b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 580129721 1250 580128471 580128487
    0x80a080702040b0d050f01141303180306092001020d05090409020a09060b04050108090a030806061e030c0406023f040801050a020918060d03120209030d020718150308 73
    0x5412456000c080240a107283d4121800c04035115424800b90400940c40c040c0310324403068809123060712660881c03000304011290783c1c605969408a0800441c10b94040c0c02c4017000041e802c0c170805183c5401192240302c89625041015120200b00d10904d0656000002c130610085c0e101c800c035840f00c034060f9000304551b4401d201048165a40da0080c0e41160308140010a10300405000741c003c0b035070241c0c1c8011140c1c40301040f0903101c0c800e1000181c0018240d10005141c0c1c10300500801002550074800e41c40c118000000c49802e400694621b400e4030710008013008025410050303180b00036450824015049640ba24a10304000c0c802004400d43c80c4001c401c3d149040305e0350a80d00140710031402403005141c03e101d07090096000d03a8282d0f10410030546a48043d41100b20b9203441050050b0140a00d110716490540d5031005805480c081e9a80070080f825054405103d60f28080950303070007c02503a4108444041c414000215055034136141039070a9032010715008441003102c3c1c00010240d5070b0aaa = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 580130971 1250 580129721 580129729
    0x906201e030f04120e1305100608010b0313050a0803040f0308090312060112061715010e010b040303080604020c1903270504020a020c2d0a0311121e070906050a080a080702 75
    0x600c445c0302e644001401610b01c0304840741d4001d54070481070040ca2031100e9884100c2074440110078094032040200900006074006c1c0054106a962405082110180c1a00e80e0760f0703442541c0205c80440c0da10920305650710815422400041e002603510300070354140448111208180b010041555041080c55a80100101041c2e4401c0d80039111007068864011701d80c0d00a540c1da40c005090030340f00c000e0003a000250500b04074034068141c9800b00000d03450301e4510b8408890360a0040d0119038825401c004009800c101040200b00d0f80c685003200b48441c121504005c3c1c16a80c806145214041400950103103026003031003907000380c0c0e804039001a1100d0640d4003c91402d07240c101c00c550451442202c0b500008a02c2d80d0200354413900e03401900364000d0000a1044082c1544001000d12605000241c407030b05c3c00141c49d03c440e00310001151140d040e400c5003082040500d071849030706604060f00034482526503024040113000143e80109015143c400031654450090344007401c00080032401e0340441d03032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 580132221 1250 580130971 580130987
    0x506180a03270306021206040c0210090206090a0602211e0c0f030f1e090a090f0b031f0b0a050f01120f09120f0e01120906201e030f0412 60
    0xe01410b90101c01c9480307150180080d8810040c0f0803c42070380b903002400c50700c3c0a014401c800c90441c0d0142603103410080d0301c01301401006400300e03404001441a451141c407801c141c0303030041036144c0c02071605600000080c00b070480d540e608800001001c00003844080c40e0002c1d8041181840700800fa95411050480ea0801040c115040181c0c040062180404014000580307801080760030424002d40b43e02c504040b840c4903480c61141c005a1a02c8108580d83c1d00341c6c071858a44484140220b5140288070000341403645109009440c0c120f607042d1030750b50b54894030845961100075580d1004d8581003200242008105000c2c3c1810040e04802101254443d6044008107480d030100610807200e43e0f24001c481c03004046070f0a17000841c1e802c0c0308a1068410440d40e031440345c0c180c6030845442d4000e5500340141049400540380301d034403645411102007682c0d0710380340d20707140b924402500d81c074074001c405150b64440010082d9500e810300a0141059070319040c6604a544115203070541d8030034082c140c903490 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 580133471 1250 580132221 580132277
    0x1150e01031407020a0b011706060913021005040f050405040b01090e03040801090c1805100306020c030c120315100807030b0f0d06050106020d050a0905060d0204030813030506180a03 80
    0x90b00074003da240e0000740c100286445603034401016070301c4c1e0098800003944c525280305036034002d030042802802e140303044070b4010040b04903441031101c442e00490401041c940a40c030020794006000c000031080c03503500c040a4001114203000d28100350329100942c560601506c90300c0c658030700050740304200401c2101d0061080308000c0c0310314641c500b0300e08800e01144c4140711510007000c680380a024032030f20800384a080ac2185a000c02400e43d200d51000f90401400b44070345200c03c0011029200007000054a1102d20141c040c2d503d29206000c40d039900140d5408502640020000448641d000f00c68170b5886180e62a0008404084c90001101c3d0100c0f20112034110420b44918824009103803c55410303940690210382a01c1005041100d03244641200341000642511041c031091a00700010101c04403105070250030700b44ca0340c450700c4c080d0784120103100e81c900e085001001003080c2800f04580c484860700d92900f10792582c40304292122003040c40207041002035007810f4410718454030390800300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 580134721 1250 580133471 580133501
    0x90a0b0d0c080102031510020d0c0510020c0303150105070309030b22050a0201030e0f0312040809030607020d0906020721050a12020c011116060f0201060909150b0901150e0103 77
    0x50b034452006000750f0003035501503803089483d00e0550081c10030310801c000e26485607000700301c00d18002d40c0403606a00075110031200e0303000300548018507402038005040c14004040c00f40d41c1e24100401c1d0303070801c0c00455035901e040c46818022940446d0f001200c4c02c0440f9042440400c056581c3c000c1c000d0000c0c2405024010030f9928000740c001c2c0200002c402c10b1a910070f0b00e04001488a614a01c1c2d500c550380380380c2c0d070b00e07540c01004142c0c0c440d190761000369000351050303030f11a04010031440080c1c1400703c1140c81c0001070340075600f106080d56000d030581c0f00800c40380c006400c07070a00740359008400100300b80c0003020710701d50b111180003000350411510000a0b088207c582c00f00d149644000d40b107569080c5400e000580d03030030005030800d401241c520b840d614440c010a000a103010015201403200083e2402507560720100000c2c4c041c6d19020b40d0441c10f100d800d0400c4001142c50410041f03804414240313000f401d02d000180511490000005c1c601441400d05926200800c030040b8050100750305c1b09140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 580135971 1250 580134721 580134743
    0x4030609060b13060308040b13030b090a02030706050910050c0f01050c0d060602030f190c0b01060302130803130506030c07020a15030b01141e0c06070824090a0b0d 72
    0x80c807403a9403191485102c11103003400c3c0b00c0f810702d02a90030364009000c0078200b01010401001201c068800a104040c0400814620b00e0340c0c907100c0c5154003208484021079038201a56a4045280500c201d01c0a003105040032410032084401194620f9030f11400f070700c03d1141c00030314a81000402c0000046840c4c1387e20082c03110b860542e44200060f0000c0009040207810040c0105071240080161802440302d00441c504001c1031460681c81e682041d502c1e039041c04204086000403601c12084240604000d44000d030b55201c0c0b00c685004111150303070025400ba0424050030825170b00801d525011038134102c034595100c3c0c0303d508801c81c1c5880b0341140203500a120b030300300003012100c1c0102d811454180d80c400300f241551041c01510017458450381c5203101d500c1000000c80c80c1d014001d841404080c4030700034504026618105918003071060702c000c0c010940a03820041d0405005400d08185c2008017201241c402521011402c40700f00a4102c2c010651105046106a11507540d150b0301550000d0304503074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 580137221 1250 580135971 580135973
    0x5070b0a03020d020d0c1d0d020918100515090601020d0c03050c0304030312050928080f07030503092509270b09061014040b031204080106050109080a050c010f020304030609 76
    0x18050002c40101003140121003003500c7c0c09200d11040d00503c084c3c105c2c804482240d0030402102c10040100384400004c68002c6582402040030a0300c1151007007001510341048a004291341d006010458070960003502001000d99010071420888006801c00c00042001132a0036150b600400b8090311076444041400828581d000340710314058103403094100815158400e20b1a204d1000410940b411444402e00b0b00902c0c90a27403503a04a0b030b018030398007030401d41400e045200c03d6104080070342c00206c0110034400c20010500042243c0c080480b064000301803030b0300000340a0f01c15446011a00d582d83d01103000801c409090203030500d480c080d052a403102d5140340c000c1f40481d0981e02101c2900c103c4001801400d138849000c0242d03050028030200ba001e031201040b01900341e0300d0503140c160084420a04150300040c015001401c040340001c10040c1c1000001000d10540d503000180681c0710b0244803000c80d40200d0403407000c00085c40c00340303c54040c440e81645184540c0d03100420700d46c50004108 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 580138471 1250 580137221 580137247
    0xb0a0c051b041401050f01050d11040e1e0106020607051e12070f0f1706010c060905030901030b060306060702040e0f0607031506030c090b090d05161d0405070b0a03020d02 75
    0xc55280012141003200d034505500c04000c1c60f009014450301b003d51344110003680e40c024801790404001c0000e01180720380b50000c0103c560741150707001e110480b600c4c0c03041c401031030755000c0076560114001c44a040d07150314113400255a10030103400842070080000780041448400c07841c1e509120b44011086070389071800c5c071070b11300404400c885040c002400b00f03001c200020301c0b44d46840046152079880c0200f210741803220034035140c8090211750520043ca81c017003000035924019851200d0144c00916101c0c6504400541651100b00045200e46130030020000141e498000b03440300507405440001e891280300d03840506d01501c0c0c4214003000d00c290001c2101961349600003c0b81c0c403461488006403142e4841e01a4166203c03960840f0101e6a51001030202c01401406000700c48401001c240f5a6255601c0300d0741455106400464800105c0c3ca091000c2e180000d030b401d1a1007034106508480340707020f0b01c0d45e036200e07405805501c003440030010342200180e00c40d4055803c201c02c0d03d03604654461000d2404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 580139721 1250 580138471 580138513
    0x206160818010912050703060f0f05130b0603070302400917030910050c040b0703030f060f0305030403110d0c080604032c040504060f18060b090403090b0a0c05 70
    0x710b00003842c6450104504000c610610065580840117005040c150740d18000584840e19115103429915a8401c0402c2410b0103590300940d9000045004070150341040700354480000d04481c002c2d40000c4007000140c0301d202812a08440d14215201000c0701034902d0483c00490703203040201500c40340d0800550802550000003001d2040200c0c102d45a601400c112483c08101c1d81c55010303400502000d00c1c001d10503040b95600c440d60780407003440c040e00c91700410341c0c90b0041070081c1d00181c1e840480c1d06d40f48100d44038203405001144612204289584e490310b41c0c9108600000340901c0341000701300e02540300e80f0be020041c164004202c20130141c4400c600c9035100300c111001e60010f62816205088442d400200c5814103440c0e43c00c1c114064100c1c030a1001400e00540304880c141e6039030156468004292041254001c40c440c0342400c44510360030008180c881c221002481050500305200c0001d8111824008452450315602d4440da404181950ba660498901030038902500d20703e080d4030450a103074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 580140971 1250 580139721 580139767
    0x10b19080709050f13020f060d090b0a060b0417031c02030a0c0e030606041d0307050c0a08010b1e04020c100b13062108040f0605210f0402061608 64
    0x4880d125540d40a412080c0c840640d2104111106813012a04600b02110303111400c60018105035000700401002c910294480032407200c060350b68902000030401041c01003501718182c1c881c103000f80303070a100b464a503038400c610500394039850040d50036490900030700947c0c00e44034045100d00c440d0244069520041e5108036440c51806d46040000700c203241c0110300301c404030100a00104150b40d030303c0c1c5c00d001c0104100c10588010010395412041402801c00041101d6131040000d00601c1ea61881444413070b010070342203a20302d6410445034168546070540002260940043d10314540c145910106000b4458080101d2550241400202813007165801c016101c1005481c011442c50b021203103601100d00a00401400f61014501140031240110141c1d203948d00807a0524509a60b5005400c4641e0056014001045000c01c4682e42c91070300c42d0508400e000001d210407414540306500c80100100108001d1043d140400d200084116840302429115807000155589a1003da03040b00c42c045000a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 580142221 1250 580140971 580140973
    0x170d030b040c0e040203070905060f0d0b010207120b100816031214030105040209030123090606060301031e0c09110904060b1e090d21020d030b030706030905010b1908 73
    0x481034031a040c144510242184103644641e0048026410040a0741c000740107e000c00c08401c0c0c0204080c0e0702c10008024070002c200b2026640d000009c010400da802003034680b0705541068904104c014600703406280d4883d0b100341e800341603a550344040c2c101c0e01c0803600151654422000e58552100f1000c0c074050640340207600440d038032a281c0030b0468070200f281c41280d4690009100402150516801820040e50004c00100710780c180301c4c0e08035052250391050200010784c80d10a10840404c20301440d41c00c810140d91803487c540c19512100404041517560f4400c0d80d810071080c0341401094214580981800007080c40348a10032680c05a5503040380c1c0140340324a1608200003041c0807280c080f1032400c01044c10304180700308025007004240c0c120200380c0d0780050107032071588000b605500740130390040140d51008028810884000345000b0300410010b05044c6095440307c070658001807103104803a40c9150100c0c8240c0b82c0c3c900180582811903001d50031650000320348060f294100450020741d44444 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 580143471 1250 580142221 580142231
    0xe0315042a06020a0b04020f0415060f030c17100b0307050408100b030a030507060915020c010b0d0323040f090e0f0106060f0c0501150305010b040f09021810170d03 72
    0x60803600e0800000c0c842c080259100e01c040500080031954030661050005080714600c103104004030b01a546460a400e00140c0c4400040c08116040000040984031901c0d0400403010001d070007400c500c0c10452151039110740e07a400038640242603092040584001e409507074582c1000341014100e90494001c08200d40903c540a0170350b0701c02c510490710f13261001001803078940101d40b026a22a0308c08541914015243c0b0050310101c1c40f02c0001c01c248001c0c0b183d0060f590160744094600b15035045400d41d1054031b20554080201c1c1e481029509500850614440700c0d00704070240c01303014429580b080c04e07015058400010320f00000e5020481e0b9030403510680e815000d440c1800c500f03c0b000d0f07000c1c102c0414a500b03207500d9441d1080e02c4004070103100d0800020050980741c190071220165502c02c803102e030b44071410440c1e2800c150252286640c80540140603400c11540080c01d00b01c074803029250501c1017000010188544004d0481c01401c0c0203c0081800001e10800c0c1d85502030070f014000881c3c148 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 580144721 1250 580143471 580143533
    0x160311120d021b031609020f22090c110601050f04090203060f100e090304060302031801020d050a29060a05161a0c12060d0201020f01060f050f060a08070e031504 71
    0x407070017951040800301031048090800c036000f030007034104070441c1c19a49424428240040b104030504042c0301841e41c251452030f1320b03005808040d54034201c0c0080c200107040307400d50121078000481c02d055801c01c950042852405001103030060000307031006507052050070140220f00842000d113074000e0402d070044074500c90319150720f001640ca0507200038240340d1040008020951183d8055600300420341c0d140d0400100801c01682139030060300c4400010f540c1d400c2405030303807121485400c0055070f0300201f001c0c00820003d500385174810f15000c8903008010010310030b04801d1158003241c290101c1584030f01c0c80075049085c4002c0d01d409951841c4a803150910105820903003880c142d420903000c0e080c020740155100c2c002c0c056610601c02080303040d4800c003c0d01007a100070078000c010291a201c484249491315103020044840030000c05c0c5030080c2020000e028138550302c1003203d94004064144544041e00c030b4800b103490000c4c1c20002030400040503042c442085401da07800003c1210b9040d100c403a001c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 580145971 1250 580144721 580144723
    0x509130f0921024605160807060509091302060f0703120216020f0103090b091b04020405030a1704050307090e1e0601151119020102060702160311120d021b03 69
    0x1013040c09402080008010300089a001e20741c00d140001d00e0010614840c2c00c3d1410500e0f1241c1941c1199240c22202c4200040c082c4051080000d0500b28001c010071464128054914820b006001317000b0810b08000a107000c0300080307541c0401b42e01811856407212850300250250300316003002c40c00119069407e440400b450300a40e5500f48121001640250a5900708010702e4035200f44bd0b41810344070101200032074001c0320220700c210241000b5228500c0e100c01c1c0340c1e1404410502c2e8038032540c4148000d10058400080c4a400c03039901c40c0da000b00c1d41107d080f03100e1003400b4642c40540c3c1449a150046001e8696400500344007064030121a500700400503980030b4900001c1c0c00000c240d1201d0010070001202c0c1710045c20700308860a0009010421119950408402c032101940c80780c41001c1110071940e0400c90706070310944134409020b840d001020104580c1c075107480701500320040100c8100384c0b40e481c9480e030511100203008071150750643c850040c6d01ca03208000d551440c42070340703490364400703040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 580147221 1250 580145971 580145983
    0x71203090b01121a01060305060f0306090d0302030606071403042c0c0a1206030812010f0b03150a05060d09110d05120a02070308030f09010c030b010509130f092102 72
    0x3900540e8400c090382400c0030410303d0000c0c007078166544114501c0d841c0c403000c26104030034040d00b425030b008030303c51610800b4000300090507075145003e5444641000b4155001188603910102140303005a0f4989410000843c6c030f0088220103404029840e4a46e40c584400200903c100d60610301004800300d0b000d2168039907841c21900ea043d41e40d62007400900025000d5004014030441414001c181103420f138114000c41e80140c004072050207001540b0b074500700d50404d40f40c1c01002d841104000d100d0600800c90f04600016018101410f444280141d1325621405400b0203050040c00301902d601c0f452440b403000d000506c0c4151921003420440c00c05a007041e0520040254124004200e112003903020b60701d060b8081c1004200310f008030305020001500003001540100c00041180d02c25041c0094900d0846040b0302c01c82c01030521b4480f0a90350382e40c210080c1ca120000c110f0300c0e401421a1071502030091701c90844500c1e01c85140043d5201006402c1c1f103000412602c02c0c0c4110b292004411081c0da07105 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 580148471 1250 580147221 580147223
    0x7030507110606130f0f020705120406021f09240b04020901050a0806030f060708090d0e01090608090709020d1a09040c0b0714011a09060906130e0a0f030507120309 72
    0x2400682c001102c5003008010899001d865460004400003201000d8044400b00040501010380015600040c001c04010b00600e031018446014038203031070a800a550307050208041220b449081c05e0190394600c2d154080340016411036810b080300c034903403c82002d0201035078030000c4450707141007502c1c1a13500b0300c0d1003564030364803042c0c44061400300c40107015524031000504041e8148151460a002c88030140055401001503403258802e40c14103811041c14925042d61000420840d0609150303035a9009155408036016410850007980b80c0000b007908000041c1c01100d016400022800b40c8450644e0160000c2c2c0217400e404d8000d40c2121040020b848000d5034003409141c03400320b041c000210010001d00f600340c85440c148030024020411207003910102811410005a42ca401c2001c80c24090201d903805001110143c0035854010001000301503080d07980684640c0e80d8800c8029264100b0bc11032040e500100e04511541c424070303000745164081c103401c8a422800c01142d41e000790003800355007111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 580149721 1250 580148471 580148473
    0xa0b0429190c051204090b100f09120606080d08270316060e01090506010906060908340609150302070201080a02090a0503160603110a121a1305090c03031206040c021e060703050711 79
    0x843c94480d03043c0c900d1b032012f68180d0340c042e500d801c0021044000c000c61410140d086c0c40300e00780f03071918503520506180414000b540e0700c0108051914401404400c0302e02c6040600301c500701c88215410004000c0007400742c105025882c2040503c20b201002440504070303003d04800340300c800d0700c0301000c4590805c00d00c69503a040d449020010800124581100b0103030340c3d20704001d050040d50220207010800140d2128010410000d0240102640b0b881c0c044410b40f9681001c0d803034280e103035000030841c0700d00410200d4595030100304044030707a40b00620540104030042c101e030141c840c0312060700c001c1c00c0b503881000701080c03030541e64003d00e64402c2d068a001c2c0059449108440c0c1c00907490790b0140010309549000a0400c8601801e6555002c01c207030380540703140800080c0c1d0710b00050801e05d41030b031f50301c8090700c01e900500c4200c8190040e2203695910030000e07100031446c0d45083c40143d260820f05d010107286a2607060b40031100d0f2000103696445080b007aa014001910745140c00d03152125031060408031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 580150971 1250 580149721 580149737
    0x70f0c0513020909010e090f190302150c070f05100915050604150b0f0f0703120e011109040b0307150f0e090c040e060a0b0429190c051204090b100f 65
    0x500c0700c0e006c0e03203a11410710b00c242c40000c80140c003903906158068100113007110b2612140418550b040010000c09640c08400242c117041c207620b90001d90203503160003800c100c40005000708000090010081940b250001440842946c0c94040003c01c06480182d00d0149403100013842d501c2d0900448030304400101400c00486c0c00c040b02000c90358044000f182045804210005000780da40d0300030481d150103955142d0784000360260b03070002e823940c18071110b07066810b1224056040e40c80c1e40885186500807200014980c02c2507000c01c1c1000c0b050b60190051151900e8901c5125810003000d00001d54a6507a0f02901d4580c0c40030003940000982e5100c5c1c0140d02030009000201c901d0080e2600942c000307054246241e0380c0d041c0316640b540182c01c60040c442016000c040b041c0c3c00b0318884000c03420080d402e542050a0b041582544031401404482001805034654051150034020004c0310705124101582d01c54803549000058184640c1c198003d4560300b900c620300300d01c241e510f052800025994400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 580152221 1250 580150971 580150979
    0x70f080a020301150c0809220c030b060f070309050d06140c03011d0a1b02010c020708030c100213091112060409051b12010f0b04060501020d020a080a05070f0c051302090901 76
    0x5031101c84042c04c50300c003042041f450311665034400ba240c0e1101c500c600046020404102000300ba070300c0b003440180c18141800c0c0100c6165940300c0a540e81080c0142a160300c4007114201240d00307100a610040d0001400d82e000b50034018690480003800e2007850403c0000e8039032071001e036002d100034456105c690701c0051000c110080c3c0040040d0708104007000105601e00382101c1140400035580c101c4016030343d0740440c0c120164050182d88002c02d6900055414071344030028494442803081c854100039540003d8100061014040b0100503104800d010030845040100303a110f01d42c44804400d41481071070300041d2a03071500340285c003c6942d100c0c002c1c004c55074001440d05c0c0010211805c7c51360140c0903507151442e0f0304092007440318030981c4a50100b0307045006c800303000c1180c3c0180c0005045410035540711001c0c41d00050a480110b038410004c0360b8503130341240100c0c1c060041c120b0040280045200d05824001110342520a13a441104c0d8600640c0b94214010700324800d0b450704035084040640100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 580153471 1250 580152221 580152227
    0xa06050a05030f061f110105070306061b031107090b0f09010302010c020409080d0c0309020a0509010501082212020c01030f05090c011227030f03150510110303070f080a02030115 78
    0xd44c000c20060706801080300b4070203d40c2500800a14403070002818145142101c0d00709004182d0003c001c0d003810010309003002001070101d641c455101c00c170b812041503c0c004040c0300d0100d580e4400d20140130755065580300c907118805012f519805512030506c06140f0300040c0b800c050303214120b80e4140c4899003005841c2e03081c00041c00450000b9180b03402c041c404102d050302d50b805400c0c1d250246ea503000504242c140304003c6900515080305000f1205030005025990300300250315082090780c0300803140360040d000e1006240501d484000d0900e02c1e04c1c8070f038080050f00002c10028000c02600d081c08032812807600c4600700c400450305d02c0ba0703940c8130b00c00c40d03481035018640ea03078255041d104003c0352021101c0070300e208140400c0b2041079105803002c401c0003415404001d610150455180034400304801125400006265000e004e10401c01000380900007030003144c400d40d10a00740001d8a44074034050201400fa07040340072a1201203890712001071090240392080383e05880b41001e503500070746100e040407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 580154721 1250 580153471 580153501
    0x60609070c06090204110d060b0f090909070b070b041406270c040e0604050d020c06030a0506031c09091505060304080a11032a0d0807050913140103020a06050a0503 72
    0x2d4524030b5581c9031850250f00c4d10302410f100c5000703001010342c4e9900781c0c0425800300c65a0f580007441d801002d0001e400c40b0074641003107075083c950850b10001e1507101c2d1900b4034100720b184e900180440700001085420004400b902030310a5000f000310503418441d40e1000764a89030201c482c0c0f50728406000560104803c003190400e205c03006070049403240f41d10345007c101103070f080c01940781890340103c0400c001c1100c104216843d501551011302084000c400100f00c03a0300010b8113004040361030300d00140d481c0d1020000011614110750512132100d0a41002609140071130003a080100d00700003a002e23000440c8001c08040b9540604120310315516a2100481c94116043c0c1c031040000800c0ba0194001082000d00b00f0880807a220003202048000107244500302121040d4140e000032408001854001c00318640c08050b43c10025039904c140000200300030075840411910341d15007103d40c120b6039400040c00d41624401d54020109c0768540300161854081d03c440440011010000030701d4590b03441e003803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 580155971 1250 580154721 580154723
    0xf180705130906090231030f02060f03071812020a03060f0923011a030a140102191d120d14070b0c03100e010807120804050405180708060609070c 64
    0x2225000d9840d540c84000351516903224016090b00406c5108510b6a00d00c060220301d10104a5031580e0905148841c40c0c4070501c0c4409464203c0300c44004040d900c41e1000c561601c405090020750b40e2a1005000c1c110f100e02407442c55000801c0100415100f44800070142e59070b800500c44071041d4695505c85001c0c00810081d41202a1152085000240c4c60050f503580254841800606503042c17039030440c215114050700e42444001005082d0841e10701084810700c081d04070440346150130813440c000d8064812500c0442103080c50083c030480c040d80c0410b840e0300d4141c034010460078101d0104108401c0c580c0d40c076a90044e64102071920b00f621401107801c00e50800d600c0d010a8284401501c804604c150104d80c0400e0181d400000c11100010380100b000c0a455030080c604a25410294465654407050081016010346c100002c0d0a10030114140c0b0028200100180304611f8001e0011000944c007a068000314031980c48089000100071548078130803480030302540002da071200400c0380d00b50540d404c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 580157221 1250 580155971 580155997
    0x120305070c0f1407030302031c02040f0e0a0b090c210403050412050c10082d1b040e04060914010b01020d1b061104050102160506090103020c100504060b0f180705 71
    0x1925003001d5030280413440007503010b0340140d40c86003401c4080d500c140011140340e1003034500c104014800d1900b001241415914003a000011f682d0320828101c004000419160781c4c8011840108a0010340b030074001d1501c0801e0b850320040178010554080d6034401c1c1510000c010507414402803061500103501104828060000c0f161186e9110011411070005860f802001981d40790800140d0a0b10018100302c1c03900c0e140311780d0b43c136004010020400120190200440c4003800b1180303846940240107170b401501c10080161118101480c01d1703401040802000c85119400c130070443c1c40d0500600c00d4914050040c0c000d1306d03400e03031420000c07510780e041d141c0502c0441400002140110354103100c4d2000190f48100c00e141e1f40d500306800a860b1540142c95110010030030801400940c591105941440800303080250700d403165019a039050a4124037580c2440d4508820407003480340d2604006a540402c0d10380c90341280c04041031004100c0c20040708400200300038086a180c0d0700c107100628601d19624 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 580158471 1250 580157221 580157243
    0x5040c0302100210020c0a0b07050702010207060509030a14010c0305061512180109060603170a051803031215130204050d1b0504090c03020306070e0d060b1c0f120305070c0f 76
    0x5401074040360400a1b00340c0f0144d00108000d01000108449070360000300340c1c103281d42003003100d82c0001d503101494046c1204008001c91100b409440c20810160781a52141340341c0f07541131013420401d0007010410300c0c0d4030020b4200300c0860300074180140c1c079513482c4c44203480746403030702c2c41d0a11091140540600040305550002c4140c000f03490080c41010301243c8941d201042a81c6981000b0281c00e400c9180340c55040c5040007420002a08401102d820600144003030a0500488001078118041c0d082c0701000d190f0941d080112010652003e5240060121800000842c07200d41c80000ca000304c1c09000d4000c1c0c4010100c42c003103214046041c003171a25400c40b6141c80780d140e0340450280c4c1c801320340895020010850034000c41c0b0f410700c6070562010b41d03482c1880319103000c0c8001610b02c6504941c00361400d961004e000d0f000b611184070711000710140320f420080121041c0b80c2078030303600001001964404d400c0201e03922018840d020741c0d030040a05640d480c6404056868000f0640711400e0125200d030116 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 580159721 1250 580158471 580158493
    0xb0103110a0e0d200a140f0121020a0512010609030803010504090f02040c0504140609030a020123030c07050c0306010810020c010204051f020d03051306050a14150307050405040c03021002 82
    0x1c0026024213812200200e07004035100d04c10322095002d05c0d004201c08a50b0000c40600a89036054821040c0400b41b801340703140c1c0d0540c44645056040000c0400d0b059000042d6100540c1e0003a0060683d10308840d908000c60f80e846c882240d42440900004010340810801040546000c0d08440402405200d101508400c0c903030015044541c00810900810700100d0104030440c4407092400c4452001c0d60040d20b0006881c00080d10755030549002414003645d012016007061032015030400c8401c0415446590303007003420700f01c1620b07040210101c1d200e02c2003240c0e05800d82004910316048030920340040200c261080b420384080d411030080e000440d07609000c0026196240420595a480c03022412941150443e2000f4200000c000003441414108001d000302c841784110440c48a03900201c0006954460040d000080c01c000070602c2c4405030700a091060404400305040030b10b1104500303c07000255244140802c0c2c4030100c0c0c000e441d00d00c1d218400c0000d400e00d50f6200c141100b8501c1030b560301c2d03400b0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 580160971 1250 580159721 580159733
    0x3120f15030b0907050108100b0307180e01030c0b0a08150303220e0c070b04030810090c0e01020f0f0601030f020a0302090c0c1b100c060e0d0804060b0103110a0e0d 72
    0x101c0e84181c840c02000024420594000d00441000e04428686841140341c01c604241070842a03100e034442170080000002c10b000d2090310603840a0480c1c2c0c4885000d5170b919260440015428042910342d810b02d4040060700e011640100c42a2014603240d00d07610b560361403c8104080c07102c0c500d480d050f010810405421040bc40c11441404031013070b102104590500178a00300110006218900b40001001914003068500c440700d9402949842c100c8100d039500c0020b520b03103410690008203914280000a503100c0d8011161562509c02a400c4a204250b01c0603429910505408a490a07801c680d00510228861000307040500c0d001030612114a607580e80400c0c884402140e42070040031780810311000300501402203c655203007a00d0700c4240c16014900240d21800001d030090103210b403901c000410010603400052902c406041654101888043d000e13101107011903013120001d103004594841d0b980a03100b002c0000301703060310b030901b8010030480980e078580343e901002c0d611401d90042c100000d51 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 580162221 1250 580160971 580161011
    0x910080c09060a0914010509031b0411030106020f1c090e2703040914070504051c0203120c0c09091e03220503061003110409321903120f 60
    0x4003a03a40c0c401316031516513514420b0f10444101c904011040028903829503000541c00c401c22402030840a0a600c03510000d4004d0141884540d5500008400000e1450700400c07055001d0800758141c1d0001002c071060b0304246803103000c0300c0c1e010403442c80003402100c6005a1003640440c3c0680c8202d004103401002030700b005507150300038041d035100007000d1010104a009904030301c551403890310402d040500020300075000d00d004150140381c0300000e00103c41e5415010b640d00580203400d41c1c81c4008001c2c1440455480043c0000b0703d03204407412118541041c40c00c942c420010400a40300c5100010114120404800c0d13210b00035200500403a802440c50520204844201001450241d8500780c20725003440c03001401c42018842c02d00c01040891942c3d0180d000c400021030300010803940f40e00d405114003560921502129020904480780301540030034002203034812404550044690510071921400c18010043c002000c440f00c0126060851b0016528405403490104110b0981106544407070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 580163471 1250 580162221 580162237
    0xc1b0105040f02011803110d081b011a120a02040e0715080117031c0c050705030d09050114040f0807030c0b09010c0801060207320910090506060910080c0906 69
    0x5008103081408540c0c0044141c85039007440190140300382e1035500da9100d45a048440240a2419052003501308840e19040720b4120005030f84000e4000b43c41d0095a000b4848a120301c0045801d10f03204030ce01c0d24240d0142c3c10480c12403402030462003d2542400081c00c004155042d0b00d114007880800c289141c0424219a001603a03504001f540c505055409069100c00d81c4011540040003000d01d0070040000b20325405034201004920989503520840703141c450280c000c1c00e1400b0200350a0203a1a190b00031039a198010070080c040e01602c810103000700d4505a40c0103112810001182c000200288003500d40ca0b402030500b81e500781d6050300c4143c403001044500d41600e035034482c0031504141e000a04940034001c2440100b6071207040119811102512200292032604a101041114820314000e000c201a0240495145040c140d8445201e00e545001d0f560a031824070b000038116040400a23512042da000b003003481c01d01e40001041d6101e0078060a0101003001c10441018941c4139680101046 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 580164721 1250 580163471 580163483
    0x306121704240e040c0c02011419090f090c0903030c0609080a0302130618050d08090a0b0a0207060f0503010e0709051210150b040b1c060f2c0c1b010504 67
    0x190b00c1d1820024001c4400b038890b1440385241c50364046825501201d07444440d60f082c00e20030081521a07103030400034060f1044080311046618810188564000e02c200c0c03c44122190a81030b168030342403803070243c41500186800060040c1401c00209209804405140d4010f03000080c1090860b100c60007581e0109000300046600050700c04001010b40808034002c1c038951400c846d003514418000404c5129510070144560742038807a640a11814508482c0302d5a0010100c1c84030555034000b819694000c40211400f40c0a0f500000034928000c40d10244c052116942d0070b441d40e820710442150323110f80035100c1010040c2c0440301250a840c0c0d41e100c000b4003000e0400602100d10040400400d5070303080c0200c05080c0c0c041e20010020141010305841c03e0329414140280c0701c0e808240b1446031580c4e0705c0c031030f8082e107400c20310009403044146000000f582d0000c4c208440c02e0a071111a038203040ca014244811003410280080d0b0f007480d0301000303050101c01200c445a115104941c1282c01d65005032401d80d04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 580165971 1250 580164721 580164779
    0x3040b040b1806190615080105011101060b040506360f0a120f02120a0305071106130515160503040e16020d0f0908010c030605030d0306121704 63
    0x38403a1035a21640d00c9a000315000300b48008a0340207507282d00c0d000d030403121140003070b59114004003d01c0c0c2009019000d001401c10f00a460b00b64004d110520070320031140820b616400d1140d041d034041c000d040a5412040103a40703070510703140500545074000701000600d04914442072440c00740341520b80492108000011817003807500f000f048141c0024070260342c4143e41d01030041200300c05040040301c0341c07501f0080d9810b20341000c2c000b1038200030f00b0150301e44541c09200c0c500010180c20102416043d0701030300c040e00c02d864009060041d140300e01c90588512000026082000f442c0c87d6250a030b60b0010080940c1c141007020707002c026020720444046955420100d03007400001429145d4550116070a151100082d600130406911012510003c0c010400341d0b80714482454081d0300d1140081c030400008214840c841070005000302141e001e283d100b809850054a08903103e8050541070380d42540e051030040d4101e84c0c1e000184164903240c0c0170310310014000011150000e03402e69000041484405603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 580167221 1250 580165971 580165973
    0x3091a100602010b130504060615020313090b090a0903110f010f1503020616020631080d0f0e0307030f03020f25090203060d06020c0106060e1807080a090803040b04 72
    0x2080d104260020300440e89000c610a0031a540c12140c0e010544090500095548990821078090b00c075940181000c9250240c4d60180380c0e41c008000c100701c1d80000c5641030200c1c1c41740007000070746018143e82c1c1d0f40024000b0208101440c59400180700a1080c1080206000d5250700c036810070034003100803541d503556642d0051311005d243c0901c50b1042201020104420706641c00200780d8002c0d0b40206200030305d20100b2034115214102203682d00f90101c040c140080304001e6025150b400715808084405800c0c0d0000507144800007450085200705440d2907100145d003503411500da514806500d5454440c410000010401074007515900c01d019501801c036182800104900d4001204c40900b1006482c40c0c010104003400d501200a449981700c026070b40ba103071480020000307556203c02410480c80001d0355880004150b00030012903400b034548d600c0c0340c2002c2081000400c202e10101500080b2140002d180c94468084194030001d45800000c0680c0107842d0142141c10498084a0002408041c48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 580168471 1250 580167221 580167241
    0xa0b09040f0b10050f0904050408030115020c0303032a0327160501030c020a02222004030605130f081b0d17100902210c030906040f020103091a 63
    0x1400a80918818446038100c02e020940000c91000754400300900801e960103a0303682501183e42c3d10301d00030018032482c14213050002c901e50080c4103124a0048030820380c0807441c00868620703054a07008000e1800c641e0b84110b040010194a000314606070400c4008807034151201001d10b004038800480300c80948458021651103084a00f4075a04c2580702403d0318a41390314600c500400d590081ca00800c00141082e81039180c40c910420095000c1603a00c401604520146019400a0b808039014005007400b03e641d20b03800710f040110320000f00b4082000340045040e640025400121640b0428030078100ea4030b4903124020092012030743e11200140b688d001520f00309203641641c410102070141d24842c0c01c8007901008e040c000703061441d0020400150310702c64911100d0000c10380341d54103654a210070050345002d0840e2048505d010303000c02c00800d400c40c1a000aa9124140400080806884580b201e22107120b076075070100d04058a840581e4002070b01c442001d00d00800180d03401e01d0500742002c0074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 580169721 1250 580168471 580168481
    0x120b0a11070204052d010b030a0c211506031806020a0908030a05031515181201060801050108060f09070e041b1202131b08060607080c03071a01060c021e0a0b0904 71
    0x2203014440c05c42c0051100c1304803001225001207a101c40002c201c00d441d00143e49054903002c00c020080e400050740c0004410315000100c850048454040a0a840d840107604449000e008190407076406e8840500040040d8004c000c181118185805107598983d00c40380b5691041b01d800340001e0000c800d100200303081400c2e07100c401004803500387c241c4114030300c680c1050054080c84005914480c4202400740c540d1500c442d0001c142c01c00030b000c044e4131090940d010702400e11500059100b600d00082400c1c0c40398415038000d140810140c0051441c003000c082501c0400382094843c8040581c070000c00106082c40c0b200101515807403a0b440038564010080c45130004801d0000301410580c80e25481c032503034010503400c1103850501051a84481c1d0120b40280a02e410007801c412001610400d58900003001c0c081140c45401045140b10701c02c02e07510701f412020710800c0040f0327003000c003950014500703c110f0000d5000030b8640d12584401721b000140100200fa80011608000080e06014504280c055 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 580170971 1250 580169721 580169791
    0xa3f020904031e02011808031b13031e030e1509040203010e010303020c01020a05030901110304030609060b150c030409110c06190b0603010807170f030c010510120b0a1107020405 78
    0x6c20002900c01c01c50f107140348001e0402080341400000168460400710080788112004101716a00e909290030807a84040366400f042c0c40c0d03c81d800803c00341d0740300e0100020070841d5159842041c05a18402400181071042100da00c0540c401d000c08522912103101540c02030004190310815945541401707810140c442420034110f42003d101200071400c000100c5000c40e07000e10b0646031480518039000d00b940102d41000f0034107814520f4080500046401c15100e914084902d814004080c0940400d0f91043c251040541e40003400104005c0d0003981c04480648495100c0900e001c20104040741040c2c030460710102012310940307074030b1568800d1f8031410700101015240e00349154101902c09558984a22030103909280070183c6d044105820300c00b02080401e880c0c00c07a500d6820726030201c4e010340380486000e00441e1101d0b40000b08071904540c04030025402c8622050291200b5a5000242a050001000e4124100851001038030755100381d40c41070002c0260024182c10180414519510782c0403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 580172221 1250 580170971 580170973
    0x3020109120b010b0c0f0109060605090907030309060e370504061202270103050c0126071119080d2412031b110a3f020904031e02 57
    0x8481400500c401c060359040d19007042030313a0780b25551680c0c0c02d49004501c03801e6002c0795003049201420001c81e60401c1050714400c0701c100856a0359041c0390f0b6501d0043c4d01c800b1380001c150b52410840d10740111410301c0b0300d02002c0c0002031031500300080c03440d0341080d04165014210ba400c0f01c2480c03103954505440c02408003100e040c40168070309905004030510412004c2d105c1e90801d034811000c940d144044810801d110810031205681d40d0130060307121686a04040d0101e03803420740d048001c0d01c502c010b2400d0781d01044900b12094031181800c40301c0040003038100c0440d229420742c1500700950204401411072080840a980e0b0307448100000540304c07204446074451400b0710001d03c044000140304026030380408007400e8411380768101218501c4590018001a06d500241081800200b504001c1e03440420396075040030741da551086110042520040410b82542c1c0705048505086801507040c7c41c41004c15040390f9503913503030009200c041013510100d000c250604050300d00000820300f110b1655103140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 580173471 1250 580172221 580172249
    0xf03050a1d0a05070609140108060607060501080d020d031401031b030c0f06090b070209040f06060306020f03070206180d3002030103290c09041b2105060d02013603020109 75
    0x800000301001c20251f031605110751080044c0707084e11000241c6000f5608032130300f80010b5941310105504da028200c2044018041d800740c0386a144d0003802400ba00c0c44400c1c0c541c0850340c0c81e5032034254402c85510b59030545281088030010115081903801e50280071090050310300d951400340d0242982c559603002e03070882103050101001698907150b0303881d801600240507550111040c5010801030900c0c0c0c0008100324030110356907400f401100003030341c441e11054080f1880c80d240ca003d980d030442416440103141c0d170303c0100d0380c03501c2074447d0b464003000c1d402c01030410340b0800885e40400c10411242c030070b2202d0036502100400c1440b07840d480c0300407129190042c0340c10f80800c004c402d02103800000c14418038200c2c0081c1083c22a04c03940d100c0b680e94042040d04030009058044010324000b08071030000c0c0d01d01079050b50701c4c642403442c0c4101c07402020028142540030401d54010340b0300c480d50082c4070408612418458200707414840d203441c1c403070006002e00c004683c03d40c0b0000d460000c0a405c00e0003644082c1c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 580174721 1250 580173471 580173479
    0xb0c0d060617070503060307031203021e030f16030b0301090605060a05150a0f090510170901021602090406022b150b0304021504050301020a08010305120306010f03050a1d0a05070609 80
    0x82101c0b54224490303103841580c903038a150104e880c0103a15400100428411031015a503d03903d179000c0c08010314000c3c1c200003440301c100513419160200303480790898403200d0700205280107000310591181c0f1005040200e59040322900003402c56000c3e40095542646843c02c100f034034500000000003429041b0f620410030700496031500b0140c0640801201071082d80103079146020300862440c40142030041403038210164502005091404880d145180001d016000c14040340040c001c1e10010038079030440100392041a020841c03004006001503542d00c0d400c00184c408090458450000d400508108800110507206003100b15510b07081da040b000780e40300c030341400703c0407c010440390043c1c1c040f5100c400028501e44031160b00e111b585d120130340c550320010b81800340076007044295048902441c02d03a540d02884c11102c10f001d02c002c40d1041d00061070201160444c9019600464103d80c400d00001032044000051030b4901000c1e0030082c826074481c0f84c0d62410002e0810290b00a800c103850414841c0b890 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 580175971 1250 580174721 580174757
    0x1306090e070b0f25060606050a03050604020a17040f060903050309060702010203060a0e0a060f080a020f03011a011b0503032403010b130f020c061e07090b030103110d0b0c0d0606 78
    0x150402d0640e01d041140d0700c45a60b01c1301e904000c0d0300741c1c1d0080380400896560744d0014000d50f0000079240701113410070000801614091098400020b05600e424002480d484071124a000c5c0060089601110010100740491300d03a00c240110980300c1d40300c5c00e56034200a54614500940144828116070041040014079102d07091582c04171011400810b0306078880c500007202038510381e0030001c020b95400707800142841c0b0004132640b09900941d07002d0340c400c85d10018103003070740c403518480b140e04a81140380c00c0e002c1d4480c00c1c102a880406c905161074050243e0785240c1140d000342c0f042e100d2098250282000d00301501404070707254108170020410049204042001d462003807124991803952991207030a450003070f4045501440003a41035917564641000081c118020301541981c9c04c43c0844001203030580030b80425000d45202c0030341742c0c0c1942e04c0e6a80c0c0900310056030401680001140d540f000001d00003400c400d006811301c2440d036480b5403241d843e940454044d98880b404201c0d840c1401031a40034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 580177221 1250 580175971 580175977
    0x60c0b0a0902061206040906140105010e0108160e0a0e04080414030c1008091e070e0f070c170d0f09050105071d06070c0e0f01060f08190b1306090e070b0f 68
    0x10360040505550703540c5c6130004000f8601c1e440e01a0105081c180c07400b101c1d1110f48a02410b0b680c0c02d8a400c02c00950036401181e959400b1940e108001c041010210142ca00a054008100800802d0b241c0001e880d01c0310814081019241142c240c807000c541400409140c803a100c1c0d81410507030051818520500014440d035807441101800e1107811404244181e00c10300250020048541c1e0b030000410704482e01036036402c4288a1440c108100401046c3c2c00c6c001a07507801d00420842d601e244101445881d0120b21110010380e18802d00300401c1800c0004015004007803400c103030004006203030703401f40c10141e003501c00c020001020404400c40680c4040d903c0c8442131310080040d2074280d103a8078a460314003244a0241c100078502c011150400048520201006059640590318003511840c0204260b548090a8680909000240d0060411010b580d4880d0031101070062130003030b4200c41840f80388200c49091f041070070083d4a8403480c03129000e040100c04000d211403444070749010301209070a20540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 580178471 1250 580177221 580177237
    0x9030c020904110414060405070207030c06080915090604050c0604060c0b04140f06100f0315050a0b0406080d0905091510020c18070f0c051b01030905010204060c0b0a090206 76
    0x800d041c0003181c20300c010203280d440344142c00703003007080b4200c80d0b0b003007620b81038030203c502d588140d06120004100724808503045d004c60741c1c41000340948600305001655074110081c17a00d11a48107000180380c00380811440300c0d004580d150007500f8a4205800d145090000868466008501c01c000801c0001d501c1741402000c80d802600da004561118a40307040f2103008c0141741442c1d80f160381546070b00790700702140703003400345c0e02c240700120361643d13602d00408071030310719120180131044408025080b1584907001503510070000c22000844000a01c0001c2c03c80d45181c0024a0903400198103a0800750840d03010005031108442104080c0b8101700c03a50b000641c064042401250300300ca510301c5040c0208808440707070f1030050440c44c005400d080800c5d602401202e07060b00240358204003201044c0142c3d050304e2419000300141102038060400b034800c1001100920b410580d440c400500415170a1001c1d2000d080180d170341102c020700d6802d0003039481030042c11024a0b11300d07011401006070350313040403034001d2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 580179721 1250 580178471 580178479
    0xd0b01140103090506010b030612060103020f0d060f0c020304090606080903090f130c050319020a2019060203092503060c09090e06090f0a0809040e1c050c010b0409030c02 75
    0x198400e400100c003e0440d03002c0041491180d00c00201c4c100600d50302462103110300f82c0d0114000e801980c1c1c0b003581c4a40a100181d00030311110b9010242d810315107412258a07015050105011694040c0c42007118a90075100c0c00581020409210400d10f9002d0303d0300408041c45c055500b820000080c6440b88682c00610b40304148028200c590b945503075100700360307008c007060003040030304404a000f40507036200b140c00140414140c1030711001980e55100303a80300002946d4400020701011043d0146030a03840b42d50f502d40740300d0b804501000d59502e605642050340700319405a142e0030401d9040c3d191080c00c0c40c94070b000ca103507070000c94500f410b04c121003402c480d048080800d10808600c0300fa1803a03201f64010701030150501c056038141100002c0e1407401082c000080b40c0354106000381031b42d120500450014416641040100c48078907042d023114662110b40d006903a0182058200440d00200800000b004180c01054540600c2b42c28400c8076011681900c00380024003460b94014041140345c60001d1103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 580180971 1250 580179721 580179749
    0x18090b0c09030f03030f0411060a080403030e0c03010e250305062a040303021c020303060d0f02040b03030a0c0311060f040318031b0e2401050307020f190308060d0b01 73
    0x1a0303408200d20300c44034580b081130702d949003000300100303680520032202a43c03002c1c641130070a4658144002101c90520042d583c3c840365031500e03a0100d0141552040181322441048903860719a9030a03c9031480e80610007004005082041c481071101c0b05180f4171503124408201810800f0640210b580745c2d000030004060301c48415010200c010564101c2245100d5400205002c420540c000403108000440c00080c66501d4110f080708aa40303102c00c80b41150000209503030762001920302800d4400c034501c0113002140e215880740120340b440d04003004120000c1e415602c20402d16030806041c485030809400680003528003600c04a007502c40240000b02000700c0841a508544e03100c0301e40a004c1d684c8140c1d400102d04800045101c10645401107404441d002c4012840c05002c4000301081f6030110751404004a4142c1e0040d212504020900700541c00382c07462000ea680818040c91180c103d0041e980e00e080b26980c20020840c48006000500400041c00c103000440d510000060440b0810888066 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 580182221 1250 580180971 580180987
    0xa02061c0f06062c030c0d050c062107020a0b070507030e030a03050a090501031505061606020c01020301060e062a031608030f07020706170402040b06120118090b0c 72
    0x24020071001400c0740746014000b180159201007000020a441e0031300c10401c40540b02d48080000300b05410a40c11703400401090140e00f803040c402c0c001c4601035001d44401403014004201290300400b20f8114108800c06150240300384401d41316084801e41c1300900240d000b80d50b800551500143c5840140840410088101071003550855890398024090329044038042c90084e0080d082080300d07402207200c0d560086400d5220344104407041030300078000d07a8800d107808207106081d407200306840b5007106100c0390796021031000d0008210540700e4000069584d80b40c40001002c0c0c1100c6801d03244034400402032000c0850702d40210040032204a0300c41c081751221a1b0703060b8a94800c250380842d0410b4a8001072051046184c0a035200d501e0480b14464542c0e5030200c100c1e1540a64014030000c11040400d0003810180d101d6108e030700502c043c0001640350701580000b80740750000c85696045000102c01030001c3c50003085208100c0007000401d1000c0032403543c402d0700310400101031004900c80400d1000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 580183471 1250 580182221 580182277
    0xa020309040b130e150133030e120a1e0e040e010b030a0506090d021f0b030307061a040b04270614090a0506010f0308091002120406020114090a0206 65
    0x4183d1040c0a0000c0214640301c00c02d50381c0701e0103102c104d4440020707004000601d0145c01c40346001c4640c9208a00400e080382c5202e03601c0c00780d001003103070b90415a03601c2101900074001c100104030140c0c041c0d03120b9100d0b4071405009159201d40c0035138410010f640b04810030a01c0c0c1040d0720301c48a42c021580445c00d2030361f1050840c0184910845154507104080001e41400310228040f03004a21040c1981c1c48480d001d54140c0c0ea601900780f1500110b030310030444102c5400b683c3c1c841c408017080202a01d05d0301d2095120301e001d9400b503240390100c013094400c5120b401c0c509449507030f4079a5011341d41405450211503d5004003100d1080c0c80c03c00744160034100d010042c0036809000041141d59100c4d105007450101155110160002220540300d2240007081ca001c0c0c40311104102da0b80400f80c00e00e0081c51b9400d00c007544150507422002e501c20404120440800303480503001400f142c0d8000100003030350346400d8404640150002e070313080e0000c8580d000580c989100712682158040c5901c080d82c0c00b0554a1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 580184721 1250 580183471 580183489
    0x1b030403031e29060406020c0d0c0f15020c0108040206190c060e0f0607210e1609020903120c0706080c07120e100302031513022107020f030a020309040b 67
    0x10000c0c515101c04032043c0f911400924403181d441d20808041030a5000c00e00c10f491145000d00b0025074440e070034036003251600c100401d480c14071503040001c20b40e40d20200810f400700b50790003091b440d0500c4034182242941c100a1409010401d113000000ea00f4180c0110f000c911802e0014006030103d040e904040038000c008111490342e04c003004020410b545001d442c0c40d010002d907014007038004c040110303404510844620440c400c0f0001c0e6442206544c4084900401d91102580d045000b00c0503040e001d00104ac0c84480102401c01015a80340250400c241c14010404d0500071803003814020f05c1c08022000500c00309070380711303420001515120f82d420003000b8052200002c00d40032040c090414040d40c0136250b000300d8041030759407454040c03070910190280e001c103c81c0f880798071500c0e0f10107030810718103494620042c0c41c2a80d001494882e01c1c211651540c6030031010320180079052824445283e070304120021101d080d03a0301541c01c04948041c003d44900c11040e44a00c01c6489038504c0343e80e543c0d031a0300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 580185971 1250 580184721 580184771
    0x306032a010f1b080a051303120206010602070b09090a0906020304050c030c12030319180c0509100518190903020a0c060212030109020d020f19030608060105011407061401030c09051b03040303 84
    0x4440d005603230701c4ca848240203401104500040c0207080c0005002c031700000303904096440141000c1e00f0102400700344800e4200c02841104925100c1e0060301c0418000d1000b1800382d03000394003411200c0103c4051600e00a5080c9115000e5040444800d001440100a480d04440048901d9004400d04415040a4440411140900001001d00701d0810420729029000c454082d1000e910b1541c401601501403000e0344611604254400707801100b50010585c0b15600c049850120400310204804400c1151620b45045003d44d0002000405202c1052045d000811992006150f001402da00754511400107114044500d80c021441031031410007501903a1840ca131003101c841c1ca0390f24142e0000015068442e011004c280f4140c0c0c04210b0400114005040c0c44040c0c40c1c04030b400b100c00e50840c1c0b0950081400307455081e910308284210381e0703081020324021401030040300101030800c0000011114081c00c106503442c4a105aa802a0741d100260307540b054250500117668400f01d241e01c4003462150300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 580187221 1250 580185971 580185997
    0x1110051f0b040312030b010c0b0703200d0b030c03070302010c170a0e0916080c13051003050601110a0c06111e0f0c04060503070b0306032a010f1b080a05 67
    0x40032a004480074050710849000b6005000e280010080940c00c842201c071015001a405400300008503040000d442e801001d41e140c0013840240d240903e18034078202d648000000358001a18808200c258043d060100d0b0046000c0c0854030035800c002a9201d0591100a040c0f10290b100d280a002c105958003407100d070707000341056444c1c03400348005003511000210144075980b80b80108440130803684201d250801591100345442d190303100d48802c55002800b84400e0459000f00200711911082c40c1c610034155551004503d9090001c00505005808100380c485a0701074000c0c0c82c045158500c1100c2121101d01b000e42844440500c41c0d410020440c40940300419a421078a40341c0d03000240c0c240403441020150b8403a50740e080100410f03a03146116a03a4107900100f0300744204103c40d401550080c5004007160b0b044400960154a0000c1504000705c0c400c4e0100307140c0c103d55812021981c1c002e0058580504200242400b5070300561007040c3c06081110046203140312070b40510308440004801023 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 580188471 1250 580187221 580187281
    0x5030c030708040603050c16081e18090c070b011404020d02032502030403030203040e060a15080406053603043501050c160602040308031305010c111005 67
    0x8240303841e880c2d000388a90130009241800003850700f0803200603a646a00070729801d00d001103c9445158094000b48841d420f2105c0941a07503001c000b06c14014080d200c1d2030b82079011600445000c100c020341005102c011312010400c40b070f50001c0e80b00c0d1a500c0c151540e15584000800c41d20b404a802406001c481005440c800414010704610340c545c610f610101c00c54941400c2600398102702d031640154030000b40903078010306c010300840002039003195000e03002408499407180d940344c50080f0309004060500100d070000c0c0900c010300c4464003615070300c0295400003440b4034a0f010b04d808020070313045a08502e1840d61812281580e107003802158014411981c8120307016802c9480d442c1c04118a140940600c944103000200d0403078103000e414821441c60340d55909080365604001a6940d0a0388100d803c151300b000088000b0b4190000346004500c144102c849521043c6030a6085900d1440c4003010300440510002d4040e40024070714003100c10962000c51151140810040320102d1404e001c0441c1401d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 580189721 1250 580188471 580188473
    0x150603050a050708011b1b080708031f060c0f02120105070504090f0b0108060603070923040e010603050d051608041203170c03010312120509010b01021014011205030c0307 75
    0x41201e0502e02900940c0d128565490740c1900300d80414603440081e60142c2c84040e000d6004050702a580a40c941130140b40c3c101c9640c540c21303190302c401e800700d43c050804030610107800e4680c80c2c40c0d4401007100f034094940b00d0801134080c0004655040042550741050a41821521038008902e02500720200034491424030540c060319a8005001c4c50910380d181007001d01224440c1d001e424071041c0183c5540000d501e400d01485100d40c00100030100303002100d080043d1a4041ca5000348840300e9480201082054000030041600c40403591034045a0416400b4800f1a00101e1042050401e5041013aa00c004e0050710f02030020301600003510017000428000b440340d5000e0704941c6550f00c030b03544484080b81100038106192009480d0030171104414001407000502001d000440460241059401010300301c03011720554004540e04410760b51250b00444071541c04010002c0040f0000c2d01c24003440d01c0d0000324800c0881305120312a54400d200510006004040c001c640004110100fa41e5541c00300b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 580190971 1250 580189721 580189723
    0x5090f0c191e03021305010302030c0c07140a060c170c0106090e0c04061d060607140f0a02121902060901050403020307061e0804050303160e03191e0f03050715060305 73
    0x10440a0703190b40d0390850005071859101c0e200321080d0034801c104540300ca9081400450003500b006003a8040184104600f4070710807420803801000707101c2441006c0c070850900b000d012610308a6131145051008410300176001898001c422101c2c03a206000306501c4880340003507a40586040e0784441d500c1072800ea80c10000203404220107140c030100b0703642840900c5d079a040308150850600d00918200c7c446402050040c07420800415855006503141c00e102c28401d0f0742c05040610359418404554420b440348401c5007003251a266004681c50044c20395443d0307019071aa00340300801c1009108220000e4241810f070700550035030340916006030841da112502c0e45806040c1581d03da50341c00d0320710101454803654612503c8942d00c16684a1301641c15519190206424504000b210398180640406400751540301041008400e403070003032004485200b2401c0c030301040c082d1030307004d414282c8000c107100011803000c486c2c42008070f03070524055590351003d0809241f4640018800211f20342005000418010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 580192221 1250 580190971 580190987
    0xa021504030e1206011e05060307030c0c170304140d0e011808060127020304030c03030905010905030a180e01080a0f05010209030111090306060a0f120203010b1504030b010f05090f0c19 81
    0x6e9100d5030090501005001148039034075403041030351100c2d0030030002c3c00b203620030f4100d500340c0e1401d410060350b1402030781d850148000c0c500100084141001c400c11040c45a09900c1e4500b00007008007400c012415140000c21440c012070420341807203006640d41d01c845001d200c6a20040002030203441c40c95844813140300303040b03000f4504400c4031000760744442c12100b0140700300e0b8025a8140c40e449064016507800b41c0160201071029211956240a42c4000c41d80500040021142990b50180da4805040d4001131030103041c0c00a0081c1d52588006003c0c0f14000a02500d440d42c000000c800500202e2812078068480c0542c1d40c1d81650a00c0504a01d44400d41c01a264104040f002e49015990b80c8044c080442040d101e035000b40345c1c00e41f40c1000f40311004821003000c03d0010b8000706420280700c02141e600c120001c1e5250816500090400610285850705409040c1c000b41c2c901c205440c00000640351000501982d1898582002240d64040d0300c4003107842076046071100390480344d030702c80c3e0140043c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 580193471 1250 580192221 580192229
    0x12020c011202040609090b030102192a170f160305130608070804021c1b050a15080a020315030a030801060207170a110a0e0a0911060a021504030e120601 67
    0x500d40025468844040e070003070b50107440aa03034880d405c00385804c0c1003201408440d000a030b0555400c010300fa205080d0040041d030030001e96221013145503411004c2400d54218aa8a16400000b00c0c0c42c2c803001880300c404004400c034030314980a0301c400400c0d541c0780061003400c01401010300040440c000700354100019009880c8007000c061860356558400b074503204e0741284d6600c002181d090020b8018500100403408085a0a2009880f0840341e40c521140c048000c410b004002041c002c208414580740d00141c000c0e00405c190300d540ad03134081c800506201700281026044640100024184000c90001ca107881040141215402116030601501d401000c0c003e9900501604a0101e444040380704c0c01301100c2c850000a0111300f4007901d0b80d2451100c54424103130310400001000a0420305c140170346008a5200790001000305861030003c0301c5070840c1c840640114420701c0041c4802d030b0081080c080c0700c00e55410940303403075072140f4003151111a10b22401b948034019403250450303800000f440605803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 580194721 1250 580193471 580193477
    0xb030a0b1008010e040b07141b0d020d080c16020405010e150102071805090c030106031202240a0506030a170c0c060313121101060608070e0406080715020a12020c01 72
    0x1002040d0710444820b0024051a01c0400958001c1000070700c40d07076282c50b8040c2442c9001c0103024140b50880d00c03c0d5000310480121403152019842d5104d006000c01ea00400b640d00091101040b4a4000741c00e9050003046e01d01003010115030751050402e54420381c000b8540c000e0081001d9030311001c034a81e4144082d80c0e40f840310003440e11a19125400000c04000752401d1a1000420345c691070b003924041c05008001c8601c501031101003c0841e1000d000f2407014520800c000c544040388010000e25160b160744070b041e140c002c8440009070400d403c0b192a900041000382c00704c0c19941d000c0c0405e1070140c0004004160500803141d1699000030f1801a060100c411030035900d0345080c0a08021007400f09541807404402d10b10181c0c40054100900c100b06425181071003440041c920341100e0840324541d2114001c900000c0030003900e2544951780700141d0808a904009290030315002550380d03007940c0200e0400e800380c450701001d031500800c41e400a503503000f85030700d100c090086070007916420380c10078403804 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 580195971 1250 580194721 580194739
    0x50715081501080115050409141f0608070507110a060e0f0a05090c03090a05030c21130302120309040f06061704030c03030c090305060a05090c04060803090603100b030a0b 75
    0x41401e46041840100005079180b440503400c0c0030205002181407400e8105200701000005601070b03039402103107400e1341e0309556070743c0701d150003114403004a0081d6100d118910580b682803003841d40200c80c254100c155407034001e46039500c038500f000040c0c0180f6466540041244ea0000f0916800342c4841000b2005481c2038030348070944c00034068030030f089000346584840070706d00045c42e03107802d003010b9540400300c10304444080109448490450703110480d0100d864000520150303140c4031042507980e4000e00c49041e2440e14621501c2e4400d0b0310100c5c00000c0c03188011140d0940803a000f0420340c1d4880320020001c1010401d10140d0800500040c4141c40114000400030322951000c10311a5100d40e0305600d840e0044000c942e0114000c0c10030350190424000c0001e0f020020030400c001c1c0d1841400c2c031100006090404140b04e0340f511440301040c0e8400d40c03c0041c02e0011030380c00b005075400c94038241c9040342c42c1c1c1c0320740000300040505500001e18050022040090202094202c2c1c04815001e40f06118 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 580197221 1250 580195971 580195981
    0x11518020a08040f050304120809040c0c05060703050a0204090609090605010f0e0103112b0c050f031e030c030c060f01050d0f030516081b060a0e0607050a0c05071508 73
    0x241d006911511000c101e8110005012480b1200038500769880744050300c1c074240e20f400c0000d010032101c100030b840350a000f085c03050075420548207000d400203090030510304101c43d80c0e0b10710795078a100402800170540c880e0080340c2c03420003d40644000e407000b11801c0c05590748500303040000b0040c0031000d55100741010000250380b0040c1c840754043d2060b008214060f68215100c0168a40207244070716003225000105910079840c41c3d001c4041c1e80c240b154a00700c184035034204201104429004944624240c20504665a8001501000d0424039032018850a505080001d0440c000e6a25404040c040011291812035002ca0706a200342c0d0f2040004805036254000e00c81100f844200040c00084425240c0010900a0001d400c0c1c014202c0c40c003000309002a90303962400e1301f2104400160181b400c007030220640c418001c03594841d03150f0404100700c4560090650303503510082d01160078070500042c000b514030b10500d21500025080000c0310459652484421100b1041e900b185001544e0500420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 580198471 1250 580197221 580197269
    0xb18070216090e28050105100e18100b040603020d0614070f09090506061e0a030b27040c081203060a06110705130f110a08100e0103230115 61
    0x184a110301c8070001e01c4d88001c82d441a941004a50809104a00700c1c502010001039007400f032184500c00c8480d0300c2d50481c0c1381c00a8401079103c06005812a1021202d0034410381e00001009405042c8a0b0f20218540d510040454028030094101135009150980e84000380100c0d60052040120198455240f5a540718002c0346c003500407174500d0700003401ca20410050301c41907820181d00540000c01141c0340100c01e840c100e2444003100d440c400380d2000420040c04240e0076124030001e0309400d0b1074041d0802e031030400411510703030001c0300c000b00e6a0880011900b4002c50129a6014246010469044060101e08540c143e0400c03615584504502d083c00304885105064011070300d80f00000a10a1504001c100100e001052141041c0c0c540c0d11000800c944405005820303081c1d1694607003d540e011900d0340101524001000350349960300c004002c21944241d040c140b070450380c20500f01d45600500343c090b400e00d124a000c190450350308042800b58203440090406044645161010307250351801c044803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 580199721 1250 580198471 580198481
    0x70b0a05090d091a03071403040f03020628050414030c070f050111030a08091204060507060f020313031202211602010e0727180b01081f0b1807021609 66
    0x31a1111613804000745158020034040d640110150401c0c0c0700c81c0307554483c00c09507034100320303403c1d2920b548920b8010141901070042d190400d03a60351481d0740308083c1031506021031f040c04c050703010440d87d40c40c001418030800d41d1a0107400001d130019240d54003442101c090f6184040c0c00780408100030010b00142541c0901c0703a085250420602540c00d10070491010383d00c220005000300c507075000f1a42c000c56182c0c0f0200041c80502550745074141c0325060340c1030900850b40032a01c08229140704006121fa080340044012034020350602e8024880c0c0700c68841d0b28080d0041d48144449070100300141ca000c11100b181d11840b60030718040d0700c102d6980c0c89108900b079030103006c01c210700b41d0401c0c0300500c070701d6540c034400c21541c00002c0940d03820051025100303404c50307e8808004c2d41640149080070100901c40318010b004103643d500a000503054050341507031a401681800c5842556032400a0880e29803134049841d41407100e0303144081e882c1020000e034440343c0c010050b01c05105800000720f2310280604c15 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 580200971 1250 580199721 580199729
    0x10c091a1204080304030903020a0b070302070905220804090f0603200609040e070b04031109070e060d0c03140103030807020f15070e010203040803030a1e1a1302070b0a05090d09 78
    0x1007001035032101d4607500501e07840940306404102003114044096240d0759509002841c40d00c61155403103d10f81402800c00041d41c0291640a0600c030500150356150141070381d40c8501d555540601c06c4d02c40c607200311203100716030203600c285082080b180840da20b00d60000d02202e010341c401e101458203c040040d00882d15402c0300c0c0d03019000f802004214101580010300c0c1600d1201200e0035603031a070304201d0803600281e0085411300020003a000a50800c0d140440d0015885e0801f8a945190070000032143d00039078030710070540c43d9a42d60030007409100e600104050700400744445000c1d40c580c10300030000d10007103500703d0162244203c9030000c80b500041a80d500100e10142d2402c64541e0130045903030400c510f48242c1144024000031807241d83c02d01c0218000d021035000007404895400300c6220000041d490000e40520304110700c03040114410400002d81c1c01103440008460b120158200240107040c000b401c10890f8108000d400e46840e4012801b8404010888401710070034802199800c0d06800303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 580202221 1250 580200971 580200997
    0xe01060513210b0601120207050705011b0507060e040b2205060609060313030c0209180705040203070219240b1e13050919121d03070b070212010c091a 66
    0x141d001040d583c41040c2d802a2051605110ba0706001070950186c1e00a441d0070303510360b000710101f00001d41c2c210400900d050001c603504000c2c1c030902e41f82e007612101c0d40d03c00e903011f0100c0c010f8101d007140d680340c0c001d42c0200c90040c0b44000e106110104d0f62501c002000c0c10b03201840c034180c041182d924103031003500d00700700008095515583e41c851143d03440e02c0b00d0140440078800d140702c07100010394415007400d2180f030002451040b01c04c2440c0241e40b030240e4a5008601843c41041446040c0b176010494182c14801c412000300340d07501610308030329034070022a007505240a00c0729200400310b000e50403e040b0b520b0f040391015a160002071440b903802540614599001482e0480d0000d01581d607008185d1120440060741c4804005e502d000c90454150394007102e800704107002c4407801d190040500401811107980d102e11000c1c86038042a81c65296000701141c1d0800421000d04540c0c0d0a07040841d041c1d00d4000074480d1000100e0040d103081d48038020304180511402000000c0c0b125070040c3d40300300d04091 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 580203471 1250 580202221 580202279
    0x6010201110705030712051312020402042d090b18041a0705090405010f051c060902060721030605030c120a05150421020c04020309010f11091002060903071b0e01060513 74
    0x100c4000c1c0d1642c00c09d10f049801540a210008111a40c2d0b14000c1c4040301c011021060401d5015117072190b011a5002085654541800c03c0e2190700c070140d42441c104422141c10000380c846080c840e0301c007034102000c0c012001d030034400c01c09803942c024003516404401303950510142e602c45010004104040c005d554004240000f40b000c118010801c444c00280210400180182c20780c0100c2c40c664044501074508030040c000c0c104181d440514504c504039018907082110310b0a00c00000d840d552030b111051700c20300e100c0c0402003a52005110500b00b0030381c403d04a4ac44914101000d4000313803403c4a042e5100e041c408844824900010300c8010b2000c103d60151806109910403c0000d400c082d1031040c07199070f92444544166200d00c18041d2100301e10700c1c5075440d0120041000041404800741400b19001132083c0710301101c001090b141c00e540d002d81e402a18080e03800d0002d90200160f4000940e469202c0000210380b42c01c24010607820354480d416103200c1d40c807075401c400210b205000200c111620a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 580204721 1250 580203471 580203479
    0xc080402130b010c2001080609040210120f020c062208040e0c090405040f061104050d0821040b0103050709020f0d0c120c050c0c01020c1305060102011107050307120513 74
    0x15481602d801c2414104981001001d4403403244981070741c000358004101041c01c5011303660308a81036681c001350848000300327a0f00d40b69000c03611140400c12445d0501141e205070320b000c405641c00c095460750303441200315102c0051a4249660b040d003030f070740e050495000b07a110003d403180106559400075040301ca20780c5450300d0700115a0003140024500c8248120500c210344540d6a980a03181c0070b203028001804050b801030828104440011b5280e5a01480c10042008127840b03480a2290407034001130a00d4585600c0040342a4030101d0388091949181d16408102c10403400440c041d040e130b40102c04480304552034040c540c04071f204180d4000004501800003800c14405502304010203c020700d041c070582209400100709a910903ca14000301d0303c041101121340340100b0510360805400d01c01400e00101050100f480d5001314410440d00341c0e12440040d600364000d412603100002aa0949a51015181000350310b039000600100e404070002510301c240b003403280e401c0e955608080c806072102c10b464 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 580205971 1250 580204721 580204759
    0x3070c0f02010c06050f0709140307060804021203030403020a12020613080714060a091a220f08030126010e0709020d2c060c041809061803050d0c080402 67
    0x10340104904004441200c0800900a4091507024004e40d003441070041c240700c0703c040e10100654004601485411040c09625500003648004030f03030103400e2900190b01d80780041664070b090040620480e100001c1400101036002030015080d80c001c0c02522102c44000504a8a5000640f15500c040a04181036404940642d00074a5814400c4c1002e502551992003102d007014012940d140b001d542e00d101000500c040481841d10b0305400045450280c03400c0c2c0684960000701507030500c00e100d51000f5103000c01150809010071107400802ea99103e40e510091803900c4600f00c3d2402a00321b1441c5100302c8000014090b15990040f0343c4060200582080ca200000303410808480c0c081545540305050401c80c541041c550000b0f1340481140c480f45104074940c42d04001400c0c80f0201107082000300001407990440300e00103035800e8070200d050900ca04140d80500301c4a1a6050034a644459003c201a00400245004012441c0030322020301c0d81c6009646196040702c019402c030020703804884180103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 580207221 1250 580205971 580205993
    0xc150809060f0c0c010e1f0e07061b170a1409031c020a170a200309061309020a030915060b031609081203090106090506030a1101140d05010e060603070c 67
    0x800c0441c82c1440d16580c130540c250780c1241003c0c480b50f00035403429004140c10307100400d103101a00c003081c40380348a11020b0300e6503109648505810012200c040c401078010300407650030801d806c03000300c480201c42e403264800c6a40c08449500081818600514481914482034501c80000240030b40708246183d01c00900407065110300d0780071406004041c50024412101d0300b182e203c60075800c207484454000000d41210802c0d086078007282c001801d1506031240000407100070722000d03101c4686500c103070398003c4460305454009024480c000701e40c0388003490b40b40c0d00c102e01c4180250301a0654120303c180e4201260301178090455250030800c0050710010250080b078503860454640018850303510500c01d0b04113141e0740c110515541000050020040c024010f45c009081c2e184400c012900704000000ea4071000d42900501c0d00e075071130b2440211a07001d032442466031600d01741141d90714034541181d100104000d001d4201d16003003003000304000f42000c070b050340c1c881c4c0071b961101841e20000e512000709000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 580208471 1250 580207221 580207231
    0xd0201030605220c08060d170706051801150b0708030c09040e15250305070e0a1512020405011715130203010608070c0c0605160f0c150809060f 63
    0x10303280d00c00001c06440348810507590011000301d10401040c1d00e803c51080e030301c400781c2c041c0c100440b000c28800c9603a01c94001030202c0e60300c0501c0100441d4030140358441ca008004d0080c000a1610f0f0400124064401401c0b43c030010010080021720600c01210103940c1d100e02030800c3d142030500070100081d000400840e004100504454100504000014141d44414010790141d811019844140220304608285c001100c1c1b00c0c3d80902410b114841107124030f089008008041d228400301d1800c030f025006104002201501c840141902d403172240c010200101c9948002a0f0071401026111515200365020745005035111881e260144426081001c40a04038140101c1c1c201000303202030f07840040044c900308120b100940c980d8504640504003043c000c2040c0c00f8007007805800c600080d404500041601d44da406c0c00e5880d40c4041c0300044170094584030041440b400c461458060000c50a048030844070000514110b00d200c0c180119190070081d24201032a51120011070760b80030310390b58416484 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 580209721 1250 580208471 580208477
    0x60510051c0204030b041a040312110c01090f031d060702040c0e0315091605060712050d0c0c020f0906090a0c0c0f0c08010c021f0902010c08030f010302040615020a1101020c0603010906141c020d0201 87
    0x200030342e0201e1900b10b80c2d80100c112608003c0fc14550300709030708040f120310103035a5160180404014180070802074032617000000c0c03166507642c00c0e0811041c010003100c00c404001400700e410035542142070b980406030560f15111703184150f401040f4040c2d400da074003e0640c2c00241c001800c151a56490564010008058a003486003e01040c05840318601c61503240c0181d41d641c901e071018603801440800d80c03204c502c0c0d5014441e05c40030403810b52103509000307821001c44000000d44c0c0c66058011180034040100c0281000c2c841304400e0f05000003c4e42c81c0e016211400000c00041a50b10b40a030707500e00b40e082140403e44d5014441407004019984034071141801810010303082d961aa0b40e0003441d5100715010850800004014401d5040504c00c5c0340140030082850b003494000310790040d654032120b0308000c0c51a03e117011381c60034a900c20300800380c00e080042c100300c1c2ca03540c558500c0d5001d001d960007140c5c815401071b0041081807a12001210140904980c08075400d815a02808641481c1070b20607818 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 580210971 1250 580209721 580209727
    0x40513022101110307021b0409050606130209041109030733140318070f0b040e04060e030f1902031606020a140c010b010e04060510051c0204030b041a04031211 70
    0xf540c0040e02c0254030594150b0702400341e18140040080d003140545012034022890860f903e0000b4000045440d00403d00b210781085134003a0180701e201a00c42c4480054000c4d00300b43c009100b9040001c060245400c00701d0a9440c441c0d03d880c103c1c001c50300505002d03004c55400000034510003108130014200401a4078001d0b803c01510040110a58030655450f4400d000c0c502010710824030034407468018050080034080020724000c0d5004041c0983c0c01a403c0b000494000318003040300d15800450ba001054080e6502c0340500f0141440b0b68000714001160400c000d04010700740361002c001c4483c510b007042d1030003408040310303207400e80290094801c5005101d04074861108143d4413101030200f090a0b007002252070000d080005220036130b02c01c2c046001d40d04250701404580d440480300002c041d12403600e1600c42c103490540705000d01c40b902a40080c1e600c0054084140884180d0382032140d0302030b240d034204204070360114403111602142c000e000500c0c0c04000c0c00c00340d06660070420001e00405c01181c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 580212221 1250 580210971 580210991
    0x306060604050d0309120b01080d08010b1e1c150807060f0c0203010e06010b0c0114010b09060304150905030301050108131a060f090c04061e0905151207020c040513022101 75
    0x1b1a1048100142c1c0d91034050001001104010410481203501c1da1a080f103555140c410b1625460184048400425910014181c810b69100007540c1902e00f003040b00040c0501d105410307000402d0009245148102048004684a140000e4000c100c1303206540e040503407a01108116641e40382807404a82c55500c4100c1c89c40041e40411400b4041c000c281840799031014003d50050845c5e440194510000700d030b00004102082c0001c05039001ca000681e03c441d0381c0e82d994a00b10704d250401410010b22a441d00d00c004052000000256058460a0321481ca05071901c2c1d11064008202c2e035401001c0c0411503000c3c0700c0b0030011101c2d90707030045400303049009211a02400601e14800455036a9004080800c0800c402ea6001d450881c8000304411a002c80c003c3e011801040312000e0700816024890b0761004544060860701101c1311584605140d824605040ca0000d4907608819803942c45141003602182e001d540c0000c45503074403a03004103043d00000d80d402284103010410988012655078400c3da480b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 580213471 1250 580212221 580212239
    0x9190f110310080f060105060d290f01090e0a02030c040f0f0e071b020d0303061502010f050708010e010611030403082206030203060604060c020f0604030f031e1407140f0106050f0306060604050d0309 87
    0x12681c10001000d02020002d95041c0f04481d542f50001ca070400032003c1041080540200744a0b410000c4054090380c3c951750b003840d240e107600c507642c0242c00000909900043e20841610b6400039941103200c1030010352500c0504807021800840c0088070314540a8001006240c0040400c814030700c20b040c0455400c0d621072044280d20850300400025075101e40091a040300a8410664130410318107150040354100174035400289014007800041c044d140203552590801042a10300a40e400700030a507840318000c01f2a21903503411403003000b444101d490b010030b8060290080e6440703501c01810403424a4a031010841d28a0740c0b4040c1039800c041c01081d04480c58607208002c001070350040240d00e10070076442c500204030304041504041090040078060405d0756200c8070720b82c00040800c4000340c94034864100012403080c1c05030100c216100e00c0c01000114001904540e0403a02c0031078811400800300420b1540b143d100321803603544080100030a00451924621044400e0b00a01e010781000e51164021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 580214721 1250 580213471 580213511
    0x50c270409150b041508030a0f0c2108090601061b24020903100513110f03070603050117120403020603130b0703050f0606070209190f110310080f060105060d 69
    0x111404076129554120030b41014062030201080540c602110940b415040a8036401044648400c09c90283e040c0301407039101c1e04413402c4041d0004403007410b00c12051911141110701105900118580c0c00014003101000319105048400d1511001124801156510145c000e000300445901a00c81902c00984070040313240081c02c00c0c81c05006075070f04c1020040501c1c0c00070b0080603200c40c5050404100b034038410404944245c951044640d16201c280c0c40024a44201c81051903070035100b5400001000d40e0b26030002c1d030482d195600b052903071a0345410000e449118450302007840450422003000182807050045601201002c582c1440d2003047da10755011010568507080000d856106100c0d00c4403080b90b003e60042d0f0100c690038504507043d40424070b6500024136a082d2103a1914001002000c1c03900101a07041c0300d20301c20091944600b0996820b5001030301e83e072003074241d07a5002040c00390002a0140031800d240005240e541e10348010030189a10001404042c1d9807180d4983d04440003021369 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 580215827 1106 580214721 580214753
    0x160801051909110712031401051512090c0a0b0702030d0518040b130603050123071d060706090302010f05091c050711150d050c270409 59
    0x3c1c0d4564068510080c2c000020410f24070122613055000600c41015903044540036602d800c01e004800704d001c40c544c0c400b10000c20843d0040710744041c041da8446081d00848000301c90700c4001c101101e01c282d01452540c900484c01c0c0341103203401d10092007041d0103803800030f04241c100040c0c007000000d080d1840d409540d0f10030104029483e100e4205812020190b004e102d21586c900e481070003061003a100e01d00980f2920383d00d20f84261210321583c06500151745070000402604c6044c007a8500c070514003940000100300c5800011194000d000c1d805019400000d201e4469820b00c0082e110020b215000300d40140f1030321300e4420035120f9119001651880e00c0b503100c160b10301c2d1411090304a0b4030740981c008010300e82d1562800301003005218510606500380200d48400300c05081c0c5004e840c9c240b070400c0890501021000c1407103141001405c40c010004105000c00e40c0301d0560300408005 = true := by decide +kernel

theorem cover : BRFrame.Cov 580035971 580215827 := by
  have h0 := BRFrame.cov_init 580035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 580035971 ≤ n) (h2 : n < 580215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
