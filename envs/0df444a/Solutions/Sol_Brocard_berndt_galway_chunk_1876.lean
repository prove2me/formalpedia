-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1876
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:59:50.565305+00:00
-- url     : https://prove2.me/submissions/46535b8c-6f2f-444f-9331-239728175747

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 337230215 ≤ n < 337410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 337231465 1250 337230215 337230227
    0x4080f03090127080306090601030e060106090e010b030124030b190512010b0105070b1b04060f0f05040501050a08060a0905091e0c10030518010c020d0806060708040302010c08130303 80
    0x42e4448104518465003030005a0728030f00c0c51840010404482400461180d080180f036154110b030050601242040c940203800740b030400240c0c002d1000a00c140c404121002c00d0404640c09010b41900c505d29540c180700e40d00e036030300c10f01e0f4000e20f1410750014881c0076550b10076403060341280802080501a50000e0f031390300b55a01024000d0314881c203150318028180c0481407185c42089101a1035142c103004c41512090200f14000304022402030840c00c090703d15801e84002000600100d440300712404150300401009850058052424050104010702550381c2000c00da410740701c01440c2035007650382c900c401310b8201070b11070b40010000341c285000d102900c0e401040d0f030501c41041d164482004014404000da854405030805604011401409110070b88250449a80800d4450100c030100d0021401c060868540350381510058011036034a002c07155000c003025070001000c8840a09009040c6c83d0f248042c4202d200090510042214540820070a44180c0b1381d01d514450b40040150765a050240030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 337232715 1250 337231465 337231481
    0x90209030709061202010c061103070c2003030409020d1b091d042d0209040507170a080f16080c010f29150c0313060e0a0312030504080f030901 63
    0x400d001d8800e02241c0c2000794456041211000140c0c0c080c80159600103491035495210705840d182d4440026813030700c00b180b4001754024142940c0b6009045000c2c10105c002c2c2c0c440f540c000d09041d110b68240d0002d55000030549095500549005a403000302caa0980d00400c0c1d8114440103400010160007030302c3e80c00002000072101e00840d4a508401403880e44803480204440007810144c40b98480701b07032024a0324251000286200140c00240e000f9000540c00d034004480440750380c2c0c800001800948094040c000410300103000522403140c00703544071840c6000b09003402c1d12001740803d50000c907003034110b603e403045900602d52560700d81c001030b5054007902103490304800e00c508280a407100c07030346c4c0c880d03150b210b003058080c155580107084400c00107203d03c44405c40c18420002d00260380070085c2800101400001401004011842c0503000b610044001d02403c0c81210801c4c81040030451001080d84440b007146030001c1c080d501d900d401c3e0310358001c2c1440305401007408410007414003015800724038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 337233965 1250 337232715 337232719
    0xa0c0911031003060906060302130b100f0206180a021023090d030c080405060f0c0d021609230c03070801080106050f0d080408030708032418060316090209 68
    0x108084410141162901c001d0710b41228007000c8960030004111030354808444079109203008102c4503940c0e00084c3d542c070844000c3d541d04075603440c18454545403122041845000900f040d00c01c0c0000c0c950040e445020041c0310080c441105404128424030901c0000010341d8000d008580e40c10142c403005124284605421072190300c614500c0400036404025540a848001c1107140d00c5001580d040b15035014038001110100800c1c000401d43d80d5580d00a000c10710944031600d42c982c1052030500e0701d450807006500c415500021400319024542c42040b900b500c042d842c01041f01c6045e030303016800109082440301118070011003404842020368000318012540c82d600d00c1c480341d80f01c110080c201c1d4120f10640758401103c1c0e0904c5000d04003401035200700c602070044542891756501c0640c3c19684110000c44005000104004c80303085020a62a484280115044600485003010496294070070154800907a00c0d5800100304e40c0e01000f881c03c2440c0d803084445031a035a1043d0103070194003c100c03064 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 337235215 1250 337233965 337233971
    0x509180105010e0103020604030224030a09060b06040e0c030c0903011b030507021f0b01020109150c0f03020f0d0e1f0c020c060c1b24030708090c0a0302090c0c0a0c09 73
    0x189080090f00c800e0705894004048914051460b400c10580f00f005210200084412418001059098002451180b0600c0401044a00d101d1505104941e0303500e108034454103041c8810f00481840c2500658011304c801c00721070356902c0742c1d031803200036003e07400350943d140d03081016128071940e0f51001c1048050081c0c400f400180c41e18007040e80c5540044010714846d181e080c001c0ea074559201e80284041c0c0c5c0c010f000019081500b610744540003509280c101d05110b803955005541242e001d08081104a00c900d421070030010b000d000801d00f481121544052a5241c40105907105024041d80860303091012015200c60500300d242c031f016000000e04000135010350b00304035030b103400d05030b0894001d280b40740050840448899040600702c48510131580c0c101c0105200c0c0c00c079a25500c038807007401c51420780c10b1948914003800c004000000080402c032035500168215255910b03902c4400068a0381112110b116527111144605d203401030301841581c62049290603414089881680c8060340d070021418 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 337236465 1250 337235215 337235219
    0xd1506030f020f0d0f031803080f0c070807140d0204111204032c04090c0f090515040207051c0e04021602030c03010e06150411030a02130611030702011107050918010501 74
    0x200440c80a440078003080b16285c00a070009203c0c00380661684000110f1843c03450b140d46941419070844c504c00040103000040320440400c04100290060070002c0050903072500b0a10000ca8207810602114041c40c814022181150758075008070440c8281e540213503868004aa100c070340c04010680c0c00368003090342e074400d0302203010140c0c1c0e0000808002a29450524012005101c0141a40003040e59515507850012400d2402f40d4104402020000340c08500c07414007140d81c0c1e141c0102c00491a2240d07104003e041c00040000c20000b1889503200150041c0324404034081d10002d180d0340c0f199034000c0c8000390400c01c111004485402e0a80294100c0d078095411405140c01c80d03498804400c0795500a100141da00c0044a07014030a07418060408030394600403148011143d04103489001001340c0200c1e040700765a2681c5203010050080340f500c580e402109a440b15104d2050721006410040858030122101c0300403c015801081301501d140e01c0c03481e0101d0020303810040c018010001d135003080c1c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 337237715 1250 337236465 337236469
    0x30c03080609060a0b031306090305040602060c0702090106050901030b0a06020a3503130501060f080f011b0e06040f1d010803070b0114030109051c121107020d1506030f020f 76
    0x3510b031007032201801342582c460a0000010490700010200504d00042610f1070000a0300c4e4010400314038401d0b168030703403110304000019041400082c03408064507002d002000150340d5001000d41141c2c02030804aa4501611b80128040c0a1200205400174000c0800207001507000800d015040e00a625140d05c5c00742100414040108801e02d2000040c0c0040c02c20200f00f0402005581200e90ba1144c4c0e190001c551f074595094400320350151a100005510410210509010413000c0007424002040707000c588652400403092110383c00c404100c2c1c204039840d6139854100848001d4030714600d103d00413664400c100c0c0130001c40b034059a07060000b884000210103900000380c6d42056400030700d40149070309051000c0f03131500b0503503035865041d0b40781d07408500403820074000019034510002c07094801148618000d01054078000c0c04281c03887c0b40018440c20101d003041914883c0f60704845045425026040001407030207040c1882128610745a00001003044650403400d44034425104241e26100d0081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 337238965 1250 337237715 337237729
    0x6040305100c0504032108090a03080123150d0e070e0105130f020705010906050c0408190305040806011202180f060f0321031909050d08040303020d09030c030806 71
    0x40000c04940c020107404a07401615008003200700300c14036006040c555079459000c08104503080300d040d0340020140c4d903809650300244031944080000002c00100385659030040000700148140310085d0f14046450306d82c0082e030405000481c0303000703000500c50b0b286c11644804503801130510044540ca844644040c1ca840880c080c4119080d84803901040c0c2c2c640802c4c4442c050451000c042e20316911481551510003d101500c0075500403000042d40c217065260580480e1005000b034030f051081480104458031002821005010740d88001100300741c0c26280c265010f0265820011240c01088000b20b1110040c2603041b001500840704104000c601c600c003551644015605055140b080b840080e4481c140450b80c01180304c0043d003115070001801d0601111004a011103040c600b0f00041442142c0e4100c00016100600e844010401c2d2942680c03440e680e60048108002405030b003000003400c1c18041d6058580222088800f400083c46604d4020254000c0c0c05e02140031840c880c0200b480d906100c0307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 337240215 1250 337238965 337238969
    0x3180111030a0807021e01050402090705090d030c0503090607120207092306031002030703020a030501050f0105090d15050f010519270f09030c0b0c030601020c1c0b0f150604 76
    0x10061464151002c80c12a1568002011003040d4031492121b84542c0e0310b520100720a9000f000000181803c0c60b00c10850f104030041c0c0407204020040c0106665595000110f08d042c6505082441c0c13544042d01d0321500307600800c2076450b44101c0116410041c810345c415405031040d05a403e803255203881d0001c500c2190400c210718101c80205200708510341c074040700400d800c280014100c0d28012441800041a40e00c00c0b18844006500428045405130301070143c94050701040315000f18042e94580001d00c1409410010752041c0031400486052003400d00c01005880c411150502591410160104c5120000c1c030481d409000203483e030901d1000680815426030f03c80c0380c2100341d584035990854000390021051000801d684840b420801c20241c4901600342d4441d40700e600404a0703500300079600200c01819002d0741c040400401c02c0d6030303a0200e10b48030144021101c8262086a815038070802d42c0c0300039030003828015642c052200710301802d04028450b030821440364098a2442c800c0c0a1030340694 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 337241465 1250 337240215 337240247
    0x70b16020a030e01020312091c020f10050714071113020703170603030408100f15080607030213030f2a050a0308030405011e0b03060a0606170a0f0c02031801 69
    0x4440720019210319404101d03410148116401e100c031011240700c908005035080c103070aa005807030841c1540f05455140700030079002c3c00903102404c0d0200c540358648c03180021a1000d1035079800019080c0e80607000d001e00e01002c440e24551140040d1601006880d20800243d104620115010076a00c0c3d1034021510502c0e8140e4443c205c4454404030fa101014002e814154107000034080810640c03c100308200c400301009001007a0601410a18004c9030700d00c101c21001d11071301403c01d221603e0009503168201d02185001641c80500000030491110755810041400d01203080c070100b80300c000703030b5040c0303207894680c4c103085104206659030200031940c0d10a068020400410800220351080d002cbc580c0940074000214602402c0048821818540d08035151002d64442600115050410507103604c104a40d80400c981410b000e005080c0382c10b0980240c80300c0b100320f4002011050310380c0112510700d004000900c07102045410203034607600f046540c00030403214144c0c410340940c800e10381011602c0791 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 337242715 1250 337241465 337241473
    0x3080c0903300d1a190b0702030c1f031409070303030b03011d0303042906040c020709061403010510060f1b08040906060305060f1f020a08040b070b1602 67
    0x3118110401e00680c140c0b1144559403102c0c1c2480000416001000c1d4101c0040c0000f03807100040b0b80d400c90315440d65402600420041c5a0000180440c81441055817030130440a83c8803145480020b01e481c10304484190000c40743c01d054110041c00e080c0c1c1004221260300e05022062003e04521401c0c40225412000d90b48245010000311f40650b21042c110301e000360010444020360440f401016496007059000d07648000b040205000c17602c0348220014440031003200d41146401003c283c100c501400d030368070841e5a00c0000d9041402085200010b111801003880341607954801c0c6d001080556210314025404d01001845661140d2040001d40f4240c0d150b00c40217055440b01211900c16046035032131401504070000011401402c05031004250000020601d1401c0460080c1a60f03c05030607280200c03c4040120b0030340d55900340c10000c4000241444c43c81943d4400200d1410756019406410780d80e0010f0f0101d030400010005108290007001b090009407603403101c1c000040703401c00c003980051708 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 337243965 1250 337242715 337242733
    0x131a01030c020601090f090b010e0603061003050c09060102210d270b06060d0219030e062e0b03130501110412110d0203010c090302011413151b05070303080c0903 71
    0x7660307404038504220485000400c8101692a8442382e0340070b070014610000d0036820407206140402c10305038818680c51068000524507030341c541d83da4900d60100d80c455902030340020000e9208001c0d02c0400c0019500d0400d0104115642e04643c2c2d02a14095802d1402c3c02081c418103c0c5030681e400d804601d00003e0315050605890b10460008094003240d80b1007410001c0825448507030000d0610100318100791450b00112120207411221030802c0c480740c5400c20820442c1044100c100421104440a40c0c00403003000001c0b8201d84000380d801c50703400100301100780b2000748400d00070828120b00c0340c1c00800c00c81c2e03070044040c03190b4002c41c42400206150501c038900083c4013800007119048019016a00519140d40043d0079141c80c3c044020000f55520300070419580c4c00005000500b030040440d0346031140c0380000b071281e040140030700a4100204000241034620039829104544248843e08150019600e400741e01d414003440290b00150400c0007140150f040c1404444002c80001c000740003c030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 337245215 1250 337243965 337243979
    0x60108031e030402010e090408251e031b14070f08070b1809010315110307050f07170406020601060f08150108040222020406020613051e030702131a01030c020601 71
    0x9480100f04904114460500c000d040d2100c15029000d103110781c152540365905079011075501175508070080e20031016441d036040816151200d101203200d0150032013444840d00c0c102910004144124009200403252050050100e1078265491108598060700c200350b907a8210320305818064080e811283e00200c0c010091500c00e0801000143d92403083d610040c5000b1f0009201000241c1c026203ca405112007440c0c4076900b4425803107246044070045007507080c9544000c06a005044501009220004043c401e0003248200f00e0f003162001c40ea241d079501d450380d000070340310107081c840c10700070405003400e106078940a0281e082c8950349038803002c0f010348140c1004440c004406441603070460704020707450402d610254584042c417000a0005603466150210092910200404140d0050070030400d420018101081481c0d410607c1c0001900301040e0308e103414210720502d00002e600054056155066805682003c19500c50074941c0b40d540d8002d248c015400c0e900c4005610b00140c01c1b40c00140601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 337246465 1250 337245215 337245217
    0x13060305070f1e0e01060f0c230d0305220c0b0301120212060603060610180801150f05130507091805340305070504050409060212011a0711010314070306050102060108031e 75
    0x4c0582d0b40b070007580c1c407034840c1c96510000e8a0204071a025049c1c6040740c42c1d58030010005460550100e01c0d080019160440c070104013424102260fa4080e115008107509100e001c6082c80040c10045058903525650b598100803464500803040380030350b10341c030228049010041021031144030060041c0156940319030402211807030020340072050042c510010240566154050300240035040300002d550711000700e42c0d46510720b050b801000c1032000e03c50144901d880d110740d080d641c480300b11f40100329511103030410f50b0200041e8002e100c040343d002c0c0b030b00810080581c101501600d03000b803104109603008542d038880c481507100300c0c0c1e10908080c841d0700100c81c4031382d00940d48282107141403801c01c1d1322100010103480083c1015140b882e00883c14171011204038003040d0040145081e00f016400d20b00d00c680e01c1c0d6000f8540d02a01c42032501040221036402600030422040002d180c0004e40d1803c0c581c081d00600c5180142c90044c42000e00108458400204440440080d80508041c000e0100710307140c19 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 337247715 1250 337246465 337246487
    0x2603090603040f0b130507080c01140a0201180b040b180a020f04181b0509010312030c03090b0103050f010c0305061c0c081e0d0207030206040513060305070f1e0e0106 73
    0x407000d8411002010440c803011285c0141103071642c0110221250502d580760889a800910240d00050080350691703030401844500b04c115111080c1d15070241c0381042c0d00409101c00c010030100401c1080004100440040501c114440e0020b074403a919025508404118284000c0c1d410741c4c04400998090f1501807600300d200d210007800031520625188483d200860840001c541d0b41081410f41c01841c0b1096201a004d054155070f210313455803441e1240b90300c540046003040c050642d80d05914520b980700c0d07000006240c0e04240080100c0d690b034908603648003010110b42103d54a81600d03458098801c1c014540200001002500141da51650000041070003400071582c03803240420000d641c680074004564400341c10000e00350442d50410403942064800e84944c070454000c51021310040e55400251000d480058510f1108000158140f10040000341c00c00381c074a00ca016400514110f80c040d03100242c82d820480c0b04a05da03030710020229004400e0241440d841b000000620a0301c4c459010001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 337248965 1250 337247715 337247723
    0x30305040204151e120819030f0603081b0601181e151703030403120e010e0703060c03111908040201022404020909390307090204260309060304 63
    0x20340c400580c10030b001600f03140c1d00c1480715400107070f20007040c00c01200c00b00c1d0007440b94644012a02403203643c0c6400d030b48980710302c4158004003440d02a040c0c500c03030b51014104401041c07040040c0c54480c02c04000f250002032800c2464210000301d4103103090003042c0e40707040344c6400380c3c04c041c0d13140c40c1e4807104040c040700620704000301c03c1e0142c4c80d400070302c043c001d40100404800c980510b0504000c0c10300001c1901d01c04169855000304140400281d0154082860316804000012112034403101c050141c1650559600184507100020007809155400741461040c581c4042211102a80108101d802456020040d0040c910181210203024500302580070b0310502c19120700210110070784552440f402d0f6900c0c04003030003008100450408208454010030903400600928010050380800710034111a8024038450203644d00240c4d002d64210b40700c20040043c03d40700455114111480207400c141318071508512000206103114078458483d020f82c141400103140b83c0219041840702a03440504116 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 337250215 1250 337248965 337248971
    0xc111c12060f0503070f1a0d0912020f0613110f040605061207030b060304210210020c030c010b0a08030711150304060c020d08061c0f08040f0f0b09010507030305040204 74
    0x180394120309100d1600940340c40d80354444020b0420040c90701e07045140d0060300e045500b1038070500000043d01005014a40d010041c1c3e44d0301d4448500ba4000390424190080ca407418682128641d6038000c60300e0200d00c0c0d1000c0448410303985440429210f0b0803080005003200c1034102c801c44850415004c18220090007600210300284c0d0b64001c20030b1a0710801002081c10214014403202c16890b00840780c3c002d0701210602c0c15030420751206106011041903448425504981800e4060300070311103007000c807040704811511180034080c0c55880f5880130102e402213519008550396a481c1c50502c42c0241e484810003582010041d54544c0c0d00d107214880c202c0e13072000700e84100700310a0240700d000b14030031846488041409403988601a150141c2240c1d401c041c4000807080201688a090b9102031180607403255824216490608080c1d080314841d0181c010000040c020401d040401c1c01d8008988500758a8840c41e0f40d42d00c20082d01e4040e00321503a001910802040c00030a209800c8035410600041c000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 337251465 1250 337250215 337250237
    0x8160e04151e0311030610270509100b062109070b0403030f02100603020609060912030a0804121701180b0406080706110309030705010c0519050c040c111c 68
    0x80d0514103004696a20180010b8040c01008207824000124140660080c002404c01d00900301500300680a402143c030100e00741c500743ca4595005400100e002d480c02040360382420442c403138070f58021042e481002070030228025128188603086680c1503060b82100c2d185061814484068214081c080224138840c0040200310110644020301c0198401d444145c0305288185010741051040c03440d00751240e00c1c00c00100b000d070300c2d02d0341102c0000c401200d100d5501c66010001401e002c1d04005c10450520010a80120290300516114040da0085052900c003221b040001c450140b80d20218034010500140108034201034889040720740b01c0503050102d00d100c480008a0121915039200441c698080724041043d41d801164030034003a00c01a001d91320b0011882c001c20358030f484a2055504006005519006001091080c0001c0c003402d40011010800c4504000da40c4100481c44613200d01d280001813045103014421050108404402130701460001c54640c010402c40308541109002550f4a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 337252715 1250 337251465 337251479
    0x70609260f2b1b030809010204030804030b070912050c041806020315040c03021602090402040b030a0302030901080c0909040f06020f0d0510080304050a090509100c08060108160e0415 80
    0x20000042041c0d00190280618540d04a5444035070b0002d03580c14420b0441c1c0d4050b40d2058020104030309505814001141d40b69810424020301c15079201a2801e800400e000c410450742c40401c60094019660303000c01b007a20742001e8007101d458260028013541c46a4514291030800c1e820019080c0c111240380c64080d080c0d5240d01050740e1003244c40c000080941420314000345007510500d0382d080f0080c5011030506004d03004603040031140f228045c1c851504e40c8001000c56481c0e40000c001d10801406544d01901030303140181d81e9802015606010644010006400c5200c2c0025148001001400308070305441d10703103807142c80f425656002d440b1140c00304803102c00d41c0300b00401050b460001140c00141454806010701c080207003074018031007a07001000100016a103410300c034070a0721110200040c43c0c1d01e4441e1450324000c2c0b1a103020000724103000040c2c1005030024520780c0b0030102a2a0000c1310f03a10b8a4031029180c1c000c08400c00800e0801c4580211400c0a520290b000c0008001c0c81c59040d86a4107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 337253965 1250 337252715 337252723
    0x91523060d14010b13180908040612062408090c030d020a020108341107090c08060d021513051504080d0509060a03090203010f110c070609260f 63
    0x80c20180c01c0d07840d1007031000b80392107818080d8014402c0d24407060820305460f0f076036581070b02c0e18441e04050030a0341890307138010240740e40102c8009a118980e1592141d4401c4040d00315a01d485000310410314241c80080d0311001c2c0191106000d1400c100c02c111041c80900030313540c20202030314440c002d101c2c40758000c076151403c000600c800050f54008180c0c010852000405041d0020086030024080c0101c010151113101c0959481c24a148603140d030200003c1811034511003001e1200045100348200003d050805038000640c140385507a0303c01e00e03070391490107110040511b804000c3d003140800500d401c882c0c043e100135051502c0700d540c0b9980807503a10000600228004500140e100000103001c0204104c100001d1b074003618181440360803d107140e000150180215100c0704c0505849600b04001c6503020f41c491401240e0003601046041d01c400324407170305038002c4440c40030513120b803440100d10540a85c0c18442210399036104404c042d690070324007501c9450440420b202600ca08282c0fa030800c40248 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 337255215 1250 337253965 337253977
    0x309060807021f02031b071203050606070b101a07020102060705130e0103050d02010e0d020714040219020c010906020c03121602030f0303090c151e040f0303120609152306 75
    0x9040582c507070415540306c8024541010800c405608204981000140b021040a400c0c000500780002d250340c0e8007011071550b200d4aa4020202e8501c031041002c0c400442d01d401042d0f40091003144400401e16520704124821600043c1c056030114001a00861140008061030043c33102e040d00c8060f9036203480d0034000000c5c0c008403100c0e000300455403190b941c244203007024100550300521040d0014240a9124141405110719601c2c20140e009901c4e1103940446c1e68000100d81001e040c1c401441b4029282c480b02800340780080c0c5480c07800600c0910000301c00000210007800f80c2005d0740c85003201d08023076001d03603114821b030715012203081c0150750144803074031407100d0071006035070f603480c0203905142802403d002c001d1160494040e40c64564100200f5100040100c100c0c0020142e04104406054055070f408590355803d030754804002c140e44141d21000b990040b020501c00305031500f610100b0f4842d01c070120000048865810845450200c61094a030341c905103046c145800b180c400b0500c554410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 337256465 1250 337255215 337255273
    0x6320c0906070812060117040312090c080109020a0806091f0b0d0b0a140f0c030901060e10092f0a1103030124020708120a0e060304030206040c080604030906080702 72
    0x300700350b9442403c1d14000355100500b46002045e4561102d00240c0381d180140000c0c0400201c4842b02058084586c03001c0c2441c1d4108500da0306256550324664080c000702034089010340c0398400c001a00600018406005007250300142c11004e085490b04101d42e00840520811141c503001d00c0c4c181612001090306005008101112045c5001000321059580a0404120103030b4210104924010900e140c6900100a0001d01741e0704c2c0c0f030300034070300d07000d800759410681d4181c80040a1020f03545545030b80038111420b000b810301c0341c41c0049030340540b86907042600f000b0441503024001c0300900104000d01ca602061b050000c03175902008012844c50704240c01080b031000c95503c1c155104503200710b0940b0002c00398801030061900b0116010f8440054030750260007a1804a1640c10b140c2c011360080580c0310014082c16181e20309403d000355207180907941500c42c1145003401050303540c804540c3c14031540d0541c507540d90741494408100d5074500c1c000c15500071406080008400d590f100080c1b94421050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 337257715 1250 337256465 337256467
    0x2010909091a0a0e060c0a08040803190606020f10062312030d0207141605190503061f15020a030f21060f060f0e150c0607050706320c09060708 63
    0x8904050700d09070028000c10707081030007840072131403a03170b40701d13101390789c070640c02821a900c07071b2542c0400806a40d23084000110007070402c00c0101d16a44d002405000ca40d44140882d11488a0088001308460b07403800341000c85400525011b860081084008904082c05000c10795000c0d48226000e0840d0004202d0181d03668000030468180103049501280180c007000160a0b000034440b44144c11010324800d140c0250f100001c40c2c0742c40450550301c0070040402a05480d041c0c6819100c443e80c1c036010f01403000103034500c4000490001101000045c6c10881c54005020306c444a0f10180c0355a201584044200301c548451080c2d0040f9603800c5540202a0310700200c0d4081c10720039400350100442d00850b080100b40c83c5819800c40c0c3c0015130704d00f210320035107807405100c040703c010341440d11945080700c0382803091200340040725034480020310006000d00010050440c0344006400d0311410b091031810800d52011a40380f800350301000c01908910043c071403d2170651502d010504580006d0800d941d8810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 337258965 1250 337257715 337257731
    0x607020109020f0405010e070804020312041206060e010f030f0809180402040e030906090d0501090215180a030b1906030b070f09090c05160c090f0204090b090402010909091a0a 77
    0x14001060f405031001141c080c4103a40c10024203105140000b02a0420883c050b40070400703644042c49034400c40c04201c4040ca03611034644983c1e078442400d0b84000c41e081e51038030100185031030510b400c035030584501849000b00d4a2860b203460015000390402554140c500f00461007003903640d10b441005002000c1c2c8112020300d401d0040000f142c4640095000c103170001c0055040d01c2c2e41e250215011032100b100c44503008a01406d200d8014440102c0080d00400910120500380342100040c00c0302c100c43c03441d8030380300c4511501130003030400342c61200074800c20300640440c9003a1740031081c040c2d070720781030406c00500b01c0d0740c80e00d44440c070390030641c5e00300041600000ca070010640c0c420307008400352164003402d1012185403080240756120359000d036540301341c92030540340400c254140000010020800c0a0080304000f1900d40000c0d44035200310070602c1d241c201451103604000c942503210341e4050f110101400d241400b15005007000e041d04440070a0160051603003002c840a45500a8040c0c89001940309 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 337260215 1250 337258965 337258969
    0x109060311010809071205012304020a080a0f0206212511030406030e25060905010c150506181e0f13030e010509030109150b0111120c030c060702010902 67
    0x810580c1c11810089003c00700300300900001580c0c421500b5540700d0741d01035625818003500600440e19030001e03503041100500307442c4180b60341b040d0265000302d8130060165a20030710603541d616601d81c010110150712100202601d0300901410b880f15a00c4082c074144090420441e07200e26084464100c201c40090f0700c2186030a060382d0030305401c0d1031800c003c07404109940c0501e649010764819502055242c80c1429009003041c001a020288803000c103048104003c107454641009600a11b000581080c1e03000480758404d0421501d030903003001800603040d8441d07420300c01414000f030100e908098490700036a109915004031030321030030b4a5540888450900d1100c14441d8502602e00d60701c4600940c00e1100c1950341010174000301354503007001c003100c0f4422001a1914010610015850351070000d0040c180400e1600e145020081003404121691a0000544482030300c80d00b440c240354030020030a4400d03140a001400301a1480d030441c0d0402040041c02707850403000320f80080050b515082e8110447c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 337261465 1250 337260215 337260233
    0x1b0112140109051506072018060306150d02010e01141206032e0c14030103080307020106050102010c0e04020d020706111e1c05040309050627030f0c01050f040e01090603 74
    0x20002c1c9440d130b0340c0102901000100b20740210034000d044259003041400524601c0c0039080a0700c0005010080042030200710010b00c618220352807030082c000c61001401c205181c0100494008009001c43e0554400f60011030740d1201e45000c4505004210200800c0038143d40b000d020101c2565842200a280803414103007071407102e0700f144407060a2102400032101c00070070101c969080546000510302002c0348100d0b0b081e541c01944019100740080080140b0031101c1c02584298030701c1e0001d0150719a0365004a089076503082030b810004040d1640010107203001c2c0c0090036402e0301850003505080707080d260a0101da00702840f03041c082c0c20003d000c40d541424a01480501d403103107003005007004000a0042d19107600e107150b00300740c02c0c1d07540001000c01d4000d1070a00054a000b50031b40e0b440329200c0c00461506a200d0109010300c070802c200307210091034002080e40b40b0b40400005051011560b20065070941c1000c502511707206030a100100e00030940d551241d0003404800c07400f280162640c1030008035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 337262715 1250 337261465 337261471
    0x170304080f03070302190809040501030602030601030e06191e150303080f010f03020f03031603020c04110301030c03061509020c01152306090102010908070f0b06010c03021b011214010905 82
    0x61600107014410101c5d03004034103021080c00700c04040070304084515054120384940f600861b1300c03510b07000011082c030069901642c4900e00c20f0302c040200b41104802155640411600510f0003008040b215500c408140c101c040804111222074040d90881c065020596102155561000080700e00400900d68042030300e5411080f40d403007008003541445441012030055000c064056120003032062481d4504004072503a925050901200300d58080c40c00a40b12603107030340040d00c114100068000c0248900c0c0849040380c3d8441c6004500519680d61702002c1c1680d15891f41c100150307000b0016076415140010141c01c0014400081e03101100021010440c0258010351000804428200740701c03c000d000d110360b120412242940c85140900040b8007500c0c0040001303010381000b00b0140300300040d104010984a220341d1003403d0700d651b100c00440300040200c2d400740041c0c0c0b08000031711600610303060701d00301c0d80c5061504000074004110b00f41c0c2aa98101000d0382c5080c84007004000da8400c511031150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 337263965 1250 337262715 337262743
    0x105010b031b0414061b03120901060801020f0306040906060b1303050d0305090a110f060d02090301050c0f0a0e0105040f031406090c01120b0f0a0e01031716150617030408 75
    0xb05007030420081c040300c8451804d0701402100d00103101d891020042d000040510701c1e1400b100e46e9001e007000c070440c041b00e05403240402c40d804e01314007144103c01030003a11103440340354803a0740c01d50344c1d20300401c006802000802d95410b9a81c6070086880014800204003000c40303511030001030b03443c5103400c52078201890400800c040c50039040c45a00503000c0b90f2000e10581101c5d04070306030051000016401c840325001c4a41c4100001050f482c540c00e160041c0c544c120089008102c581d0324220b031024240b150210001407001d003009403000e0240290008070f050300301031411a080686a034403159242695800c2079945040140030420b01600070040030f58881c4000019100b0140d210001910780c2c41c0711512940f40075160026040700ea00e5800c100420884001c0c076454071360b5036403e90702070088001c0c002030743d100c60b850380781c035007141001002c40704201c4000c80880c1803c034907500c62032014440701802002e0305e921218000340c5201c080e84409582845103024554030391911501c44d103000c08102d00c2c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 337265215 1250 337263965 337263967
    0x260d030b01050f031510110114010b04050d06230f070c05030301060f02190b04051b060306060d0b040f0606090801050c0f0708040807080d080105030f1f0e0105010b031b 74
    0x5039902505540102c0c1d024003e890f140d172505203141c40b009410a90282d00310094440060b00c156214280d00c1d40c2e010ba81c00200450020013000f01e80c03810007400b829100385800c2001b0084c0b8100880c8040c0300d0341c0640700000700c80c0042d111104101d5640424000004508000d00102c00715590909400040c103092190581c5c840e60344454582c013051040c80e09201014040a240e075009204c07005014110b480120904250340c640f92490b05400e0354240e404e841000560107640780d100700700c9651598010070311790940d03442804100f11940080074a10f5620b84440803002240c5075801040502081c80c0c201003845c60134148002c0905100c1d070300c4184540e04020910070f01032956411284009000c51105590b2499410440b6140c0b003280e1041d09540f164090000d000c0b400454412001d8240c0c0c1d036400891390f41d840416a81e101104181c150741d400042c0180704c080c60003518403096076000540401c480700c1f1000e40e40d084a80981c0302440c03c4100104000110440f603000040704d00b1107a00791 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 337266465 1250 337265215 337265231
    0x60106121a1818030c010f110c0a15091a040201020c030307020a21050d0f08101404051009110c100903080f0c190309141c031104260d03 60
    0x228403400c0d00211000c1100c02d80040394001007120701c00e40d8404003d0040725503032000942c0c5640285010314034210b031075103803155403140c0e0102c1c07804451b800000355008000107da6500c1d180f0b5980c4d8044020a030903946c583d260800200b80284a0404189210752411680340078000a41004031401d800d078802e4104025200042c1d41d40a80d56040d11800800849100c0c130822400e0309442842d94041c000f8810742c8142c1015640c804030480e00031380755948840c039944902a1524000030540103100c03164014600707040301420254003141c1e001d034003c076100e070f0b120742e5806d40103040311241c480c40381c85a0700c0040c03540100c01c0100310f95011010034003410084c0980f2074400070301086020302681d01c2c42c18258042150008410240c0e00116034068410114445550303020b0004d00d88501c0441d1100300d0711081400012001c900440c10610282c0e0701000c200c03009104030020a40c960030301407640b2080c48003140219440703c01002500181082d9a0400c6000304454139013452a030019080600741000c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 337267715 1250 337266465 337266469
    0x30903060105010e061c09140709180b04030e0301060314010204061407080301030b19050a1b140a03020904271401061805180d1e020c0a060c020111060106121a 70
    0x45813030344000c1c4144c00f86d0f080d110180383c0d00034013482140036000c00b02c0084401080e54002c5a49000c81e44410020041d9030091045000041c503003080c06404031042c0c60004010038050f490014500308000c00000c2c485842e5501e8007107002c40031100d80c80b2a07502150901c152600001d20b041c4000700074002e6410701105541e220b0712488140001040d002a200105000c144100604402c5500506c0144014502402c8443c0200900441c210030680c1051140005a02800e840170034080681c1c1c3c01468010704240640103544600411034001e50340300b0310380d0654003860f602070740c1b0b04c0740c040020720182c151410a8101c0e0240c180c0d417540b960b4904542044071000700c200c80c00d00c10810035004144c581d20f01050840304011000511000e0107032070483c1b03080c1580071780084202c03041e406544c90b10108880c01241d4a00d1049045500b01440c8041405540d0017180d11000092051612139540314010003031500700402a48000b002c94851205405e5528980c02400100000105004070a14010340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 337268965 1250 337267715 337267717
    0xd030f021327020403062702030c040507050408060c090a05060a050301031101050403061d06150a0b07020a0305030a0203190c0f0215090607200d17031e09030903060105010e06 77
    0x400d2642d0119105440520011030b42c03184541060101e90441d2a182e5900b4000060480c1024401c8503098000303d6121103020703000340403059500030300200340c22010343c2c06000c01000090000420311400b44800909000d04101e500e20510301c41001980703d00e00c0009001c0b00920640050f44900d0342406205449a800801e0700e0440e0340111140c0141d03211800103850741c0c0300300c0d00003408980c02e205000e2101c1d800c0d01a2020340c4180304003251156a0307480c0046c0c80000c4161032042d40400c3e01402040341d88120781c0540700c600d00040081843c1c83d5a541c40501d160b110481410142e00041645801c12201c1e0320f00000072000e03030502c11304811180c1e0361035840d0214200000d110340030010200d102d08450400340d41c005500540b10503928121070400c0c40d031004481500081c441d15900340c04406050580708892000d50003100c40140e404940e010504940000301155110000d1700a04003070f4000002c0d20a00440700b01c00038655540c01e03a400d050803e20142c0203e41801007211901e54581c132994 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 337270215 1250 337268965 337268969
    0x2403031c0c05121b040f0b070308010b0c1e0f0a030f1103040303080c160803011d0109110403201008012d060c03050c1b1f05161e050d030f0213 63
    0x100c44d4840d04450780e010701907000d150421510001d001e000800d44541120042c82c506000c1e8682c10400c3c0e90702e03403484101e03103e00da0720030b881130300031001d00b1401100a25659000044003426286901d1804481e03d1400045000079000100f03524000071040303400ca04410001c1c03102201030351400b411501d0150805002500b108820007001030305200f8108111105007140740d10070009507503540e480e10070020445803c01400c0c0d40000000000404000d43d105003140240181405c60801d8510b840f5070741ca460311090307800d0241100c600c500307489503904030002e0813005aa0b1500741d484d50416106403003880352001f580261142801c011440c60310080b00000855142e4603003208004102e2034116014002c0680019842c414043ca0008003041e00900d0010118161000c001d21000506035200340c52a07213800f14080350040001068071280400c402100500034101141c01c0c44d8108803031400300800c0002a117007908904d0701550980d41c140584180d55450f0042941090400f20001d035980041e8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 337271465 1250 337270215 337270231
    0x909050702030307140702041109030705030f0604020918030c100b030c03070323011811010207030804140f10020f06010503070b0904050a140406090303060501050f032403031c0c0512 80
    0xd0500710b5504014008551744287d0151040c0460742100c0f0341d8500640103080c18a2280c0101c0c64041410300f80044c1d40190311007544010f100d140c40d41d409219800c10080c1c8900441e40c44800c00f60b50501c0300304010151006510700400c0c0304a01d0100038070031039003080c0b9251702c030b50802e0321200ca49540c0043c01c5070559801a80700c82c40ba004020642c6044142541381005a5081c4200700d90600d08111a4500103402242115082c1341e040e001262a0f40c03480c00024600d003000e02040c0010a240b01d03d100d11410702510031107503041c00760006220003070118423480059200504180c151b04042c0000740c01031809500405480b4100704a84615003c0c54801134000d940d1800002e00201160f01300007407410303c0100154042c06c143c00d2860190800e00002c0c1d0200e82440c40000707641d48a441103825003080070280a0a507124842c4280101100100b10905138005007650340d6142e50520051000540081c2c111b02c91245014080c01540d44507445401442804d200324521041e810300032943c01129 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 337272715 1250 337271465 337271477
    0x90c070209180115060206040228061b0605010806040c080105190207020622030b010f060f120b042409092a1805041b050f0409030c02090901050402010909050702030307 74
    0x500280d003801444c24212241c0e00c03a81c0041d0010b040f640105859001d9030080d260445500e50b4000c40c2110860080024440310307121890421885114103e56101c04100c503080c4200c1e4000d6071034260603100203030881403003a00300c001030104021100014030000e01e8600002c0c02246001103104040c02e05400c03090341d240d41c0019046e411951756400300c40e217035980c55550309a845400710711030f4424071301400212440c0d40d01800104100304880d07042000c4403c2a44d0f0a4900c0b04841000c48082203601c000b0b006c265100c00c0000c00b43d984d940154040d0524400030b8001d02b0302ca00480c1003180340143d20000485141100490100d002c002c28060750f401814606140100303400340c81d9000100582c81001202c94140780d0707101c01000d40e04094048ea0055a045031140411401b00c043c0041a2240540c01201c006111103582426001111107600a040080e84d03510260041110408103d481c01d5550350340314200f000315038022055030050907105104000303e150168001c0e55921004d8901418041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 337273965 1250 337272715 337272751
    0x7170a0209040e100501050102100e0604030c0f050601090f0c081e06030f03040605180f0a1502030c07030f0209010e10050409020402091206010924030b10050a080a02090c070209 78
    0x10b458020f0106000c403c4125107014201c640140001e1000380aa80e005004034241078040000c1409490b44028008020b081030b910345540907a014000900204e51b18030854405001081c0e003030124900920400c41302283e80a03072500a0030480d900c2100d000c060204030018000140c030f401c03003060800701c240b401e14503c0c1d49aa40000385000c084090840107444000303030200e5040e80c4078001e0080080500140c0e00c8041404080004080444500c00c0e00040041d0081140541c2d03101480392240305401920328002e0180720341410070321507070401d403510001c519000c811030900c8613182c2c1c010101510000f015007850211407000c0111442030510035902c550003c1c0540d0340e9641100c40640c8000c1c01060602c0e14802c0e00c0341c40340b4091080781506450718400700e8642419403d0f00201e601c2d982d07001c249603421507694859083e009070a41400c0340d046030f00401c8988900102401500e480e500601d0f200c070180c410000d1120004142409680c4144400f00040c0c490a080c25040b0500c007000f803060311 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 337275215 1250 337273965 337273969
    0x3040305040305060403020c040b0f03030901080c04050a0305150a1b030906020d06090f0b0105090f0112060f0807090b010306060c020d050a08030c0a03140402060417030f0a090e07170a0209 83
    0x2000700e40010b0002d0107034009000c201500014091001201900e05004c80030540042111044034058101e030980c02c10082c0c51841c0d07210ba40e0300399000b410f0058540c146503ca102088030014513800c21119580588507905440140e89081503102402c0c080030300c80a400521441890035100a00c00281616075a50740c1c200042a01622110480340d0000c000d465591420507002d010b1030010100b03894903140120394194440c40481714003000c00303805a400d101c080801101d0040541191920b555a40c0d00080360300b060341985800144400350042001c24189403d1108880300030741c0c10340c18503281c00010001c1a4109218000c0550103c50b01843c102103410864241360305c0405c024101d074000810043d401c64182c000e000d441415a40411030712040001102081c4010703030300654001c005000400181e0fa180b441040d40e0b00d4140181c0f420030718090410491034118614a401180104809014184c8104c8849600820918281619080703018803002c510402901c110040f5400140080f181c2d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 337276465 1250 337275215 337275217
    0xf0b040f05010c0309030e03160501050f0d050403030b19152d090617010f050907090b1215010e0a0605030703150825080d08060f0d050604050616090b03040305 70
    0x203640020007480b0b008280100100100903a54048011410281002c85a402c0003e29800c0e64003000904d6500981044015162a004445415255032080107540301900e00c90213100d0060384240c40100ba0402810304000320700c1100301c025103a12060781020032a40c0c2e4540550008840c0324103282019084034203203881c1502e64094281e1170764811b000501105039002081d241160800d0380d1b0300441801203041611507410078030641910f1248503105014502d060100941c20002ca030400c5250180c0c1d42d541420182c01061203a03406184a4080080c40c481500c04001c00820910f0000d041502d260700096902c0940d00500d820000c021000426036402540306203840c90f4030b11f10521120356940c01e455079885e41c40c070120b004d814a2440c40000100708540d01019a40124003500c038582d81090112079031903006088541c0949121000650b40c1c81d01c220400d5124041c0001e05940e1603d0f00301580b030001e02611840c140e0181d210307001c115503032100550094504a002d85907594a450404070340d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 337277715 1250 337276465 337276493
    0x5010e01110610030c0b040605030109020f1c0f0609050708040f030e0d0807061407020a111801180c050c070608040503070611030708010906030218040c2606130f0b04 73
    0xd4810300b03060155003070703144111008a80c407522508103010384031100650540039034494540032960500043c45000307a25005031030200c110321112410305000c0520484181e0210100c075520942c7c894540c0404c0c8540e020305c9000c0e0410784000e00240c141030400410544001b40050981c0c44800300301c40c10180304004582c411000100a003050030120700302800f543c4c2c070002007110340a24200543c02c00f051030b0070f21148518035940103015a00f141e074031882c9090140700c0960b584841c47c000b81421070913060501c1070103420300f00c0200e10001c0d058040302d0101da145500d00c1d4248007003444110501e2800045072010b590a0b49408040e503200d030b18050340f442c0100310700144080c0c14004120180e40780c400181d485045c1c0c5a0f907081080e43e072031580c0c0d0102c84103400040e406c110744016895400510882d200d411500c9144409500d5544642d048140202c1c0502070b0314085042d504d178403c00381c00304092030700903c1d8181900001c91315075484800034040c4030340c0202aa00e4401c00075050003050780240e00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 337278965 1250 337277715 337277747
    0x4060302060a030b0405150105030c031005030a0c08190b0c070f050d05130f0602030d051305100c09060905060d1e0204080a0c09090b0117010f14010e06031605010e01 73
    0x2c1c44a00703a602c09400f4210300c0c0b88940c020345c60440084ea01d03091403000c41c0c0100c0b4041e19400c3c40d60712030005a80542e403008045005c4003964000020b00340c2c5042120f51403050003121140d0340c0341d0905180f42c2c14503580f0264241001550a00100803844280480350000600a401d40e9921001d00d0003c440c4550300d940039000d40110702c1028582600940200750901d252200d9401003910341c0c030000308004860045100603401031050440741c20305503000b240c11413a6405001c0a8851558485240241c800d04080043e1340b114803040c07249802c00e40c038001400c0315007005403c5504080114902e40140b10700d01034016124a02e42c002c40344001058210804600003e41d651a100e05c00261798481c0b00c40101c1da1200090380c0000c601159118800d41280e1044e1280f00e1646030541240a40a11000b4920203541e112080300000100744a962907005001030278280540c9005c1540c4900280240454041c2e004003000549160b0103081070002c2d2402401e000311940102c20040325103c540e605884 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 337280215 1250 337278965 337278967
    0x61e08220203101a01050c0d0305070e0306070306060e0102030c0a0816020a0e01050a14030c010e03030408011518060e16030603081810050a0f0e0402120705251208060406030206 78
    0x5101c9240c59040340d0300c06000400c0ca13015080032500111024822880100ca80d5081802d08100140c8030760006504203a45103802c6030071052005c006800c103030301950040040f0350740381010465a50031014003e0381d000240059803d0062880ca2a611030021150041c6910f034000707071303040c9074102c0580c054460ba5005020610041c1d1501c3d4055041039080c09403038410643d0b1300e0001410461140c1e802c4040c3c00150203418021200710043d5207000c880a48258140030074000407469200901c03840380c800c804010440c0d005407038001c205548030441000300700144e040201c1840510080c04040d600004044054601c0c0c40c1801421401444940c100030719a4100041c000507011505024501c0714404135401041c1d05641c820541d020703c5010104400700c2c80390000e480b9424003c200c030000c01c100c06000545002c03440303404285040411180c0d01c000c5100864a0302e140c0e030041c14002c540b05900c6068442001e240d171512200d5100f83d8420108000c1d003880090866102d070382006006513400ba0000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 337281465 1250 337280215 337280233
    0x4080102030403020d0801091a06070c0513061706090a080d0603020d1a07030504050712050c040203010f0e13200103020c2d1b0904140d09061e08220203 67
    0xe407644401517048001402d038500200350201c0c5031080030040d46401c00300c103102003409401e00030503402c90350080e0703407403c1041000942d5840e004020b00241104810015070581003e14000442c1c04c1510b5080c0c803980080b080140b4030703800140d200010354101b4045030315000010000c2c0060a041d0700025002040d1440380810003100030b11500418500341d4034030046079140c000440c100c43c001c940207005a4003074242002a0700114580c0d6440e140039106492403c1e40d18001718041e0b920a9002459011140d0b404108160018001310b4010380320000321240c0c1c0c140d54032600c2e8144410001c0f180c80c00503061040c01280c0c0254100c070035501d542c8041c1d504d4a44002c01c171440d880c1000101114041244e03142c9445034001082d08410038460300b05003070103103000d14280030007600001d0040710320400f103168006d07a40340c040221600d241031076507414507254201075005121811010600f0a140d0680e14100050780d0000c030300b150300c40d803602d00c0005440b038079a10782c0d01d81e8180c00d14003035094000c3e1400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 337282715 1250 337281465 337281467
    0x140f0d020102120c03041a0a060306020412030906020d1205070e100e040c03090201023304140c060405010806120106090e0c041b020a0809060906030a05040605070207060c1704080102030403 83
    0x241ca0410740e0181d81200030b503610220701d4130600c400c40c0d008010110041c804a01c3c2a0b924a00a42020905a00054080c0c807540c0b05401c0780c6c1315410000070f407003400030000d0405601281c0d207001350100744080d020810f20960040c08103000f402030041a25201c42c00075141c644030f00d40f07110800e40300a240245840700403070b02034145001000c2140c012410032a480700d4090090168011060303044c0c6c01081e4a14103041c8402c0c40800100703071201542c2d40441c0d4403503022202a2858007560003412651281c1020800d06490a000c0580071401800c040c44104117030ba030000e1850b42e0050098500d0708045540d8a0820b00409054011030007403460702000140d02c10000521038100102920100400004414030f031802d00c00c807900079001a40840f180c5ca0004601d08060840001e014008070304007c5960f0005a5641040323505031541daa8807820001404204d004940e0081c030180090010b90f410074200510717501c1c40c3c22000c0c200b019620000303102d99510b0000c507801001e080c0d00031500d0b03040505d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 337283965 1250 337282715 337282717
    0x513030609081c0f050105090c0f030a02040f030c060e0a0b07110d050f070e0a060e131e06020306040f060303090519080607020c090a050c040510021f0630140f0d020102 74
    0xf03c203144d4a0301e0000042864182051194050754030851081d041400084c3c860110b40c2c4020117000400e5000e1100081c141c0200c0c03c4600618412400f001c062810124000c1c40d011240042501c2061528801c002d440d000c030080710f01c41343d00030034002c8a150084000c9420b0b40546580201070344500080583c01a0010941d08203403500c0401c110a04e032164a950000e8942c203004030040c046c0f9060203d00d5884200b0310302c031109072081080c0f00000e081800310303114103101101c058424507000403c100c141d107043d100300d01d0081e80200040007a0760071600c000b8070540e0306009890090119001c01d410f00425035450200503c2c0000840303030f192518007030003503d61012004a9000c0c16100f0007060000400d400b446103d180d0604075282070500d84000c005002c0312145c01e040941c02880240344060040074100321a80188140c041180c900d0309080d18000d080f1001d00b8007565401e0702020b0b504c485080000c010142d007160b442d00203918074411180c200403200d26110114882e003442d03c58a960190 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 337285215 1250 337283965 337283981
    0x5090f0901240806030d0f0c12020105100b070b0402060904060807080706030e070e0718210507051818010b060a0305060a0e06060d0f18030315060513030609081c 71
    0x441d003440c40e40022102583c580300b00f40d84d840c1d07241e0014103000903481c2c45015820810038861420001480454032000c040c0700c4520302c0714006035152400c001158507500800d00050071405140c61403c0410b45420f806d8100142c4000c1c414600001e400005540725041725003e8403105041d104130982c1c6110041ea15040c510031007012908240341002d02403000308240302165070425000c00c0f166105c000849080780320303c2c80b44501e03407802d0101068101e002c500e07215542454100c14031200c085424403900d0b04560b80d0000703100c1d86040409504a034024402d860f00b060485222045502d8410565409080315031070a03074200e800411202800c07a8140c111501600d829603003040c03215200c148024075490308a8503160000c00402010b0110b1078158819651141e11a1b800507511507055180314030f130040410305400007525680d00070010790010ba040b1004107281c3c00c020349000c05203850800403014a1001a00c2c0981e150030841c00d011b40001100d003000007103000c100b14004035010030f00081c6519 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 337286465 1250 337285215 337285259
    0x81501020717031905030c0a0806040f0c32092e05070303050c0405062b06080d03060803180d051c09080607022d0f0712170403030e0105090f0901 64
    0x400401000d40c5c028421680a00c096403105480d0a111040c143c1b8500d80181c0403030340195982c0c4214400e11011320a051050610756100b103098200c81510150034808801943d44200302c40c2c0101051240240858072500300584030030f43c050603c8040495035a8081c418044207881a014810b0413551090040c140144291010421603c8500618990340180d00600750030441c00c00c03d46131440f110298089460303c20703080c0040c0c0c0c900c1c022084010b645050b480380d010380d44a50104405036405020f2500a007404000031070070320403104500880902c541c0c0c1c4550081d2030f05001042030250500c4071400203011800e003005841441040103222085512500f941401043d0104040c24400720b401001454140c012102503170130100c262146601c0c1040a464900c50a401444100e00a000701401855035a403044d1900c492030920541800e88002c04412501040000f8400a50031401e03844850b1020f07c0c009807950440404541380400d42070105038015038200002034451800c1d80c00c1001d035410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 337287715 1250 337286465 337286497
    0x10c170d020901020f03090a0902070212070e15040b181b0c0303060109090903140f0903060406050402041803090b0f09190303110109030801030623040b0708010509040308150102071703 81
    0xe038500c00d030311b90281c09441d0341d00200040c010400c01402d0b402074191203000800f4102c00d0207040010528040003640801541c07440c5408004501e031081d030381070010260583e0103001c203440203400120034401d00c17001c0417148160000420300020204840b000310b80b40b00c501e030903910f0b10440b0344c660362a0030488007180000d841b91408a04944e441c000c0303080040d490386070b0702c041008030054940903030000f02d190220140140004280c80e80c04100721800345015440010721400c242c0180410b440318000e600903294088401c0200003940281a81c0488140780003031034948000312440c440c2442200591603000b5051444141072620360313010282200d2003a2500d00100e042408601d00365504408007501146000004002207001a0004094400400315400203008903095440d210300068605031049101c0304201b06103190444003150240c03804075004803951400380c0d0300404072000200201c03802c1084400100035a4000c0080b1030243c036824101a82100004070425980c1d00124524161502 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 337288965 1250 337287715 337287733
    0x4030e0909061f18090303150b030f010801020c0d1d091e0703150b1602190f0e0c070602090d0b011508060d030e0d03170f0601030f0507020705010c170d02090102 71
    0x103210801201e640a0b5142ca43d110101a11001403001c0242a000e0640751001c00301c040780c8d0314a10740060300d07108800035142c1c14982c081c5511104142c201c0d8400c0c2e0300c1004412821203000a2481a00c40ca41c0717000181080b10428030004510a0a1025046264a02030010074481080320820000c507a41402c220b90b0f4491008405442841c100c4c0c0d803404d408000280200d188500050001e44108a40760103032140c1c42d07011420a03003545000c15a4030141c101c00f8804120002c00c2200203051200244503e82001907030440c051060781c00061200760b00286e036040341e4413888200c0c08a107420440c4000c0d81c0d0395070305800b8032102000000da80019106030014107a07103418100e064080e0b4069581c149501c044505011003151201c2061f0240504c540c0d01c1800030210019040c4100703429a1900d00b039052610001d0300b40ea80c0450384a01040c200320802101c1640002c000e0102c410928050010b0607484c00e002c400040010a0080d400c000003404903030740d01282d00200400d88003a400c56040305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 337290215 1250 337288965 337289011
    0x602091801030b060d050115060c051204080312061f030e15040c0e0414100209100f231204122709021c020c060103060b0103020c03070b04030e090906 66
    0x400c0900000f8036010101e0086243c0d401c003030b4050313100188200c3c00081c1d10740e07004030040c00c24040c80e070110002904083d07000003046801e01c100b8400542403001d031410581032840d51900c86c081e884607140300002c0f60000511030756408801d042c0c100c1083d00f5a801031480d10320f00501501c2404c3e10a13906114410030f40c9510803051508520076608020f400c0d044600780324000c07802c01400307003042e00c02d0300a071540100980c605202d01c901d9003182440c0161384182034801e018825809c80847c101740080c81005040313540d08896030384418032210407280c1c03c4940307803117419455009525101403040c03a04410801082014807020f1600340b271545a80080c03e00003d80104503080006842d5483e5890f0281088202c420760050710b418200174201071400000e40030000100e0300520f03441070050703000c14010000d0002a115801c0940030030700c0c040d850700c10010855940d921030a040108202d07040c0000800381481b50400304081c4100030300305400b41c20700d26400c0340d89880568000008202e1004421416 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 337291465 1250 337290215 337290259
    0xf01090e07050105071514010e0a061508060d0212120c010501080d0c081305061611092e0504050103050708120703080117070b0c01021e1303020625060209 68
    0xc400507502d8618042096480345004055070f1006d04085480d44822a040e803840c03502d0b10302a01aa00c0500042c0c640350080d01d042d2031003640711105064084072811040b40d0f019a880b0790004099518513079440081c404280e190307940140c3c88802d40a001604011100150018035950a0800080c8656621810a1500c60103480d40780d40124019408440015041c1d2020b46296031921140c1140b0980d108040b5400740d001d035a60034101d07481841d143c81000350380107131800e092409480c520754910303255001110880104529030009050319000d18503240d0804505c40c0a044054400e10265a43c0d00d8003c0d075944c040d008459960041200358007603a80c481050b14a10341c3c06070340e00744c01030b440d000c11814501104c1c501001c4501445c0c0d000710305800c0e40c2000700502c0300c900000582d584015441d00050709440c40100310380a008000340820302010741001c0c0c1c04e40350100c400541c0d6080608071289544014280e0100ca03006070740c01e440c2808195405004d050405450541e04034100040a00403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 337292715 1250 337291465 337291469
    0x4050406051219050304120b07030507030501060801050409060213080d080f040804090b0f040507051b0604020303072d1109010b093604060608070e0c03010501050a09030602030f01090e07 82
    0x40d03807000003041c01c003502d41c09080c1101c5000c0d0050f281b5050303c8403403d0610400091040d24007005041c2407000c0e00b035142c0f0078990312115a203010401541070039801070109006120711403085885240c41000d0000300d138125038108442c1d0503219500c5680d400c800347c4618003030f14510040380440300010481c0544080300c40c400c3d030f44a50200c2c0340c0b078102003025005020665580350030103c0a003500b10700e40c90700e216650240f451515400d03200c98a00c1480300d50a00c00394601c03490b9801405c18800141c60020949600d40e80c41900020364064210756101586600d000300c4a031140c801e0b40000510028521109403480281c44003a030aa0b01c40100d0740c000c0c45000c2003ea000000310600c1868462140c074000401c0c1e0340b8004811107002031000b40c4844440030789050326855540c61040028607001c00c0803138003c0c042d41307400900a140000e0300c05842e020501c80c5605110000a0004840c0c2c400c0850401079640144110749034101184200103040b024060050300030b1400c62180c2440e800000c0e07a40c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 337293965 1250 337292715 337292749
    0x6020d18180204082d071a09011106010b030405060f090a0f03051308030d05090c0a14181801050c0c0309130902060a020d02100207020f060a0c0c0b0405040605 70
    0x103000c0707140401d203029945590103000c04180e428403010500034014012401540c140304d8080112440302c80802100c540701c090084d01031350000c0001c224034a0b61001c0b00c0c4101c00e1a1100301d45811011006884640801910042c1800303203400100d00c4510400c01340d80941c1c0100100d40807982c40b40404280070200780c400cc0c2e020390042d4103170000214011218008184246044c9040c490501107144d50641c4a40261000e5040403425401e0030f80d080c03107056880800200240746084502d000304480107070038054a294414035400b110900d4036400510120600f162040c0001842c040040c4100b103000a540b64145500b046c0c042801d10a4503415115541d5a0704082c610f041b400c0e00c1005428502e0707040018440c0c0d2200071520259681c1c20151140c40c4180e006811142d2990200a0405103040318410340c80780306100a401507220900e40c110b040c1d40c261810382d9644507407501981c1946086034014150450b20321b011815502c02d00180c030403288181c1e0148012600c8100f0040c1c08400346181d82 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 337295215 1250 337293965 337294007
    0xf0c06030515060307020c0907030b0f090103020a050909010608060a0903170126011e090326040204020c0109020a1e06050c03030601030203040c0801110418020a080402043306020d 79
    0x5400b92820200843d0404c0190048490724101c10021424800c002c4540e240469641c0f400043c2c907003440c0700101c03c40d070000c50321803100350b0642c1e0001d1204e00e21800781601802c1038000144d1009402d5000b680a0912141124428a805509540900b072408811000281c040010b104680d40e8095014162210031110714648107550760440004038030041503414039034981c0000030a8424101248400f603240700c8021407100301c00d0502601c42051203003030400000c1c1c10030801481c2c184100209402550403100035a50750040e50009016060380d9102035884900a600054103c100c0c2c058410104000f11000d00390f00e0303403000140c540d80144a00861950000c10010750190310a5000710340c0280704403000d820041c0c840f6016821100034000f80440403134002030502c40e0000001085981c40320760a815441d0a005140080844030090402400749072500e407a04041d05815240d8451400c0c6071740e031460100c0d5010b6665a00f00c8185c841d01016000311003580112510841d02c00e00721003504900c00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 337296465 1250 337295215 337295251
    0x1605070b0c18090c0a0e01050f0f03040c05040e0a03110a0b15190602031201050d080a12060b13050f06040f0312092102040f0b030a03080a180f0c060305 67
    0x22901c40e448000d6aa02c946841201e10690303658020200e8000c05a40b410280c65451141c009001c4082c02c02400f41131110522481d000300141704112003c2d90300d200301181e20390311103103000010300940e40c2029034440c1c00c0c9031490b11511170001d2030540040c020340c0c403101320380318250701d10303443c0c41000001a00400b0f01000080300c0141c2090070f10041c500c0506800c50104c8a2101d50101ca001c5030010401a000041c60000d40e0101c8044907000d000d0441d6958007498659452844500c01c0400240034072440d00c2000b24480039a9100303000510800e60a20394821215102c030051007540d00405200b2035500745519018140501610700b07a83d03411662030002e40c250b441d6000b40101c1080c4030300820501c0c28021880c41881d00c8900c0c0c0d0300b1026120040e51010034030401083d500c40d008551201882c12000ea0000e5900240c00580c003505410070354020303100c04104002800c1c5050940707401d00030310080b00342000352709111907000394007030211425015100c81d0b00b141600e0003914014114482c584034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 337297715 1250 337296465 337296481
    0x91306060e04090c030803040804030314091e031e0a0510050408030123132703091e0308030403050301050a080309090412022409010c051201140d0c0e1605070b 70
    0x100f03440c400e005488107070000350750b030383d4400301c6600840c0d04642c00007020900b0020150002c1d4551401590072105a003040000c4020456040c42850002c4110440c01e02c00043c03900c3c1031000c1c140904500001c00f11200c0c078030300e03220303600c5c07480490417209481202c00392074003500a40710f002c0c003660f40309000518691030001031880d441c582c146c50038505030985100d2611079071044040c403220821340d0008244074003145856a05c903207a003841c0315a00c12440a50b0800039920030f1400d021b692801002c1c3c0345072082101180340c900b015410080c8080400028007090540080180d4101c0c0c50444500c62000c1d10f0340c0e4415168041c2e040c0302c0b03420800c248041400101c0a50361170414108501c1240c28500b11130000403000300195031000c058420748028000341101c01c2c0030312100020203051040c9407580980441061010512440c3c3d0110b07008a080d10240c0d1302c0d081c0c0c01d01c2c442d8101c2c070440202900e80145a2103c541511003490700f4000c51003840400d8003807030035246c5491300000d01058603519520 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 337298965 1250 337297715 337297721
    0x30418020c030a143606070309031205040305061806010f0b0a050703050d02031003060b1905270a0605010201180f030804020a0b0f03061009080a06090c050411091306060e04 76
    0x48400c601420500000190008034000400c46140415824101703200c1c0b0f00c0f03c0500c400564001741d0084400700941c501194008050710700f100c3c1d22000c031080c009400d0340304503410701a6400003071880c0505810701c18810003d27911000c426070a04250381159a0b00c2c0d03001c400042452244090308401880411540d078000d03c041c001c441c3c02800c1c141d24011420103400105d900440d103001e0103003c080428070030702050307105102d88030b0301c01c0d200e01d151461542c1032214003900e107215491085910031130700010201c440800e0b1603c0428050b1545c8030782004010140906124080c050046d0310b09085140b003002c818048400d5150003203c1803d0500054504650b200da00a0050380c000c00704500008082044c400106191000320311480d8503418134404101200e0b0740d043c0080208114214280700b03010020410041155000c0800255448a4078140310414116440583d1040c80d282800c2c0c030090040d8014154242e0864482c22894600404842251034901030b15001400c9546031840030b04140c0c2c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 337300215 1250 337298965 337298987
    0x1a010f03110604030f20091504110c06270d050f0310050910030b0a09172d04090f062706050925020f0c130b030609030418020c030a 58
    0x3800d1546044c0d1640c461003058580d1880485d2080d11140b5181450300c9100450b84c0d50701c0d0304445020003420002c0c0d40c012100f03504c0b10b00c0b911841e9500d210614461103031003101c8601c0010819a5020301e0540c0b400070b001034010130f003124103074806c0442c0d141088020800030180101c0d52149070030024000e00d006410b8100410103051220508000304e491b0703585051151180d0754210320480380905525010701442000791040403217a081011880004402481003c6100745c0b150340d5507128078005005205003036540040140702c0d00c40202e030450301c0040e14000c0042d45c0d5914014000d80c440450500704a41c11480f070302d100204500800c1c0c018130300c81000d0245071605580003081c4280c0352000a4805482510b00c00b0042100f01c1d081e00b103902d10700034230180fa00d400303001800c042038500c06120384881022106501c04c4680c65001d40003040d06034410260b8480107800c4421070320380205810b903242e01074029140710303003000510039801c8411802198003d1640d040914141401340c3e0064800350903032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 337301465 1250 337300215 337300219
    0x110a0e01020a330204050a1a0f0309010911030a02150310080708070501111c050f04120f051e0c10020f0f011b0e0f0910120803041a010f0311 62
    0x410712010208603242d83d141c0720114054081040c0076200700031140f1841001002480b00e9005101c100034030303070b5421102c0f8100e8880300303441e4562204100915465109400c0142c0304040040280440c05034154847d47c00c3c0d41c420f841c1c107a00d842d40f5038205640c0b0407088000a5028020300008030f6080f440c5400fa580054100d080031a559490384029818000250082c0026501a0302e0400003980d02021011240000380041c200c03801d00095003200892103d550741c414004001032944203003110408840050404104441e803081c103a03c1c0456661114840c29101881b5981075141c80e1aa0001030508002074140288903030a00310003800390082c02ea008280a5001c0c464038a9071552062003454140184400001030b02e0170b1400f41038504000c01c10700c82007001611200424652503444048444610880e12526565101d140c5e20000540d60741000e04100c03004017a82d402c00429502560085100c4c90400c40050703d82c1c0b01c07642c0d01603400d108100100c0c28003030080011400b00d40144485800c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 337302715 1250 337301465 337301473
    0x3030c01061401053c040602160b0316110309060c010b010915090501030b04090501090c0806010e060105041e09020f070512091f0c050703080408011802010e1005091c03090603110a0e0102 82
    0x18a492178103c81d0001da001c000940c012021307030250840c003440f5103400380411411050941c18030707280e001000945080700009000c80300c024440b450804105940000b00b0003000c1c1070791b5154501c80035000c0d2407006446404102025400700d0020078030a104003018015a4402e07401c2450300004402502d6429900d540040d5a1500040031490a0060500e254010340901c1079181c0361450003403800c44140d0101202102c81c005104040e13910400302e604603144010395490001020358001210070407980001002c1d0701c0081c50566000c00100500031450040c0103988140381c88100c00b0044d03100d03d00c8840d40c481c944082d8110000380c00044c0c5e504c004d0341840d14900310045580c03610b21308165038000341d980d00b80101f41000052001d0040410304181c007003001414000f154000782621003019032840c410360700d0f07029142d00140700c0c0040c1c5407180c10080244516410481440c210400c00000a0303000407000b080114181e8001c1c042c44000e2104031100d2403074811401d0040f10303c040031900950460203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 337303965 1250 337302715 337302817
    0x1d0303061c170307120504020a1203110f0c1e0303090d0507080f1606110a0204020307020c0406030807020103050907060503040f0609023a022404030203030c0106140105 74
    0x40c01100b401400c01c0c440700003a9241061072010b408036080fa0f1010460908200401006032603070808003081b40c5610b4114a01483e49140a0343d91986044c5410103034810800d4032040c0ea0400194251000029a085011403080b580030f181907042070222079802d503108001301c102600345010014441d07802102070b200002d80780c2884904041120400c0501036004101308000780844112880081c8010700303004c0d018010031200c0e16180d200d60400640b0841d404000120f0040c024444030701c0000b8000d00c02c12690f03450745040c0d061070b0492501a40020b20f480001960709000184400c2503d000751209801c3d59030795070359986a0580c10b001210442d8650010760010b8071040342c0c00e401e40d1140030504c0b4451405212404a04042080d0421407020b200ba9a0015894041d1070700c1000000030070140c5a02051000d04045104603400290540f00009002104c1d9030194010b009498107030040404020843d001140c0d1402580e0314040c0c103009080c060381c600110700b682203030401240c00748041044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 337305215 1250 337303965 337303973
    0xe12060f1b04060518060f180f040e0a240905030304060f0209010c0f05070e040f050610150327031805090c2209020301091535160906050102011d0303061c 68
    0x9001020080115002010b101200f0720b0541210540070104ac4c2e010400b240240c0c20083c0d50748a01440648600724515005407030314440840c400030080c0c40002030100d0381503441d00310713502e5004440c181c4032107107006000c001400c0d084c000c8500c901c90581d1420800d420035204c130070602c94810400c9900b0300c110f240010380e4102042c03206100300c2c0201070aa42d00b44080c20030f2424420001c0425118030015441880048110070680f91021503610b000200501d031082e02030ba5141c48110a0201501e0a000300410143d020035070000c0380c0808440c0c10351050303032030051040c4008180c070118180c8070280441540c500c1c6040500c2092001c0344620464107a44944800403a0b1080c1c110221441c0c4408031414044042e0000303000514540a8a054006d425a00300004524a0a80880340010b82c990b28a8151041194041001038017842000b410b0351354180c0c100901b400d21800d4003550809401a2002169996889840700c13244003441c0755550350b0080081400c3d840003841c4c02c800c034421001c0081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 337306465 1250 337305215 337305217
    0xb0103030f050c060705030603010b24090a0e0406090507090b03060a020705031b0f010b0d0c03060518100b010f0f020a0b1810020a17160e12060f1b04060518060f 71
    0x2170400c0342c45540e41c0342041c000b850700b918000207045006406000010107090508030710700071592803404006440711041c000144814000b039000743c8540c8507182c1800188481030b442400201d01c1303042215002a640e134006000d170f40c00c500011790300d50058800102124070580080107420712860582340381840b210100260340a410f03000001d140c1c008811024090424450b03803107800e504a0f00c02415500964901300d02c400580802450540c480c00424200030305074040402c00440003007611042040d800304040100040c0300c010740065002000740c44150b014010070719039400d5540c0a4042400c5c0be80ba80080f2000c05859a0310900c0b01c0041c43d01c901206125056100d4041d81015a50701e13000030000b0090560701d501e140b44042c101c824080f03191140d2400e11a0035089090202d0b940030745030000f80e0044440c51040805008140412a0200905902c03c1c40764462021241c130003410100c01c462580203a01900d40419002c04c840e103003103003059080e021884001010285440f4605d00d0002e16 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 337307715 1250 337306465 337306471
    0x8030403091706070f05091c02040b0603010603090b0601031107020d02010e0a081c020303010b0a120b04020f19020d020309040e0a0203030c0d03050601030b10030c03060b1303050f0a0b0103030f050c06 88
    0x950004424084416400300341d6178040c0b0301510f04035040488640000da4804030a90125410803200c407144001c54445400032916140300600e000e4070307580c2d680c90140150180e404110350910b05100010071540c020f00c20309041c2c155070800d15080c5501d5a09000c3c6951041e0000d90501c1865428103245959100700c40c0083c026020240020a46c0802c003918822981d0380c04509541062005001101002066911040682ca840075000140c0c007071020050500d4012181c03ca8000994284810fa00c0c000415001000c0d18002480c40c24030b460882c1c40788040c4d24907100503001088401801e18007908407064001c0404299860707450507038002861a07010750341c50034040d003181c440b00e2215a01440b500364804030a003420700c034402d01c810010f1601c411249078801410740d00c2600510b100e00c07a41c0640041c100c41c19102d036580c50868201e081414442c4012a240e10807582281142500030402440703e651043d5a039200f80d003141c0d4241c480b180c41c16085d4040040034006120100410004a40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 337308965 1250 337307715 337307759
    0x180d0201020d050a200f0f040b07020906030a082a0109030c0b070c0f141608010209030c01090302060901030b0d0813030c0806040302100f090b0c030109060e0408070803040309 77
    0x10340d403034a480c60390b41512801003644418600d1310710b90008402d020030818100c404500c220707580d9034000e6090050540a81c07003100030810000324021919000103402480502d000325010b10480c2c0e1400c0805648114080300148076450502844190b0203901031030038003200b8844400600c580c000304606007101d0241701c080d4006100300c40c0000c2130042800d15190400342a2411045101c2c1d180c03506c00c142402d501c4024101d038100b00c00031078401400c0c405d0402015100c62000949d40d134910f801c501075017000c080240702e07004900c440951580606d101c4402c80303a0181c0880d05052000c00154018902c400d00241c204030340c00400800215010018594000590841a492401c6007046c0202c204c56030400f5111b54050b000703005c0483e0b000034140036100e080300804070b003515400303c0c684047c00a4034002480510b018043c0440140c055010b9816203043d03090800c0313101d030356030070f881032000041d5009085858208160783c0032035030102c011980b1a0180c145081d52075600c01d06625960000ca054078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 337310215 1250 337308965 337308967
    0x12060f01030b100806161b120809010204031a04020105090d08040f06030c1d030c10090806130c12030c0c0312030b060c121b0f070305070803120708180d020102 70
    0x110400c00030000e2160441c1c0200c0c40e0f241ca09040c580c0b03440e6070700800b40c802001c0e44100d03400315501610543c07004051504100e010341103440c072468181e00088490084101103404000000d001c15414425103048940240c030004024140b8858140083d801038000d9040003010483e145d0b880c0c840d400c400c2002840352403a00d41d203620709a43c403c1058640d800000800d0b00f0013020702a040c0d80300700740c1c80001d280100c3c0b0104007143c0c0c03000680303803541c1d244070583c1000030b0000c0c08401c0741d084203900702101d6040003074600f1680d49450031003046c0d9085000074a903488154043c8400e649015079000720f02d10a00f041d5030b000c8015294030a036032145a00c1203d84410b1550401c60700d95141c003520710640010b44103681030881c11500e098890030603030b01c008441c600c08101c14150b44681c41580500d00300d00b5041d5031988080940c1e4903101c009078001992103201c1c900d0000303005280041121030401404036800754540f11030780115408440072703280e100c0c000f5001907220860b030701c207010345501e00c3c803d50001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 337311465 1250 337310215 337310219
    0x20117090d051c050930031501091502010c03050f070206270102040e04060b010320090607060204060c02150a020c040905031905030117060f1f09090b1e09120912060f01 74
    0x290240403100c441003038122107181c2c1b04480c18154213042c0d80e0040c0c0d1716660141d1400048004075209009030f03002c851011031640304180b1b02c2da01035009141d200c4d2555418003030383e075400c8100307001d500054444100507070240001601103801c105800700310754541d4403212029004407200c142a0380150300b1400783c05180900b840200162403181d560301c40c6081c2414007104030524622101c616040d925800b04d9031380041c581065a891504903a9001d030b01c19421900c483d00c1c2d02000f003c4050010040b401410002404a16616010140d0704074071b85942c002e06155169805000103004400380c1103840788000d014001d84401c10307240802c0742c0005561203940b21b6141c0094404500c400050f0000943c02c0901404040c48441e211268842045c001c13501c00d034100c2000c01901d00741903038007071403000c1e240550507010400b6294081c0c0c0280710b55000b620200b42002ca10b01c1054100391205100750b44810001002050300703801a16800d000148001c00c1da0f8030856015080410031140740d03a01719254801 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 337312715 1250 337311465 337311493
    0x1f050106080726090a1a090f0a0809040c120903171e0604050c090d060606120203090c0127080102030604200f13170a020117090d051c0509 61
    0xe40c0541d852a00b400e911150000070714115a00c0d076080782d4004a41000500820b00812045c200c00350f00416280001c0c8a0501d8000610010350b5110880d019842c40c030112580000342413040c03603820416061818054008200c000e00400d8481c0c0c05010b2504410402c4844900c11440227034000d07250510080d50039450a0381c000c000810061a481d4240a5000d17100e100c0f450343d60744481c0583c5c00141580740c0c10140c2445000314503a10358050034115503807003000b0207908550100c490b81d0b21008005440c861802060f8001114046a144e01000c0c6540980d031003015860300395160b95000c1007002e8814050366910700116009407155030340000a00c151801c0a01c1500700407040b1002030140c645000c2002d40082c890310b51040d980c0b0101042c08881950540c1e0311000410510482d10100c0f86886c3c1c1140c2c882e000d00c2c00076400300d14180c1404010b9540040700324071992510300900041280170b1001c3c0d03041d4100010181201841e11410035084459100e158050000c0c94014a500600c4c510 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 337313965 1250 337312715 337312727
    0x5150f06041d100b0303040510020d0e040612060b1305100512010e060c03041113061d0c03011701021303033b010e040e0d03020309010e0a11010c051f050106 69
    0x80000624038030300c1242e41040000b041c0001c51915403500818200c814000291860056810582c0d101d07080403e008041078000510f60080d01f501c2d00d0b04000d03003001038204801c540d014880c410350001616803020024110b42d201c07242e443d60081004081a214400c000111070046856811807051130200f400203181504c404803210060b04000d020b0172030605456502d81401500c10542900e001c00031800708003082c41d240c5c4003482c001e00b507650380c0030003000380c00040d007201e2042481400d401424812043d080d080032500c503600400c1501d142d83d2820009035041495508808034655090085234104105881c03001e005500a9540045100c048040107082c045421740307400c5100101c4000100e101511000030800500901b0002001d52902011501030301407090070140c140a9501c02c1c000d91034150340514060001c04008203d01c550b404070203561102c5032400980103880f440d168407203d42c4030369250305500e446401a1908800360b444540d084050154240c013401d85c48030010301160364400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 337315215 1250 337313965 337313981
    0x63705090907060c03090305030a021507110a03080c090916030c02060403020a0b0402010309060f1b050a02030315040902030a060f0c090b0316030b0d030c06060b07031b05150f0604 79
    0x5898032501d0814104440c2e4402c0e0900c90041480100079038041858011561540155040401d80c0d548120b40c500003074407100c40c01003000450546d4008111414401c5400071606c07400340004083c002c0550302d003555040c10041c100360500c1d6040059042c6a112614541d001e20b0300101040700102d840c50000e015100825002d4007154012000c11022030303070001d00d0340190b540000c0c13445016150b500048024061844c130160181e410128450305804590b84040c07241107064080f40391019900c003044500703220384030b00310005a1042c00840c2c0c880320100e260400002e40240000f45041d59540481c0c03d0046109040d155250341c2e02c40c030b00e204016070080707014403549450507404803130500c0a140550300003c0c201581050948520502c440d000740d200361501d0794005c0c051040c0300d0480c034004110b030f41c0051040324400d040040004040221105650b0b015a25071201c40c84001404101042c1c12a0480c0030f40785071007100b620321581114014038600a80083d42511100c0c6011018001510105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 337316465 1250 337315215 337315219
    0x1104052814150a0509090f07090e10061d090108070e0105041b0c022b03140f04030212071203090914042a030212010213080f03090108063705 62
    0x200d101c1c5550340b02c00141c1c072107041e204251500d4005900301180e541c01034010154101c0131400611106550010846115100e15520310a07000c0e11102441c41e000000d072080401980c42040502060703000b200811601012841e15204a036514800540280400c0c1e222842e240c205190901040d10a02540ea024207810f41d810f121104d6a00100d03201e44804400c02020031034400c3c0085d0071076031244007000032500c10f190140e22194405240441c0101040411004240f51041f0f61201408074000e40e84102c80000034141002d10355001e000d0480007070423120080b4009da04020a00500c0743c04110842400307030303039582c00150515104001710380c201200900c8010350502040005a6040d04c1504151000b44944030f14291417003407003d806c030b485e07040250310500c509410302040405501804076800000441c008030ba540d0700c5200d854042894107408150810003208506501924540760007460103001e0b0b403452008043c0150380c0c822889032000300b001c00d021081c0390584902004074050a81 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 337317715 1250 337316465 337316489
    0xf020a02030d0c0f060504080406030c08160507170d05010314011a13020903030c010c09050d0f03030207110415030510141828060c050c030d11040528 66
    0x40d000280d491011400150800c6840c2d00c011003008501310440402c29444041031216051524021080350458004d40000a25003001241000d00c1400b5003400b51041c0c040101c02e508046004450a60140d00107070b0f070340d181c01c12880122003000070041c500405c0710348000076554114946240340c0b13407000d058a1400d81c1000c0101000e200340007038201d4500740886042602403181e2046a0213400b41c85000ca81c14000402c12001100c019080004403102c0c980d1100106a261010400800c428000c041d0203072a20fa540c2c140024040c1d401400c0c3d481c000d40c10310905040c00800981990b60b00362006000d00080c08003003017009001c00950700108042c0d00140b1941140007142803180070018440c0d0880741c01c0301c24213982031009000c1c0e0682c8882070512881003030310215030b15650340c8004504548031482c00070b00881c201d02c20010f80d0080e1840c030001e5854940d1412034000500128100200c041c2000c1200040c80ea0300e81c0c0541c5050a580c00c3c07004041018240407040740700d03650380301424541f5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 337318965 1250 337317715 337317733
    0x171b0709060b1801030e030703030501030219030308040308060102100c180e0702120706060801090813060305130f021f030e160609030f03172404110301170c0303190f02 74
    0x12200c402e45100c0f014585004402d030844100403005000065103100850100040031401c0c1541500054140c0f402956650458025485d8102191009200180010714101c0c0441c0002c1e00ca1a1403940080c414070448440c20300c51440030003110104201c4201048440c260503115075404800c280003080105a800d000745045e00010b17465208d500c00c0312720715082c00110034017002003e51115010388200b4000b00087c00107407400c500b20b40d03c0341c1401035085080540008085110f801000d200d80001061039400807802d41e24903c0c4801074a0080364001c2c095034041c00000d20051400361002480d0780d001c1418110141c1c070034103003400008400e00b02c0509210600200f50040b6400b8100c2e176008a205c0341c580c840b4241100c450403502050203900e0415000c3c071189a0b00580c41400b0b17400080d244400480c1c155080100b107a94035000c0d0901d101d0300f800104000017004e003004240d1800c0c08142c80300c1c80e00e080002429580103521070745a01d00c070303040701c0c20120794040c801c2940d85004e4001003030148 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 337320215 1250 337318965 337318979
    0x190c140d02060106180e0c0408150408040905150d0b070f090e01060c21020a0201120207021e0d15151d0c0a050d0c021011071e171b070906 61
    0xd00140030345414812028441780e11540c1c0300040900034210b0554011040c2001954a012588280315000c2c031842000300c03000d40c1074035442001d80500d0380300d81e042d490246030240c00030252900a1402c0303030780302030759105a2040e00c0e10109561100e00c9810203060a141c6008060304010110040f1410400c450030203001e901ca401c1800341c151003150401c1c00351b0151030f1074403000c08a050002c00310030101104029505540006190340e000e4401d0301d40d00751620003070030070008070b000321003001e5805040c101c40380c00c0010902d036078040c998101500500d0000b02e103858109450101a0200e10b0966030f500d81c0c40d541042d81c0701c0c1c000203000c00b8800401d81b1007542150340380d0b5003005042003168545c00140034501d1030040e001c50703022031407042c1c00b40007075000302501945544000060951050510f0100b5281001e41d60458a0481e4480000f0340007199040303c070740c440703040c0300821501b000300804040301c04520300018000340074005c070041601168403e085810228242e000071021801d008003031100d9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 337321465 1250 337320215 337320223
    0x9020d0b041403041d22030f0201140603190213110301090b031203150f0a0801050405161805040515040516090b090112030207180c091a041a190c140d02 67
    0x96030a6016100340303034556046d0040030841e40d1030034041c1c01d10703140240000c05822040e8100e006000d42c0003000300e01d45840c4016070b48070040f42c125515401c0901c820032040400f800400b00d580c0040d0a0a60f0103801915440841c0c030040011400184084010880b09030280142c0400c00003d602505901c00304070340300843d40c000640000c031710101189101b16a40c0361082710a603000c2c8010702e5070055a5a50601c24001c2c40152015142030041c400c40e0460080382e5251502150645100030048100b40f031410801000044d03c01c541d41d018100c91034070700520001000b03000d81d000e00094000e807501c1a4405401c0541544040202405c0c0011515a80d6918186504407039000c03c082c681c000705483c04074248189904045109004800c4200c8841c00c95802020448882d44135000307826210480801003071040040d40143d80f408000910001548039003141e018102a09601e041400200060088403481040600020035a41002042c0402c401112692490b901302500060035961002503c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 337322715 1250 337321465 337321499
    0x50120030403081306180302010b0d030206180f03040602030406120605090112060b04050c0c07290c120c0c01090909052d1506030c010504080c090a09020d0b04140304 73
    0x601c40f0f000c001034100a6540000e10b0310341e9000b58200040108003801d08113580d17460304142c0042d840e040419000303041c400b00d03a040442e05500203050070303602c1c00d43c070f0850b640c08000c3c002c03402d005040c0c003d203100f2002c001a20103001146c000d503450300d040034001000404110340108020f1b080400801103078441c0a403490554400f2090f40c402d402030f90810001501c80315004581051620080141c10207800010784070504007032050310840ca0351241002d000c00e2103601a40811034103c0c1001c040500604001c080507000e030305c184c0d4118400071217001499041548151460b82240c40c01c0403035503a21558100c007404040c9010030600407692206565040390720150004030300c1c440c2110116501c450000319452070354208413508900e07074079034400b02c180098440a0207441a00300485066010307201750f0303042d03070440300c01002910032410401c44405009402294000c4e030b00c1c03008002603120562034803012400f5400030300b8903060034a08061221103a000c4600c16400910040c0b1a032842041e20500d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 337323965 1250 337322715 337322717
    0xc010f02151311030a061a03030906030c03090a080703050a0207050d1a040201031d0318010f0c060b010e0901060206101e18020d0c1e03090c0302101205010f03050120030403 76
    0x20300c030b54030300c3c18101c40140208810b0b418800e001002080050070b8010030080c00300c1001070074003141490103041c0d0720b000b0390000603886642030001074410200300010350341c040410b00c00c036400308607551220052070b844181c0540018100081c2c9258083e01000320702c000f03000a8440c50190582610f544a200f02c5003000c0209108509000c0380540e031194010b030003e80b09006902d2003004000005a03907e6002821103906442d860501810755030160118210030111925952703480000c070713034602d401410f60341503050500c030745402c1e02c1403036450703024903d40648055002481c603410403030300a25882895134072042c0b0882e81c840340714140c0c1015a0b001c03822200308a2a001c110044051020041d00840380445c0e1100d00d44002400401d43c0034240b540c10001c50107040f11203000b8008110107891001d80e01038200b5100b03910030801401d055603166036440540c9009040001e102e5640e506540707083e40882c240001c4448103005214080c418089a09030541e0025400b103218640964280801400a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 337325215 1250 337323965 337323991
    0x901030206270307090e010e160e0403030f02071505130203030a0f0504051504030308070c02031c0c0c06022104140909030409050f01170c0a0b0906070b04050c010f0215 74
    0x249001c0801d540c201c0e081c079004095586460325617102c1c01c0105402440039030f81d0343c2402c9540b404400045460308111003282e0902c141c0707604014031400352460241c0120b08141d911354801c2400c4c00e41c1c0c03015021641c810710070050420007a003141e8040d100041c003440803111040b1502c0006a400101710b07207120031306040c4103c00f1a45240180c0c3c2c01d00441e0b01c1680c03c140e507a141c101e11400090018002e0780e109495a403501c1d110554204e401d0280140000d405500400d00c80702c060314803820005030b001080c5800e801041d4207594180c4242029031202000d41e0002038020f003d21804000480b81c11141010075041a203890078011420445180d11130180c1c0e40180031030b06d1a201403040360041c1124072800d00840c1044201d9045800c000d210b00d840340700310400e941e01201400702e00c429410030000c119414403414a81500f03210b5002c07540903a40700f40100010000281c0c0c1142d041c0c4524000c1024000103003103040003404042410030a44119000359a803038494030000c1808903000302c0c84401c50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 337326465 1250 337325215 337325257
    0x62304051503060f180622020d0f1b0b0705070e130b040c050123090907050903011a1008010303020d1b06241a040e0907260c0901030206 60
    0x55100c0c010700a2150035014001c02c003c00424000d032428001c0d45441c80490100c820700c5e05141d04c07000156140e82c1c8141c00481009801c00000c441e070402140001d0a0584d8007507503aa07200e4140d20fa0500c12910201076410100c41040040444002058030a4075507107402c9070740ea512030f20344070180548030020400e10085081651514002100994425018803243c04c09003040d5115044500c0b88a002a618503c01440d040d4508002e04681300e250411078188401a010800e40c030000619003000c1040603c4900010741e802d0140c1d042c880c142c0d5104102004441e0184403000f49030000301000c0c815a01c0040000076030000d4440300011151410f41110884168201c2c0e04240c01c0c80050841070070000c50000200c841d0b000c0b51044c11a103001120365613540c880d14120803056000180c00343c0c2c020f00041145242100aaa0307100d4040800e6500954032203083c0000545d2000c3c2c8515500301e14082e411089804105000315440102c50341205985035a0000b0211300c54100c12080c1840d1403201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 337327715 1250 337326465 337326481
    0x10b040512190c0f0b040b0414280501081803070213090602070303230c09010e0307080102030a05060a080a0f03050a11071502160f0b070201050d0c03060906230405 72
    0x2014210600c50311194400c0c0c2c2c007802c0208948006000700b1001802c0510000340100c0c0c24400c59046455480301c45041034138029400318480002961150070192005c400380318103d000080710145001d484050030603a00388800141000802040384019580c2984104101d82d000820f580040c1e504480100131050124504c0707000d00200c072401010320b800411400200354140e0801c00200e0700400c0b009100e2000c000100d00c1d40c6006441d1056009410010f69805500c1051003122140c4085d00b210b00b0503984000a6007207a008562220304d0507941d000340403e030b1504a0a00d00105400380080035500155242c0700c528108040008040c8440040e2030700c001030141e113100c0408a40e080598000c41c1d41c9115120340300180b094184d00601580a00066032517440005d101910030000b84181000d040c04608020703907100320001c3e810f00006100721070b035910031030081140c83c49003580c0119600303242c0a8108240d0b00036030895043c084041c0000d440004884c90180301f40c480031a8082041d03164115 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 337328965 1250 337327715 337327723
    0x2100b1c0c090f1b020102120a1503050a051e1f0507030b041e0b0631031502070210050702010e0d06021b0f0607020a02010f030906110307180b03010b040512 69
    0x100140741c41c0c0c1040b03000419000306601c1034660030100001c0c41180c4405803000c90807032144100e88000f000c6c400c4027113130709021540e21031486441540359600501742c4075180d0302e2500205000441d841d6200302c0e0005503802c2070455010382d40d0301c500c00600360841010141d203200d00b0324110b1071180d20396500c0040c2032140710750490710003104040e00400000b004c030003140040e11442110400b107141043c4404041d8140f01d0204c46a00c01c0c05850391114020030168900340c80c0d64501c207001440511781e000f10125104180341440c0074101e1000680c1e40ca60f5105201103c00407440c2034080c04400e10038200541d0b00700701c1c4224400b1080b42d01e801c03070800c10f2402d00002d000e000c04c0c80200c1d5079040c0300c4415004d130020300400380f41c04405c00c0b0303007103a40c991000700e80d2034034042c0c1d000303001450824034107182c00d029400120f0040c0c85902c010a0b08400c03080720413042d8104880c084009007000362030052100404d09810064003042880e9443c642c10201020312611580c81a5030086045d0701d034888042200348 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 337330215 1250 337328965 337328969
    0x30503060a0302100c2f0126010f150305010b0937090f020a0e150c011107201014090a030602030f16020d05180d080a02100b1c0c 57
    0x10311113070440c928460010003444442c10100c40058940403905004404602d10340820074040c1c2c0c04031008007911004680b07c507222400c40701061282020901c05d140c078103038154081e14600704900611071400000070090920f040d621410300d45810014802d80501e82e084413032020081d149110310600046c1140c3e0303501d20b140610480b10402e01300380b01c0710400d414081c00171241d810009010303034408207015104074400c138814100426046031244c955400d200070085e8480340042c413000d08091141c88d0b09070075104d0a1944281c00b00001920608000380501d0b103010501805000f4950808103501082d450010703143e4503c14001d002d40b49610034840c00c81119046507000d032075842c00e00c4e902e00e000c401035041910404480304040c800103100d01d001c1159515044401d03401440324412120065079140d108a06100c444403c11510300103503196071820450051255a62603943d5400800083c24800100903403400c442c03c10a4881d0389a8031a6042c191003180150030300c210740c0721451b1201304081f040e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 337331465 1250 337330215 337330219
    0x60a0c0311010f0e010c09050d1b0e01060e01120c0c030503130c14030106080303040807020f060c030703080a050a09050309101b0c0312170f07200304030501141003030503060a0302 79
    0x80f802502d004545500060703501c28400d0001e0044500c1d4030401d0b1250791756400380c0c1d41c210542d07e212401007103400d0300100100d426000040c0ea0f00e5101c0b000d02607501c900b40c00050102e02080480715555901000760f0515008146003001110900403000f0b100482c802c2e000b6042000200110316200540349114903400d6001c00c0c803110319070f5100c0000500321000e801440c0702e54070f04400020021380c00b1080741c1c403590740005085c0c03a080e4650300f0443c0300008480c1c51900240140910300340200108018042d060003900d07841001c2c5072401180c001d03a54014001c0c18410b082440d100001003000082e01d070a140c1c100d62141440c2e05c1030500704c8031041807020808103949100c2100003404480074006003524000d80c90030705105002c80781901c3c0000c100d088081c66008003c009174102d011650b041c1d40201040c500010055841d8445807000032949640d6091500001410000c02c217092160400b54452104c100c3d207245442104082c140300c95100107420701100000044d00c88c1e0300c1c4140c0e00d014685c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 337332715 1250 337331465 337331471
    0xc03020f15060307080304240c020a081509030405011d0f0406060908070b0301050a180e120c161508040609020307031a0601080c0910181205060f06060a0c031101 71
    0x362401440a07a101610700c03500a004407040402c001c80d000c000c887c10741c1d84540780000807155100540e49441801c001c46410400101c011400603580d2800403c000c01104000303103440c00454039001301159000e40800e01d6540704010401203660003900c0305802402d1030760450490144031000c14400480718402651083c5800c10100f04981c000340c100703040d11890303012140ad076901c80101c0403140c0b1080c0101988400c0362072003003100c0003400301012001c9285450105020745810003262510041104404400c0404190800c02c404100038180403215020040b00388a03140c00281008503103180c850720204840c0c40005000e114194011407940303507000d0101c1e5079490b92420903180e0030309e0a010929514286102107021507101e506c1a070702440180c2d000500d0007119004100c41d03c0389281102040c8514000010040c4800c81200781c02840c61060403810b840c0c4e81d02c1c0090400d4001810851010341c520240100c50300da44058401440c460f04009181c0c0c021410f00742d84c1c0c0044400e070780010b582 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 337333965 1250 337332715 337332733
    0x60d0212040f150501030c03080c0f1b010f051204020d052a0f0f090a0203190e1533061903060501090501020a0209160302090a420c03020f 61
    0x40c2c40c030003520325103004050803400d00064440c0702007903d00c28030016007d00c106103c140701242901000740380304220761084811108010011314200501c003c21403400401c0d10f0008020703545c01101d0b108035142c2c0b601c0c0c5945418241c1c86501c942c00c06c042d0010303018280129101042040c00c04c40d24100c001010401005088004400c020f0109130f208510b0040768403806100313030b030705141103941064440144448415951240100020b400040448000412642d055a4044031910414140449500203086090700c201400286a000a01010110a01a1130701c414410141c41200e0021001c1100ca1b0000c01c180000910703a07000398a060180074004c04442c107021a0103900c00002c807407081c0c891802d145c1e941d10041e40c44070100240650070003489030008030f07040c8490f80310f00700001d09414010f0401e0f42400100301005c0058110b50030031811140c07804500c600c0388a44640480b800c110040e1121400300160b00741c0c50340074a240003840714200a0808248c001d1002c202e1414440341111074400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 337335215 1250 337333965 337333973
    0x302130b07061803020d0c020102010617060406060b090a0306020a0c080a0c020907020303010b0706051f0608150f010c0b06030a06110a110102211b031006081014060d021204 76
    0x68081c0340100c1c2e110b483e0191041002c503d80c1e032001e0b03010740c042d00a041075202404054030b402c0301c070450480c1195610308000c00ca100500c0381c03403000410b070130006102a103420705d01001100d416401a4031295014480b560b200c0e5502d42540e0f060341d0b0f0081000d0b840f44203200c400c1d01d403800d810000918404001c04d1110110340c1c000500b0038400d0003100c0340280b54940b441c059071603200c01c0c06180c8061604100b01400b01ba819040302d42c0200d40302c400c00c082d604011000d000d4200998000e240001c05039014081c0e0086070b840c0d111034400c000c840043d180c100d0f001c0080e1080d1120b081c0202410b000e00d001410303540e0309010200485400110520190b14800c3c201107099020007100750124034000c400340c03100e0905200350751011003120b2580c03035051201600a8201d000082005a0107110000107585041c070000c05140100e8641100020984c2042d001404600b001014141200780740c2d002000b07062410840b4040310318080e984250f0741d06044140d440688a0400c01d0070132411506d0a1100b00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 337336465 1250 337335215 337335217
    0x50307170304110a0308180f060a031d010501050303030403200a1506140901050d141510080a0b070516080f031515030402010e060d0f15052e0302130b 66
    0x654820407030345409003d42000c211142d41280005048808181b010310b1208181000758000d0302c5005010802c1041440009280c640c0070080c0740c400a52541c6a903024408071002003034082501000134082e80d810140403940d203002c01000501003000e134105e2001c4c03c6100795804a04d0a083c0c6085d5880e1f07610504000820307034a8068100c2d9480c1c9414400a0452045e40082c509900020125000d6034645010841c0c000c2014100303407110100d0307140705990841c003040348121028461405a0f850b240c04201700800300100d81c410349141d000081c0200000d050308400342c0e03000900c0e0811907120841c40d5100489002c42000c014810000055130f011107207400c20285205030781403040356001201c51014041105442000d000c9400c20901c0800d00640c09181c40d43c03444a8050841800d0a8800726110213135009065000c4502e1342d96108509889418000e00c4080c0c00280ea8a2400e500342910300015080c20b591203a48048100d8600c1d00c03424800d0f012200310082c00005808540c3d01e5203641c44179 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 337337715 1250 337336465 337336471
    0x101d011214010806071121131e0f051309030905030a06020315030703080d0b1306030b06030c010503090a06090807020607391e0e270115120503071703 66
    0x442c402c1302c1c00164928411b101c125035001050015041e046841040c03504a60f0650090111184040c044000c8000e07154807140b00500814003691702070031140600484c05c05103600302c02c0d40d29400350402d009685071620b44801c1001c10f0036000a842010382400c81d04400d190700802c0c1d00d0f0144090a07410302c00290065802010b0100180031080c00400c200345e5115014400146409018040c0c0c0b8445441540042000000600003042089002c00c059040700c0705a0000c942250340b15040c000c3e20b0804000d2641d0840007820038600c0e50924440b120b0740c9140045000f0000c03500ca5452800300180581540e40d882d5010f849a40c0302c114525040d1000480a075121b90342d070045100c014a06000b5024420b0000030340c1104004079030519203402c2d914210074003d08111607070f0300c100060180c0c052400074410030007034548030014114084442000740581400082980c1040c1e1002da440c2500741004c411250710314840d0700041100d1030640d00b5409603840141086007607041c0408a1080c1c6401944 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 337338965 1250 337337715 337337729
    0x102090f0406050a061404050316030501050601090302011b060603080706090311060408070303050601020102070f060605010212030f070818062d040506010e060d05190b06101d01121401 81
    0x1403520030000e1100301e900c64450143c0c03200c0004010408140030b001500514441c280d07200b480c15440b0404686400000003030282070f9202c4c0241042407103804e210300c40d0001401d00e441e4001c10710717540000b0b14030f052401d01980b01c100800502401c006499100800660384002c50b6903c80b481800d0480003060b030188250302088036464901c0ca401c4c2c0118816104540c450143c5043c000e064030100c004020040c50036040d5903080040101088100354000d6015220310004200d090811000a084c082c2030200715051003024010b0100818684604690100c0c46207407070850343d41e40800382c059030b0240c1c080c180954050b020030301c000180e00e4580c4102c45d28821501b500c03201c400f115809114003040b11301401d1a00100010b020b41141100da90380c100c90010321115640c00d194581a041400044642d0301c403012402569040100184030980e020401f2641d203401d01520000103271000e11500020f1041038011800084268090110a000b6145120040201c9049843c00401d4034000380580c030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 337340215 1250 337338965 337338979
    0x12150612010f0e181506121006090c0c020f090603010207020d0b010603050f22111e0a12021503070302120906060f100e06030a091a180a030e01050315030f010209 71
    0x21302d0020300c4820286125072110001c001c3c103001c1c40f4805031390400103800a40d0007030040030000c0c0004810424980c610140060004806141803108000c035000101100d00f40000304a0310340240e51018009601460300360781030304207540c071180007a0081c81410f10082d807060192641e0024800c401044d40e051340e105480400c010745408003815141d000c112074842100b0340c4203070303200100d22000c3c10032a1207500c61400c500c020a003040c002107403811031422001c13203103c0c409003501d8940f91000c0c2c50002004800c1c0210300a403043d4000c0b460a840c1d4100c03280b1420780010104400c1d510981c12030300a0104484540e80c642003002d0b80c41d0300d580099400e94841c8241503400000c52800c052020707840e01e4140c50728014000500280603040c0c0000b007100f12616900d20030b41011900c41c60308808038081242c2450351601d026149410206200d984c040e445510404030407000070741045084205203001d0038659203954400c4c80501603440060101c0e03802d4052404045680ca005402402c3c0b901c100303d0b07070340f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 337341465 1250 337340215 337340221
    0x30a061d0a1209060c1502091311070218060102060403050a180f060e1504060e06090409030207030201020d1e031805010908041703091806031c0e120312150612010f0e 73
    0x44071810324130540074008448880481d00301403102e47c000d00d29a000601280c404c018078049042c00c0f21448803129000c14000030709001185410420010104818a201019400c0840000f55030340c6000b00001d040c040700180807803441d4042c440792809402058607032a551038aa07100c80e0041d00d000c5c401c410202e046880190030728500b1380030000c034894141000c542480e01c0d150f4115040d400e0b00d008103802c00340c01c0040c45116102e9002d040551070098000f06145403961000a00d85160104400200b0468040e48003588030780741c00e01003541c902c81c0781c0800c0c4000c0301045000c8042d000c5800405540c6410707541020002d001028008980c16000d26440400507a4a000d4583c455968013540c80004040c00460420703c1c0e40758503800c142c01504445092402684501014500000c0c110100d0000c0701d03004540d2038000784d5440403041034009941001342d441c00805115030040c1c101443c2803a00a89525203440b03000a0fa0301e140b140310110420755070340391501814803444d0302403480108108000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 337342715 1250 337341465 337341467
    0x30412030305090c0d120306050607060911010c03050406030911030607080a0b030d02070504090c080f01090b07030b030604020d15111e0903061801020f0703021b0102010b030a061d0a120906 83
    0x440c480025014104c41450f021720b80c3c0301804035040030610014180e8805020031140c58031030241400911510700007a2030070752420301103210001e08594034100b000820615001a0f801000d0380c040301d101d8180441e682e03c4525091301c0301c204604000d501442518100122141c0c01440540a0034104a04001351441d0780c00785a12800c04c40b40c1207001d85d00600040105003842c5c1d0011442a0044211100198a503000e440c1410070105048900d40c0d110395520051100030120b16400100c10b05041040203182400700e80c0f1860014070183c401c10301c0f000e00b941800351058851141c14462042000886034140800c802904000002d0b845038011402c20828888a5001c40d50504801001030080c0c2d981c020031030789141c0c0d142c00ca02c0b000c0d54081c03100380711592019024011300791281e00982012451203004001e09280e0540b01411a810300c0404559502c021032000c83c1d02c1e800c503e02091001008841c0d55035141503a468020902c41c12001c0c400344030070354040c060320030b40c6540c0d0105800e50fa088 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 337343965 1250 337342715 337342723
    0x60d0c03110f0a1b080c0303011404180308090109050304091e0501031703070c150b011805091305072c0108010e070b1c11030615040b09120a0503041203030509 70
    0xc600c449030030400c554401207016402c0c280c3c503507244c203a40c0303c1010b46650325506a84c005010400160388088010300c8810342c0702004030a840030650b01007080c410304400e0203c0070303000c2000103401d00c0400300114041c1c0ca803c0d000300003040e802c07d00b02d940d59a502c18043c030090081301d605003a00c04d5084000c1080352140c1c001c140c1240d40000c01c07468850300c2c10311403a80540c8040c1101050044800c2c0b04c0001501c41440391180b859080d40c0042c020007585c0025100292000660910000c10103061010703a842c0c480b4503800441d10940441007481d0380c43c03c1e5282c46099003000400303582031a00c590910007100d00c0c00c22404504c80c1c00a080c2d03642d0790003181c2a103004810070768081e00300b003105000102c1054081c11409511902072200c5c03050003a40d010071600107075140914074600008010b00b6050007500c2c00f07201000201d016103401c0c580301c200c205074002c00d941c0340c1c030940301202c00c08180441001b0350f01c1c10365001820740381e48554501001c035203401c0449085002c2400c1500080c06034030081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 337345215 1250 337343965 337343977
    0x310504020702060406030c1707170109020702030709050a060503010f020406140c07050f180f010504150f09050c300703060b0a030c021e0c030f012c070302060d0c0311 73
    0x35104a044c541010790550252180c2c064007010446409221007441c6281050380f40161030a444000044038400381c03001080805800c0100c65900400c68840143c40009884044540c210000038150b00d45460040203003c8a5100c02d0741903007051016001010306900a20841e02c4549404d141e10000300d1000403107000b65807002c0300316002258200040d09003015240d411420007042102036000c80c80d03144610100c180c8202a21115040040c40315052600c11400c481203980e21643c80e0902e0b024005a5084141c060313003880c2d03034583c40460f0604400c08180d130081d58146031010203d2600003c4561004100d03c103107004680c01300f0100c0d070300c540688101c0b0180c1e4100401035241013440c0c18240c5c06030002d06080e504510a81e10540b0342c3d0040f18a6141403044020098140032000c101094580403d00d0900c102c0350b4035115102012650070710401010842d407501144140032610703140c41c200500369201940240b030010310855805256480600b40c0e5a080d03c0420003911940c40c40d2010340184 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 337346465 1250 337345215 337345219
    0x61206051518010909050111041215200c01181203050a020306060301060c0309081903080f070e10020a020303070b010801050f0412050903070f031a18071208310504020702 75
    0x40001132101c5507040e00880182030007140045a0201941c005a505921581c080360075110000d50032010440d5000b001103124001400522070050a0030701403101440041e00c0401000c0c0000315800c6030b1900307401c0201034840001400003520028100304a0304c030607100710000001e10380000941059903500c02d490041134054842c0b801c41c0e08001c2c042d1940c407100030040c0c061200c044800210000d080066104500d440000316161014500d03010b440014041e10711012b1080010401200c1c0c0d9000012030500ca008803100d4000324070700003080e03080601181e80a07401d4000003401030180581980118102e81e9007078020030035691400384e03490a014090768001c1940c264980e003894034920413000f410488000405841c03a96175503005001e0802c1060380100e8036455103081510b106141380340c046a000c003101c141c2c0403004016004058032400780b8040c0326500c0c854050000c0520051100740e40e103000440304d6801180108640d01001101e503126100749140810f00d0200b00360519000b55181c7e1540 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 337347715 1250 337346465 337346509
    0x31e0703050a0c0609023a050604021c060c05030402010f0c030e0405060f0d0510050f01060206061017041a0c0708070209062b0303050f0112150612060515 68
    0xb96031084900012404080d241d041d203d002407400340c3e42d00e0b461850051102510180d5a000b00115030038154940958070b003810b952500003002041020926580c056411907500d9604c0510000c801c0d075410009102404852410781448030301500a0000c50040d4000d8891004650200a044890200c001001800580b6000803401e0030304040c8c2150390401d400501030b1a10007e07800125a01d45404103003950036070301014000e03000005521403c0d4004030200b02802603036050840107035032100081c003010b004d241c0c0c070810181103074407981d180d440306404460310000c581042e0600f00912103060800e029200104070118140564020844104503032100155041910a030200310007044001d046035040603410341411010340b40032120260850103000f2801c184c080504000701120f038014031360203002c50060010b225050710540034803040340d4402200b21030318950030008000b80040d5480200302001102840e401c000103504524401c003401d5003030420000a600c1000500405520b20b503d21680e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 337348965 1250 337347715 337347727
    0x906040e150a02040b0a0306180203090607050304020a0e01140310020405012312070c06050106021f0507021f0c14090105043c03020103050708040309060e01020f010e031e070305 78
    0x80d001150b0340404101070040c20207648511411141c1d1040c102c2000003a0755440920003851103c04401485030302c1d403030450842c540042e516661742000760200040c00408400602103640d01081c0c40c02030480700d0410103c95940725000b240c0440f803c8402032003409461002880c207115442a5021a40142d4a00c03080542c0c0089944442c07a00d50440541500c04020b41100c22060081c0d02d4040e812a903103002c604075031810404d00301c0b101030304004119000031803e50701040c051041c011200c0b5052000060b40e848092080c3c1c500741015042000103800b40c0c1801090300001e51090800301f126440c0d020080c0e02c080060385851007010103041c04240180070900184004034010303a0302045440c2e03000680c5507503007a9005110003040541c0509106034400f0320031564580078483d04010b081c100003009050a41d0090285141345c000c5000b00300301d50384240b005038820410411080346490007000410f0b401c803001c1b84c4031351103080c0503482c290f4000c400700e014421001c111518290190f5929040c0f00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 337350215 1250 337348965 337348993
    0x1050607031707020c01020d031a01080a0216050309030c0a05030a260409060501110102070213020a03060e1303020d140d051902120603100207050c04020c2a0906040e 73
    0x40c0041000303404121080351019110091580c41c0c90042c88241c00801900e171085000901c0c1c10828608031080600389000c0e00d82c00c000701c1c282c0fa24080000d00305210103a5503008082c0082c000d00d103a10500e0031003182510140900440104401d5109a09444500300d1941c00d00120140074801d250f0181e00c405c8801000c07031040a00a803041c03808505201010100346c803440c0c1250031a0300300070035490350f54108000a40c1c0008603144071006000003503041a010343c00141d40c806110600e9540d80d50002442d941c0030348241e001d00c020380178011912520b81410166040342c19801d0b1002c501612611103442d806c54010100c5a0413005207040300c910300500c40304098040c3c280905a00c03091401d5099030300c0d030b40445001508100300501d10324900c034508081010300e002e40004440c120148100545000b18101203128980482c041d034001d0781d101c00c41a0240c0c40c109810103150043c0311007607a0004500c0007000b00d0321190200b10f03107492094484604110031102c1112043c0c1c101d0b4080740c448008a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 337351465 1250 337350215 337350217
    0x1061404090f020312030a05071707120b0a0609090608190344070f0c031b020604121502030709090939080c0612040c08010c120f050906010506 63
    0x82c400c2180081442d943d50111340341003442c0c012503510940100c02c021688109211f883c1c1d10407180d2900303024041740725883c0d850a91001d4480b800700003052141d00e00c0302015411580803518080c001a09ca1071348c1da00e00404c800314500442502c24242100015410000940c07001c04030b21031808820950320030740d0141d03049590024580c402c210101d03002c001c03814085d100c1020600c032041c000d00d0803e032081204944614024143c8080c0f244503003610800c00c0e440201c030008181d16051070b0804050700200d0f0480c0d00740350303040203501c85000100824030111600d85204111302c58244000761342c0b00ea03041d440503400202d03020b80005a03031600420150310a40c00c007500090182c0401804094001d80589007040c00b245600c00140a0030841c01d044c60328040f03400c0003014180f020b09a0401e2000c000fa68601c69042500c0500001d080404c00307001d407000400307000340b029600030002d0683d4100007510307181c1c10f001ea03d10218585840100034941a0140f03900c10030400b800380505030300b040100406 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 337352715 1250 337351465 337351481
    0x15050c0f011a011b0503070809010e0102010c050a053f01091815020c06180d020307020d0602030912040f030308010605160209090f062703040e06041808130e0901061404 74
    0x1403030b00c4d81d00c24102042080c402440d0b00c0e030107a20404d5035045581c0014010038404640907045a00d8152000c620b2a0700c00140ca0798210145000c60740c40d032540007243d000007921000c1200210002002c00d5907442041000d80244070345d01d100ba141d60f030341d89500100b01da211b05500301e007030302c0c0c00041c540000da90091000c1d10901301d4000142415034060415180c11400c41d5400d80984561115001805042000d4801c04069100031442d00c1510b1f404690642900c0200410312a00031011038141203082c0060300b54242c800c0c0c2c8851b11140c0d610a81840c0c01010f100580101c0d80407400417504900c00c0d0100d82e0b00c402c1d030a1051020605640c02c0c000d60250042240109000382e5070300c030074014028010180907050a40500030b00f1181603180a540d111700c0c2031000c10544c0100420403108150f0031a00350702000460b00003c1d0700340851011010151134090040225000284100804543c0301d135050a9a0050441184568809440508903070707035070140445103e80c2c50302c400d07020f141980054034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 337353965 1250 337352715 337352747
    0x50c09030d1d0d0f0b0414010e0a1709010309020607200103050103121202041d060a060305040201081302010c02040212070e0609240d02040602061e0f0412030615050c0f011a01 77
    0xa004c4161320f03100e0000e01c0c140e40455454645125641280c0001d0050b80103101c0640c01802c0b1036940e590750010a0041a80a0340c032004000c1603480c941e81c0a40e00664445401800f1036036103000d07502d001d0311404a662083c00d01540b02050003040755109100d600c0c10380303a10a00300da082d100d0b28081a9001901c0c2c10500004a40810010480000e1180c582c2140c0fa940890781800342040d03c20444000b034103400c0703102012320b42000c10000d03030b03444106a60046c6000042040b14400303400121003c801c18034020b500203000150010001c00f03500c42c0180310f0080c03070369640d5850050a0810201d4032600310b1450f40310700443c0490001504003507100580b90700c840d803241e180c9030400a00704c0c203980242d8002405604188d081000c2100c0f0180340b0700c506500f420030091301d840c04074111207028101520190120000291418a0f1402580604007800b00001150f1342000042c10040c5694051002003507030b0302503904180201001401140e4041841c800b030401030515040046910402c5291259 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 337355215 1250 337353965 337353983
    0x7050d0e07060804022806030b040f23040510050712050702071a0d15060207030506071107060509030f07031415010311010309080712020105060a05060306090114040906050c09030d1d0d 81
    0x11303209240086c582000340325984000ca031110155080004072064014464002407c01e21458030303000d200d00400c0c0c442030141c0c0030171801d1b45803410710300e107002c400f20100040b10b45080e05200c445c1e9089a0f52900c2011001c200788001c0d43d80150403a103844148c4210381c1141e4000500410880c0c4241c040c280c6110451000039442e001413501c0c004c214070a900190158006440500c180841407000d0790b0300103e903091841e446803103410410b40c0c5074003920031001088000b10b1a50000e54042c80032400190104080307500c01c0f81c40c0e081507081e00c1224580c02d0124401c10204e25030000c0200c9115040300e81046013804040f03045001900a0000c500741201c0001d400c0100d64000b83e00c00d610400840001c2e80002050301d4080c05001c10f6940e5a04590b00c9043c0910412419541c0d6503003460542d01c1751100c3c0d003200c140880200d000750a10075801041582000d007044684224007001e0103c211040301111160070602006481801030340d4001500b07050740060074103650829007240701c8581d02c204051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 337356465 1250 337355215 337355269
    0x803190c0c02010f1d090c0309071a09130914011508010c09140607080304030f020d140d0c18031a0f011217040b030c0304030e0316090b120607050d0e0706080402 71
    0xc006c2081107610144550001c8144594104100001000f5200c03842d4010840709541e45440d1282c06a0100e20748140301205001c510f10301b01c1d800514226611541042121076840c0c0c8190191030703610920002c04980d44e07170018072920140595120213000347c44074102e0604200e50f82450005102c5138a800a40800c2424000380c100c800840c42140a90b0b229607160304088002070a000a000c0d0610800c214008812032000440d8204d40d851b04072940d0000740e002d1404801d0b540b469560140c03119a854694000041c04030f00c5602caa40d03403400921500003640e5990209401103001e000d11002e0742014681c5400040c0d428031079182c0054044146401d081d41c49521107a65401103407284036108000c0244410141c00c4400c000a504088024180f22004500300b000381603214070030500000d40354130b241e15903521050b088000c00b001c030380182c400034a02504064515400b09074500401880e00c1c0f110011081c020030341d0780a40381c40d55944080c2d510b40d50200840e2007010491805008540c2c000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 337357715 1250 337356465 337356469
    0xd020406080a030519050304031e0c02100309020405060a0b25120e010e03070e0a020711040c02030301050901081c0302030712090b010f090e03030c0a0207030803190c0c02010f1d 78
    0x451495503c43d0351096502d40541401c0c0da00d111302004084e0600c00300340103100000c0c0c0c1084640b84007000113848880804401d4030300326031040001c903000c3e4008154902d82540540e064028640d40c0d070003030768248510340b6175506120070194148640188541c007400300e0b0094034034000360341001c0e40702d0280c0b003c032035081520303040a1500114503000104046628002040d604042030542040c0100d014008251400821001110f0002c1080c10be0541c0000c00744204518190401440500944104030701e17280c0410195403a0700030300805214240c403400004520100003420421642070b030400c81c0c00c65885020980107500301621400600c185540e0404511072036118120b030480c0541000c046551521001042160941d001340f034540d800c1c00e03801c005854001085071b030803034080940a9550540184104d05019851304001c2503010000140081001c1c41180d0790300c148a80f01c0100080c443c01c09080c0c0b00014075003c000e0100d50089251241140991045200003400c0c2006204034410080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 337358965 1250 337357715 337357723
    0x204082803112e1b0905040e0f0304090e0c190303080c070209040510150305070302131e020a1d0121200c070905040218071407030c0b0c03070e0d02040608 68
    0x10840d00d03042d030403015082080c007540603007600ca4418184c0c5500c0c110b500a042c0d010f035014050081d074030f641410810100801030703543c021050304192515980c40303441c038202801c00a100007201d4407038040608120719000b4582a181000d0045400b081e5103181c1c1c0c10760319110010440e0f800c4d40e5040c403d00d0090703260714800610803485140036084091143c000a011104001d10b1041d0400d4021428000100b001452009807078044444044107003160300d103078028080010340b40b200c00d01030f41d641c40080c100c10340142c0300c5100562540d00183c50003100c000c84070b8a1981c0aa800100382604092910501649410800415003c04034803400101460312111050030341041c501240002c00740880c1c04240201401740000d900140044d0805400040030351220903840c40f0503207083c40c04034034a5030080c00c1941c8a0f10440c003541e80c803000e8606000d040b6818040c01a20107400800001c0e0a060019040b03134824000354079241072081c0c6c5141481006070804204a0b006a51a00041a0000200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 337360215 1250 337358965 337359013
    0x3030f0a020616050301050a0e0a0e0d020f0f0a0b01140316080c040f02030105030d0809010209030a030801030b0714030a020a0201060302030102040b03010815090a020621010306020408280311 84
    0x81c00034080350402038105003800c20300203034031000c0200c1400144000d036500d9100100f125900e25040ca00e45d15840301c0c01000308540c42e441032062041410b00d5899540104219201c8402101034680700c5001c400481c0d03c500c21181c009180003000381c014440e944100155009890000e0211a05000b0b82090010341b011b035900011401d52041003103110034a05401040c0411140f94403e5040d5450000802d546810000262091005680014402000035810b941142d94001c1c00c03200801e00390f050160070501c0a000c14cc03020518074001480e494040c0038a40d000245c07200d003151655948540d240001d4001600c04001c5540719600000980c0d4240045c101412034041a0356580d4500a0b02c94034022a244103580ea8a400c081040407180303003c940481d9407501134891607505e10240115036a84080100101c6144007030400100902200b80d001d4019945074201315034030b4030383c250700602e80410305032a00c1843c01022502000040d00ca030b1809840000210200c840b00d4004910300100110740c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 337361465 1250 337360215 337360217
    0x32d010f021312020307140d1b061e2001060905160215070203040509040204020c101e06080319111903020d170a0b0a050d0b0604063203030f0a 63
    0x2c81c0081c0c80550004a01c030082100409403181001941c2c041390301d4184511800880e400607589101440d1075601144072071aa109071250000600482030b02548000b9000d1000014460440c0c8003413002d01c1c004009600c00d440d11241c42205860314400072103803610032450044c0d5207520000078201018085c0a0291402500410709400c401d900249007101c403803c0005004400010300098030307004404c8909913001a540d16419545500104010340b19030410410b15104a03500040300803e59807101c1700c3c0d11040c4c482d20850940c0300d049202521001d0185031f107260800c20680404c07007030707412081c12071044600b028455056102001428170402200711807821401c0d41a1008040d0b06004682c0c0c0b00c00740381000c510031351091001480f02c40000385851111543ca1501014540e00c0903295001000002c0c100041c078001d030700c0c00f00380494040d282c0500683c02c20001080f00c0c8a01c44a075640c1d20039049441c080c00104540c44041c01c0200101507416010400c220007840d08864014a410015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 337362715 1250 337361465 337361467
    0xe0d0206150901030b07030902010302120412090b030121060608070608011a04140105070c150c02090c0f030609101e03050f011118030111041d01060c02032d010f02 72
    0x7050081441c41400030700303031512400c500001480041c4210444030341150aa1400286002281c07005800900c1842050f074000c400440400040040c0c203216288014440d0b9200b050303440d0385042d102003034042801a4a03001d01c00316180c81c29502040d80d0040114025031001c0fa00795640e0a41302e017064002d410640000d0351590060141d096541605880a0541210103183c0303480c1012409504050f6003405042040004121090054803609407024007107214a00c9940030900c8006444030f58055000c80c05152a94002103030580081c0690708044061215185155154000c000d1140d20040201e124215004c0000c140030700b034135000162080162500041c0303142541401403611030702040059403070b810803c00260000d1140203440030905102d80d24409440c01c0300c0002e024011402d28541595400f0800040c40046480300c0c495001d403011502c0010303600d0300800c8650071003403c0060341640c0b0140c003441d0541209180d0000705c110710207030112800b2000421030f01b0b4a14941480c842c0e950 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 337363965 1250 337362715 337362721
    0x905030909090304030c03110301021207081006030213090e0703080307170f04210e120109020f030d0c0b070c0b0f0124081b04050a0608091011070b09010e0d0206 71
    0x1031148981c0d8119075104025070a00d031450b0303609108a00c02e400f005040e03144056000103252002d40695450545040c00ca069525007101d0081000c1400c403000c20345522480d40008580d4001d208880070000c4600911840e1030a004108001d00742c039040048092240041c00008113000780040c60003102140d840d00c0ba40300c42d00c00340382c14040c00508109034020f200c20500000511010540180007020350946000c0c45840790142c42a940d48618903400c65021000010400419488241618800c0301e070402a10040c1040c9691004903c441da400b2a015090120101d03843c038410960001e01c615000f4012030b900e94803080200b006684e00441084d4000040c413810070442003ca41d02c14940100d80903088550318010041c0c0340280c000a07607400050071003039404c01100704840240c40c0240078000e295940310b000411110084605071854040d2200142c1d856071070307009040042154000f403038105012501c0b40907600402601010141d035070b41c0c164100e02030302031000c0d01d11000541c010b004545 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 337365215 1250 337363965 337363969
    0x604050303191413060605030115090c171f03021e03060109050705090613050a080604050120090f0118090b01110312011a04091415030705090a0f0b0409050309 70
    0x200003a400c8103007070303080101e0b88560f40344402140d90300c54a098040c510007281410302c000200700b140c00440c0c242d42801e980032403141100220f202140c0c6d000008020046250717074129010b013244045a40307480140c1001c0303030071403c0b00700d1418052204050a80c200903501c0e40090007040c004c40801504840d41c3e05681c0b0280340c1070100900500b2505020301492800c0b4134020b04c00c1c81048603041c46450040b034540d00c3d491003440d80c1d0001e801c0282002c01c05030707140c1400c181d890b801120304454660030a00003126103400403003051a0ba06404100908010300d100410a40004101d0700c46d0400c102c104050001215072018180109800307040040c4a4007245d0005155440e2030040d0410350307000308203a040141c0000007050440c0e009943c070100d0140d40d50f00c0079291303102c0c0743e01841034a4101408403901049204185000d06c1c145805c04515407174000c24992128100d10039907501c10071401c000b030304480305504111400f000c0c000001401c141200e0001781210480682a2019030010410944078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 337366465 1250 337365215 337365241
    0x513240f02060601120e030d0908091f080a020315042906070c052b05031b151506130806150612070507060f091407060c080409020307110604050303 65
    0x503021407000d02032501e415800038041102d01c0511888403962030001e2001080103105a41c00d9042a03c0c0c02c0c002540582040e5030240c1103810058403406680c102d07802a0030a0403240900c0c45890b0300d5031201540c450008000a400040080780380407004103850b10503903200e00c02d900b2410360f9100d00c001c0c07441c1703491940c0c01600441008240181420001c5070007007181f0030040003c071001203400f44a02e56485d89608505540c0303080394451861211813040421a012000c1d0090004002c5c070007001e8050011400c2d03485018405c002d40c1d452280c808550100d81140700e201840d8406840b140c81c100c00e0000007403611400381d01c42d00858110100b40032040300f6848140564541c00c69207181008a0b014050510780006400c0c6001d01c0000642c000c108030701500204642042c202d010002e03442582410200c40544030458074a0707008582011803005d01880c00d020b075240e0401441410305003030440c030324001d502c00342424082c0480c84452424202080105c0c40c030a49c8680c6c086d544900b4201d10080c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 337367715 1250 337366465 337366487
    0x12070f03050115080a0e0a0503160605060108040b0402191d01090c03091e0f06110703020f030f070f0f02030303101e0b0a050a0e09010801060e1302090601051324 71
    0xb182d51a08240144d82c840c030b110b80c001c42d4541001a400d082c64a84a1034202030980040c090301000c101c0f220038041070081e1210700340c0a58400c0c07015a5074840116807000048030000c00b6204030602003000341c1003403158403050310f5210a118412546400b13454041006004040f60750644c081c00522665406010384135000c80b20b820140f2400c8810b0382c844101d02210350500344161401d04c146028420f000080c0a21079400c10f80401266815404648039944078100590243c41080920400100e00208807444101132040d1241845440d0351141441218204191a1200e50200c000c016136000d0004501654105001041403843c7c901c0c1c0043c01c0610130851400000503d03c10042200321000f1981c0610040c41d2007030b030300c00c604103064481e14002c11455402244d14000801c0d111070550000e001e5030401181c1004a560b20b80c2d262003d001e40c1c1200a41000600021680e503500800c060208030030019612045262500c05e2440080b40900d0031400c02c91584500c00b0320b8541102007541 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 337368965 1250 337367715 337367729
    0x230109021b0c030312071b0303020c2a0d03020a05030d050103200109151b0501150f0b070f170307020a12050315090a060504051303180311011412070f030501 69
    0x1102c0e000c2e000181c0c076805079402000c0c5007100c000009030f940784100c143c504d1040a12011403050b01482c10000d0081d04035010b540035901c10a0070b1078180040b0b426416412900000d07081c1e40000c01501031202c808a1044100d05500c650500400024814400380c901400109000240e562650910b40109046039900101018128040d05040c1c0d900070005000c3d500c2001d520303041240700940840e074002003002200c0c039811280010710104041900580f950000c0307516404003e648411888800880b1446142c02e1080c0c1040180005104001400000c5001e07621500000410317660441059100702c2d1980300507000155090304100301d9410300310640e001403514a046141c47c0c448840900e4121034014450500440010a280c1040c0c0098003d06000740040c406414280d1108503002c01000c2c0440110384440d402c1e502c20404403440e10110b03178000b58481c1c0034611740b80c015601044d10364500b92a0b94010020440c040c041003180d04d0091601d41c3d100b10400c856810021b08440041e00248 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 337370215 1250 337368965 337368973
    0x216080d1a10080708070c02030a201e04090813170d080432030a11010f1404150209100e0306070810031b08060709061e080a230109021b 60
    0x11505500183d02036100c5a039080c2441961150030042d40e040c0d005600c000e5152060415810420106603001040d0b001040c00180310101064204081c0c20380b0455065601404100b501089290541140310102c1c0105541d07454076201d003110204c1c80c11141c02610b8803032031840d0000c40c119010058110700b8411440c141c03170641000d40d250100c0c141c0300360107208a46a4005a42803689260f4001509031080004603a5500c1d43c40760040c10303c1d0011480902254601040c1c01e204c0c950600408902c80816a03441c40d0641d03c1d41d4a41101e46004101002d07065030078060b405c01500d40001e0300010000c0d640f10540706850311400c151602100074170740400c020f0308400f400160000b50701202c082d07a1344500030040d0070303880f4a110f02071003425600103055031043c0310a1044030782c0c02070400d5041d41d103d544c0b0346c01341c00000c0d000540503141c4800c17000001144000000c4048946500528000f40010b4003407550154404460754000c0c001c0c0c101c6030031540e001540302d00a000d88001d03c0343c000000d001030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 337371465 1250 337370215 337370239
    0x304120c0f0e0a020a09080d1d0306091509031e03041b0e070c030203090a060c12090b34050c1801030b07080c0d05040f0b0711100216080d1a 62
    0x82c00d41001c000d4841000075401150303800329603015100c00c201600100040310300740692004010309101403150408880700d462481e0b02c543d4100030031440d2007405040014240c161104200a0b0000e0000340402038901040c040074455442c0c2d2150701341c985002e826903503102d0400707051103920407a505604085084089504000c16010028129404903190922485196860406900318031030b41c030304240d100c1e1100301b001c100d2035042074030003400c2c074010301d50744a05121060301640ca8800d103000f03650501d0009e222682807038030026104105680c03800100b06460011040901ca1b81d134100e4000c603400d403c000c500d00c030705040441d403403040406c00d80d645410070351440d2100140280e0250030340041006034400258007a0010045601d9608030103800c100c82d1a081c00d003001d02a841c80300032201070662801145e110b6201d0320721981d641440350040c0010360702c1958141c0080d448501118102544001a10301096103c005044200c07144100425881008030500d1222150b08007214031410002c448 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 337372715 1250 337371465 337371479
    0x30f05130209060a1805180a05150621150610050909060604030c03050624012f030f040810060303090e04050c0604030f0308010906080a061d0304120c0f 67
    0x19003a40940645160352541c40e1500450140304440e0001d0b032241640b042c55143c0c4107060760100c1e208100d0030400c20164000c03800e000b61205c12098001c1c040f80d0025444801d075402d5000c00c00d4026100401004106a034041001041c010403d4501100e41080c03039000032a081c018411640000c08858800d040100c16001070000e0081c424228040c86104000544e5612500708403809149c200d041c0042450740e17440c0403079031041c1c210f540f40d0a05900c10902c0341051409201d400b10320030140c68030000340c0c04c001c541d540401416101c0d41d0f1550360a003540000b52009100134001404100102c50341d03142006003551401c03040703200e00700035145421010004030703500402c52002c3d181c070134100714915107981c1000d41c80d081450b40c1040d88080004cd001042210343c4804d426a80d11035200c0288a82e81c841c2003808551041c821491240c0001c0c5096001500650046840400880b1100f44280d41240c110f86140c0054102c400d040c2c101c6881d071800c0c021000070403001007a500c02009103060038101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 337373965 1250 337372715 337372741
    0x3103020d15051612020912070e1b070b13030c082706040f05011404050a060306060e030c1c02060c06040308010f08030307090302120f10050a0e010207051b1206010305010507030f05 79
    0x1307080307085130398040f40809031940d401c10006003407400c50b011541042c0c4c542440e1200c10000381d80e803011080e551000d400000385588266680c440d003000f002c003e10340d00d108032440d000038007890071000c10152001d280d0010f00741d000034101580032000d4040b8003094400594554039070f2a43c0c1540700701428402080b4000d40d020295058030000e19080760440010382c000041c50060740c0110b07500c910303074840c0407850591651209088401c142d8404000400c00d40906880ba07413480307213080c0c00c194190883c00c0e100d4480000940b40c20303c041d001c20320740301508a00d541400005d0750101e0002d11100010044803c4007036034880a042d001c00598694101194040e21038080c038440207024000300360078942d080e43d050000090000010f4141c4e01c0382c040502c4600020001212160031052801c4503800d0110414400d813040c140d4858001e0181c5020b00502c01074030030a0080944d03002850425015484405014650085d8403602c000304050906080c0603080e0f6012000c2d0b0f4218600d41010070040c0e40b1030309 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 337375215 1250 337373965 337373987
    0x70e0430020106051e04150902030405030306041107030f2001060308031b1801080a0f0218011202070302070b07050705030708010c17090a020904060609020c030714033103020d150516 80
    0x581c0028584a1f021000701114400da0190704014804002c1000340f02000c030085114800440f000c110229669481b49118010388134094001021841c81d2040d29000c0c0044818002d01c40e0352124031035030540012030940d440d41d0001c80300070030080180095060010702c120914142004c4950038a15111000011030800414460421240c140403c0c804200b0344e00c8514405d030b46801c03d5646e031100ca01d150f002045144240740c0010100e201a9030854510306c00d541031994180e001e00005440d0019020f0140c000c10030a548034040c011000542d03a40404ca0309000741541400440d40c0401500b014003403040110751094983c84034801c03c0740155003c15210303480766042f05d2601c104c0d141c508010707001b421180c120620ba14400160304020510000c040c01e003c1d44981800040916600d8a49440e0700416031311020622240007482d001000b0800102c1804c91004455070805039260001542d00742c070036200703445401c2903906002441000b4040e10381e00c0031018401c07a1036000074501c010224900d00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 337376465 1250 337375215 337375219
    0x5060f0f07030e0a090c120c090603020d15030b071107060806090907210c090e06011716121509030f03091109070906090905010503070e0430020106051e 67
    0x1e4000c1018001c0d2542e190b0301c0006001050b003180c4441c0404003c0141c004a100850520001503181014500910340c040c40e403aa100780742d55203854401e401079044802c1c880945500c0b20880205988403040440046004580e40086070405807000b50502010074600c0004d500300000a020058001c401c45030081c000781c0e414021907984281607401c3c0201c42d0051b03081300304d480185034000380c1c82d000d0310b208203401480401031141d959070388007040383c000c4584203449030004001004407402c0c0c0821450920074501c251401703001c6a046403014110700b6040043c080c3c3c00c16150344148001003009809451a45204014440481e2030180c2089a2102c0e03440416442ea007081c41004011040c4138071540019201a28038209154080c00006650042d00001035000200050036200ea001d0141201d002074080c113005410138400500081d0010300c1a00e00391641d614034011200c0d9070308211038400d12500752082c08180341a0007801d450040d4003d6115401854221075402c000c0c1500c0318884d142 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 337377715 1250 337376465 337376467
    0x702090f13320304050306041101022b09120b0c0c0a060614030c0a0f031b0b0c0a050607020318040b210106091103040323090a09021305060f0f 63
    0x41c0c80311030112094504004088000c0c4940d080e0420500c1c2e140300010301108005042c0461058001c0c5540780201d100e92135240e4000c00119001c2240f600207001c40e20810300c181d4101d80b8000f5101110f1045043e02c1c80358818000182d60b003001da0180c0d030300015051104501a101e01c4c00e440e278050b140005003100540303090000310144821010019900d00b25480002402202d03074400c6500c403410780c103082d40b07406401040703a090000d280c08002c0300107680c10090159030103400c41d00c81c243e1a400d4510482e030031440c00d030408030b054880d20300548001880000208152111858814280303007002d4030481c203542c01840702d8100b03640010320b0301074540400e0f10300040800d59003001a10030071401028580c1d444142c8945540e003c0c040d00641c0540310b03110014080342c0c1484407403041e18401114045c002030b00313015101001c08040c00c0d0301c9061580c0e10f41c28605200f40d450018804101079405016159400500f898030010111000b1000305001c0b00c40382d08014500030000f00d50300c42c20000500210b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 337378965 1250 337377715 337377721
    0x8030910091a18030a02030a060209010e1807110c01091a0904050c0c0c03030304110108150307080717030c0d050d090605100e0604090201020c0d0c080d0e090a020702090f 75
    0x4810540c0000a084008200107014180499401e039036021403442d00c1c1c120a02d580f100441d01300003c0401c9566406402840350606a440d604025001030b0032036030403c03110404100300350b5100d081c0300c03940b95400c44080005041540d40648254100c805500898109440c41015a82c10000070000c9852020100141410800d241c2d03440b48210b01c40140e2080c503003024010200e0a04025180b0240c402089a038194244010107589000459004000b01110620f92195502c00c0c01d00700c0d0058000d414180107480b003140080d0820311031341c100f02400c0d802000c04002401075003c08441801072440a1440c010081400c551030300c0b207407400c0a05103d00040e01c01441d900903400201e24a812620401003800c1c08800b44c10002c404d8480c03900401c101801052071450a07105046406605800501d4403c841c003050200710f004801d07058a045030100b40000b9825024400601031880b00d40c0c5009c3c043c05104208000d170107010f09040b9005105004200045c0c840500b8960001110360440000399 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 337380215 1250 337378965 337378967
    0x60c03050409020a02070602100908030601110a0203060711010c0309050a022e03060302040b031f0c050c0303040f032703170415020106151b0b0603150f1b030108030910 74
    0xc8110307886800075510001d01021300c5a404100340c0c040d11032641c280c400302c0540d0b44048060b00d2000d0405400f1010800214401c0e6000b0b8440b03511070030182c0b060703c440e800c554002900707005048502102186900060391410300b428403607501c0c16012410204000451511102c0e0381d060a040002d000d0003034000001d000300000341080111459010746901924540300000340600b1091004034008ca040030080340c42841e0226841244000b60140c95441012007c8900d0180c4100241d9000b0b0020400421340e101c281403004500c10b6005618400c0b014040b032a00601c180190f00c44c40041d900085203210025010640c61001c582d01310758100040d20340d20324000b507e44982d0b400144001c0004560880058064204804036283c2c5007003e0600030745000c0994100407140b0754036156148240c0c8080000301c4e000303943c540084000d0101c414010aa690001e00c00c1c0060300c4102071401c1610400020180010081440400c100c0741d03d07040d549040b104559900580356042d100f924501003101c185 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 337381465 1250 337380215 337380217
    0x19030522020f121615030203160c08040909060e0c040507020307110f0d0303050712050702030901050717070c0f0801021c0902031006230d111012060e09010e16060c0305 74
    0x30380240c140c40d0346144403e03582c400c401117446072080d081c0800c508692510700074401c0e24403900f02146911501d40d40030032704803481c110354a41100c802c102440085004081407041c0d028a80c410742d000a04141000e034468603044080f0200751240c2d06000c208406030b540802510407043e40481e484030256102c0300001d41d1500307c0c01015401c107032280d400f44180742e40340e042036010f45800e032201501401c2109465040c0d41c4100e51072030141c1c2c42000060315551144e001825501c0c01440191882d07058201d9210055100e00c100b5190400450304c1841250020300c3c00c2002130002c45c0003103142010043314140c40300e0301014864549640d6172030510a6480511190200c2558010b04011a544a81c044030b440c2c1d0140812440602d000e603100742080c10408040b104503a0015640c820b9619000204201c1020700c00c1079070100841620340006001e41c0b030040a0107000307001112705003803401c0e510071406c4805c006003c0041303030f001d401c1c8030f10707984103500054094030102e140c40c41d8502044d0a0603245 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 337382715 1250 337381465 337381489
    0xd02040504050a0506010f0806010813030207080a030f0809061e1e0a060815011a1e07050c130212040305031e01081c050301030309150c050319030522020f 68
    0x4681400308014180340d15901070343c800e0380b0988903401c00140c0701f0400c0310700c104112100c5000c5054a07010401c80c0c1031100320025250320910444240c035446041190404035460012030200d80c0d0700340101595a0404032042d40503121000600c0300c0e00d03109080c5c000d00b903000780803550203401500104a433807075241038410603041e80d401d2004150412600c00c02c01003150303105490040c010070311000c0c03608503926000c0b4121a00300e141e009240e2084261658258000900e01d00c410340d10b042c40c0d09000141e00c2c082c1c260759008030080c04030042c43c40c0c00c0c0825854180c0484905900c1004410a0812108480c82d005070705440d03d55125582c0c05181d1000034032070308882560515074400080c0d070400009034034240c0c00100c01c451000c500c0c2180c041e030b00c1340000c1c0030060204250480a018004400c1001c03c012115441c01902161040e00c4050030359110412962441d003a94519201060f014003d00c0d4124038520030402c580341c4070800b60600b2a0030003c00a1040c0d60040c0806015a00d8895180d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 337383965 1250 337382715 337382719
    0x1517074e0c08011104050108040b0a09020a09020304031e1211041701050402041406030a1b0905090d02071401050a0311070b090f0c01090303090e040311030c07090612080f0d020405 79
    0x22002516062249010310740d441201d1040d0308000d8060b04402c40c600030b8500300d500c181c40c0c05005d61a00d58880f81c2e1a04001d069440142c2d91349814005a0303540c0f2411801402040e40040c2e0342e081030306006140640359144841051040103c600055600c0400c000301054204c00010700c0e0003140800c3d01440c1705d140d112403e403001c42d01d1441c04c6014107501080c09188200e50801550010300042d20140302c0c102c03003060349600116a40e001181ca030303280d005403503900c1c0c0308010180794483c92108210f54064448071a0360340036502c000c0140d5010000c0c00094641d4031140c202040d64240001c00302c2c031440e00810100343e12a10041041441c0f48142e50b1080da1180110b419454030b0b810056441c0c426444024082c8126801801f10394068201401074a400d075961039106070034004195075080c00600200d0070011107042081e503481c0180040c1c190094440050100c440c6824880415900143c106152142540c0b41d4503002031001000c8a1a4440420026844000143c003c00c024003076980116 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 337385215 1250 337383965 337384109
    0x60309050c0307060f08060316030215040e040c06020d02120406031a0d030c120915051b0a0c06090801110a0809150c0d0e0102032404151707 62
    0xc9113090308030340d492203c0c90a0703558007013880d5990400c2580c0d40c1560030035441f03210310043d000e2026040ca25000d81c29880401d0700689460b0365200207070a120801c407803e54a4142d446802d00401c0c0e810300019000023540c2c8014401440e610a10200500c2507210b6041495070b29201d0011844500740b583e49614001051044a07003000d04000c2c00001d42030404940b2040280204507885014003a180141c0308421140c680c0c07401c6d890402e031000e40c0421030701c00700901010018407000c41e081100c540031b544142180c403045450020003426180040d0030100d200e034101502502c000c9025019605064803a2500c0c40080d168541c0090920f4a1600f040c039180c07100381d0400400b180c281000b0040c001002008018000743c1e890b00a00304d0005490500444050301c00850340800c0700310101c00f0180000b880000d030000c2582144008040030352240302543d900c10039a1030300160600500009018400d0318000070700c0c1148040c0075084000302280501444450b000940407548102d40b140000208101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 337386465 1250 337385215 337385219
    0x604150807030b06011d010c03120516020706020d0e210a05150c0703050304060504060204090c02060103061508070b03251808031602040b03030c0102040b12060109050901060309050c0307 82
    0x66490340c4482c04250350480c8aa00800c8a07944110041d10b5050540d2401c40c03540c0407004011038003000c1000c029010005040100301a68145104160052006030200da80da00050600179051003920350140f020f54106011203400c480c2c10607141c11007880111024890351041402c070030301c01203800441600500c030b42c6828004024002400071104040700c05184580d07500d00d41c084201d8400d0740c4004000a01c01d001240005aa80d00255003040c0310b8174015040a44070b04188049038001130050005a000b1401042405803600c540d180c42d49012106c20603a41c01c092516a9526441c032501080380c07000000100301015500000d8283c92020060301d000c400401350041415841c210410060710103070700c2c0002c0c441000401c9942052012407510b124002c01c2e02000020140d0540007a010b01040198000101080c40240050502501640e0304c48814508a045c0c00000404c10b40c144031100c2c00612061f5503545040303045500902d80425500500d203030590030040300c0e505158051241c0300c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 337387715 1250 337386465 337386479
    0x10b2d03190510030c0b2b02040315051003020112020f1303051c140c030403020423090102030103030c0b190905060105040e0c060414011107120b06040b03060609060415 74
    0x482802800144014482d5480c1c0d0351030203040b00c1e02440014440e0040007000c002151004c005480d4140c081d9483d603015035444041c440c0300c801c0f0841d02c0b80d100c40d40001d0034030030004101f2061500e0000355500b00030600c1c00384c11120080c0000e0001138140859422464140c1140d03404903000c00007200400c0d500c45030800035401402c3d1960008554078000c1016603407640c902c0d84070030f0103102096501c044645080c200b20307100741d9210701d00d00d200344d0100700004800350722036000c0d035040c080d1221200403659203d116021240f07180540741a0b002e034010001000405e80c042003106959422070110010350f20f50184032a40c40070708070b92080000e400d1401c100240540469254100d0303806540038094441804c10b9aa214010b1640003580417005110500034030070102d04074980028103040c000c006203002040245001417603840300c1281d00f1654010000c00010a2a542c0c0201058509000310201e100000323803959001058240034004080018000d9680da03001070500f4003540c1294000b039515400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 337388965 1250 337387715 337387741
    0x111b0613090906150e0f1506040503010e28050601060e0d0618140f061f0f170706050405061c02090d0501050f010806040803040807050102190512060306010b2d03 71
    0x607004445000b440000640703030070b00110b0140b01c1c291b8040b000e03c150f80e8001d45000c404400e4000c181c0c2000080c407000c20340da1800d220b500003080e07841d001000030309000d01c1e1105d00c81051281203070010300070741840000200c0019925054580c2030810001948600000c038a60340704041000d491142400300080010764001c03032134a2503900902117110140a07540c40d03150744081e8105800141da00c518009091a46070b1444150f802e166080361240c0c2c60303500c202541c00c400c0b00703401103642020881e61201501d0004c000322401070169062007414186040b0004440d07018281d420500180d0005156a000040c2d504490250400401d0b0b007010810a04000e402003500b01c60b825007800743c40c4008155804000780080c4503e600c00803081c6195034030380d81e05080e0b03041054112010b40d000d12041040c914501007511b2903c03100e0340c07026102c3e816070607104800203029000900903003000e0014072000d4103000c2180c00d544400202c0d400c0400c041d40400182c416800c1ca0200c00d09408414410b082d40642 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 337390215 1250 337388965 337388981
    0x30c0201020d210b03120c150601030903090501081008160617010321180b09130506011b020a0803070303021c05090303130302240106111b0613090906 66
    0xa07003214100100c1042c25506a044074014244800c421910000f041286400c1025425005821b44529805101c00d2900079000305080d041280c000000140782c0500351010207074480409d00c0e040c4109036141d1070140500d030315400f0b85e504011012000640954018445034001c001e41c1d41111500307800f80c29010500c0019000b120005041c150707000c620314600000c82c1d41070b82e07001410160151000361450002426007074280c0c3c188203c00c281c00c03000e507114481200c001e1029070349103559004803408100001040140c075032082e41c98101800080d9078050030b010800d403c0e4040d101510b029500002b40c01a000380d1200b01e9920000502d00200343e4107401600c40720080309034280a00c01c8110380101070340c0003159031020305d90050001860103480740340003042d818000e006540800c8000969286800310640c403001c0485038100040155660001b10594112001c0c07024001c1240c0c54107094010301c04c594241e51040c1d9020900c21000181074884400409042c1002c00485801c4d14025020304405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 337391465 1250 337390215 337390217
    0x230d09080c0a081803070815040309171507020615010f1403100f120807150905030703030b0f03010c020c062503090e060108010b0319020d090c030b1b03010303121503030c0201 77
    0x71040c1c44c0d800e00f00028840280c030420070261103010500380c4155000100180f0a900300705140000103600e0700c02100b0b524110954001410a03202c002c001021240c40181040c0110341c07004c010041c00d9520303042603001d148800d20f0449005411041c04030380a2600c01c040300e4401d1400024405498200021142100ea04e000040c1000e0390318403580c0314031a48210007900740d44080156000248041809c94200402c4141c0012912810340f2070380e00e180c00401e012004a0758550080c0c829107040040c21101c01130480c001d02810582c0c02c002900c80a00098042c0140c1c40410554907109442440074911602da418540041c011400c00418200c40e600c503007450b000c03c0e08080b404079407144108034165070101640c580b442e1114010680051141e000c041440c40c1e01780034042031861503003c1d02402c1400b84c0b003010a540e0139414030f18800b45002d809614031030306c03a00400040d41105030a49044a416050584c881c2100380003a1029110000144a034200e00c00408410180c20041300d4442c1030007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 337392715 1250 337391465 337391497
    0x20c010c020f070b071a090712060c0305010b0903031e040302030f0a0c0b040e070f030e060a0b03060c09030a14010b0a03060905010b010305060604090e0a0b0115230d09080c0a08 78
    0x14a4000ca0751522030448041c0180c3c1d5280c0d011b04088520002041d00074016504590700540d03141c281c14184008540101d4a4070340315800c6407290b59140c09094058200d00b000b080c600780302c075400680d4a225500c406941292901035594021900030b007034400468014043e1017070375441c8442c02d40c0755900d1840466024403c10400b0239400c0700c5070150303010b80d0700c046400c0f05543c80b0075038180da040b50031240c40c608041d11600300d02241141400203034042d00d04c04001061002e804010941403020041040842c588140500469642d00007103110303400f90860000c5200360081e07200e00d8090710614110503006400200004100a12a44013880345800740c0002c015810082004409a40064501a50044090006010f4032195611282d1064400d90481e4810562650b030a000080c0c00d170711040d000600a403007064440d40007618100100300d040c440c001450700030000d10400b1300a546070620f0180d911003c103820000c00e40100c0d081404100d0071140d03207000030b10f418812603000000004810790 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 337393965 1250 337392715 337392719
    0xb15150a0e0d0b0c030906070c0218190c111b030a0602030c1b03031501081501030c090e0a1d0604081920100b0303040528180603020f220f020c010c020f07 68
    0x803052042109e0b90f54003d18940c0c0b04801c0407071030b4800500141c10001700b4055043c2c041803208640c8140210380c1540d8884404607002c1b203000c00c2c20110100044413141e400b1541116550b030b404104151525400319005880e5200c54018000b07138000c3c0c22089100b51003052004c0d10040f80040650312681c0003802400030030b2807100045035240010340315150001050a01401158082c5d000040e50100c0342c13a1100780666a408261106002a1250b001442d9166182145a98168062030041c04035400a013020702306651803000500c20040000c100340640c1110040fa18800c01c070300c3d0301c0c1c887d0000d03002c80240c907100d407201d844428031315001d020280b420080e0328040c1400b1003902d003110f000414443e424500010103042c140711807080d040000c032501c2008103044100c00e440e000203000320003000810a007180705100074203c442409a1061000324540c686040259001920202015801252850141d40c00740d011307000c0c11000e0035465091094172401203a0004503c011f2000c0340e412691030035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 337395215 1250 337393965 337393967
    0x4260f0c0f0f090a0506062a0609030a020a0807030201060b040b030906010806070c03030b03010b030d0c1407050a090c030605060c1b06070302030403140312040b15150a0e0d0b0c03090607 82
    0x2071a15440300d60005141d03c00584080910740c0143d6002074060906842e0206031250010f400b5660561140388040380085400381c00010024564010210401149828420840a0341d104101e0000906940d4001003001c1014400e400c5203000f0500c00392005d0f1103e07143c90002c00c45400403140802d491068600003d0700da00d000a4407405404161110440a801600e08401030103845071800e40540d200d50210b07401e034408108404140000d6910005034468500e00310000c0700003a8040c0368158006001802035079070743c914210880380e07441d00005030042028020f40c0a031015502c4150b105002159030b0706440300116100100755070316501401076080c441c040000b640121a8081d005138010321042c0f0011348610604114280100216402c090034248500c0041004850442c0c411071108203006182c90503c0b168078402d14103e07285e519031001100606800c0c0501c2100804001c0c1c82c460740d81f038070744641503d0750b0a150445a0820030340341c45014010664002c0d90390016503c00c03200020421 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 337396465 1250 337395215 337395229
    0x14010f300207020907020303060a090c0f110124140105120103020402130b0a030f060e0402030604112106060a06080108030702210d0c0311030f04260f0c0f 68
    0x210303404240395001100c400546104030301038064101640c20400d44001d40e9507110340301d224000c95030013580d4a02d0103506114014810703911400c0c0c510704040e9040807031a04088044801d8400349080e100c186080d00101d4090040c40002c5e40200c0210022030032065035445c2058140e400c00c5c883c21252500c02d800440f5036208640c0c001207440d032614014001131509800400595810b0600203c0c42c585405d0065a25403040c411400440d6481da1950340802150103060700410f4a6480c0d41200e19003500400d40391040100300520600c00c0390b401100e10342c0c5100ea003900c000701c1601c1001c48a1030000855079140c00c161002c0d0b128004462001540750300c60340b1140d0580e0702e0b440103141810296420301c00e54214100210341c040d1401004072800c0f0404008060340e03000c0540d11404803a81d10f0074044c1c00d1510207100c2c0052070b04204030319601740f0761a00132101141d030344e040040700c007109940c0d5041d01440c0203c9942002d00500ca4008015540022854002001100e24048810600b4100502 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 337397715 1250 337396465 337396487
    0x3060a150e1f090902090604031a09060a0605030a031223150d031407050309040e0a0c14030714030c1519170402010507110307080a050f030306030c0907120614010f 72
    0x103e041c01c061140302d540780c000c1e146060b0080e100700c2c2003544035030710304c000041012101c00c5210300000070846c505004005903a04004005400c0011030f007003a021a40b268074801024043c001c0002e1303d400300780ca0540c0a5181500c0c00760000303d41c1c103203010842d410b80c071054034004040c0030f101c0b5000c0494585422550758182c0e06441e0301102280c1251104902d03000740030300ba00d00b80010321448200f03403140c5c0140701e09054490302502081d425440c00a4a040003074200300c0e00c41d491002c2d1401142c500240c7c0c1025034942445680d10b420312407000916002a84c0d05140c4c1000c0b5081b9801082d00c01c000240140a4034071040c4101069a6082150185a200940351036142c860000c28055401000103000c942e010b403090300324141102e00420b103400080e500040c180d034807034441e001c1441002c2c050710075600c0404002d1440c0d4109400083c0c2d4400b014601c03203205110140c04140074602900300c1031a000c507102418407400d80e03a40125880d0150103c84140820784145d1040c2c08140300b4040410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 337398965 1250 337397715 337397717
    0x1e16051e190503270405070305151201021606090209070509150a0e030a0507090b060405030a03032d0c270b0a12091101090509071403060a150e1f 64
    0x148811129800c1c0360100301204050310240801c2101c900ba4200b0709030740b0611904000e000c032492040002c103010440da00280078104142c68241427107940801120303900c14840040f20641c0c5401c810342c086a00a11031240354642c0900d04000030f40405ca81a000001c100c0c1c000c580685260b510214103451b02d10583e002c0f02d601c1a16039685424902c6031001801c905003540c0b50441402e2442d002107480c1490898050b03c40ba03200e04420404076450f400785d0b1069100540d0704506091908006c2a0355603201c030b0004007816281d0354900407044842550080d0800c0c2c0c0304024194100100d1072100078000074125000040090424040140c60b80030280b00d41704440005141c036a16041100f80b946e082101038508000c40010b0000c03800c0524014031a01030f0290529240550b0300c20000f401d00c242d41e91269020380201c10401c82d8072a0065035007010110410b071610381c0c4e070341c8120024020094940104400d40400700091a86d80e5119100384103005098030740004c14040541108400050322075140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 337400215 1250 337398965 337398973
    0x7050306090703060e092b090918081303020a0605030717270303150d02090703090f0c060201020705010e070807170321070320070204021e16051e 64
    0x80c4550030300c0c15a00398030000503d00011065110840200c8a03d01680c3c210760700d90240da0104440354800c10022030b02c01104030820f468a6245102801c810040c0c0310b100c00790f40e900d00411421124582c0c02d00b54456104034465551140b52220103e0510300b400142d00400e8031600205826005808036401010b0341c0e1901410700309056070442e600700e802880110080c242a004d119007200740c446000440e20301401850726403030444910090203205e0b600b07840c400d0b41358840c10005a1101070040350400c605203404074044d48542054600340206217030081c000c00c40c040d00002c84960643c0585081d901c140000d200203501d0583d41586e400c05400707201c0160300601ca04001103002102c410010f50480b0382135a0502100742c205c0394046004a00c0403c15081a204005099516105500304040b912604482014800501c909580144040207008507800034454a100403003070b051102005001440b0355641156942511170091000b400300d4443c418040b42c808070b02c009024107884c0000303110040c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 337401465 1250 337400215 337400221
    0x1a091f05090a230f0703030504062a080405030105101a1b01050106020604020a12030e010c0602090406030804210203030307050310080615150c060705130504180b06010503070503 78
    0x41008003005403001410b80309100c42d03100083c1041014461401c00343d4400f880c1d80100c415001d042040d10400031900d604107203030600c0041e030007900362400d55007546000c84248104504903250b01c0c801180d80702640f000d02824170100f01c1c5400040c011368105800074041e50b01d03034421781013802c11140a1002000c46d1802c511982e00d04500161521007070000c100300c21016100000ca003121000c0e0041c00041e000581084254207004c03841c88021700c41c0c500e100c181c0d40410307240200350700151000710307040003440a64801440390580548055200061041060980e00d01e41a10305500134802c030310030140c0c2e9200b4000c000d400c2d00002c0940d5600600958038590720810708440640c0000c2002c07884040040c80070407944002c0021074070699050b07441070706280c03540e000c104c4040842c5200c1441070401304005000041c0100f0303419006265401c001e529140c1c00c07084030f007e2012940003e41c02c0761501640723145210010f03000c1c8080e2806400f840c080d5846140044600344011038003280812070400c04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 337402715 1250 337401465 337401523
    0x3011b120f021801080c03070804060c05040b030f011412060402040b0402070c0f081605211e0a1b0e0c0927061201050127060504091a09 60
    0x40d803030200400150004000440c0300e0290100d0300005407540850321032034491901941c0004445410009003002c0760300310328144200030b00703188008000410540ccc440360001c004078004c0741950060482c03a400700e40c881c81d210306035000c031100901c9000402e026410590703100f03080151a61040d201c0c564007034100d60f80c4913024000900f006106040d0050360800c86440440c01c0c0340c4120740a001011081032110340741010715450718850364500c10f003124a41c1c8080025544100c03102c1d440300e5001240c0c1d4040d0307a09001090400b2115825242c0000c10008041e2040b8804176980d040180314028000d0b04c0d09507031542c4004c10340e50740101030f0105190004900c0400701000503046012008010100c0703500001603558083c04543c0c00159005020424086249428043d419500050000070040c540c03510075038060701589101a035072903581c1c006a1060300764190700000081c2501030414441f4009501d04002c02c002c5400d80b482460504801165002c4800304002c12070700a07584030020000f0b42214 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 337403965 1250 337402715 337402727
    0x50a051308011806150b09090712050106030603030908030c0304170102091804033f09140303041505090303060f031c05180117040b061512010f0503011b 67
    0x598020460101800141ca07210034010511507044000407154440c600340782800503510b201640b20a0b070041204248108100c2405072182c04200311901019234444030025110300c3d890640084017507007442c002080395038050708500210f920035076900c83e07540d6446640320703280d000d460b082048a03001000204105003c100049515262400005107802481d01c00103101071480d8a100b0b11070312103101080107050300103060101a00604801c81d0a512a00d200d0004041100c40c101c06030900b28000308a0194141d4800c0000030707400b072050031108082003040340da650811901203408000015100d1035060320703401400d015003a814011803c503100c0c0420005c41406060900e6094801e00c40e210368454410100c9001844181e01c030300c1c3d079802107400700b080011514014981401501a00d00844035a1440181da01503001604803a00352150400210081640360400704880350102c1c900b0b03802a010f450090403281c00e190740e4000d076650ba400b031500b81c4041c3c241442070908010306058086015071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 337405215 1250 337403965 337403977
    0x121020a030f081603022d1c051606050901051609060c02060f0310180204030503030f0a021b0610050a06021e0c0d03021006050a050a090c0c020618010816050a05 71
    0x101c01103003001e0244d66080c44400c2c24100640050303108043d2409880704a02002c3c00011003c03039200440c144000030302e5541c044403040c0c00f1441c12002d022251a0b0321510a40310181070819200f071a009071400d008014140945803003041e540b0700b5012031241840c0d500041c004c4080364940100c81440c01e5421342d910440300030123030303082013003001405d042c0010741c002581b24500010848285605100c0940850000341500300540d6204101c240003054001060300d61050040e004d510711070f034a109854020b40152240c1241201040c10803120190021850510601c400c0c0190030b04141da5000708102c0360124400d4001582005a200d00b010181a071854444284441121036480401e40800c1002000c42800c2d4016045860f54800c00682da0088100501342100c84031500c0d420031300010300218040c031504031050340e20408800881d000351407803800e05800802c0c0d23907203403e0000943c540303102d440040c890020782d08400045408900c0c0e450020f00c41d80c2a511a8244041d070101039440360701c24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 337406465 1250 337405215 337405223
    0x709030c090906110d0e0f03030915040206040801020a050a1101020a08040f0203010902190603050a0510060f030e070303080612060106021002090f060a020102040e0c07170904021309050121020a030f 87
    0x4c00410305a910b40f180204448034404600040c2403115030101030404171075250448103500104140903100740700098500760300c5615140145992661720024841d132256030b2003980c403540046085c4002580101c0074054071a215140c1520b841010f401c00b42c01c034030a02c04100e021030b060030045000706510010060f00544080c000241703ca4558002452051101205041481c0c0c038080502166a00d030282c69044810f45d4818841c60516541e42c6c03018405e140a10010060841f5401c40c3c481d2094000c80c40c000000019644059240d082c020a0118225482d501a45007050341c100326480009503141201c43d940d0141c90001d0070000c1d940301030740c41104003d900c01c3c0c101c2000042c56440314014032100040b80c00051703a4501c0d00351180b0300c81e14004c04c0004007000900c40034001c20154480075604105090804e40c0d41e460a500040090180c01e41c0c07a0100d04901a0200340c80e032683d03026030b040c0c81c2500e1050310158505106200e6810032020003d40240103004108006040740c01440c0b2070a100d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 337407715 1250 337406465 337406471
    0x2040605031b1b0309040f0e0604141609020702011403040c0b030a0209040501121e0803060d06060e0403090504110f091002010e0f011a012f07150305010801050709030c090906 77
    0x151503541d400c02c000d00040301141c10000f001602c506d07061144030f4624900603014003448521411091305da03800184080c150181800108010ba101444102240c41d5000100c114031901c0b09003d400079041940221b020603118a00030f00345180c030303405584c0f08542c809000b07104103040501100d0f81d0780001d80a60b19054080c4510451a0794078001d0502030002d001402c41d12034902e09100c0740200031034000d40428400300c0c14a6010903d00fa04581d40004186d8010a040c050307172612200401441c0e100081541d00384d000c8c0803c141d40851000700720350084070180a0740004000d44003403486007410001048400300700400749402d0006216102a00c0d500000502511440c2407900b1701c50bc082c2c070010165900c8c40703101d10708244150000203071102841c001240d10078400d0745012503c2c0005951102440b1711f190704130a0a41000490050244a5140c03052840a07a4025001d04000e00414500b542808000b5002a10032400c0c1400ca0f0f4005210411305842d0054030802840501c001340d1380551 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 337408965 1250 337407715 337407727
    0x40b060c010c0203120a110d0203060a15080402040c08090c1c0b0f0a0509010b0f0d02190605070506060402090a030b0a090c0308030708060108040503180a0f060e03060a02040605031b 80
    0x40284a50780300070031180c01440d0345010301601c421012400800381000d141c1f60810b11699121103005031915040d0300c10f0010303625201c5c1400601444030b40e902010104510f90f00d6a8001e552240300e190250740f00350b070140183e138840001902c0d07038442250307100b017103502241002c0314500e00020380000c0038058490625944040d521600c108003c1214074084402d82d4a060055a0440d48144c42d0301001d000001c00c108001c100c00200d105440000191240c44010070705000d5581e030a40700794215400609031a801d582c0c0c0c403c0509560408101a030303150240e040000c0d8542880d00841d242030900600b10050b060559403070003a0074402501140c24950b4400d11030002801001c20701c0c02950090715039940b41c1c1390400b0018038246000b0540303410000500144000110000295225030903413000a01c014030301203001c80e41d10a2140e101e10300460300310303000250458205110508643e016070503181da80c1c2e80c0040e24000d92281340b03d40b8002074000c1000401003040600e1900140030b080c818289000c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 337410071 1106 337408965 337408987
    0x30901030509100507030b011701050a121e0804030c1401090b0306150d0e010e030a020a03030c050c10050a15030203070306020a02030f031e0f010311040b06 69
    0x544a00124144900074043c824a0000b8080e04000b04e00c0c14400080c050540351110b603012a803400c0c00354541c00301140c06107040e5040904000301451408071070354041040e07444192a15481e00c40301c035000c560f614840280c800c1c040c00006891354114201410003082c2680203801c000d0b4004400f00450740c10232a82030440d1459006152a070703031070801160045807280300d40758041c040020f4400c800401d41d0322004040e480040200a2911050300c916580c0c072a80d03000c4030160340400c0c48000024840e801140c00b0f0ba08a160003030400f80450b0346030785000f48805444403070301d4a0b00100010807480303200d24411000142c4c0151005031440c0c001c00e4854596000190400d6000100d0f803801c14001c004407040d051060080c5a900d04e002d44c140855001078074031800200000c01e010524407004c65224506880d080856140812085d408000050070b010b2201a0000d600713000704003000d = true := by decide +kernel

theorem cover : BRFrame.Cov 337230215 337410071 := by
  have h0 := BRFrame.cov_init 337230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 337230215 ≤ n) (h2 : n < 337410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
