-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1966
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:19:55.905859+00:00
-- url     : https://prove2.me/submissions/2b44ff19-41b1-400b-932f-e119ea788e5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 353417266 ≤ n < 353597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 353418516 1250 353417266 353417297
    0x1e180415260304032f0609151e041d010e04030e0a0803130311090f0414100f0c090614160602040902032703040e1302010201060f14090f0f07030c 64
    0x640301461055201c0d03205c802240207030880885428482a142d860070f0100c0c10340c580c1d101003c45680001c2070702c1809004188456507c03241c00b8075030b18100c0911604030182c0d0010702e510010020b40c1c0814001c050b424410600e6505260030900422190354281c41c0802e002c80d004490482600100411003101c4640700d81c905400e40d0003164000c1c01e0441041070500400000f248220f01408054544540a2400280c151030107000940701400c8003000742000000400280880303520b0420f685400d0100c00e41442000c4010001c410300800000c00c4110080b074500e11880c400211084014211400d003c0e41c1900401a10513001080320340c0c5034200b0001603500e072030780050b500c10080c100c10154041442c8000d0002c400c1c0318812410a5001000300f0301c52400d1000801340c12481586141c410141c50b840180d0041c0007680082c00542c801050016003035201840c00c1d0505001540c00101a88513001034409a083c1501c545204114082c0043d48440c0b0a80c4180f207042c1351850011804210002c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 353419766 1250 353418516 353418523
    0xf10050a0617060d02010f1119200f010822151e0e0d26090616081302010c1704150e0a080718021e18041526 48
    0x1404040860b041c210b98005401040000943c010340550b216070000d03465500081c1595605d480d6101440410a124188010104007005040106d04402040c043c010700b41610403801004d440b4070f140c0460754080001d8203100310b9250807200c0c11b0312410050346410100303200c180740780540d55610040301c1c40d0183c081100901d10b6880b8901150000800b903030148030700304128a00b4041c03424002c0c1040c0f56481c048200003111003c10001d031a0401440080320600010651520455140c42d03c1c4070040c40200c80700812114000c03010b00366541c030301411150707094135605821615074110b50050081400954007446189103602d1050310050140480041c15080b5508103800445055030515005040c060b04026201040c0000310f900002d07003890700c41c085a41d24064091004000c0446d170b00e030224500ca580684101c0c00585960606040c0031004110f4640c01c00400307060f0781201c000244580f81010b00c519503011503200010b50b04070f400c203204a07542189491001c10300e0440080e103084000800e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 353421016 1250 353419766 353419769
    0xb090f0307030c0b090d020727140915060f0d0809040f0e1e120f0c0f0c01080610080106030209010509041e050702030324060706050406060302090901060e0f10050a 72
    0xd403100c0c1c900c0c1d00c090919404081e00208885c5140d4009051048600d800003540c0e01207580c500c500b000041ea2600b081c004401d102c000918440d03060800c2810960184500f40707218803d82400c4404900900384807148a07d0140c0d610b035000205440e46110504086601e40e0000b40103400701440c25031070a02007021182d8000c500c511007580c828a00e55140e1092044442d0300d144e114454148601001d0300035140c115040b00303040c40300400a240b084481c100fa090b90308100c1100300ba103980a00e1031249544800f55418514005204e10000036042c5c80c20240d0400c0c0144540c4d03464aa0740e01b4804c060f0000c0d808000024140b0030144104242075446000c0c3d540031200801c107032041c6621012810003036030000340c048410b54000340200040c0d00d0765000004460b1178882309a15101d802070300070a91740e2082e1a00036140500b800b08002c02d104084e00440100c074070a4422603151b55a00e50501e007241d6050203009014542007021a03851141c0c08190f0380c00c042080003000c6803a82e10000543c500150703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 353422266 1250 353421016 353421023
    0x302060c1806090a24020118050613051203010b0418020c0d03050406060b070503040312030b150f070c06020609150727050409051506040510050909011b0504080705040b0d0b090f0307 80
    0x75010280c5c0300c1a42802001c0d00e001035001300040c031318842d03075071151a401c1c006e00120140301700000701d000b441001c11801c0e41d5203100040c10783d925610703400545500c1d48180105201c815481d00003007800c1003c1d04c226440c0f180706030050310b1030b03054400045029010150060f115180c40d40d02c08140e110440000b4015a03100c0d400440d9a180780d4500488209285480340d800e15140180410080d10384480e11010b05901d408100e80c0c42d4406007001d00c19028580002d0102000741c1c0340450b81030340000304c0c130740034854080440b1804152070701402607583e0100c0d00140010800c0140a07603059442030490f04010300c0c1c5241202c8640c40b007010030201c031441502650154000c209019a80103188141501311405640503c40c519001e92078070091a01d91007202e004100d401c0000340c400b00290f010080188100304984280040145c3c002e08170b40082c041c00303441e03009400c8001002d1405d03108420342140e010b030a0014109a80c0c94001048031b00804509190194810085600005000420a0622 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 353423516 1250 353422266 353422319
    0xb18010f0b0405150603010302120a0f1103162402030c010c02070e0f16050903010f0e03040504140f040305070f3804022b0c09090302060c1806090a 65
    0x44100c1000103682c0083e05421600d5000303180b48841c0d17160001180d064980568244a5184540208a00c7c05069140103890071305240c10207010003125841c0d8951801c1e080307003110401c1003a01c41900f031824070346c801e07040011658001c0310702d14200d40c008550894403d006507401e12101214190075164503058180050300310040c1801a40c1c00326080e540c002c989454554018903201002c59509100010020184100400c282c0030070303542504100d4100716595000d10149334080c6c0840c0d03503600107000c0d5610441c200302424001031064203202d4032544e04215024100d440740d03102629264020070080e1000d41d1704c6540ba00101d0400d0801d10040400d0905c05801c0c0842004054451008060b41040c40410314090102580c0c4036800c0d84e010320303c2e10814000110902da14903000c101d106d00000c140c0380181c44c0004211500741d000351550390080c1c090303d02c55642c00702203090a100799411030a1940c071550804180c0c1c10080d000d008660400b61840c800e842d22025281c0300302c030a40202c0d405650707 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 353424766 1250 353423516 353423531
    0x1215151106100e07020316170702030a0b01150c02030a0b1806010e0709120201051c020d0c0206040506150108040b07052503090803030601051b07050d1b05011404030b18010f 76
    0x200c1081440d130707200071244003840c1400190315420342e50a0002c10702800850191001d5610a0000801c48035100d41c01011141900c1d0320f40303801c13001e40302d00f44100d0803039503818907241c0c038264002e05040500540c010003521404456070f50318403d10201400902000e038451201800d01081040740768013030030303031703803101c92103a251a074001007902646030001080040a4040740700141d8010040c1c80303114680103000140d02420240c0d4034000c0c02954141000b05007403a2654002d141c0110f03030140143d002c0d2095075030a50713540d060300b00152604014203001a01c1c10b0001008603251200f03090700030314241b0385646040c031403001c080b0400041050440100c0854680c100401d601b004104c07004003202d90186042d40f43c00e400107022030007901805840c0d006542071110200308244410350183c40300804004d42010385d070500e9008024040743e162407104103000d000c9410340c00b4100002510841280303591400d0b045aa488800240141c1602c1d98000b01c03580c1c8081c644002c0c080c0c1005111207a07000030b91070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 353426016 1250 353424766 353424779
    0x1110c030d0c050f070e0604020702010c02030607120b18270111040510090e0a020705011e1b0203070b07030902041b0f030c0306050a030605100b0c030307121515110610 74
    0x10719144d603454856001c04c1d000c0000140d00304441e42c1c042000c175070041e10b0b5481400186c40c034030f00035800258035019010402291941229818004400e401000c02400a29800f03201910b280102280140e8041400080c40c050503441d411015098001c01c005001d910401240d003510700d40000034902c8074010805004904040d41259610075141c87d1510726a80b0b0040c0c0c4ca5040600038001607036035500040c00000340203003500300d604190005800e44d001d1400c20000740005201e400c1d0843c880801042e0343c012142c7c400000d50b101140c100d14144070540729408250000c11406108981050315211000400b40c01254101041075203600c40441200408100508030342c2d0421010041c58a48030081c4001e449885504054907484100081e480e1038129848108614a501001e00351000140b21a20548080041c50040640740c07035402c7c0800c034900c540c02c01d55007944850080902c03144410480303030041e41e5450480068a003072440c050201000b8490a00000711840266103190a4041140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 353427266 1250 353426016 353426023
    0x70305030f0a02070c030b070903231e1b0411030708070806040c0c0221030a17010e06130506011b05070302090f010f03080d02130e071409060901110c030d0c05 70
    0x2c070b001c100441c0382c80159a80d0440c14400c60002500750124840020912405100c40038080c5800104255001071003851095100400031541ca03c103016010034440382d2584440100340ca1001d084c013030202308a4030040c0d45030f40615040e00380d034843d45443c64a248000d0030001140a00c46590b104081d0340351828010b8245003024100300d0046282940d085070403a8444249518540e04981150604034a44003081a69050b01c02010050100203540c02165411104170314000902c0004951160798078080300340040d1003112204d0700b144840030003041d0000107911a079880b13a0141849416000c1e50740901c85400c2e6440d01c00c440540c040c0320140305501d0300c00070307083e40804036451950041d030510f1036403c0710400381e100c0200945000300764031481000580540d420342c1400e8082c10410b44d5140408a46014251400404505c0028100520410034400c03120b03880f202905003841c0c0011203004640d11b410f840c50060007030085010307910f2551b8003441000460b12880d51500030807030781c0b03007041401d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 353428516 1250 353427266 353427271
    0x1d060109080f0706030b040608070b070302160608070e032a0906060304020609010c06091506031101020c01140d0605190510020d020703020907170f011a0f040902031803070305030f 79
    0x1c154080d412201c2e10040005164041c0c0f40d8a18010074041440ca02140c01340680c0e0f048039806000350100030942607010005026514040c0d800c0720b4240c0b0324107003205036150041c00f80304d00003101840054402c5000381611900c031a00030301215031030341d0705403280705000c01e50241490f1030389009600e25200b480d103500840d800c140111042d40c43e41c10320354006030b028401c4007001e60602c000f8600c10300034403485178451801c032900144801d680346240200f0900030103542c00200c592080141c00347c3c0e055440000e80409214042e101c103162106d0310951850250048805844800c0d2200b80108098640e04136082e640020320b80301c0c01406003448100101100000100c40031540310807001803600341c0c005510401c803501031729041000c2d1100d103011610741258402e454401d80c038020038001e0552141440074101c3e11035103c4114040b4500351800351512945011b07000b108800d000c14049902150300960300003c0741c2c1d0381e0740084800c0c249501c2c1141c100308402e0300440c4011003004520b000d004008d42c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 353429766 1250 353428516 353428529
    0x50904020d14011b091703030f090f010c050a08070e030c0415120804080f1b0607060906090b06190305060c130302120604150920060c0f01060314010516181d060109 72
    0x315a40b046c207211656400700400e07150b00c004060000c1804880706100b4007420105040c020b005049420704068a16881806440700103120b210024903880d2150072400c669540003001b400079801034070100b00151148514034015641121400581400503500410405d4805e540158aa03854040c41c10700302511070706100903681141803200f01706030200041507040b8904441680e2103d6080c2450402002c012030002c29151501d50110300740700308202003502c10303c81101c01800340240c0c05074141a081861000801d00c0d80301d000401c49520007180a4400b024030078081c00d1400c0d41d070f0380000380c5203400000400e40711307003040042c4024040c0e40c00030f60b094002a01418000f409240d52500c6803003c0d8a000508407290181440c0d00640d213000859200c4c169503412101150300c100c104a0007005c0740c0c80b041f1001d01d0050013803450040107000d001e204a0110441100d1050144010ba5150350300310106490508070600100d0041280605088010042c0d020b00030b4914040c00007401c0010240c04c40d6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 353431016 1250 353429766 353429789
    0xf01140f102106090f0f060608070b07110315010611010f060b071b0302210c0d0201080f1902070605160c0b010501030903050d020403081c0501050904020d14011b09 72
    0x40c000e001402d85181c0d00e2000140c2d90450101c05070030160000c3c800810018000c10713103140c078042840303101581c6502031030044408112445c1d403410b01c01e42e20050f074403d162a001040c400300c00031410b049403940c1c50880141c00c0e11030049082640502c8040b090300a000440c602d6030310114200c1d0300340705100510480030310030071071541000c00203e21401091001808410b40c45800c1c016071104561300e1b4011940a4480605807a035240462000d54686580362400c3c40748284804140c600f59002032421a0181c492440790703110721008440340800182140d50aa903403c0341c11400b01441d01c0100103c50190b00d00080383d003802c214000c02000d4403075400e0b00b0481d50104030740124680c4410b040c110303002401e000038040503910f0196018061603c0400280d84041000028800080010444060141710600305000d801c0194411a4428081d640c2c2024010000070014205000c6070043e40d40500f805d01c915090030340a0909580611641420391991080d009548641108601d0041c02c20154403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 353432266 1250 353431016 353431019
    0x70b0115110111090904150f0209010e01030603020a150207030f030504030b0c03070f03050604060b0408010b03010b01140a0e04090b070e1003020c100906060e07050a0801050d0b0f07020f01140f10 86
    0xa60f01d0ba0700601c1a60361154110324007142c100081c020003040c13807486c44071050141a081d01520750081d0400144a400320380401914916503102e449145e00b0740343c3c002e2004160a080c01701256041501c641101c00307600c912240400800ca486404c0b8100501c2075076916620390841c0b400900702c0c00081d12080400c07030284103020341c003900801070014035040c928002800c0d03074428001038050003003503000103070b44034001070007107545201034210400340e000c1034000b071003003100001c011036a0640c01d103500b95210b0014018900c042c1e2113440c480184010050000c00c12071500e458106071003c0070344180c00401c401034040700460401354403900222059060460904030821a403a48903056440182c80190740c0c0c81560003005520340c01403000e406224a056a64076102038050003992001107102c1c00f18804000004440c0741a200009600313900c00a40812502d40540844001c800900324100b54001c440c80180d1001007440383c0d905c5d07801752910500341c0e401c0c1002c10302034108000c0c18100e07d09400303000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 353433516 1250 353432266 353432291
    0xf1b0b03010906091109040917040e100e1e0703150e1006111902240301060e04060501140a0909020a0f03050903030702120a0c050709050402040c0216140303070b01151101 75
    0x550715034106c256004250328105161661000440700000d900e258001708002c07400900c4c0d900520312a40f005a40c0101c0c5a44034564201c240c0400c8a85400c860945803070b00b40c60500903000d503074200070541808540c41c00400c0303604506941a8009165400700d0700108188064800c0b02a0001c00700f504000300440483c141d5940c27518803d5518510311085406a18210344a011240703c10310080540c1007086061004a054154001c2c85204006030300745104d200c5034074041c407401040301d8058507401d03070079212103940c80101d40100b09000148400c2c40e06c009103c4102d4002880880c10941d05c82990100168000d0101c1d500501000360a0703006100300038140d40c00103080e03000003001a401e0750316007402c01400c032881c000540c0000d0842c01030940011340001070b0b0f006940264800c8501740300411100d4012a0381c0c008058056404000d001d100f000000c074001958400c503140501900d01d4445903403078010741c100c0d00307034401d40c1c126044d0001a0b4501d940a1303a6800384204c114024028800c4002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 353434766 1250 353433516 353433551
    0x3020c0a06080c0a02150a02040503120f07060c030b0301060f2607030b0c070609060c1403150103270b0105040e03040e040b1009150302031c0c0f1b0b0301090609 71
    0x10b20f801290000010311005042c000c0000d40203104100c2446c01c450300d003182201380170f9003061088a0103803061004c5411030950000a4a01d090010a0168200142078407401c000d404800f021030113055681101c1c280756102030042101034804c50a0b800d220614040e002c80f18810b501d02400300e13210301c402d40f40f02d031100045510000c4941045800c0c2980d00c85010500d6075106820b03005110b01c0c5840b4800082020036088040301d24442d80b149030003011189803800c0188400c4a01411010400034604129030081d480982203488d01c5900424182d0200058000b00c2c450241c11b440380000c800040000f4509401071b40460509140590308092401070421094000a44001d051051600015516940204001c0d0007414492000e010620340700c00c8481003074003240402d0f8028042c26820903160780040303805640718091680e40080300042134075100c3d00c4869103d001c5800c1408007801d070310b0a400c000c903260090445101c2003a03aa514110145048410b1644002d95003230801500c0e29150f00009d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 353436016 1250 353434766 353434771
    0x91701050f07022109030313080a2003101109060f13120803160309080304060f11131205252c04021e06030c0c06010e01150c080904050c0703020c0a0608 67
    0x2c0090540b104241710020303040d0701504c0c0c1d601201e0300c01c2a00016003020f000502c200207a028110b00707425511140d20360075400d200342c40da2503010f900c9402803040036201640320300c804903e03c1866508080c00c24001603040d07032080a450b0701d00c1401146091840d20402802e03401490f128507a040c0010040e50764103410b0000504c2226407400b944407410040703000c3d8101d1504c0e2039000d03007816500d14042c585100100081c2c0c21400c0c100d032030517909040c40f03c0314408030340350000404030f11101d51b441d10200b50003805c0240c1003198103000f02010003421101d5a4217440280c2d64081c01c1c0c3d15980c0c10b003090504460b007080c01c804100901c580c80401e042c2403c2042e250010303015900801020a80500f18034a0070000c41440d420183c00010030201544c054090072000302c83d0425a012030741c1e94181828204400c2c000e0850440030720117041c0580d03018004c070664451240c4200b50034941c5440c002412280201c03145a030100f4005214030426905000d500c02d0074600302d0354a06000d00300b031401000003200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 353437266 1250 353436016 353436073
    0x14100c17130507060f0302040815040506060d020a120f050d03050712020301060801150e0a08010b151c0b120a11040c0807020c010f03060e040c05032406060703091701050f0702 77
    0x1051240e4405c2d034400e404a0b40130b0558030382200c400c1c048101d21804880b03401c0320141e441e4010440450f100d460507501a41c0001e8000384008141420590301c2c0441c0804080300f02d80c5030301800311000001e01d0034014005c4610f420713107000809290540c0041d15403020303240f00800441c81007005003c10754100501034103543c031850700207003a140c880c1425120f000c1ca19110a82c041e4040c5400501d808054014100d44581943c90329107110912015490034024038038003090022216409100950b000d81c000d100b07200c4014906840708485164241c2003032000030080d640c411505420780c8081c10140502c0402030b26a00c0c0998413850610700c002d4843c00580f44803030401c041702000f00c040d284a03803c1440036101583c007541c1c4500301403505c0400400380d44a0180603000d060f250b8100d00808602c1841c2a2030751701d81c6400b1503510a400c0040942c02008202d00b40009500d0100720f4a0700000c0703116403101c100c000020306d0705003101140b050807001055a030842d41f01c441c034039800012484100a09a04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 353438516 1250 353437266 353437277
    0x12070807021b120f06060f01020304030507050603070e0907030f05150f090405030408032703060c04090b0d0b0403050d0f0608030904020304062a1409090414100c1713050706 76
    0x85000025860400a00007040c3e070300c240030318500d0721500031907824001c0c00c00701d414222414184005980324080d610015000d0380100344100314a040180046a000d00c4130b00e0014649184180020040035090b21207000081d41c825070b440c1b06192034441c2a40160116201d09649983c8200080d010884d1180081c000d141031008242086010015200034159007800e9070b0302c40150040011003080c141c48440c05010142c08104510f090204404d409204500c1c80903250505121085000d06209907445802c14200c11894010a042014050103144213075075441d5610405030711001940e010340c1c01d11051600d40307402040240700000c00c40300c0c144e030f00b65000b41e160740d03079410101c00400e0491208440103419400843d00007010020a1441a0382c1c1c2d121110341d0315905c0869840c4d03005131103c07590404a490041030110340041110b4400c800450112040c10750203121302e4060780e5441ca00040030034010943c1c03a105000c5000e010fa8001405a410202001189c031010766075040e0b80f003644103008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 353439766 1250 353438516 353438563
    0x15091006051e13020409091502031005120a02060a1d03010c080601120b1c140c060322060c0e100305060904030e0a030c0f1505070f150f0504081207080702 68
    0x80711601c510f000382a105904544440c0d03550b921002412080b042124241c00e02e0b01c0d05800500d4610950b409144488144a01c450802c4207100c03040600301c003160413a200b00070940d40182e4801006002100030f035552a000e40f110b10a40600705c0c0741002400e442039050030241102543d12018007a4007102c01d1821101e02405042c0d580d00404540c00e9040e0000c0c51a207140481303940032a81600d03454407982014440050728004251200504007146e64444000c0001c942c5021221850540d411501b502c00305041c21180d840b801111180300922022440c40c01d115174003450520001c40b910102c9003003e0206240220008240d940c00900040130703c440080c1880698803060602c9001c0c6074010003424009803102842000e0029520510f0b440841c0705e0400110584904182c42d40a98405c0209840004968802d82c041640010002c0081d6440130003004140b01402002d00039401031014903521700c1c071000c1e404010000104010b044c000d81c1e505011345d050703001500c0c1402c00407000070500c03900e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 353441016 1250 353439766 353439769
    0x18080f061b070501060314060f0f04020d0201110d0804120c05030d11070f050303060310090f030f0e030124050307051e010309020d05010209100807050a051b15091006051e 75
    0x9000b1040e020344991318108021042103001c00c007441d8036014003000c41c0d0441d654083c001c42d20079000c95110383c989058002041c014244140300f8054240705040000c0c1c0381e50340d070007018036000f4403541e081c000501400602c010b0040030b400d9032111420b94607040040b00003a44032540d40344183c0903501c00555490050350a0305907d88207a421242d03101d007000c01204c0f12030074815500e4205071040e511a00480600d045a940944103101a4540c8407030826031a400075107041e00c03a07a43c41d12000007485400c80001c54180e4084c495070034480c0b00d9080d802521000e10183c0d103801c50880d04444d0203640114000d00c46a0b50700e402101503082c65004e624401400c62004070003802e40810000d400203ca050a601041019005818907110940e181c19824034501001ca51001c0c0039034050020940401aa81c103aa10500082654203031401841141402001c50245044e07140a4050b00d074925100600104030401e1000c8284200500c200380000740c10000003900319070403042042440c8042c0c42502015 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 353442266 1250 353441016 353441071
    0x2030720030915030403090803040f1205010b04050c0406140405090415110a1d090106050d0e160605070311030a17150d11041107050a0f0203160618080f06 68
    0x450101a10000400c420208040c0e0341350803e90301100170170510503020801d00800410b45040b500304ac1e4603412000d1070403004008081e00860306a405540b5031000c01c2e040e854030b0013414000e08408600d0303540c40d8900a001490000079051803410004200b10400c040d9488039029508182c00907010081a110f562003c001440480a403903121703800032850b20701c070316000410461210042e040c0011603104503010003a03007078800d006400110b58244079141001c41c465021890100c8407030211600c0c1c80c134080d081d191030f400c1544030b240010301c00502d84040661265010101500c1100114103142c2003280c042c0c0200010740302c1804a010760000100e60014500e10306020000c00f40010b40485c005041003107400a07a040168011400c05605040c1c2a84040442d6013180d0040080d190303a4405e0703a40d100d032520791410207a0707041c8038602c101c00d0480c1c4040d003a68000c04050700d54151440c2a584041180e070b03070300e0740802003a400848540460310b0000c5400d0768004015485042070440c0d07000c0c2801c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 353443516 1250 353442266 353442277
    0xb0d050c151908070306060f080417042d050d080304080a050f0a020d030b010914132a030b06190e04061e03150203010f032d0320010203072003 63
    0x60103482c038400103806582120429000c4d01c21580c0c107200c8240c8401d4159442080d0721155800102c1e400c0005012901d607a107403109440b00340010504d400c2e40c5001d0410b044100c01c0c03e030300068800b01d2003044c0501380701101d4401003c041e01c403051020220348075410715010040010b08030603000646144443d126004a885c1078610030445501c2c0c0181000003036445622810420101c6e180c282d41d40000e42c0100c85520444484074880405814039506022a101810740c0c40303c0a940c4030703228000e207001e0a0040810301c1c8015016201c1a1003400802025281c882200c40c0c020802040407043c2104d600900b040c9402d210308105415400000105000f000e4650040310b124043c103841c0098210840b68200803240180000182d40e090070154408030721080c881c148010328080000c2000a0904401a41c50b4242060010516056568040e528024010120700069075201c0c43c0e503c070182c00450783c52036101000218210300d0002000f400d00c00c044144d0144401701c440c8a10798810b4108202c5d007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 353444766 1250 353443516 353443537
    0x60f05090c01030501060e0a1a0409060b2203080a0302030402030c030f010e060a2d180614090a120e1906050901020f0a02090f060d050618010b0d050c15 67
    0x55440c05260140e2145041840140024103110000440a100d61011443c1400050807000c0e03549c50b05c401a92540e821417500740c0041c9041c800056040c076544280c1000303208415070719590b6a11020308111080d00301030700111a808400c0c06001003a520403c0e034080307184904005a0b291110700002e032905201010b000c3d414030400300840000e0030190044503285802c1411625292580400b100a0700c6d10305c0c81411170702a030640340b88035020207209006c0380d01c49180c0d00003603518200d0142420b103280b1003005542c40d6445040c01e00303036641d070301807503070ba00003000c078040e10004500e60365299091035241306a02c20070880c050101c0550383c0700d00c101072003c5170394131011509a1392a10080c080c2d0308005500390150082500341e424400002c00c040c4005a80105070111690300c0541d07019400e400501141c1c0c11140f480c02c0a40091400c000c801e00500c002d80300070032004803010455003503840d000c0103180641010755032000007400c0000c481000c00e000712518541c00c3d0b0b4a005088480c0503c80c01c02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 353446016 1250 353444766 353444771
    0x30c07020d12090501110d0507150f0b09071b02040509010e190203060f090619090210020115050612221b05010f050304050616050c1002030612060708040807060f 71
    0x1202042110b6030310002e480855221061507640d80d4006507014881a4804803440e0400c00e28207018500c648000c02005114006550905000e1011036080740c1541d40001040c50b900c015081043c94420314207540059185484009000e1210007010b2031081c0b02c00c000c0c0199120300118259440a4000345a1130000c2411240e090f1140b0721450700342d46070040142d010b4000c642c04030b80e2540015840500c1000403a00400c540e03154840c1c0ea04000c0d040e0107451500c20740c3c0b1151304005aa4598814251903460b07400412480c101303080d100300c00c0d80103070301c4184105020030220f1040c142510049030f11503424600b510002d140c0c0c0e801100301ca40e80780c1d4020002546000860b890808110800307003540d00a03a100400480440b01c01e81d6244001c0d9405170103036020340c1c00202d5a51030110550002c541c6860500d0403d102880e2031450f10410034070781d00e505a00070040000c54100081096803500310a40100102e04013204007030511280030380058510100003580e02c00340302c800e40000359041107a0408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 353447266 1250 353446016 353446039
    0x150c2705100507060f020c06070c1a091006090612200901030b070e0d0b060f010c02060c010e0c1c17070f060b030105070306051e03010e060a231b030c0702 68
    0x41207940003940440d41c4c0d034a8040400c4001440348203075207500c00e45400801c4203868080c025148584100400c590000b8809003030b0300c4445c82c2c00780050042c0b103020b000b03099180c560000e40040e111190130550003140382410401061416a0140305002d4000e82c66908000d04d00c0811030082d4114000c164001d0403000000041041d410104c9218082683d2403000c030b011a001045042180e0f241c020303099609410214a0700d14200c0d07200c440e400c10505100011b14001d60100714241c0110803480e140340d5603118046030341c2000f8030607040c4489003160040c40655002142d281040d0580f0300203040b40d10100440011a5008002c4072026030b003008828842c400c151410b08044e141000c002c030300950a2802161003030b4020700400054900040c54408070012002100495903968100d0650564a03000880e40300c1d40d06000981c012450381c171001c140640f44014507000b001800013004020390001c07013040842d94a010b00d164001c1003601400c1ea490715180c03240e81e882e000f00503001e584035100510 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 353448516 1250 353447266 353447299
    0x20d1d04051e13021e030102071b05030f03071211031c231608130f0501051b0c03040b0304020406171e0705011b021912150c2705 57
    0x101c001d2030804a0b84200050381e2540c2e02028a000c0c1020025048440c0028100ea035501e540f200d2808184058001030428000c0e495000702c0b03410b00d2010105004952506014606040c0403d22040001100a510307080040e0f0300c42810500040e154020001c0703007000801080790900456004800a05000310403581c0081c00c0c200500c1c095048280d0b1040c9100070400315020482041d104001c055103103031070b5460503c0150b50b0080024101840515900500d03400680d103140880e0119000f24000145407802c103901c0542c03014540e500307410030401030087c00c40300000001101d040d61008551991651100d00c00305000d805603030007050505130b40e41812078900400107200d000c05a0362400314014904001b03a81c54813000c0501400d400585a00e80e00450143d030340b8140442c0502c00740072040e103180c1d0030b2152410311003035801c00c0d4020802c10080500784005803088820741c608000b0100902101d80304094540b200403080c06003511b100c805407446e80b0ba804d80c0500010580500510f070452b40301c1c607 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 353449766 1250 353448516 353448541
    0x705030604060f0c210b060f1308070501020c03071e090914010609020a0e040504021207030f0308090312040b09120307032f03040206130f03061d0d020d1d0405 70
    0xd0368252161604503c094a039200d602102c000b0b60100c040045d031500003450010142844c0c040aa4000108210241c8412100d030700502e816031040b0f042c0c3c096135041c80c1641e070409030715620036411903010012010442d82c002c5400400c03a440890001c100c082075000380043e900c01c9034044080c40d40f5244040080c40301e102e015016000c0840000c001081d04d0f0f50700d134412070042c2c0103480e001410160054071070303040030340c00260400d00040402801c002d00d08036051030190980c20449094032a0406541059002068140c00c00360f448042d40c02d00c60032a144810081c1d0080019000744518004a0342c203a41c00d20001c50703501e60207440f0320742d00d2512503005000b5080680c555003c8505000181c6501c07001180101743d460f65000700d082ca1515250204070040d006060b841e0325448a40c04c0026283c65910b4101000310300c41c44c0d006c1581c21700c00d045800750349060310026510341c01580c000d54003141e010403c0c18103240f80d0f0602811000304004000301e00c10030380d412281c00528100070300c4880500b21 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 353451016 1250 353449766 353449781
    0x1080a0204260a15090b07140f0d15031b09021206010807030902090411030c0303031608060a0909050c120a020a170102070b090319020d0507020d062405040f02040521070503060406 79
    0x1040303042c40c82c0d00c0710041240d008c000c4030a440e503d0407041c80021a0781074840c00030641d1070342d056400300e41600310340456903640080d0b510848004210402c408180d0980086000090a58074011414915500984402007000420040c10031080340300185515000750301500d030701354014044c46101e00e041d1906085841110040d58841c8c424005081e41c0c2d8600001240d04c1100055110b07441660462000d80300200b01501f00707a80526900710205291600c2d101d0303c2c40c258000c2c001403481030402002e0012241e40107050480541201e5a00d43c0903880302c01118044448900d000500d001941c4100c500a0048130002001c0034429001e014180303000101030303c08850b022001214110b0204020b0340d89001d518444000b14400b40040c80140c80c0400c0e550000b00d01458004c554503c2c00c04541100e045040009144070101c001d060115003428400d0401540c143c0001310320b40340c00d12001070440c8940348412450540b8800d240041004d0900200340240000b03130403510141890b151140207481507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 353452266 1250 353451016 353451023
    0x40905190f0e070503030705030412020307081b09070302160201080a1104080f0c0406050904080d060f0902190206070203090d0609301704030f030b10090501080a0204260a1509 77
    0x20f140001c541860040201c03040a50b22400440c5480e14001e4000c1c410b98480c032003607130f15000e000e10000300c5500c24443c58900c04910000d00d41700c1204030301000074510000e002c0f0b0b420544140008014102c0904068100580900707141c003031596005000c001904a45071181c004000100d40040c14000001c1c0801c2800c200380140c42404424005010440d840c80c0300c0c07a640421403601140104a51200514000714a90008260b680d2100c1011010074540d03130000d03044541c0000e141c5a96600024049141500c51024007628140400025902d010302c0c501c140c820b00101c0c7c00307401000031a030310240c0305581c445c001c105440c03101d86980080d4907803210303000c0f91640ea051140c2c107000d101e02c603200790950088001178191344894804036107200b00360b095403080c03541d514a1103299503074003c1202000c000940c1c0d40c041090400000500160b0090b1550b50118014002408a0040540e42c0945d890030304050030254400d0761007031031514003c41c202511080c1540000900c140d51900404101c500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 353453516 1250 353452266 353452273
    0x170a20040609180f030c0501020426010524040b091617071202070f02040516140301150e2b061d061512060a050106080f010b040905190f0e 61
    0xa80b0a580029161030403501d00b0306030514078041000540c030050422026009240c8030444440c6030f900c007401c9030300a07004280317011401d21a072003c49004e03400414241c1d688800902131402c08042241740a0041101e02806041d02c444030076250301c8a600008003c48000d150203130704e040451110003c80c81000104001641c0d1a6804400400801003907000f006a561008104548a0a410b00940281108035202d000480c1c0b1080561384500072075008d02e001c0c0210b8006c01c41c0b070324000340c82c41503403804803080424103000412003400c6402c0216503109070350401d0000340100c40005a1103042055081c88600c40d07035140704101e85e140800070b0000724410072040250024904641c402100c10640110f4958490000070780c07208180d480b0f100c2103a00181c04862064031010044d8182002101c0e21016155110010000154080d0981340c111340301c1c00300c2e02c0ca5941802d050503a944a14003440c00d005071900c0201d21007801c14045021419911170b070800c07001500070100c1000d0301440d01082c01520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 353454766 1250 353453516 353453519
    0x408030a0c02030a020703031805030f061503011a060904230118021206130615020a050105010e0705030403080903040f080d03110307050405040b180f01030308010e0709170a200406 79
    0xd000000304e54480f08150024240c85155903000c640300d08024000124a0302940130020b5640c904019219030360070300402034004d91070701005040b900410501c5441c03003681010801500b0a600042408285a0581d441966443da00021501810154068100100c44004604a600086400d441c10385401c1900d00031b158103044402c000f03a011341950000205e10b40310214541e454130100721401602d1222022403503654405801e90400141e0000c0f00140c0c228501031b10400100380311703c0d4050155101180e8003424007102c020294000204020207000c2c007036000c1003681c0d001700182c6000f4a20380c400300d451180c8801915455020701154200404d00f0b0002c500030300380120701a81c2c4a10503035940d82e41014544070400026050000480340c01c54003009500010301c000301c00ca241305841400340000300c3e514628000700740e980145d000c1880c05004100707100203680e020080100b116010554055128050b43e092406c0c1500741d28000c09141c0c4800c0c1000100f10b28004000e03180c0801c550400085 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 353456016 1250 353454766 353454791
    0x415140609061605060403020c0a03080301150e040606020d0e180c1b01090c0503010e0d0210090204020f0a051309020c0a060e1524030c030706030e160b070b06121c12050408030a 78
    0x166481d0200420ce28000e100500c00007003940800c100b220315074a443c4110f5103000d4003080c102c514581184006030001d50030800e080e504403064981a44003030b02c03800305800000f8448504014003908450407403000080034665402e998542003050005100200840c01e41e515101580051303d10850b8069424601103008880002c50401201c24182c0c01805500c0940e1500c9c030028001004102e0f407040c5e0902c40310303503041c81c40c6001d071a00d8510783d11207a030f581c00d840150b0041c5029940c40b0303c0005004201c02003400402040500390154001c05c00315840c12034400290420000da01d07100403025104082140e46a41010791aa80b03540c100d50384038030802102d0074981c6403140e54000c103401d60f201041c1005010320907407040c83c10907010819030790707605c0400841c0300358020b480e4407143d84514003140c1c0c0c00c10305c000e5a4460790001d20448148004200d10910300c1d031901c400c1488405200c0c421046400d40d50b00608550714650380078001001a460149015a010780041e00c480321003616000310566503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 353457266 1250 353456016 353456029
    0x6030506091509060102070315020304020301200409050c0d0e01090606050f01020a0807060b030d110c0108041a2805010e15150c010209150304020415140609061605060403020c 77
    0x42c65961180c160a940d014041c01968031003d040b182c1144500d0303800001140000e510805070f0340408002503a00e0805004050039605d84a441580a00340702c0900f203400c200d00001c8a04941c5506004116940e0310600d140301c50284036540401d071401e1001c402c0050034190311401807184640700800c038540d100d20900c680342c0004200240035900003841480400c0054000d4440503110b5000810140302000100b4200640d04e08507002094454400b010700c0d0005000009100d42c00f03180c201d00615250b224011903055100d5001c0313100e510782001c200d4141000c10000b0341d450301c5002d4a803040801e041d80c1c4000781400d1141a040542070f10225065585014104120800081040420b402d0004400074560710548005005c2d640c03c00c43c181303143c0c6031245038000541d1900e025680724a424014441591708050383c0110101680384144a554802240560511401d850203620f0320340050100e0b0540c4034000b031020000b185122030b4010004d000459a103d1480385d802d84071440c5540080c401da = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 353458516 1250 353457266 353457271
    0x32b0603030e180c0f09121e10020a0f051e03130c0e0402150307180e010311010e1507060906150602120c0c04091e050c270a09140d090603050609 64
    0x6010b1810010508125109405040411300003000c0050300110100390380c0c40d041c0c3c048d0f24040580d0380c0710040c40e85014103110402d02c40725244429807502c44883c800a103141000403c4400744003021400654000c500b03034142d018004952206a038a003003c04080030120f200c40303412142c04501000c085100344c1c501d90101c1c02184c1c05490b85042e07200f0350030110f0a6410041c00c18042015511881002c40c1c00b117004003000b400a03824070404c0354114203080b00100c2c00d810b03103c1e048c030500440da14929200c0050940050b80000410303525403569141080142190840c0130780840d0929000310b075501c00c52802c070402c9562680845150610108022100b80581281c40e1f002d90000505201d05091a41150b03410510403c00d0350781041460701082000042c1d20f100342d9080d40940342d4032000d41810720390629000d0070220300080b10038200c14200d41d040c80080109a03005c0d2914440743c200301c40402881c041807401c0c0c0a0395802c02000100030003001da02e1003120002800c06011840c01c1c24402441070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 353459766 1250 353458516 353458531
    0xd0f0c0522030b0402040504080f0d140a090c09051902041e1e0302090c072001080705040506030a02090303091309032a11060d09051b0405010602032b0603030e18 71
    0x108a0780da51780801009003c01001641c00810800c1103001c1c1a0740342d0001e005902800a002955001c402d00d40300c240b2400510640c40319143c070f40c20001103041d83c5400030481d146201e0103d0140d1310800030409042081040c895200c1c000308002c81c4090300f84c030aa030944c0b8404003c014419070f8a84010000f00c0030440a0395506a03030420a0026040c000c1c031040d44092542912440d1800c144e440022516a8180886640724130791040c01256034404211600f04500386860f50400b0b00740700c00600f00c1d03c00070705880282603001640046548081c03055502d030711002452244011502c080000180c800020203c00092a0102a84d26000d42440400ca40301004c40440d041c4400c0d0b643d01d201142215400a0740310a0601c08140c04008500416640c00e01c618040c0c82e204082c1c10f03000340038a40e103000c1e05101d1801e140041c00004e5001050b0340d01550040417a500484c03d20f55542c00030303648510a8004981848408818160400140b81440d4025100b13103041c000d50703d0185003181001c0c4c4401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 353461016 1250 353459766 353459783
    0x12080d0e1914030f16051605010f0e1f0903050d020109082502040509030c1506010c030c11130e0606010c0203030406030213080709050610030b01090b0d0f0c052203 72
    0x801041c0c0100c42110700000741c2d0103ca140c410494151304a64100d101502114038078544070008100050004102c1107254024044465043c40c001030f1007010480c00240400030314860a4840c0c0c0c3d02c40c03410380c090b000210039203036a113480d40b00020014505404240d03481c2c1b04440340c041d162441403150b881d919801148490400130020b9098442d440f510000790240c80500c0200c0c40076035110b125182c01684071800031a5650f0680c01c4c03150a10305031074401600405d8000821200740d03041801060440c2d03151070800c4440e4800c1c90004502c424090681d0f800c0410307100f148030160615403090f1036281e4840c08640381c3d42c6e503020045a03541d83c0c07030000a4058006101c00c010b0030303000e60094120020f060189606503510b8008aa150400c0d640c0103901c42c0352110280202c03800c0040c2c41c20540c0c149803030188010442540040c02040039449080040c076000205001e1540e620380c410120502401414000c60320300030402402a080440344402d2505401c601e2140000c61400030300803a940030154 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 353462266 1250 353461016 353461063
    0x30302030706110c062e050f0d02010c050d02010203060a0b0c070b0a030b1f090e040b13030c14060411101209030309080a05031e0609040605090712080d0e 68
    0x201405000700c5500e00c0807003041807242c2200c00340305000742c52151800c1c01d14192507a42d203481c6d07910410b01950074542075055455080c00161105000c040c005d100664180301a00320380d00c0101e502c1c1114400103000d50007050707c101015a41034006600841c0704942421a140e229502c030240d0f40705101440120780c0c060a410050b2061041c0640313050021800e0019400c160440400e20100050f500c40c0030000703c0305414004160040c4d41ca0380903000c41088080249800e83d10445680350152043c40001c03180d040341c030109446000800665584405c00c50290001c041d4030a9440070142c808803100b201e40c16031820582822044910003405668441c40c0780a182c1100c00020701d15650f041e0100b645924400001c905664001d10075841d550b541c00d40ea928041d14408150035220503e8981e480a03c802e010031503989090041e00107400c4480007420346c490300d4000d0701d400c030741d9488540250050142c10042c001040058613001031012010b1080039020071116884500d8070800040807000400b4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 353463516 1250 353462266 353462273
    0x170a0c03030b0f0d05010510060c0f03300506010801081612080f0406020601090b04060b0a18030204060902040e0606072a091508010b0a0621060e01060807180303020307 74
    0x801000c010010340b5141e80f82500002040108500301c400f03035101d0b9101d1042c07042801349403080200034040e51a04e5116000ca5039038408030038041010180801c0340f2132450688a10b0b08001c3e9598116414614a0318000074a607860013900040b40c1060100b244240001072010010403900b1300114885580394a02c2e003000d41c0d128041038501403c1d03601d174030180030020400d1445002000030340900d4005185941c949821001901c081c08a0940a0b900342203040000d000f0103800d846405450b030074519120308010034080d07650324850f030019602c181040390025215203035900400551700b43c2041d58025544000c2072000c14819400018180340c082c5a031070b0101d40c0420540c03650303514050503a00f85265909500000c1d681d1143c0444802400307038208220541c402d01c900c110b807900039544403203900e1400101030200681003070407001b98001904070142c5e0f141264011005001e0120018100f542c4900c4001d024810464000d00841c000105603441d0131044100708040304d40c942d008510f002400e54 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 353464766 1250 353463516 353463521
    0x1d01031511040504020d05010510020f0607030f020903101b1d120a050303040c0e012c07090e01080c091015050a0c020907081b0c0613020f0d030507170a0c0303 70
    0x15031803410703400c0a01010070240d0f0f80d800205599901000041401d50500d000c0040070300c5250504025548849048a03100101098140c0d004038203060000f20141821040d0010f1311030101c81039454014100071070f1810141d41c2c82243ea20f4000d21541c2c4088100070b40941d8480313001d40c1401c4000750300c1c50030b07103206160041442c0c078941c69400644001c1d08180d80c1d030314919001074a080342d580c02840401d1141c5880000b449006004145245c220140c2e000603a00442c4405006403030420301d0300340001c03000c50013000498020400828100501c0d80d4901d0400d444041a40d0010302c03400407480850544100c21440009807181034130602200900e60304152103941c07000c1c5030002444184c4603000c02580e59200700038407610954840105070b150050000910400707810784015204002d000960426100094503544031040403039640314038810740006038503a01900301d40341d802501a14003c00b019030040281410380d1040c607081e103401400030b88010f02406022140800122080303a2000420710a4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 353466016 1250 353464766 353464781
    0x50403080d090b010b0301030515060607110a050d0309091d10050402012d080901290d060606021e06070e1e03100914060915040309050901030c1d010315 67
    0x141000820010300d40e20200b903c1c070300340c1c0040740c914808030040080c00404c0c0b240302a15041103043d002980f5050740019820b000d000d1000c3c1002070f07202200700542d204c04046401821000780800034803071961070002c00e150940c2c0607100e4030358182140504003c8a0040d100c14030340000f0058592a26260300c82002042e0050003641044407181071a800140320007034110341d981c00d605441128580c3c03542c026000c0c10b00a052025680c0c5800d071810050007141710b2480d03409001c985100c9405a07640005980c035004d680b0050100c614110340001c40d940c0018104901054280004a240308400070164540401710340090110300400c1580f5640e20304901c4c40c07010801040c47d0400700f6410303200440e180092100c800c80f440c0ea0b4900e22070040c0186001090500080e1034000c00c4145020b10704a03498603001140095490f101c40d010a04060103100c1e01c001030203010b044430206695078244888545803500c511140044644603480402003a821141e058a40007a03540001304140c544200082800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 353467266 1250 353466016 353466037
    0x14010c08181008040210080412050702010314160801080d0807030c05190521130807080d0e030d0509010c090b1803010911040c0503010e040615050d03120606020703020105040308 78
    0x341c84200426903031440c840380718120540d9600d60518252040c00a421258900c02d014400410108400622920512803118105117000d645850301c3d03100580c090005c000061407400780360380c10810541515014090300d00140c0d0b942030f105903a41c4600a407605004000c00001030500b800140030140650400106051180303801c03440c1101c141c02c01000d0301c1c40c640035140056000100c88040340fa61140301010a010440c1c42c4555040210100680710410140188802400f00e001030174041c4010560300300d001d109105202000c400c4a15544a520000d5181000c9140c00c0100d65541c0051045000c00311590300e50422441c00d1642060f9550001d051551094600c0d20803e60ba54034203015400d403161091200c0383d0f006228504000584d03000c803120320b00300300342403004000d6030b1400b90030150030a41145001841c0a4140201140303000c0c9600119042803d495044040551008040000001d00d020030407442e074803020200d031200414800a800a041444240301003014072000b021034919 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 353468516 1250 353467266 353467297
    0x80c0702060c0d09090605031b190e061003020a0806280b0c12090d03030b0a1a0703090f08100e0c0a120506100b070b0405011d010c0914010c08 63
    0x455030014003580d1221180103460703040348546000503500031a01a004d8000400244200c82c00c14000c07a69840c0740148a02d214107c044611100751583c84604910039170300104001001d455075050040d0764819503440340a0480c0d500740345d0409100c3c0c400c0c0e5580726065502e888480d11800200208282d00410240707410070f640582040d030a0f0003107004001000a020f646807622511941d141c18280c120080480c0080d081101000790795907071011182035a03050074005601e0a0b08070200f45400e0179900018000c2100d42a6a0740d1008500301908080b407090781c421840320713100c51500003810854800c1d6640381c0c0c000392031200500b28540050f015a50b1690407114020118000101007503420b611109060000d40d80450502c0780c2031000c65400f004075503c3c4c54a962620992014610030024060b00802c41c01021030100402074200d60380e500754080480d040459184034480c000c004400340708000c28011240080c0348480801d010080800c141c43d119400d400c0f0340c603442c00d03981c4880c2444406a4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 353469766 1250 353468516 353468527
    0xf0b0d021c06030f290112022b03020c04060b032d0c09090a0905071502030d110c1b090105210a0602030613110f03040c030c08010c030e0303060f060a03230709061d01080c 75
    0x20310010000001451040c406842704040c1d0401074185941640c2442c01541000c205000150704841100d0704030103112030030030341915400c041d2019400c4940c4014203201100c01804080e0744075001030084460115401d100d16141c1c06208000c95002c050010f1007074000c1c1c01c0401000c0242114880e85688a005582c68400221a540102c81003807400d407100102c00f07e415102090200a11340320007820304c0100e041003000100080340c182c0c051143c10b100d40700c40100d00010105656400d1940280b000484105c10071501c1c7c500c01035041122a103000d10403402061910310114082c0c440b5045000480d246060982c68200c00154001001520000c1c10f14400000007550f45d41590300500b4088000503c3c1005880002d054070402000d2034102e600c24400e00c2500d40d0350307444c4207040a45c1165019074030041003400f07402500c1c00d071020007003800354640c0070002078421041701d9100390781d11340c5c034440301070386655064035440d003c5030300000c1c2e4084c1160105441d50007a080e43c0c1d0014032040c040707820074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 353471016 1250 353469766 353469799
    0x307050708031006080f130809010302120a050a0f091e052103160f120e010b0a0314010f05010b0418020403080a03090506010f0b0d021c06030f29011202 67
    0x103910543d00303811220221581080050740c40000aa04080805041041400d2961061150391040440508500340014582406a0007941243c0342c1880703019420942c0e10700707411840010300b0100c608840c0e007424006017410a0b1810b1003500d00329940030341644110540d11584180718000c12608a4241c400d010240107020520489818440010046135541380303000300001541605480042c01032240d9140915002c54100d1110320340003100039030001d00402061801d902400705845841d40000010301c01105100b204550300f012a400d000007480440d010307401d00012a00f0920a1040e09001403105000b031201d100c111210a070313081c0001504041d200e40350440142d1105080401103940d81105d801045010300040e80188503038103c1c060224034011002c0402d00c00c1ca012903210b142d00151401031035000091007a440507202c40c0c00c001d1245c03a45080600f000204600f03845010704455a0013501000040705100d4a01e500c0e0304d1182d60346032155040b100e84003d80c0482e4001c10103200c50081 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 353472266 1250 353471016 353471033
    0xa0801150303090f061209050c040507122304170c1902090a0e060a0b03070f080708060c0304110405090307020d0c09060e0c03130311120d06240503070507 68
    0x380c0403054820300a0300e5468090718008082c1d105240c82c242d444010412540c202000c04c211950001000c240c0000e41d2030100d0800c0d50b10028250b01a02c0c00090041c200d074009003882940c0d90791142009188600a0011881b40907280b0206281d09803c001034001a0f4000d01511031000c01c0030702500b84011041050b0601d2120000090010510414081903190501e0300c1034200d807107040100082c0385071040b0161a1000200665504c907100c4040c0d540c81e490400c8844014510030b1540701d01140c4440f0103d4468202d44110410b500c0f82c1c2001c21001d80c6a50200ca00595001e01d04e045c00c200d0710030511014140c018504100740c0011b001d044003607220259074081003403041c4c0001440703034102150301089a4458005e980c20254080822200b00040c000b16900101030514181e10300c011344c0723800c480501095986800600650400d1580300601300080c0046000b0120248111915400720301031560806c100140414240b02440020500410043d5004141031038160f00d40200d941f100d026 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 353473516 1250 353472266 353472281
    0x1050f04090e03190c0c0308160204020c0303060306220b100806130b01061404030b0c040302030a0308010509010b0307050d0c02010209060408060604050a02031608270105071202270a0801 82
    0xc42c1c200042000c44842c640c1040030004c004e5081c55080300e07060b5121107000080c1d600000f4050300002803408103a048072695511a55801841955291403541e0f007541c2729042624158003920510b03010541c01c007061007041d33040c030901d940c0c260204195030300d40720700111340606003220a07440103001185502c801c1c17204510908a03011062682011441c2090791210142d0002d000c1020802c840e407000a548001c450459820078103031001d0740c075080c040030514880d541c0002e41c144100c80d0240c0030150091100c038100c500803116100603a0741c40d00b41c04035900c403c5850f40d0009808021203091000158004000000c0c6840014248410304010402c0355025400188241e404002000014541409129400400685c0030340c11414001c142c00e5420741d07040c4000090000074000540c0001d59280461000005004100301e2a064070480c98000c1038251040b0001481040c184001e000b0a4003c83d0048200c2407180c0906901c0070810322498210360740c2055011802c1200052009001d026614 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 353474766 1250 353473516 353473541
    0x120513030c080307151b0c060605061c0e0c010c060e011e090506090a24021309020304030e011e0c050c090c270a0b09010e031c0f05070b040201050f0409 67
    0x40d034488880c00c2c403c0483d030305140d005080908107483d11001906c0c100c45081444004e08150300681c145182c1034000d881c09403c466003050021074012070b030854002000310481c1d01c1000c00c1099080d030565071512180e0903601c25010030140703c0040001605a4001124240b00c0000010f080c0c2000d441c450040403120500c40ca8691103440700400d102c000e014094011070800000c1590310070b541d50f110740c522111203002c2d00070192a0351045110480c6e1301250740019549544400e444d881707058600c003e401c1614283c0c00182100404051940a0003082e48a20101c1d403c0703222124200360100d840f1313290b140003110540110888007403540c40d103190f01401459400511a141c07504999401c0341800c501c03e03103010708134400300300f0703180343d05c1e030501000c151440b40081c90791341c0ca00c600041c1c5801070b0840e80300ea003610866900d502c5d40801c00030881c0401c2000d40d030740b1390364529080741141c2d40c1c01404006085d0351659800b01d0019801880203141103803802c480ba50500b6601c0c1300c1d04044075000355245 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 353476016 1250 353474766 353474773
    0x4050a120f02070503070e011a0f0c010c140a1403180105040809010807090608241f03060906140402070512040905100501111c02010204080d120b0904120513030c08 72
    0x80401d0380c0511859020340300030740060288510340305c4100300000307040c4250140020305800c280100c180220413110350910002443d035035140c00d00b014078001c0011566283c00280c08031205010044151308584e4000c440c2d0b41d500c00d84000120729844558405080b80403441c209003c848800c0c0c078280121446070f805131418546030400c081c000341050304001c0940f0100990708000340803080e00b10360310a402a00401e408a42a9660b82060044403000200d1551281603442c48100e44070301c0205a40011107182c2d070508c01c09076a400300b20140c2d1312a01854204603280b0604850340d0400e60f025200450040c8212409041c1d660413200480e13009400403a180da0b2140100f1240c075888100601c004c21088c80d1127401240518603058075500140700084040d10442d4031030580318401d405880140c0f4118095481507607501c00c000d0840080c401c20307162420300b400d0299a180c6070580c512485213802481e076040d01c4031507e07400c9446522201e01260f54110b9504080003103054061030f02d02504048005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 353477266 1250 353476016 353476037
    0xa150f0306050105150c06042901150311040503030a0804080d02130906120b07031d060a060623040e0a022122021e0a0306050a0c0f020102040503060f04050a12 70
    0x5c3c41240c03103201529031082031041081c254808400100396a220fa0014214105400e400e4418407103c00000710006400701c1e114004140354003200c030720001c0c84d041030320108064000c101034040300b801a4403030700c0d905400034815039031100d0240070aa540188034111040c50060301c0b640c95800c03600304007202004410840310611120485205a0003e006107140011900d00d80e50b6942d8854080203046408141c1ca582280d110002c1c00381d454189080060290340f400c1c50050b82c4c400050049100700c10000e41c9007507071000000701d0200c4100c0039101d60458140342600741f000016046402914040e00507500704041025801c8503070544415040380d8892001a0030524035088000050000d070311004540d004210005a6170340018446031500f5050300f11200041100141800c0d18550015002c281130000300448260240e0125250f120300351036010100440d000102d00300d000783e00815415038400b401242482c08170702c403450b91042c8501c2c11568108010380c0e40001182004441c5070118100110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 353478516 1250 353477266 353477269
    0xf13150e0127080403060b01050c1c020d0e060403030e030a1202070306110309280605250504180923070e01120201080f04080c07030c1e05090a150f0306050105 70
    0x80c1d0021521804552a040c602e80c0c880c802648514031008194a5072000c002015901807001e50341300d030042009980c074101002e00d14800031291205144018041c0e8000242c803140542d00d00610303988054201801c0a0443d0b4040c2c40c140001044242d052227010150b00000300d0411001e4031000340c5a0182c81038a10398a00481501c1ca1520810702d90b00051003040040324000800070444440074442011030300711040040c030300c00703a0401c0140010341050700700074030030130040c0302c0c41c0c6a141590145e81140512003c11900c84c040da00540c80c200c0036206640c00c2d00c9075580c1049041c40d000b0101c2d51151646528005000c81043c1c0b00c240042e00300c40340400c030b2075200803117542c010f05185214040100b41c60340000c1031844002d00001840c6d884c14041014031820b281174400e200800411110580e0b164101107489001034400c00d00410038100450841c0b41ca0b0103d010111007028182d20b22071303191614a440940500c104034001044054030002c5e01c0d005840e0040c0042d40901d4000480c2e5040c5030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 353479766 1250 353478516 353478551
    0x50c06010603020c3408031801030902060301140f0409030e0103200d1113030311060601260703090b1005010e03010501120305370807080f13150e01 65
    0x784048240b40c0b051207441d00421000c1041c4204d200c5a80911007000c0107603129015601804007079070030407200d0040105803107400000a0900040120260910440c0c0740011800e070345800303000035084034061004005580340809202074a00b4010701c150403890000020808480445005600113202c0084801065070541300703001a46088250720781c0d00c2e040008401800d0f105103e20180180d548a82030700c0e100d07413804199040b00f0155100114010354909000781550500500d1508034020000800d907a503000358044030f0340408400004802030700d030803041820420300404150505459040e44400a4120003c0500c038180000c030040e840b50501000401120314811507a0207a89400010b11030302c0c541c072601481c1d16a01d8604140c0d40d0081e414400c014180b01038115005590b0002008121001201a801414032a41e00e101d807a44d02e07281d08a83c128419907041154042403004111621211444120000d01038058801c0c800d10004000d0100d074906102208503940d41c901070b02c0c000724142c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 353481016 1250 353479766 353479769
    0x103030e03060103120e010e03030d020c10060f121b03032003132c010b030703050c0a0e1203130f0509091203060103091103061305010c0f080c090a0302060307050c0601 74
    0x168002c040a605540d1595107940300002c080d002d10004441c6801c0d241c0c030a0034400d07042c0002805403512102448200c0000e500001042c500714040c4856001c40c80f4154401d401c1184c03108600f0b0189585081c2c101e40c2c0c40c2c40d54507800c1c0d50a9414014001401032086c102c40000e44c42991040e022601c55020721700f0400e240c240301e11183c0c00030000710407402c0050b4880d4040d200d40d0f803038054288160202100301b601084a521001c00d81907070000440c1c54480024610658407610180700641e0380b0401d01540d440ba05a900001c903440e103240103032500308440503080e900c000404407440c10110740e01c419402e4242c1c1e8042900e6000801c0c00303001c0c1d030070202e013213503002416071008196101c10304d441e02006000040c00c2d5410590b8a007001c1060055503003500f5030108029003501c540e42000c403a29995a80114810f0315150300b440ea440728000d1003030024a00000095841192545510282d10039540c002c0210310303848401403501101581e1341100842c011f52498403216506d0702c15154403810040e05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 353482266 1250 353481016 353481019
    0x10080f03090a031211100203090607090b0723030c0a140304080d080402041d01050603011b0c0204050402130c0c030e0a030f02060c011506050424090b07140a06050103030e 75
    0x9020803060754542125980aa980c890701200c2075290204003180d48000d10b02c4803500610401000074460a0790b03500440c040d071900c0040d55400d640c2c0d0b410584030100e00340b0174000c0d00401005100d01141001e010040492400950440d10020b0b080c5014038607002541d11001d16004051404100544a0344010f00c03500340c00c0c0950b00b0b191820b48056210b01c480e189080c240040c5900040c115540c40c1e000d201500c1008100840c074291034010300b80286000ca420a00942c6014108541000107114221170b0028941d20002040302c40d60070304c0f0240001403c102e1f040a060051101a80c2c590702600801916a03070341c1e4092450a8100240349000c007400d218003600500005001041031100801c040316010384806540d152140c0c0300310b005200b69100b0300b001c0d00c024400814140e0303108000b082180c0400c104a501d08181384080c42c3c0340c20441d80c1d00804552046410400708800501402c80e560098185a5118205c500b0346030415082c20301c04c440c829a81c100604c1010741103140702c1681c050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 353483516 1250 353482266 353482273
    0x70b0c0c04090809010c0809030a0308161d0d0614043804201203030105100306080d2312041202010509060f0604060f09090c0605130311010306050910080f 68
    0x169100c0f58028440d10070500d0400c520130001350103002d016001c40707072001e0001d402c84078889104d050013042c4080030360749002595142959140010320584100b600700f1100003011042e501c0f920700700300112040c090115600340c0c651800c00e134101404000b80e4480e44c020303d1030690202a4402015500e40402810200c60445141512040146d40000c643c01580311142c000c00700000c11000c2203481028886a6009000c0341107600100d6001c4050b5040341c00680f001400c00c5c1c05910f09170281c45003805805101d0744031090002d07610b48104089a44c410360a00520341c0007030b41c0340a816035544030419151301c007030040e01482704203c0d030441c0342072101c610f900c001c0000342012074079561110809041c0c1040030b0341410114815944a41c8104003c0003d561100821581c2d1700540380034010001058488040707940c40000c0c800e01480c100c0340006110500c1e40b00007800d40d0703541d40c0d541650754029030405540c1e20012030303652141c008190282011003404130166140ca009140381c204161001c206641 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 353484766 1250 353483516 353483531
    0xe03010207121404080d0509120102180f0609010e0d080c030406050406020d0309050303070c1407030b090105060109050112020c0c130207051213170102071b0e0601090605042105070b0c0c04 83
    0x40c5c0100304441001214500650b41ea20982e0000300d6010244080d0030242d44009031880c4002840e4924501081043c0e8401a140c5401000c0041d54000c3c0b0247d00c3c04a1403201079803525140841e4a00070300c9101b2004242802c0b8805616459504070703070001008120009008d128481d0100005032641c641c900c1c05004d000707401e03074a883c1c1364000a442c100a00c0400d410b01410000d9241d942407607285458221105a6501e05080c000e281051328002c105504e054045003441d403240050307105485042e110140c507064203c00b820002d601c0800c441859003d54408808682d4620740d04410b105000e14016846407594108142002c0e40c0c1202c1d0b83c0c1c0c1c081d007000b10b1600f00e949001c088086448510b00c1d5181000960070150281c861040c0041c02007103109088075996003104040000d440e902034540713026589007001543c81e080c89001c0c0c840402c0701408100301044020b48011120074240230703001103203401c6680355443c041d400d030018081c1c00d102013284030418a041020141c8000104e90038032001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 353486016 1250 353484766 353484779
    0x10020c1b0a211703190f06051008130611031e2511030a091a03070c0b06030f070305011e09020f040b0303071a01030b07020313090c0e03010207121404 66
    0x401c480802e01d8040c080701450030501c00d6a000b411440f42e100300e8070716581c0ca010019440301d00c20116844180a2925030302d1025440e40c0d1003014141c91000d40607461008102100b9920010010529130a100564404100059841c05028072541c6e031980c47e6510781c00d15842c050840f152000c0340c0f094001d0484200f1140c0000d45035801308001c0400c03400c0d154078050007002c4807000c0040c03043c070441d44400110301821030382c001c0d0310000322090b01040303820300302448001c045288030641708800065405242c003004034044650729030704128028111341400410000c190b0a1180725881030307600e83d551325044141c20a42001094036040c600c101080680f00d1680080c0003500c01d181d580380a1541c40700420803d450403c101c1e080380c0e8200d80c0988031024003540031546110240400c441a54500d400302d00c006000006441d00f200035050401c1219003014409002003005085031070402c0303801002d101d00e944081c0700030460310b4014510541d056209450140c84034240ca40040e0055100300000c0000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 353487266 1250 353486016 353486039
    0xb06040e0c060c1203090703260f030c0705011b090f0e0c0703030b0603090102090a050105040303050909100512071502031c0c0c140615011e0e0310020c1b0a 69
    0x101c07a000c4034400d483d124008041403030030120842e4548904800014094294400a2940700312445036a055a04094103180d00c40b2946150b03289844010b420720100800303040003000307594003c504d0701c005814642c1a4079a50300b5500800b040b4500e40c88402d0211a62681c818405009454a42e80718104c1d585031408902070403000403c10803d01c0702c0031072000c5c101882a0825882c07260f009040c0340d22030070030083d083e000794007001c4012b20594291400040b90350150b01a581221b401d906c400b400d001e004001d01501c0b6400510361001c00fa6110804189075445403c02c100c00c0401c2801000d010742405c0d90791250b003118044107029940103208a00080034001c14a801420300100c0c08641400e10b00c00c150b46040402000801400c81042000d8038080c0002d4858419040500e03102c04021040005542131940d00004145412004885d849036038061400c00340c18035400790803a50f850702c2000741c090482e003000e00d074210160041d001c42e107205100010f004c0e108200c100c0d104580300e8070b4000076114 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 353488516 1250 353487266 353487283
    0xa14010e09040813060f0201060f14010302160501050a0207020f040614010f020106150305040303050a09030e04020f0423100509010903020d0515010f090e0703020a2601090605040b06040e 82
    0x104095040c006010000f01030103031860100b04058000b442034550b5000303004560003c20003c0158a8000d0000c0c500c010700300d88004030703840c200e180c0c00150b03001001140a50302c0401e418914206100e41100002c0092060342d21032907010f0301c016200c644030300c10090103414580003188118241603081c40708920103020700078041c0c0242090b01e010702c0c01610a0b405403c1c941e0000500014001c9076202068064100c10b03c078900ca95402c01031a9140078260044480c05240a000103804000a0704942816402000034000781103145090940c0c90000749800c1901480460209520f40300c4502c281c200b042c002c540c155980d040272818400c04000003005100743c1e120191040f034000d520401030003001c0c8060040078400400c01540c40d0b84421540307184c002c55100c0d0048540c904096550700340004900c0d98241d0f580106810280c03071a0260180030380c010210002001c040c168840c80b80d14100340704003500d075482550081f4642c5054100007007030305401811680540e040c102d00d800748450210b600711 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 353489766 1250 353488516 353488519
    0x3010509060a0216060f0207031b0b04140f1608010501120809040b040b04090501051f0302030a080f1306090602060606030108061305120a0e032e1a060a0c020a14010e 73
    0x41c2c0701e0034030340380500510607a0131000d000a40b5040c20080148415001000c0b100c1c000d0301d03504060b0141c5180389103019219a0058600310200c00402c00040540035107510780d010070011107615266080a4506003c2c082c4e001201c243c4408104100044c0280909401000c40c0f02444030803c005494106c458801c42001601c640e40c0c400d0036014555955000300c01006026000300b00f0050b05140090007001c0603241e111041c0c0d4201803051344a007a030590b000c150780d8040e001d0030300724040d550307142003d80240d49551011082031005444e0903017200c440c100109000da65120f901c42ca031050107802c102001d809540205001c01c010b104aa80000d44190403420030324030b80c00050490308110381005800c25440682d143c0004200f9041c5900c42c081c400c030400220192001c00d031564030744890b03044090341c1c172044803018540c00f524080502c0e48204c0700d02c800b01001940c0d440300c4034001011030b804406000007003410b160a540035800d145220501074000c060900f241100b80c07100207040400c0d102e268a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 353491016 1250 353489766 353489771
    0x1203040824012c0c0306120106080a030513050909060a0b0105031003110109050a08030c0609010c020715020705030604060f0506010906080115050f03070309050d0503010311060706150b0d0b03010509060a 89
    0x560700c82090100400c2280012072100e00c82c2840074840d139807503006490740c610500005040c0c415199042c4036900441f00300742c0c0180980b0115650a071800c1d0420b90004409107030030703e0001003540b201c03505644a2141390b0090012490290075070412907640c41040c03810071030103000304480ca02d18840803038181d0340c2040d1340815021036080126601e04150f00026044405680005071030b40740000540f610319900310559940b0b50b01d81d900c05088403052020030700140c2c0120130400509a00203506441d024091055922140c0c80700013080c58040207403000c0350004d50316031411003420024415241c00960034038009212600e0840c0c02408401d06001740c3c816003001c0d410b020071541c0a50102c0e60030003c003495841d264541150043c0060500b0b07102510940951412100c0340c912400131070f8180e070307032105469003840c503808180036690300151006c540c55941c51100c811340c025402c0c0040024408044419955900e040c03403230007030320001044540668140803d0041c02c2c980462a81d90006203034400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 353492266 1250 353491016 353491049
    0x5030901031a150a0e01210203060616150b100c030806030f0a05211e030a0f1803090603020a02060f090c12060601140403110d060b120304082401 64
    0x9084200c030b91461182d01555070b20104511141c00340180c4003400c01c1c1d45611032040b15031801968100340ca4035202010a001111306060340c60107074082d503009507016015504080042061005004921400b07a580710305d110700e00420144070f8001c2240e2000182c40c9411071105a0002030300c901d40c98000141809241c03000141c09480820021403448a2a012103900020b41e05000d512003030a00590101207411100041c98500b0802c2124208200c04509a944044c070601809031900302416001d9042d46410104030f40c4061401040103010040e0007222110b07640e0318010b0115281da0b8000301c07d0500500040407865008551183d1011414202206a0380c0d1a010b8034202011030b04003543c4007030122001004203038001012032103080f00380c844103091300e4031400e00d03c0e182c0034910009040c48550410801c0605054140000e4140702e210b02042d0180901c000848000c80352065442c81e82c000b01d020000342e4000c20030483c031340359603e030b00400900d114290742d0480f5005020784400030004034007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 353493516 1250 353492266 353492291
    0xa110619060605040b09042a050c06010905011a07050109020402210a18390f05150a0c230109060b0a262e1b020d0309080403080a0c0209070c0503090103 67
    0xf02c41c48c1c08051084480c4d00305241c0c000a0403d0300131001e500c5c92407098030008190003405220300340c1030754081c6114a03105403000f0100750865100c100100ca26540741d000350001a2103e00203000c07805c00c0910184035403030b0100000034a07910300a1034446550305000c4000040880741c032450300c1031038001811076040c0d12603601148002c051030707200c10340303600040b10300e0821002c0c0c400b60b00d0165110342720b40e000100d5031801013154000c0a071317078010310024082200540940c011104000203921469184402c020004402d052221002c581145982d4562910004004240c800c2c3c030b02515084840b11951410900c072000c07003c28141541010024034400c840001004022400c2000308511104054180e04140c1c20a020b4100070941080340c01c2145141000e68149408245849150300500e41c0c3c515110b400c802034604074030150380c0b40a04000120210316140e000b00442c040070f4688c0350035101d00e8410b000810070300529a0080128400004002402c080101c540040302440c000c65215407403003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 353494766 1250 353493516 353493551
    0x4030515221a07090503060108030a09060503190c0203041d0103050c22020d0915050403120209040605060d0c092111011205070c0204110901020606060a110619060605040b0904 77
    0x11124107100c0c2c5188204040250b021003100103031035040d0142c402c41d0f6038801c007803035490058000842c04216842020b01c4040e20542c0a5a4815480d01c0d80b2690000403102001c226901320a4140050300001424807683c8040034140b0240302d8145844515503240d911a1034403200741c406854411422141844240140c2082221800c50130300e03400c42d07403880e10b80e059030018000400d04603690302c502c2c2400c0d006446644603c0344540c2d05601c4042d040c804d4000e40e0002544030041071907019558610200c3c4c00d88078800905000300030ba0f0000190128800000740003050f2603802200d90801407030201d01485091a0410f0115030b012003414010905000160f602c49010100030412520b0082003023072980e8440c0c004044240281d07820041501600e040076000d20500c6810b40c0540c0c45000400e0540c146038008040030b00e03080c40c05403502d5602c0e000032401c220058490804214494801d0804011544aa2030091170f00f0700740f8501c0c00d46007440100c07481c0184011503100d180d81c1ca07e040039650954 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 353496016 1250 353494766 353494793
    0x70b041e030c0e1005010e0603070309052112010b07020102031204082502120c030718110406080106110d09030303020309070f080d020106090e0303040210230403051522 74
    0x2207078526010b0b403903590034001490f085895000b0300e000b0400014455000d01034043d00c20030f000d8900f625503a80d150055000c0c08682404032810702c56482ca021510044485040300044155800f6a40380300e030650700060010107800c9407241d400304001150050f81c002040b680d03402c040a040d0020360343d03542024195400782c2295140405036070704810188404051880280c1d5100311058002600340780c000f40e640359044101580c0580c015030040c0070080c54060708481c8000300ca08082000000801e04556940143d841314011844190050040e540c00c0040124032002c95801400038543c100001004049148005801d0660001c0450441802400848068030041d01c40407170040d83d5103034455450040c11034010040d4a8a00c0c04101000d49010354103200300d04000640c2035071180d408120140c18171140b15400d100280054425000c241e1049040c142050510a0740b07491031402c01c0d1f82089880040340c698034140c2d80810902507801c0c44900000b4070143d41041e80c454491410900c0c1c070600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 353497266 1250 353496016 353496023
    0x10e13020d060209032a0d050102070804030b01050a060c0308130317190e010908040323010c05120a141603090f0c080d08090a02102106090b03070b041e03 68
    0x990120000e21002d90001c0080c0081134044a50f03050b40100100e40c105520400e064511101540560362468a001007085440c0104001860300440d662000590352140d03000300c60706410000104624904101e440f4020030b901e0402502600b0343c0e590040460600070800544041d2480f40032041c10305c00e0303000310350074107a100c85c505103824850a681134682d04083c1106205041021000660106000d004000c1d540110086e05041c2035548030100b4400c0d81900011f1031028041d00c041440090040515a6086469031a642c1400d40140d000c0910001e20444426080c031a02200ca2516240c1c201d070b01c9411842032800d000c410304d00441c0a806110806800e10580c030003030105001c8140004011905003d089550070b9516030810f88003241d0440708940241c10008881001d404c0004240301851100c3c075100720740d0b4075410040780d0180017040c100034907281d480005029100c047d20030303502405000c42c000c4c20564905080c0401911030390003145808445070061003c0181c404c07850310091a417 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 353498516 1250 353497266 353497279
    0x2210702090a06090e0a030e042004031a070f17181501140d03051e120702010f0b01030605031f0e01020705030a03050a051b0703020f030307050c0606120303010e1302 73
    0x14110700420142055005001e2803a1510311865800305c4001040d590899040e1912a851400141000010030903134442e89607281e00c0031084440c00c84950010409513116800d528400000b86610070001d40f0700900d10001e226224032504c00d05900402e010403a0b107449082c00e5003075a0740b42c00350f51308180d4040c8a540c980c415142e107000c880006251180c1680d862004802d00c0c85007602c10404944000c41001c1c002c200c0401004c01c2807402e18058010000041e084140b0b0800800b0005200c008111902401030359141c00a10401500d40107a040404003440c0520405082c1400603488078045440c40862024512031041c0c2624180c01c04060f044010008540f07982c03150800302d03200d0740860111000a031812000421402e110700c109401001c070301c4411316090b100d180740788440341c1c0450030036415407091009a481c03ca0040000390b226820a51307641e516281e21020152070f0901c09803140f88908408401e44c003c440001054a046130040c1d11b80004540b9030412190344001d000002039002a03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 353499766 1250 353498516 353498521
    0xd0501060f0e0603060705040b030a06080a060c030515031f0e070f0e0703020301060504050d060e12190903122007060c1103011b030e070906030c0e160221070209 71
    0x2507044050000c441085201c060b0a03502d01c1c08050311020200c440c10041101880103000c95088030000d10341c041c400d08030010300e00c5d4480f50380d944ac204401a003100c82c81d4803410304052040c4c3c140500390308012034550080804000c940081c0c1c80b4000b000c0401541d5280d94112040b80c3c04d0307604140440da14100c04c0d1000c2d00d454486240340c0600e0b9000c2c4030301108542c00403540d418407920840c0d040318803603a185420305040a0800c01c8030300d0f0a6100356905502d50103910070503142400ba80b0f00e0104800d220503507460300c081d0b58504050041200109124030070340c042020a0172000a0003004860303141c419120366031118894901d0303c041030700d000c55114660f80070441d560400310312410309000b00781c042e500704101d40c105400d03600c010f0a0035a1000c1d0118202c05100e0103501305036800c050700820f6840e100d80314400e0a04940b920783c41554a041121410010403e2000300740760400c08800011070f101030314000180d65114800014403072030403810140d406034a880c1d01038600e00d6500030505034050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 353501016 1250 353499766 353499779
    0x5040f090204180f0b06010504171b0406030b010b0d230601020601090908071203061e0920160302071a0309070510170604020c0d0c0506060625020d050106 68
    0xc10142208078003551520f2000e0340824580e045200800d548000780028640d82c603a2414070240000c0c20860605c40b0030b1101080740030000e0040080c0340101c0004080100020380414107070045160418043c4e8a00281400890308040034181941d8100d165240e84291400d0320350001c02511040040392405028441c2620300c4240003240100026400c40e00039907240c50460741142c0301e6440040c919202007105400041c00460010200c000c3c40c20001021907540020249909004203818001d00d4680c005000380d2206103c0d10061192040200100c040e8420005466110b5071210b103080030780c40c45480c02007510810031040904000351000100404400340c0c05581d0b002901c41c3e0740c0c2401038260124460404204050400003982ea84542c140b5a40a41400044001c1d040c16007042d000c0008039030814007040a00081200c568611140c120781e410181d00300200544030f24440c02e0104004130300b500d550080701300b00048800c81142d03100d1051000505811010100a0240d4200440052103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 353502266 1250 353501016 353501021
    0x9050c0c0a240c09060309110405090f0f0d090303050c01090f03051b01140601201501240c021c060e061b07050a060507050f04090c090816030b070905040f 68
    0x100408400e000e01002c0a84442009844490404400152081da002c200882c4660407040e038013801000e80a4014111101250a0b10000c0314246101c0c2c1c88102124000d510802a00c0341d000c0c005d43c0a04044048200020715022035844003a0812002041481c1440020340c002c4c804c0d6030b84488660410141841c0203442c6400c6940d034411401c40078078546820001c10b0180159600e0300f0411b941c4207079035138001942c848188152008928032030202000c503105082105c0c109401e04801400190741c500424152030140c4030003199540404404a074103082c1c1c0240300480d5117a0304440e801c2001c010f0013010700520440a0016141134180b41013120489008a00d0300c0c015842c03042c95a07001680d400c100f0b0071501c50b003040101983d204c965000d0115495502081d080201880c199241180340b5001c0703640e681041c2c00c081d4429a0324146c10790510f400c580f44400a20241c2e0241c03610040a19180d03a8503500c51101400c0f11941c040040c019500c10320150015280c0144200f151880d4070000500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 353503516 1250 353502266 353502293
    0x203030c03031f0602030304050d2a0819020706091203171005010201050901140114031203160f1e080603100f0b030105010e040c12020f04050f04020f0a0f09050c0c0a 73
    0xf04200c880c01e02044092000c42140e104179003000044c8110b942c9140b04807143d54000c1c1403803881b010343c0505910b00d5101c81075511032141c058004141c940c00c1607200c5407200484610084250f41c09000204107180d001000e50302101e61444104240b40e60500b029580f8022130010701a00784600c3c010461130100c45c143d25800d0351801c1e17000300599030385c0f0800d0a0880d000d9014100351020342030f0041249800303008030018601e102600b0750b18500004041c1c0400e507002a981e046412002e50f0984800301d9000740c0240c45040d4902d00041d12200840c000c0d84010302c0c5011a03010800d41d540020940e4404001d031407001c2149007030810010a204209000400d01102030a20035404d10000140882c4000c0b134240c01250840700b1807035421303d400030f900c82103e84000c04071b80102003550b10718032699079481180e11446003000022a203280c144100301c890780e160a40d40e4840c09041c003090084180e44a05070060b01c0020000103202e80750101c80340054050516180564410301d001d00d4200048400e1840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 353504766 1250 353503516 353503561
    0x20406060206100b0a021b03010b04060b190806011b060e070f030c09090201020705011107030204061203021c02030d0c0e04050103260906091e030f03041814070c0203030c0303 77
    0x4000303a04c0700072000e40d40c4a480d500c02d00681c01200c1308807a21402030810030b81ca5a004000044111195022400396199644050160000402e10b01c201c0e1116001e000c031070013441d2506805510700680080d0480007180d10b00e00d10484c0349080d03c4104a09035100c9241d401d060340441d8040d03503481c041400e1348040303800115041c9100701380008190b51280a60b51010b603050b0080d09480d400c001c011039244511041001d000e1152100004c096100c501c20503024098801c0060107000e03032801c010b4a090709401100c04444503042c4503090003030340482554030301c544120021038006910302040b19008028010190700c80d141000010800150401e1540c4900344004246040350603040c03844024090015030707940100e02004a28114603081e0800c10b0751841c010030380382d01c1903039500200c1d00e490403100303c1111319403000a061002020b00000d4130612001c0e40c00a01642c42d00c07003c8100300100c050081b005100056001c0710465805100343d8402203810422691a1301d440d0058500c0d66030740d1000311 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 353506016 1250 353504766 353504791
    0xc210c010605240a0203040b070c05010306050303032e0801050f09160e0403050904090f1101141809070507080706051f081b190308040504050a090201020a060e0307020406060206 78
    0x552810716111075803e05202401c11940000300545500c11a80080f403281e0460004201c0860030742d50081c05018064064601c0302d91250912001500f20760706038104038444d500510800c011ba500e411203111201004940784a4030303c2c41809100d02c0c402c0141c00281155080c0720030000c42815006440d441400100b0440e0f030300303580b0141c913680c4c408440d00500ca41c060480e800140800e01485c01885207030406000007401034001e495042004075921002c944a100ba41000d401543c0d0100e01c02c0043c1c05102d41c40341c0fa1014410310303140380340d51000b003041c0650503003400a800c1a000d8802d175107240760006030066881c8503034a031450040c41c045804c2c90513402c0c06241d01102464881d0030f130042d100c07400300420a20700645407103d50642030300c00d41e55100c80100d000314040301c50301100f0030086100d0071003691605c1c2020200016034400503c0500c1c0346260010750301c00340c5e0b400a4140c07080e50f00030100140e0200a260310a05503c9038610194001c0c0c1800000100164002807441c450400084030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 353507266 1250 353506016 353506019
    0xd02030f070c0203100903170901020307030c050306100c050709150306050115080f1f1401021218090c0f041202040c032d14010e060114070210050c210c0106 69
    0x42d2100350401c94041c0d0103a000d528140d41c2d0901e0b66011180d42406400c24221202c2200c0412408003802c5a4004459402009104072241c05000381e000e265680d090042c25440d11201141c1c03014600350074241004044285602840341c2880514042c180865050044421400c00104804d4480c031044500d1880c1000004100f01901e84505000b200c5030f86640741600c4245244042c0200a48040e00081d1440c6809029241d0200da41c002460100483d6100909110001e4104401c40204440c0104100301514000710418651507070304a0446203440c207525003284e016500d00036450080b0319035030005400b054981c0e1900c0c0207042c00707200310340074041200540c2c01101590022040c0c00482e0140440d003179a641c01001669000c1005034400003030340c0c0b08241500310003110a138440c01240070010309000207944d000e03250313640780403804118514040050380811040515000424100300b00852818548001400404155110b0203074a0798511010f04803602d5070b90210a42000b41e6180040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 353508516 1250 353507266 353507281
    0x8030a02031207050307050f07080d051801110f031807080304080109060612051c030f091b05061c0f02042c06120c04090606030209090706080a050f04110f060d02030f 73
    0xc0f0380c1b1422041c1c0c2c5290038052058040c1050340c121003411200c0321001e201c0070800308010301c501403244500c00c0c10350484c0c4140c02141c908440e06907e000c5480c08042140c401010b6440c022030740c1041c04000c10085035402c02c0c140030308005180e00211000c0c0000900020070100c15001490380f20b002d40000c025455036030b443c107002e0380d41d094401055500f0000c01c881d0390390a0020041842c9040d070401141ea00003901078501114652a811121481004a4000992210702d03c000c0a0401034464900c2c0259042c107900d042035542d040c4409040d1118190b0038204115015207004000c48180060175a0022001842d104801124601038181000001e40381d0700c0e02ca59030059170380341000034140181011084c00042d14501c9029518192600000001038640c00d152602c2003500c5005455002e00700840280481000b900703510809003008c0c01c0c441c622114a082940055100c20704030903100b0100c0c041107845158600e440d501071008181c0313051903d6950011489824403200642065440383c0c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 353509766 1250 353508516 353508527
    0x90605012105090c041104080105010909021810030c2315041e030c18050f010e07180f27020c060c0c0f010603060e0606150d0f0608030a02031207 64
    0x12100441c1c0c0c00e001d040342990500ca50301154102c00e07050300303480402c03001001180035120300c1d0040c1110200700040821440b00c081c85420b001d0090004140030043c42034002484490f00025401c94070311100000c9242c443e01192002d00540c1d000501e00c0768a6501d2802000010794a28910102001044444074914100c001c01040c001c91100040c1801d041540713681a0705903c802c1280c04204000010001c5110080d5110007041d1484a41035200c03e26421001038800150942e071031035140c01d005000350503c80c2600380d072009041c94007071540405800040c400035450342c00750040c03400c02580468080e506d11a22810b030b102c50445c0e44080c181c04540d6604034400c00e5008401070704104081005040c89500070701001c00300c44101c543c20002003a090f0700316509076104486083d80d81d040d5094500c428001c1c140d2004044039000c103800b0841a110f2140e10840d441504603e6849100c9148503480d40d0040b0094013030b080c2100d44480380550060340d6a4094601244261181d200003482d952250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 353511016 1250 353509766 353509787
    0x3150302130f0603020a0e091501031112011b02011b110d0e01020703080c01020d050a0c0909020310030f140127060209010509220c020a1109090c0901080709060501 72
    0x1e001e8007298040c44a10000401607507000d001929190f08000000d66102e5103400090811101c402d4060f081c8002c0c2c02d440c0100340070040c907001000d000108082107000d0f0b03900d090100706803080d140600e521101940105400501d030f0074450340000203604003580c150300601106014448440c03000c50600340a40b880c070300c09042d444440c0d01c40b100e040c2e8a6481510030060034001801101c140c0790300c2e580d541802e0b40220000410756903002c1010014052240103450f0002c092980c1000300300a4000010001051340c012144901d40000c0401d1089468481c81d20042d900444008211180f519000d8082c0080d1070b102c500fa582402d0076809490081800e007100548001c1d1051300440940c4c3c0d441c0045c0d0020030001b8144a800d10845030300352a1140810031071000083c0200c84c6204400320101295000740c10b903c21035210341084e4000400c00c0d40b1752004a00211b5100e042541c46800031460150341d0102c2c0360f00001d00b9400010a1400001c0d003c0549810b00f070b092000984030b02c01100c03a400b8a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 353512266 1250 353511016 353511019
    0xa0603061a1c0b06040c09030804030602181f08041104060303052709160210020316021011160f02040903050c0f060601051902010f0606020c0a0905151e1e0103150302 73
    0x10300854413903c0c0c0391b40120b01031025400c0010360182e49445400c03050700103034425280c80780c000441d90f500b01803a44c0c1d401d10a0394111841148148081140c03881c000026107000140a1030001090030300c55440560401464014024048a41c80c1e1400611640100b6424024202d0800e04481d80e1045002c05860b01c1e44003501a103007917658062012400c150302c0319454203501134110740590101940c001907208404a4114420700450440024600284071154409061800d4010303001844498120b40345507150362045201e20020741000c0c650400d0394070b40254458503048201c810140c115025051a103c00002e540309030746003003000c80e181c101c122a2540007070000c202121480322546880c48122507548000035034191240b218808841d09600040d000d68000c3c1f040320b0340c27850503040c01c501802e60000180828105089032406445030011184e01c0b640404417820030101c12004015074141009008060108042c0160708003041048040c0b030000e0f00780101d25040c90181c50a11080f01e03030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 353513516 1250 353512266 353512283
    0x31903050a0603050a080a050c030307080906090f06190231080114010302011b050a0c0f170a08160611030105090a05090a02130b09090114060319020103050a0603061a1c 74
    0x2401c0e9900c6c1960340c0005100c2e001d0203070a03c400c2005c0b007010009944658015151607071281820380d4854546600200062856480b01c402c1010044020075482d4214040c0e069003000c05011100303900c007038010300d91540e9604c0500c648180501410030944400e4149200ea4440c40549480707000e42a10607201c0c8005002881c40010070055118954043c956a509800c5548112050795540d0409544c41015540703000003490a10804580342c18903801410540d00d000040950038035115264030800030080c02c80140800d500b81c4088820065203102940070300304002c040c05803115030855400038004c0c2c03405602e400d40055a0004248141c50048039040d0040058440c190702708103440304c0c25983c0441d26900c2d9a02d10103151034100c58140034000304000410444c0c00405210425000106101e1081d80300444007840501d0241b907d0301322a40a280109959540341400000350407180c2c4001c00c91454a04062000c00c698103e480e11203a00329505a0004030310300002b20b092042d82c501801442 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 353514766 1250 353513516 353513533
    0x29060d0b07050715020c01050105010305071d06090102010204031704090b15070b1009020d1d191502090603040f0b1513091e0b04050715080a0b040b03031903050a060305 74
    0x140160301411001344a102c90300d08405000d90541c059030002d442c82c03021a03440c0c40c0180410342e01401615840b4065280c0ac28403038202c481d0340c80f0f00102d0101c10a0040000103556205039100b90111005141c008034a07016032800c258101c082c2da0303c0307845042c464620340a5070f840c480c40e21400254a1640d6254810f050a94035101e10862000c09009040118894807001a9900c0b4500181c020311040d244000f5504050380c05000c48060150032617000c91700017110301813000907090300410100742c01a05a0142c0d03a441010070000340b0461102d107500110120410003006000c00b04004420302c1661004417030303101e1600c0381014040741e224039544201c1c1516401c40c4108554405010786000307995200310840d04910f0600c511403a6442500c002003598100418480100100b8006046800781c00c200d00418041c001c2143c0005002c000301079444800300c0a0540c2e8036080070740044c0000307007940d68402c40c2e500007102c520078007a862000302e8144400288108581e100300b02c00c0740d401001030095013 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 353516016 1250 353514766 353514781
    0x10201021c020c010e06010816080a020603040f15390206071b0f21091d040302010b030609030307030f060302060706110f0409020304110910091829060d0b 68
    0x9400c240e0074060f41d59070b540e17100c0410030030401c4a01d0091646001611499620011100304261640c00c400580d9205501b003a005846180c1201d91054102c0350491201d8850700e041d140a5a1055001c00584d0620344e4903921404406521042c0405070000034180e642c48486c22a12800700808060140c2c20000001d050705005080e6140000000000352803401015595001010800003050310391403803079040801d10540c04450400943c000c1c4c10110411442e0410080f100c031900d107403a03038006100030701060416000b500b0a40403600001c05450b03251038009103417596600110b490710000b070f0810303102111945003803086030103907a0003802080c549442c0d512002c0251400350b4210880d0041007100c05400401c20000e8000380ca8a48409039490070306040044080951070940d5200d0005441031080c1d03200041c00c42400c5803064000400c2100d00c20403010314100c00e46001810081c403d12100c05c280d1404c005072006400c003103c0c0500070b6203c036810b01c48078003043c080041608a54201040710f1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 353517266 1250 353516016 353516021
    0x11b0b0f073204180f0c020a050a020103020d0608060f06010e0d032c06070f0614240102010b030d03020409051e04060519060e0601021b0303040302010c0807020901030b070806010201021c 82
    0x742d40308404098a015650001620000760710310809004955540302d202141c03082e8024210040c4040c80100700c001801e07102d2030788400182d60001d0615900103420a46058150000d400510030300d002d07101c0d246001281c0b0305840c13000b2120b00380040c1c0484c2c2016124507119000c2020160150f841d42c010305188044604d9061038110ba454600740b241c1e5050840c4e913164001062180e2050460181c7c50751280780c40f4080d94000484d488030a440d074000c001800100742c480d000407140e01000c18040216950040c0c0c01041071901d116018000c0c54903110701070750190010002c880c1083c47c100546d65840b08000c1580c40d000004c0d9040801c05000700300490402d41005800814500820642d1304170300b420b0390119111a40404c0340b64007514204030407581c040c8105410001642d0602d61400e0104001a8580c8501e002c003c0c1880b43c001c00d50340a02540c7d1068480302c1c1d602409007003007561a41000c104500046400200013035907603001808035403040c001da82401b42d4100180d010a45c40fa00319001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 353518516 1250 353517266 353517347
    0x1407060f1202090a080307140106060509010e0114040f05090c04080a120e180a0b0901061e03090b15103e01090809010e061e09011b0b0f07 61
    0x1064081c41580511354034400400001d2100070001c1d940c4180500d400141e40540d1217400b01d482c0d161500811903582c10204440c1401d07424a440800c0f0300944006854982024a1844405801080106890551641180c2555012500c0c28200d95038034480340010700c140d021b5070200381c101401e1000050f40030b0543c8003244038181015007802c60310300040340c000d6419400207540d1a0040090185207805407152410103881034500c440b0660400002030b00c03c01d1072603c1e40f007006681540e92842903210b6404030000c50761003034684034070f424003880084034054891b03103641c031640c040100c00c0e11041c040c2c064041e2000964002000900b4188403030404001c002102707904901070414070180d200021b1095101251151210946071001503000400d246090f08d49180500b03410020303128001c24044c1d82a010183c4070300300ca40d4a0b081100101c8411200300c801c40f0220781410b014074204a09100c03858443e5a01003d082c2035560740c82403c8920a01411030400f40245c0740309641030107500c0024580 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 353519766 1250 353518516 353518547
    0x3140f0c0f2107171c020307020a0201110d02060f0c0f030103050106080c090f040209071115010317040308040306020f0403050f0106050108151804060b06040e04050d02010e060c13030b040f1407060f 87
    0x42c00c0c85c0a070942c0e1005d9074012142800180c1200400c0000c642c1c00820f80e01c0501103110040901141505010355100c101800300c080302c4c1c1c1d001d07000801c0e400c02403085581900c01c00c0c07400c5440e5623591400c980a00401c0c000c522035800b85440441885c2480a107807486801c00a0030003210340c84917000e10403980b0018080e5002c10200c030605032084801001120020768041760070031690b41c910304060b40e2408110381511a64981040b007000481c0c4001c00742c405403a0052030041c1d440040408003406481590701c014024081d03500507001203034042d0300a0381100e0007a2119605903031003403444104e2001d0074001681c0001654100c2030b030110100780c2d59901502c00d80d000603015000070009000c41d04941d02c54500c40280d0b07070401c03080001c10302441e805047c083c0001d00c0243c0d02d1990780c0303481d802c00900d0011100000701d0000c2c04044001e065800031358200401d07d4040c240b50a020707000310384400302554410031030742d170103407030007200050403004c481032643e0ba43c0751021900c0080b52026440c90500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 353521016 1250 353519766 353519797
    0x6040602070305041d090106050f0d0b1e01170615130911120106080106050907080103020d030e0603070e1c03080c07111c0203120703140f0c0f210717 66
    0x3145142c0c0c0343c02541d0381805610941317411481c001d11503d081da00d41d81c0040d03000d02e4000000c026a600c0c1ea1864107045a8046003144295a480401c04403400c0e092401340c0a503010350000080e0302c43c03248400010060814240e41441c2d0301c80c1c00c10000c003c54021920b802c69030341c5180d05d00368000395000003405407240b6681000c0c020800009010b20900320f0121100303075075900d4100f1405009115000080c142030302c080c900c6103005e400c0a8410a81444060700030003448010008061041e29000500f81c0020412501d9081800006003440c505c0c41066005050040051034140c0d41034898a500a51660314558640d4610103401d10a400451080f60842e8201181b000507035111449018680320202003408003140b6401094070b8032000701044000070104004200119600041c603600b02005900d1440d5108200806042a03110f10034004600b4003030b010b00307500c00800100e0300031690311b955031407011140c10075000c03a4150310130503600814003803507000c034107007005080070140c500381105240b407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 353522266 1250 353521016 353521019
    0x3070e0a15091a3703051903090e090a2303040b0d06050108090d0309140102030a0c0206010504060f09090317040c0303090e040206180f0d210e030604060207030504 72
    0xc1c45001c555810103660b540e00e500c0100d85180c405214124000f1044615180c810a488844445070941180c030041103402d110708107600d86100d222000055500c0002c541380c4c13180318031005640c00fa1742982140001c152202c00100f000780c04c1c0c007042c0a940554040c010905c0150b40d10340300c01420039010042d220140101640d091420b001610040001c0786455a80b4918400084100c801d180c0140e4140000e8805211840e500081d144c1d50b51441c504001442e400e0324180901c84656204e04e20550758000800c021007440c05801040d0301400319003c803517440c0d0700d490800056074114064040c800c40404c00030407540403242c10040140d402030600c1003114800c510198140d00c42180d0549550313240c00b03420010141d02050340c400030101c40c103041d00103042c550b00061036482424109a800031742640c80c240c06a6031a19405084c0c14010f105218004070342c5080100101100307441c0e45621000103042c094030340990584012078000a01a011030380c1c9991702c0c140250044102a020004140170 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 353523516 1250 353522266 353522291
    0x801061b0c080a03110c030d1209050a020a0b18031906180f050609070603091208042d0506060d02010f0c06060e010f090e0f0714180c030405070f030203070e0a 70
    0x812030003c0e000303a81c0c4944c9034041d074004900e04020700460034000c4c2d0208050441d0264030a802940e100760481c004190794030103007002ca10344040e403400a0340c002d111403800558200c00c04001c00c1c0006442610f0110140b50070101603e9103d8005c03007000042903060300c20300241e02580300340c0703064080140300d035101425034071030025624107150129802e500900500c0f00010701003001c0e00c001c200d9407405011506c500d03928421400403090001c0d041c004004007050803c0f280301c01884602d4011211080491510100103881422501d01035030907025034004a2450b003000e01040c0311603070301a1202e4000e41d107404421140560000415520302d980da09000c20200342c103c50310350003070000c600c8a070003039400c0203501022180c0c401d000c2c400640c8000706081841001050ba01c0c200d0b0749140c1d50200a410240208030208a6513000c8910a1080700821442240c00c4000c0c40c082c9010f42d04030b8918503107603988240310742c0c034070b01021358107500c01107080110401c422016544204900e1021491850411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 353524766 1250 353523516 353523523
    0xd02030c0903070b040810020a300609020c0a02060307170a050f0705030702100507140f0d050c0703020606090408071a04150b06090402070804050d1a070801061b0c08 73
    0x603146000c1000c001040440c500d82082414050000309030060302e828501031040340d4580d03409003d800c1c03294011404000d007a000d07200440040c065400034503490501a0100300510b80c2e05a02c0b1012103280480204403501a4400d94403035640200003014140103035000c0104a030001080001000b0035031000d82c00801220340c00602407110600c004c560380c1050b00300000d2140c001403000080040a00401542e25800241180c442e28002800982c41d103a00c00704641a44402c0e2026001e190700041178006000c40f07800602880c0300d400010440c0351203499403040c80348a9600302800603800403010518a03d040e94060b608a4440c00c2028030b811280e07a112604005500761403603c4039051400c01003880600c0d07c407c0052201002c04200e2208400b00040c0c040c011202e40c00c9c041c90740810600b0400c65554125405000010f102c1d848091003482e099a83c00c0903600103065442100022820003170080e14928143e070f01c1c54485101e0840d510201d00324019500a090384ea540c450030000030948001d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 353526016 1250 353524766 353524771
    0x11040512191505240d151103060301110a2a061a03100209011b14031201031b0b041202150408010e0105010e04031e0302040b0a050406030b0301060b0d0c02030d0203 72
    0x70240d0b0300100315030382d04000072100b005003900104a414103402d440e0031403100c0c0c00003004004407603229040c1c5050a0000e1001c1804818100c000d1404c040b190258070b00300055803041004074003e100c0a800000e8061030b078010300220002241d001081085815101c0005000c1b031000b0100746601e002d21503d400040d1080750301490507036220b040101165040a100200b85620550000d600c0c03c41070100090030044680c2c004010761200071034040c10010b100340094074a8051904907a100c00340e0b003032040350742c10081c44115411040d004041d803220103842115011200c0004e003040c14503180485101c02c1121062049912900220203c1011420360018001800d201d00000a918401500381401c584060f00a0408424a0000c01000a03440403845c44640d040d425409030b10340d50380f00e05401a0140ba04109135110340442c4041e00c55500c00c014004a500d07a5406008241c283c00c01c1c94201c81e024082c5c14100c5001b0014082c2c001d4458100c082c003a00315204403031a200741420309108a0304203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 353527266 1250 353526016 353526023
    0x100906050105040c080108031e0c070f0503060f0405060c0306040b0406060e01200a0201030209010c0609110a0e09060103020f03030408010f020301030501050115050a031a0603040c15031104051219 86
    0x86034014460341c1007034803c0d51580c1040381031064440d4100441c1c00c3d0349010b40c2c9166040138421002d0345400130303d04021340d0812600c2070200c1d07086584440883c074a0181a0107814000d11a035400641d403000700311182030080d5080405414292900301150881d64001400e49030480d8803020b1000403601c603846842c006100b240e84507400c13040d1000c0014140d40038907548108580d01c900c406d00041c040400c801c0328455090030016500c03510707140141c07841e86403404060b00307052a014200c0c080c003c0c00000c0201058040381e0726280207486d4440c609040c80e00b07580e03014459000000510060903c0221441808170040c00c80303042907902d000450179120f6550b252500590080010001c10109000b90b50150014203401804040d19100062842c007a0000c400101611015074807810054020710707041c514000b0b40400d40c0c0c0e15040c1481c81001400344290500d9808007450060319078803900c500031200c00006144c0345803924203410460a69040c1507201058010b0040c1c24103080084100040704920 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 353528516 1250 353527266 353527271
    0x403090501080a02090f0d02010e2e082701020f280201140a09020a05040c21060b0d0e030c01090335041e0206030a0b03011a1011100906 60
    0x6080006040b840e01501d8210360600621010400390744081560301410003d40704102282e43e0b07400103e816012444505401008901003d480c6100781d207440c61004c6001c510300d0740507081880c011600010300b19288045040185865010300310341c2244455078481440c0054203040820300c1004107640101c101004605506450910703520b00c07146c01188a0580b40002c0200c2e81d1060741c11160007031300410341c440480d9149441c0c01107542c0e0b1085e500241402400800507007001c01c01c007030701e0342c1520410208080050084456485843c0c000c5070250b8880b0710305030b41801d41946080c0042d00385101c511410f80000d100b52610014244506076070780d4000d56880d2049000c0598044030100070502243c11191400c0019512105140e007540d0001d0340000b0301a00c00c003956407003084501001000a50203200007040c03003d80c80e41a00b020f400c090048000300b05401c08081000c1340c8501404405812001c41c582d03507444140580e20781ca130911114016629075003a1455200111a0402d00c215901036 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 353529766 1250 353528516 353528519
    0x1090608120406091809051009060b040618151d041202210c03130303050301051206040203060a05070c05120703090504020c071a0d050a0f05090a0b0103030323040309 73
    0x290411100c03907400e51900c00d41d480c107402c100d0000c3c000c5200e0f00581c001449950080078600030745a10000c541600042500c400300c1c0340348071050142114260a417800c2e81484690045072034903105800886648a00100c41940301c240100b0240ca142e600c0f07100c6182c40304500180c811815404080c40c00c8804130083c486280510b0116500014040c1c084219442440d40c0039030b0340c4000040402d020910104140c441ca0040801c81c42c0d4801c42c4040301d80e25116000000c10190083c0245040e52800c480f521002440718145564a00c001c5402070741c16131141000c2447d004c11548026000411485c200341841d03041d0312200d00c1c101c04030091442540b0005028420b25a100e03600f407003d0001283c5c15407a2403030710302d406503440204d8043c0020201e09482415410036019040307610344d014000c800d200500e4900811001030844a1050b80c03850700f007c0009050850100ea000344040d400211488142d0031514100c0040010524080d480040c00025240d1442da4020080c42035109a0b528038605 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 353531016 1250 353529766 353529779
    0xa09051309140a1a01030f0312110c0f0706140f13050d0302030703030b040903271206150603020f180d061a0f100c06050a09060603200609060d09060e0105010906 71
    0x83d02240003101d181c84d0140014000111104810080141c240c81c0034280c0840303c14050740180a0182c0e80180d0a80002e804a03500c00d012843d83c5a00d042401030ba080c003555801c003522103a0006500d81d11a45041100d00300d2000b84c00064100e041c4010f100d04c80b89074640c0c000c85c00704250040c041e400340e800803035003038105645801180c0c2421070031ba80c00e00000ad4150f030b0240042584802d500ba09035400310b40400c80810b085d07285002442e0005100a0025081c00c007817004014098150800755110100411034902a000b202c0c0b0a86a00404074034001e00c2045184507082c40441c441c0c5c0c0b00049181c81c03008950a03020312900ca00141003e40c071030305030325810098640c0c3c4100c1c449008040c1e19400340c0d42160090546214990064404078440da12007031000002d21822130002c2030300780340c103030084180f045000340e501107515004407401d0904002801c1008034094000c18540c880310800140300014056080414600d200344000b0582c0c8203c00c0c4011700f5603009800100e80c490351600108205d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 353532266 1250 353531016 353531033
    0x60612060801061215090611040302090c0c030a0c0303140c0c0606040b13180c030b09100e0307022704110102010b090412030915091a07050a09051309140a 68
    0x30441a0000c11602e413a21500190fa00030341c5078080c0c8494a1040112407941144d0800449294444010441040340080142240d0418002a401550040300160345203604000325003100810750011410450031b50b4003241c1c0010000411801c240d12039000c603115040310380b00e03a030103014188030903521540840340701450044020040c9210302c0c1058603050054854451072510140548070110740000342588044040c285510020001c0d4404031000041c0001400d040c0d000b41c0d00082a03c001c540803462120a80d480031600741c139103800821040c4018900514804600040440c00d034075046a06030b0710091941c800c903415198000c812181e407074150780c280f003141000f110891355400741d82059210840140302a0611034245561036001c1e00c18446201c0045d098101c0180c07061081d080c81d441c2007a205c814000c03814696000c84408104440e00400c103940b2003041c59911a0102440e00c030030005600341c4070904203a02c5644030b404002240d0750002407120341040c117008012001e42c41c68a10003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 353533516 1250 353532266 353532269
    0x1502030f0105040f090c05040e01200309070602060709150915030f050105040903080a0c09120309031b05011707120e06090601050627040209040204080610051219060b0406061206 78
    0x6581d01d1710301002c0014445424035005e41d40141c4e00014804c506800841c0104072084112961081109403c45900ca000008603c01da80607001e80d984955203640c00d0703903203910170783e00000032500c54001804080302002600c0070f040e5041c903008400c65918440007917801c10080d40c400c0042d80f03460b0420039949543c003c3c0ca00500d400d0310f04011041864400612141000c1c248401701c0f502c604140b20300c0f5204108510180201e41a0042810740c180b401418101403880200c0b410113003080c52503030310b001071a4400704459040e150700310010482c43c1e05034100b00009114106101200f2480c80082c4403170b01c6101008004d640007084141040c09c1d000d03181c4141648000e205600400c10303030110f04003120203d01c00051500c01c5118031401140098040e000300c2240a0b001480418006169000020340a008103051180d00e00003e40b9641403080d09805944075004581c032100050304806e001c0e00d0038070b0095014820000e15502c1190014040d00c04541c400d40018091000f01003044606214520 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 353534766 1250 353533516 353533541
    0x110609100f03050f070c1103010b10050d060504090b070c0302070305030a020a05010b0306010308040e280b0414240a0506030c0a09060905010807030506130905010e0d080f0408071502030f010504 85
    0x4d2914002c00c00901c440d00b683c200070011400d070f2180c2c491585094100b0f0058510080c051020b2202240c0010030640001c8051180e02d418050001110f0502e480b40c094200d40008100d0f40d107540d800030941d00d1240c6420110b045205028000001c95070500140c64401040d07806004040343e241032640c2541c18420700e143c440c0e045800108005000e010803541120b100d40c000350300c03a03903405544c401680c81090328000322006108503e415601c00358054480074908072020000ca92180030368210b01001142c598007a030540f881a17200c0706e070100a8807516414002c028800e695240c0010900d1703034005481c5c02d0324a03940840c0c405420343e004003520b4040d12441c94032824951800e00028001e401c090310500501d0360341d8020541c1c94941c2c61150b003401034501f009103c41c50503494032074003c1441c040d11880c28022074540b01880c9200c2c40c070036809204003403a0000d281e16292500211507101c1002240d070000d42640c14261000d0600146210700d1624400c04440e614000c2400140d824000448 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 353536016 1250 353534766 353534791
    0x603150222090b040e15061002030c010507020102270d1407050402070804060806030a080a05030a020912100501050a260c030610050108010605030702031b072312030313110609100f0305 81
    0x2d202804800c568071f6000c002100c6160300003081c40d001343e065200b80e60180c1303e02d500f003500308840250150014440c0c44140c0c0000009043d5414100000b12440c1d0b0000781c3c82412044942c000c940401c4521580740c43c0e540c00d03600b54542c0c13000002e00301e03400804100c1e544800843c0410116400a9086034059400e80142400d043c40c3d03a94840c0071300c00c0401503400e11002001040034040194140e0304d5544e00038026041d40800c52038910380c1c82d0210f0101c0700400b0b00b40700020516040801280c001c80781c150510794002c4100181260f00304000b002060740c10700c14180549401e560400c40c6501402080d109100c10504140c001001c400d0140c02070340c140913040082c88007956000003111202c802c0c18801c001642002421203042c0701d01d55009000c1140303000a21780c2c84c0c1d46d013a40c0d900c0090b18101c819000c0fa29541c84d106032030380002c8484202c404646103644c4040381089107048265940144070720702e004a00c400244c41d44c2081042c00c1c0000d840b0a40e01002d4507094810301e6004840320501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 353537266 1250 353536016 353536033
    0x30c050f0721090e0c03150a1d10081f0b09011e06020a021011070512010b03010f06080309060a050906040e090c0108100b070305040305060f04150603150222090b040e 73
    0x1103001c543c00501714480040380040020311000c1980c0340f02c01014002040404090b69442544000310b60300c0ca4013081c03c2c16040042404141a0b00c4400125140e02001c0d180041503002407040c140e80d00030490220f1501c0700117502e55651080c2a06000e0040900e501400c1482200050741c0c4480c1c42e009002558010000c4101698480c080a50300030094034003100003150031460581881120f0740b042e0340000506103858030310036064200c602e00d681c041c1d00810800e020800f88000380c0b107191240407100d030810402c0d1407035400c0010003040c40d40c401d424032500c0c0c81d40d200c01007131075039025501c0101500705100078051200818410002010400d28110b120341c14440030b1414402040d200d5000c44034800108041054054400d95005607080710999940c2d1070440c2854407170035000c503822205400120421004240d19100301019030380c00074050242c910301401040002d5100099001e84000302904102c5440d42d00840d140c0a40710441d00800c902c0d03e10424030056480d1150078086903040303d0107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 353538516 1250 353537266 353537279
    0x80a051b070203030903060705221503050c070507090b0913110906130e07030c050909060106030504020a0503010c0e010315060203160f020904030804050709060e0601030c050f072109 80
    0x151003000c0c4044405141d07600c059100091652080005040c5c250142c002000100340d0000080e05083e01a00080981c80f111500703034100908403800b5000c05052103d5070584203c0c82a80201c1c3d12246034207000b4540f904070f884140c9040c5095000084960300e030f800c0c40c82d01f070900c04d503d0364105902c1c040c1c0d0700140d03005540b40000000c07207080030350003950a500081c10558405030a0304d54801d0300c1d202008446c9551480c15140c05c0075000a41e48074064003800940c40c14071040342da1041c3c242101070941a400c1020480140101130002d90780000d40722030206131990203101d41600e08200d600c80280c0c42d6507510003d000d440c00000714819030b0f96250000c000154012040364602c2c039172851600040c4095241294a403240e410b0042c0d04030000d88100310806411005042c0680d01030811152844e0f6100b0340c94007680c0c114042d07079180d460484040781541d4002e0708192110380d02401c109041c80d140544c41d00160b003124500b69842908144111040c1200607210030070701400749801ca040310300707040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 353539766 1250 353538516 353538541
    0xb040c050603040f0201030e0709090c170a0c060e210f0705031204030303051b0c03030f06031b01050c070b13060905090903120406023601020a0b0c0d0f020415080a05 73
    0x91340a0306260300c68048072101c040c1030140002030a40c02d030082094030001c0c20114203c0026006001c00707d0408100642d43d8038001440d912500d03803005a00c0e100e2800e0a0048500f5500d405c44580c0121400c14040401016004d4032200b11100500901e03911003485103141c0751403520380c002406038000602c0540b03510550f42c1201c050380d4040c100802e05440700c864890b081906600c80010650004c61200e20040b408401503000c0e00c054010841140c86840400d40c40d680307008980c00a280d03455031405039950003080039007040500780c01030750092503546400c00344c958440b48206014262a6405012117904001038401030403090703c001101c0e24108c14519920f205150500b0103c0000b8800a400c021851301207035400c0c626440100102030f6400c00c16101c10a1010031002d03503891460060483d9440000c07046c90442c0c001c00f401c059a1140e085080b0a0b074480102c9000d00c685842e140003840f807441c001000280641240740c0c040350f2a6401c01841000054241c60000782000e0610101c5652030303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 353541016 1250 353539766 353539793
    0x506030d0c12210606080f0a05010f0e040302031306111005040506010603110d020a0503010918110906010c0f11040e06090604020f130504110f040b011224030b040c05060304 76
    0x606015100e1540c1d03d5558a24281221010040700d062120200d82c0a60040625000b800458078820058a800410a0030343d8400d010b160050f0740c81007001c000c2e20304004100c5030403500a005591620039550703140c0101c40500d812140220389a080d00313164407501000500c4040c091b0303001c100304906107596000d88440041c071514042503202d881a10309000543c003110b00c01c00754014210b5841612600203800741d0000d21a0a0070303289415142d50070f8600b203201954030590300c10200d06448410108200e400e44020700324904005a0501d030720001003840c5500d080087c002c90300720750880c1c0081c0400c41a60340c1401803038060780043d000e1100c241000141580c11030740c1243d00c4600386d41404041006c140e002100300219600b410103000c2880000c1194690000f020b55031104040510003d010596429498803400103240301c0c0701c000d09143c40d9002030b0902c0d1660090180b00441c4069108600740d054000f915003a2005060104000a1408000045c1010703601e490543c945500d60003811040c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 353542266 1250 353541016 353541053
    0x9010503030711040b03120301061d0a0612200f03040605371506080603070e0606040b0c0f0a03050d06050913080c0f010e030a031104050609121f0506030d0c 69
    0x1241038007440b645d01448001d1f04d060009078115203960799440000c3c550762035142d0740c4000c0d002403c4120700d14145a00114151038940e102d031250300800d00d204000030403801d8a019403c0404580d96050300b400c0c41c0c001c00c40044004100da40307904040c20b00d0341c2241c20203822000380c048a83e6010740c3c118007021600060001c0b1004564228005d082c860700039003039031920711260f003500a00c007240503038200004034000d090607030803070b05e5064031140c0c0044904000d0782e0303031540044144000c004800001c070043c42560895001d8415035000c3e18881850810860030440216102041c0c0d0300520075184140300050004aa10b4078041c10419800342c94031022a4015060b5500055902c4008004011055946900301c1c003c0004030343c0445403e4581d0400029140000e0508484a0488182e20181c0d4140ca800401651408100b40d04001892100791845101c2d8056421403c00405c0034850180c40f29111713000100346480c0480426040c200708641e01c0b000d003c41402e0700c0f408220002d6011031680503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 353543516 1250 353542266 353542271
    0x30b07050c01021210150c030503160e040e03031803070b070309050109021203030a0c05030f010618181401061704080c0a17040f0605030112031409060d0504020901050303071104 78
    0x281d040140a80f043c45000c003041c00d440e400780014500000759141c22141d000ca800d4100c00e52140045071500400700c0040c001a6060006c40c0c22880c0d130402040c105c807118244603180b0601c040200f41501d5941d05d4a0800741c001004010078a2414607084d1000c8406001035460115140c0d54985000d40203800e0314101942ca40f0303004200503095018003411034005000c074410301000c0095603601d0b40215249080d650408050500031070041c01564000c105030151510280e003030000032a841340206120a220001c0380300c0010704900f900c002c0743c42c030450030b0034080303140264100c0a055402040c0d11603010048401810060031111800f80ea810683c014a09580d80700200d8601d803405250810140c00c0c0d281d1180c100340b0200486004bc8112008804101080c03959400140e6036400300f403143e1042400103098900010b449940c18064100388d0411190500a004000c9096504020381402d4607660f05c0062106502e8101328417801414228011890003002e55100b80924000c50b06103400b464 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 353544766 1250 353543516 353543527
    0x512031c05040c180e0c0d0b161e020304030201020c010c030206071409030708010e150408161b03120801151706030106050d05060703060b1e1e0c0109021504030b0705 73
    0x31901212100902c02c100344c04035411881e8403007500425650741c030540c1502c10289000060305060812860560f04101e85000c107640e030312015182d68000d10084000c2083c664564600c84221550408003801c06500a58441c2c0c05c41c8006450414040002c5040c0203075038191200082c0d000400650040c02e51800410040c5154031144180c0980f041c41541409100d401280320740c4154021361200001008035149458000c11862500d0710642c2d020f09000c008006600400344103200340404544545241c031820725400a9806100080d80c000f181c245a040c001200c8659110000c1030141c240100034821003048420701a11070045901103200c01f1f500080013860310b550a5214200900d0041e10315846131b41c4501c0e0a43d01c2d07a1040390707900040b0345004404202c0258203002d9840e24070070311442010f138007900d541982d4580c014035036500070180c00340800ca00400e0203101801050001c0000800c0d000c20910401264040400702d1641c0300308240810404140700c41175081d04003255041595852 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 353546016 1250 353544766 353544773
    0x17060603010b1c060510020d090515030f0403110a0c060215010b0912010e03070602033102210f06070e0301050c09041e11090a060f12050606090301050a05010512031c0504 75
    0x1303200e01d5101c1644040300110b0b172000941c001c42c2c882a5030010b07645d000790003520b41c001c0005c6410b454683e294107800510009403640511078180e03800c280a4140a224000c04200080c64000c4020382196110141d41d000c204180c0c042110a0350300045040621956042081d454014001c210b4014401c20128a07801840b54081d07021034441c05178401500d9a44c80641000c0007c0d500613200e401403d60021001c3e915518030681c408500d44403400700b0749400b10540c0030400e00079101e1804001d5000c00044501e40e001003080540c500c0b031081c03400b03003200d45044600540f098040c600d410b0b00a0b4102010004c400420720b040b644030f80022240051180c11840400d44554401d540403164186451800c2441c2c00b5008007928070707040111042452640c41c0e20341203c444040050b1240411000701c005d50200c030417900407030360240000c0e00e06410b06040800003400c2d47c80c1540c000300c80a80c1d49006200340d060a003607014400150600540c54404e01d2140c101c0100f1600301da46181966035004207040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 353547266 1250 353546016 353546021
    0x8071d12010f050126100207140a0f034d031c0506041107020d03050d020f041a0304050a0b06060f07061b0905030a02040e0a02040c17060603010b1c 65
    0x3900c49410081002c020a58a020000c0c2000c2c061880c03080061420b013081100d820b01d907103200468100203003070b07400f00d1804410040d4116680c00c9584a00c02074581d41ca0756070411905a0050144411010f00e002909005e023800b111144007070500c4203c8900300070314602c282d00c60400c0c0e0401490601540b00e040c03241045140030007020500700d0100107801e03400c2c19403c5114005000c481e0b40304000c544c03a16010003045030041e25002901030b80920039117025103460b80b07008041c0f6020b41015450303d0702c0c4003a0301041742d100860800c05804041004d00100c4595919428940007200c1d0007455402c3c0303901e51a40c0ca41405000924062100300080c030507403035000130f5403d0454012034140d12035002d45042c0000e459204130040d143d25454043c006003d104c1c10441c03085900c003070082c101d408055021301001d400040a030442e24454050f01c0401604d4030300c5404d41000341da50700e080105203503c400804c1904040d00030752141d00c00b4001845000d041c0741c121114200d0b882c1400854082001e5103801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 353548516 1250 353547266 353547289
    0x90a031a070320041e08070303092309040f15020f0426280f2d11010507020103090b0c0325090504052d062b230601091b08071d 56
    0x1074052647c0000c1015000980e0100707640c29401c441e00f080b12511001541514002c02c45980411030b10085004603c1000380011240d02a844201076a080e010110b800c0e81c0c81800c0d0a0084a0009010402c035070040302496407822481d40701e5408141700343d2100f030340d0b1104245a03414032010044500d40e8040c031046641417450740140c8201c500002e038184a403009503c00b980400b018030b0b0f41c4011240301c1c04007070010741c0b05a000011083c001000801141c60740c20140b01241416905c1d6030700c1c800724480da12640d200b082e212100a683e032415400c0000b110002c03140b424401f050003c04c1040ca19000718083c2d059480603540010250b80781c2143c2020f4601850480100181c0e075568000000d001f07c00440c41034105546903007c0304031804109070340c02e403e182240d16054901003500006030011203c9a54810740300c0c10b42091358510901c82d41411001c3e488150f80e15034a030f60b203042c0401c5c44071130104400c00c0e504002525117401400600a000c90b16000102344442d40788d5211260b0340c4040c0000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 353549766 1250 353548516 353548529
    0x6020c061c0b0a15120f05070c2d050c0f10090b030a11070c060813170a09150206010905010b16060f0e0312060a0f1a090a031a070320041e 61
    0x343c1040c2c1040054507000302814140c144508200304483c441002c1d02526002c8c0000b650f0f1466640f502e61a000030944042c04240380003020900010011440482c031014054001c0d4040c1614800c6081044034030080f49903401e000300e02d0241c0307040000e60440d00250440d0a0503190958a9403184405001000c0c040c101081280010501006000c040d041e181d080e5a6036894240898981c00c90040da05545034070010310130051050400030701c985c00c401404042d02c0a040c0200303419103510840402c4c5030708219240050b440320b0b004210f0010740380a068018820390080c18513007200020500441d007400d003806800e03540c0342c82c103000d9140002c0d4800102001c01d00f064903141c01c2040c000d0b5001c1c24085c0c840600c00d6031100c9012864110341c0c05000d003120200440740d411810074601451054100801c1c4a5110100035000804a107100e03020090804505400c49a04d14201401a086520740f10201c1c0e40e02c034103ca25100044036090494007500da4201c4481c0610801d165000e00526680e042807 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 353551016 1250 353549766 353549789
    0x130309030c17010b0a180f0b0303120712060308091e0a0807030203061806060910030209010311120a030504050f0f04060603361103150702060106020c061c0b0a 70
    0x350020580c40000d01c1c203100100a01003d9406010005d0142460050a0301100e1808941850381982d038010340301e00104030004106008801e0010f810b45c0c00c92502c002d10504c031941003050650740800449031400044508115460840c2c94045e00e500402501e0350280383c13a080702401912482c00c01001c080401440c0030b2096444902958032880244400c07030284c45181d0205420000d4683d60641440c04040107003180e5079940200101e2020246c45110b03c04107054010016031260482c040c061406034402000d0040140c051000035220b2100894198200a5054000079441805c803001c0303c034101c1d01040341909882c0050204900b50520a60107458000005522501a0840d01031002c1040344511125041110b03002034400014200801c40c807082042400540d00310102140c0520143c1100d461032407074456141b1344481520810056400180108080f41d410400380c110014251002800d00010090f10706001c9a041082d508458560307820021549907400d07408010030860703108 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 353552266 1250 353551016 353551019
    0x9010219211e020d030c02030322150f061a12011806330914061b030d0e07080a05030f0304111003090b0f09030d05060415080c10020d08130309030c 65
    0x10b03588101c13035400c0d8800719041040300001180048282c9116840d01e20307101070001110500e418500c09180c40448a01c03020040107110203d1034800c110b858070704848002013580c201a221200c8200200d42020008010419100c2c0340c8104241141142da00c54000414002d0010440b0042c004e55005040d110341c1a40e880380d1400c84000d030120031000222580b030602c0300c100104030742d003400c0c078082c010503800303205000c020718107101e0003c210050b080c03c07010041185019000741182e01c18600344c102d0f580c441c11540504a070620000008040c024001e0003046201d9a2f113503264001c3c85c6a104c2089004000a005d000c442c0c2008240610000c10707048001811080250040c1425402a12540032002c00122003213080c1c130096024000c07200c002c40c06c0c00d1791001c2080c083c0400034401508a500c820684c0042c0782031280c0540909070301e6000e401c000714884144210511081012011503216622542000d50021a1641c002d2812910110086118141501d003411107034002030000c280c0b03c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 353553516 1250 353552266 353552327
    0x705030a060603060b09010812031b03090307030306063b1011010b18010306051504020412020112090f0b091501060804050c030601060f050c12030c0901021921 70
    0x310000f81c81c401c00b020421905d9a20501168000c240601c000d10380c0300c060f842c003115035800c0c0036541c00220a4110003900050081400d4240c006441d1150f15600200d01c0c0410075406014050103801c181c0b034890f001c01034000c42d0500e07003000f41501d075403640c101c411801612202001d07011002ea00107403d11503005284040241031110282124005500c0d00c803c1e42d80d14945003000c10340110784201c80010503401c40c0c03118030080c100981100340241d611008200540c0300c0380040d100814540120082d40c0e00c0d24000980040e0300c01c0c40c2c00343d8040c50b040d8003038006041c450300300d29203c0d040541b003602540c58001d00341ca4080500003100710006070030000504070380e0080903240b00d41d1082050341c0c19500d6020605070395080c00c0c0603070004650841d4014800700e124001820900c030884046442c00100e00c0d0700c0b03601c580d00079200d494141d0030018200401d07580401034241c1074038481042030217221058542140c401c1d610544c009e884a41403d081110300d1040e901c4111002281d03040c180a500d030f148 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 353554766 1250 353553516 353553521
    0x4020307050901080f060d120c0609080d241a0f03090c100201020325120608060103060e0a05030f0a0e040510030c060e300304060302040311090702030703110705030a06 74
    0x18030755000420410006100d00c10500495000301e0340a4910780d41580d0030307032300c00141607503941c4070304200070300101c4a001081707490103642d141e01c2c01134006569641c507064040d03080d2402491140b81104800c003078215900303030f1110001c084900703400000d000702800b140340b00e0f110f105640000b142e0210100c14014507410205900d24110011600e030b14800e402c05100b80c0c2030740011036030103000e1410310b4143c0030001c002100c000c45a83c0c0a107840c2c1c1c00d4031a01d0040344101e69181c1c00070a01a80110014402c0050030710540e100590703500300134035403a102c940d18103030340784100f900da03030f444400c04280740041c103024103205420301e40020b0040c0301919282c0e8520b80340d01c00b03070311040d100f1a01c94000011480d000306001c20802c88050401c49021419040a80502c80c040e0f1000305403082c480401a03030b503081400a80080c086654015990780d140d8100b0003074020318840700c00d100d4a021020b0080243e000002c85402992500380244179444602d511130520034240d10076905400765030801400c004080d03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 353556016 1250 353554766 353554777
    0x31c0c1404090f05011401050306090408041a09040f02040b19050712020a02030606100e0909030403060e03070c0902040e04020913060230040201080601201f2009060f0403020402030705 81
    0x460070404c0e6a41c0e41c0170480d440515082d0382c0d011500400124059080500c80305078420f004010300e030f14055950f10714034034180c3c14428040700d450707000c280980103181c0743c000d038107a0011030070701907003010b04040421409125994194108420031202000480d0243c400e03501d4507134020864814809101602075260b2403800c20072032190103148006031540c5400c05286084041c2071740c1e665026900387c024003c00c51800b070164101c6200c10701000000624034000c58503400b8003032020f19110205031608441400940c4c1110000714014881400000c9120040c190300070b03012a40810291200c070303160f07500d501354070b000901500c1c00020144404e43c5040c500c4e000e00604483c40070782403c00070403032a081ea401070398000d0001e414180460b806601c6000e04458145900c440d503161045c2c044262868154a80341d80766981052424000c00c1c02074500c503c1c5500c911611088450f803c403111200d00c0d074841e00f06558410000401d00012488071641510060340c6d002c0e10456403800c2008024000c0d8214 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 353557266 1250 353556016 353556041
    0x4050a06200d0c06050714390115080303090c06030c0c060705130e0c16140601080705130b13151d060f0616080702011b0606030311031c0c140409 64
    0x13000b0116808900c91f0608401d40102c40f4407490601d41e8039550b200355515415119080e061070760f01e0a041018006c02c0700e001c5024500c00000e80e81c00240d030014283c100c10383c00509690405d104000b4005030101da648842c840441d88075580303075101c3c41c0d60007060040a00710701e028401c2c5410429140d030080010328601811100c400e00d03007a603c0002900d404411209040142400e00801c98020700d24003003010400e10519440d002c0500c500c040703501d468002d92088201d80e0040d8001c00c21400e0801c1150082c0d44804020700c407207007848011917019880341c5d84035850207554014a4401001a21451002e1301c3c5003800800b00000070b9200d84060303401561020700c101d021914a100310700c1c0c10030884071820f1100d03032000310b001d4445e00c8141064014101c00d0f03040c00080070006510b85e02512241903c644502d4000944506504005000c403000d204100c10755030081201c5005020721700c2da102000c040b184400309604542140440d03d42080c0d414000c1001d10200d408201e4070203a07003044c04002c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 353558516 1250 353557266 353557271
    0x1b0403080a0801140d030507020f040608060702071503021602010e0427120c0308011a07020a0810061a09040905190f050d0512060d03030b030f07061404050a06200d0c06 74
    0x20803c0170450102c00200d001008100b00700304000040c100500703100c420590041c00020225030395003081d41003140c102c030a01d0060700241c0c0d00340040c400301c02241000c80d200303107011424140761000c1014030b013003603981c00380c1840300c11010160b083e0303a103070000c115540030540054050340e40d26403102c030030b02e11148080b198080b580a005608611400741100c580b5010f944040999203030019102015680e1103c1c803092100401c2044050b071683c0d40100002d00a21700200412075003103401c50111503031900140804000c0d00c1241c402c1000070707030580303c051200303c4002506000600d4010701d0081c64140c0c2e08401c1081041c11000c2c8804600c41581d824010402d945e4102080c4408481c82d1051001d41c03060034680303101203501414030203c001d545d580710303040014005810400188c948654000c49510580c000c40b0184201c5500400010002d020a0070080c2004d0610300010b9603900c050081c0400c01074407000b0034030452a0014131150015041c1d068610007006048007d11281462800707803022070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 353559766 1250 353558516 353558549
    0xf010c08092d0109080a080f1b030106050c0a0227070810091a0310020423090601030e191a071d04110d020c0307110d08031b0403080a0801 61
    0x7440030a5002681071146403424182e80155010b4030710302036450400d03400d9981c82e07110a00089013500209107030307100d545902e1902d140140f040d4120410003001e40f1580c4e49010300c0380d407081c4604016039042d2142401c2c0b01e511504c40303134202403078000140c00103984184813900340c0125841410315550680c591030f400b5040340c3d0710b08205544810098500d00056841c030744041098019a5200e8000c080c6c102281c0d5561422510002e85403281009107802800d5000070304222860030200030040d0004005520038001445034005840d07548001e0005040c1621903240c1d401d180400c2c80030b0b40300c41091800c030960591003802c00042e4000c64a100c03d121541c044003007a9040d000d00c801c841d0040e0032940000440d05000c041c030014000c0075222030007440061050700e00a013070700d0014105059004006540342e80c424248954040402040035005600c100310400210b5004c03800c40e98801c44c024000c4480e03105582d0f5019407407040da400500405404510240702c95804401e4074100c819074a00390280c1d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 353561016 1250 353559766 353559781
    0x21216240b100f3c020f0f060109050c09060a0f1209050a0f060f02040605090a0e061813021e010f020d0c060f0b030312010306060909151d0f010c08 65
    0x11403458201a011074019015040c1080c800e001054010300003075003c200c0c40b45942c413103010340aa00d1944952203065130041d44d910303642c100030200480d120000106100d802c040907540d1240410701034a00c1c0c0c207442d10005201000464115092a08094041a5208500300c0c0003840440b2001c42d0a0000300a200300942d01c441034040c1d444001c1c0c1040240075240f10a69808104001c04501240c500b81c540413a04020841c0388080c1c8000d002640b200e03644c400c4510200244481c694004001080d524002e2000d02c1d180d00c0001a166030312088400710a4440c400280d4002d003054400035482002d44940b0000a810071580c112000360a896240000b00301c05070981c2c95116a006060004070841d8400c00440c0484d0804910308084d503600140450707502c80440c1c03c1d0390200850303294082000e8010010080144901c00c01440c1e1405c0070480c3c180a9900c80035502e98410502c19184d44a0320714010328907070318075070b10307440c0c5840001ca1b0300181c80c10124501070400010f84801003802d480c00100c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 353562266 1250 353561016 353561029
    0x150f06040c140903010b100e03060a151802070f060f230c0d0b09010303180b031b03070e041d0c041109150409090308011a0901021216240b 61
    0x1581c6192a001504110301d52800919080150342c658150f40f00e00c181a9035441e01800000859810759070f8600c0300f1280c80c01c0c1460302c00082c01043c0e03c41c4c40e040c0399030040d803004141e00f4140c1e03c0d2108040d960070701c10348280c0c029010f9a00040c01007410444030800308806230b8010642840500010300001d6440c0308a22110380355404900300100c50440096680d126071001004a0b84041c07134000b48285c02d11010880051098004802141180c2800030091103800c022500600400f40d03030910394a4040212211501507040c00181544003001240c034017400fa545005c40d0b85401f07031041061000f250a9424042502c864010a070300800c15070b0512424140103c10900c07404543e250310b040f0001040c0030010b44202072041006400b400003041c060803901450350002d02950b44e4040550600b680100c06506160802d5030f0f900041180004598000c105550b901d0880510141c40c0c81d107003040e642e80b20801004c01444440c81d503240c0e0503a601291444418141c0f5a401040200343c00000d0010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 353563516 1250 353562266 353562281
    0x111070f0f060509130f1e0e070e040309090903030b060705011508010213030f030c150605090105010516060c020309100c05010c0801050612060616051c02070b0405091008150f0604 79
    0x1000300410204500041c00746c0c001c0340704440c04032000200103404030290249030070741c444400d8003a034072485075410081c802c0119001802d0703080810007075410305503006440b001d44e5200c0c100c10184c85208920134140698894050782d10003404503079031900d2034a0b00d580204484515298048640400850100350520940d0050400280290f18413408c5031650344400155900803010400308010a400080c021002201c004c01c0c0b040d00402c7c25030070003007003002d0f006c4140c0005041280c02d00a541c0171940d40442800c0058000b0b20001c3c0c030142c0710f98200d040d8880c0030307003107034125000c2e100d44044903902420f201c1429002d02d000f040300e54032a0604a4080000f80b103441c0e406081441019004c050300c0400320b41060004007000c0c60007090031100b5042d05800303030050342c240d04480a081c3d0313001c0b00c150000c14002064409450a94105583c00313803140180c1c01628082c06418002030881166601c008000d42001c000b1945c003c181034400c01022001150315030604078000e00131404a08040c002d804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 353564766 1250 353563516 353563519
    0x3030501080f0d0e03031e120c0906070809040e0303010b0403030908030705030a080703021611101701060f110f0c01020d020313140609090a0e012f090111070f0f060509 74
    0xa07003030440d1080310800304010390742d170341800208054030400c0b03650380f100340c02104010030680d101d500c0380c1d00144049000805044d04000c2c00c02c028002a0344e54002c40ea542c6502184482d00c55041c58080340040c40301c5540c145071884000300201da085c040340b002d002201c1c4203680b000700454a40319803545074002c1100003400c42e4400c1c803007200c01601400d21954060310510700103040c090b031352004400c07030f95030341c0300a0720003500019110140c2d0030318034200c07032000030241001c1d600d40c00c3c03404120b007004105106000400241029040c51107124000b9251148940c00403140031646166869841d89000030655015214408507a602e16002109031486511040e103480009842c051a000c82500c07102509580203500b040510038980e201405140a644240f40000e01030000b101102e003111034403028024000b1b8031891040400c1e4989941100403102c9900841d00c910103140103a03a81001c170042001d2900400c40c0210b4203420050647c000c54080c1c04000403250741d07903542030700c45200301601c1c1ea = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 353566016 1250 353564766 353564773
    0x30f3b010e0c060a180306060f06020d08040803060a03050a08031609230a05040207030f0306090e0303010302131b020609120406020c190503010c120624080a14040f03030501080f 78
    0x6442c91810201510400b1140e0600f5102e03034403624003100742104640c104a440d5a6603c1d418080c001103c000080074051900040c200c40044990150510500410041440c40004002001070312400540070045d40e0140880d99401d4461403d40c0d200d0700101c501c0041c0c04007203900a52803612403074060040b1500b00e030012103031004020070705000314410343c0b00c5500000800c8001466465600c018801503009940d1001c120402d000d000381584ea03603034444080f6034107200004800303280210840e41181d40c1220b074040c0c000305612000b005400b442040c1407151100a4000300855004240c1c0da03c6660108155503045204e101c1110050049000d90001a44507407504411414a86954045c0700c2964004903911907840e40041c2c00e40394021f60050004a100c1307020324400200d4000c0c0006400352a80d4403403509108801c0c2048411000648400c004406000c181d01194960210035030003032200b0b10f82421319242c14040d0108003426402c4000a19240c00058181404560041d4502c2e0f554082c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 353567266 1250 353566016 353566033
    0x50c030406090201020a02090a050708150102030d0905121207080f0f0609070c020603070e0108091b240a0302030402010e0406062010050a050414120901030f3b010e 72
    0x22007004000203003040f41584030743e08000c40940e50341c50141e0301c214605c038004501480c201030010290030001c0d00104030b4402c61420200035a0300401580d00003c0d802c3c40001c2e20000707905005151a005180b8900311000000d00d00b00b803c400348019500c174089070303110004251207400326094000c40c110341c52030f0395519a070080b90507842c2c030b04400740c1c10014601c0c00b80101141500081c08036481900c06c6c001040ca0302c0d84600242d41c21031981a409000302c0c020300151070307550314511200070807c0041881080c0c51ba420304001d40303a0f180c07040c21403488005000d07200d5aa682c0064001e5006560507401f14540b03a04909281c07805000b01ca00f620300c6d175620f0340c0f0402003c66405840d4000c241c8041b50900802075201c941c0c40440c4152889200d422401185a003000c4c00d00c82866030680c22107171240c1d00200301054000c01c800088462058082c600014a4800d00513520700406125403000303a004568440c5038201081e00315120344154110854201540e007a041c66802c84031003560010302904117003c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 353568516 1250 353567266 353567273
    0x20a0e0424021902060a0e0c031b012c04050f1005010509040209131a0d051c030f1802090105030325020a170304030302150c1c1803030b0f0103050c0304 67
    0x14986408840c00300c01504100c1007500b070f100b919000141ca403005a001c102001013840d0306010b02002c440140025000d04900180420703259810000310f010162046000c5104d581d00c507c8058080c841e00480d80404014046c2d40003201103000c1c00380c280300318103000115119400008440f4001c0c03048440c482c100c1803400c070040d500c40c0c006044980d80103a003800400c42c1d54569000200032000a00350004100f5402405c203038030004460802c81c02614500d440f0000a20700141d410500c420b04044e41c282180340e400100e018240c0f01e58003441140c10407184422035841c4c1358141074010300c211910032180e030302e8000341070345c038026506000c00c40b080c191303c000d0314419605911480f039400601881c40c020b407203081a0101017511a4085500d500000c2d00300107040d0706104003207204000300e0203030b421400c0141c00c2c40385900808080380003003141c504100c0040401c40d40014400114903442720308040250401400070600d1004075030040408240d82039843d80703c0d10507180b04040014405003180c8803500c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 353569766 1250 353568516 353568563
    0xd14161d040804090603080d060812071410020c48060d0c02030309060604020a0e0f2e030f020c0706050c010f020f09030c03010603080d11130303020a020a0e04 70
    0x40003580c40b00b0302044040f44000700342c02200080d5001e00e0500d075803100c2e0b429024088403a244d00006068000c8041e4a00c845042000ca5031516008941d80e11424455140300303007046039444e01da00846100040e5030080701404518606c0400d0310310405200ca4403001030000b441050b8001e0448180c07100c10019035110040c80c1c80c1c0c0900d000c06080c890420540107900c40881d00c0c4100f070400980c3c40403007006140c0074208a0a0b80c4100142c0702541040036080001d004050701214091140040152003001c5856010318050050350745400d81085001d507100350a40081241c07081c1c1c0029023044500341d28050345008840613048128010124103290085c11501908902c403210303c01d5480c0c094142100030140040c00d00c40502a1f1a580d441d107010080510340030080c44654002c0c0d0401c40100085074050094a01211030110082500c0b001100502d0052062040010071640c82c180040300303046d40001c0382400c961095030032107045902d80342d28140d0071504403001001034030107540400d500340240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 353571016 1250 353569766 353569771
    0x2010020a020313060309200303032205060f01080c01140f030c0d11030601080f04031707020a020a0e0603150c04060318080d0e011d0a200d14161d 64
    0x61040d681030158452040c40c10060f5584580006619124030302e040c00400041d2607600400110410152411074010940700d0000400700c901180364810340348224441010b44104456018041e1219841d121266114031070080c000c1d0b503024440c81e220155254080c09421120911407005282852000c6000c0c10f42980000e05c0303804901002d22400e05012034600803200340c4c0d0340c008221760320f0b850810f0005048840003019203494903401800c0c8400310350401d6640400074042541d02c0c18907501e000d81a450000c00d01c3e8001c0d00b011200f0000105602c61406107406460110b05888242c403091541e51f8a11005a5003558002e004000400a041c025402103940d0380c00356a04a00b03149403512001c200703411091010b1005a00d856025007201c001b8400c21814041840c030b11242d429050014990320030000d07100500b401c501d0300041c404880404800f826840700140340400800726031800144180b000c000954151003000d0340c2c62115507804101006480d6054041154480340f806407020b5500007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 353572266 1250 353571016 353571037
    0x60d0504031106040b160906120f0209060c030702270c0c10060e060109050102010507050912010921080109141306060803030c070201090b04050a1a160f03201002 71
    0x10556102d005500a0008a00c40d0740036600000d05032801c0ca0751428110765a402034402c000260805010303842e009040300c0890311101e2000a6800c01000c03c4000a101e40c110483d44424085040b0302a00c800000a0500394030aa030004030181c800c40d807031140c0d9001001e0a0001089803030015480840b4100504004070480d012100310b07180c000315041c03c0300d896802140b4200c000c0410000da80d42c018141800411080c40200038500e00000028228050300c0c4249110703140c140c0055068220942005c04026000b0a01e2400c11040d5420b0b4040080030300d01c000003182e9070100000b0420303030300e100b541d8046407402d000c5003c1c0d640380b00400008015421085841540d140804110460b0410240d8031500403a0103050f80c0d240740380005001044980d2203548103034800c04c41880117840c0ea081c80700840f4803c8a03030708910401001000d80900a402c01c0001c401e074603250142c248442c0d0100703c0c4c451402500c0d0300c0031038a241e4900c0c0c021064200c000d132000c2c0e80550b81c1c0108180541e8020815000c0c0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 353573516 1250 353572266 353572277
    0x6050304050a1506060807080c370509190803040311011107140a090614060912010504030302030a1a010c08031b0f031015020a0321050405010e0c060702060d050403 72
    0xa03940d41c4003001c1141d4221002803035507801051120540110340705401180780c8c24070f500f80b49407103281c4119500c581160020100e04910384510a407212100c85044800e014072222082c8002d98002080c0740c01c80440da51080c40c94600b04080d00c6181424a07060b901842c0c0a10724050079915030200781c0c0c0c0300d1150301e41003001004480403451002c0c01007101421541c008581014800020800e0640f2540c010701d00d11450440e04000c0c040381d03c0d42c403010b48141510800d4582d00c02000003201a00e0170746010880d9400d14040004040c1e166008501c078030340e0140204a040c0e80c0440c5107210449184140e40496413200b40303200801e0140c0050740d0300594400d100b40004d0440e0f41c0b40c4c1c0c41d0b90065646c41c0a21800807040c024123980c0070b080c03c0094a51010042100440603800039034944e202c160140c10300111920740f030100070032103040c1c406e000342c80e503814403850619141083c024851941451064001c2548529084c5000e00446204540007444607080c0303c51452020000c00000c1d00c02c400b03000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 353574766 1250 353573516 353573533
    0x504020a080d020c100906170a06030b09010507030f0207081e0d0f0f0e06060112020310210515061302090607140609010e240a0605040204080703030311130605030405 73
    0x49042210000840c101e0740a010385030044c00c14001c0c61880d035036501c0706011205105100301c56011078040c490a4051000081e540c071407a003034a00030005504040d1840b64407608021083c101500840d014402d995070130005030b600f1860741c904900420400a124000801500d081c0000000300500201000300c3c02c0c45c5000602080c0b00e080ba164489d080001a40706d061400c600760a43c0700c2c05040d4060240541100c3c81c0450009040c88a418800a03846070b0102c003003203050614003d034001500d150040190880b0100f404942000b50603c412545c80c454044014209250056014001c15001d0300e400030b02585032081c1d6010350845038007150000d00c02c2c4900c4003c20b40c02e05c201000d07212944050031150400405041c03c0d0380d00344c1d070805180d070301c40e181c8400b02e24120440e105456100e030394014685d440341740c404cc1c06088681d0000e907202c0d0000c1404102140d0100d21001100d1003500c042155000c0c0c4080311055004240ea0584040d58911003000301f01c0c028002184d1151140b001c0d203500342e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 353576016 1250 353574766 353574779
    0x2b0f080c030a110c011a0d0203070e0403110a03120c0906050d0c0e030a0c1e050105030403030914121305010305150d0512130303030605040504020a05120a020d11010806010504031101030504020a 85
    0x603004070725a40d40d0351b074560954091400130f402d07400c00340844c1600c01c10b41100e46500402d985102c180f0503204401c403201c0006050500c16a41850002828804d840c240d909605000700129070050400390780e60301e05440e41c066507004000310b2084611a485050404550a14080042520342c444005102c401200f04810742d50510070795010328070411194564500344003681036403450f0700b40307031511078481e07060705001c980c1e008802e481d030103030303040c940850251903e20f811038401a40c0a8281001c0c07040440021410545a01601e40309a1843c6092006075030341c0c004500f030780c03c1a9141001541c07952101d141a003048a403015100b4000c10440d40f000783e45042d038040303e03072200c01812001c004280090040543c58041d0700020076088400340550f040c1900003852000c0b141c1300396886007104c00039141c3c0362039080c05140c2034250001d2280e00841e181c0e0030071040150040b00528002442d800000c0c5d001e40c040c2c4107440c01c1da0f030040460b41e0605982c2c070040d0018600034009980c010340d09003000940 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 353577266 1250 353576016 353576051
    0x1b0c03070501060e0114090912090d0f05100e0705010c150605060a0e0f010905011205090f030a090302030c03070f171c020f06071409040b040e2b0f080c030a 69
    0x2400061001e100544c90010012203d001c6a06d04a10942d5003505001954500040004510b204c40ca9460f50f44c0d140000000d201241d90f0200800b110f008003041402c0c044042030100320041c0c401c030144804170000c0c15540c0c64007103601809011809061805001c42d1115809003806006004001100c940300d1000410582015003214001411300540d00e6030f40c14030807410035182c0000e0800811417800c001c00a408081c024a083d4079481d80e84000802c50281006010444004102540d0340d40301104001440003843d030200382c2c00307441a181c0b281e156040004101046404d2041c418240608100001169001e02c0c5001441440b51b0000c503842c5040c2400c1419034800c03c0d030014101c030542c0c03a04003400c0c040300920710800d1009101651100760341c0b40c2d0840d140101c04850014146021800003801049894299611841903a250203006802ca40300f1100910b60305040c2040d21004440480315400c11917103071000940c0d65004103018244150185402162440022401e41d402881a50340c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 353578516 1250 353577266 353577269
    0x717030301060f020304210204270b220311240708070f0509010507080403080d0c1b11090402120d050d06080c15090d06020d050703050a051b0c0307050106 68
    0x650800401005540e0300407064108010081c0081c5040a00d0721018041d0717407220240004115914010300e0302199240d0707200200c02c0305003020151a07071b004400c4182c40504641d034210303141c90740c68001c50601e0a0400100d03841c4065100c100300700c20401d0f9012950041464414001446000350031200000000b0150309005200214007000b0316200a00411400b0042c0100c418490682c0b074128440b54040211039911200b0b0a011b3781e60300c6107242c192141d04ca15440541064008580b400f00c010154001c140641c940d030f0745841105034203045580007482e08840c0180700311048420341c40d080c104002c0140d8803500050000d500e49041000d600c0c202085858181e00041c000510080306183c14401d0310041e01d01c80d03004000c0c404440000c100050a40321429071648000300b1190301c3d0b03940c1c01480b03910399517101800f5502c1d4142c5055805c0072345415191000440e06010000c2c0b0704806070b109443c80389003500b0200006148080d02034025030702c58102e45106000400032a000b06030b09024000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 353579766 1250 353578516 353578559
    0xd0f0c03080d0c03090b2a0d0c090509010e1b0403050105090c0a080309032802031207260901080c27090f010803031603090c06120e1c1107 61
    0x10380d90b40c42281c0e108203ca9803072120405251401c180d0354085030400d0402544006c40003680d1059014081040c1d40d0070003060200f0100041c00152501c4221480d040080714081c1d60b00e81c1c503a00e64850f410010b902500b40500c03084038040c240002c0440290a40c00c08000010800e864681600c81e01d4040c20744100300ca5204a41d0f1041c1900306003030500e00c01800042c01260040e6040c8110840003940720980066a0040c901c80940c01d00000141075800381390150340101140c258100384d1030070703540a8203c1e20054800c00741800b101c09110036491002840740d40c21000c07080c40d001e8038600544400708054550080414107000f00892901560110601e40d4211482040342d40c86d400c040002001001f070030300040b106404010090f0300000010740340c0040e1144170b02d910340380b00300c0002c4000b81031101c00680b251100400000e0051f07082901107002400f20042800310480c01414540d8606d04007200e244251225900100024070a02a820141c0581800d803044507035103440100c0ca003401c803107254 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 353581016 1250 353579766 353579783
    0x2120d110a030e151b09031615020106060507080406081315021b0109050303011a3612070501030b06070b09010b0315042003011d070513060f050d0f0c03 67
    0x3c041c8030040005003106a540052100d4901e031030541a100c02c82002400c0300c003800c1c0031174000d2055905014a22400c4441d0052141e507540d15004011450315150030500035510b840e9011911f140b00e1001c98446a400c80300091070980307403403800c5402101c0184030b44102115480014002809585500c642035480d007005a01c6840d0481c3d2218034010820600c0d4442c0c1c50100060001280441036034110f454490300304440342c0104030000517903c5007086000558102c00b400d00d01a00e203e14000c0c4101d512162441c4c0150566014005866000700d51039074158800401045558829000350311032800142c4111308001c00381d998420300f06d0040d26070000036511100c10390801e00342000343c00d000c8659127a01e43c2c100d0505468034903111484081d400001c0340c03d541c412020703480c250007000e9001604801400700c9610040e285840306014011680b10301aa00210705500c007460150800750740140f060760100034609010000701a09411044070000200359502e0042402d600c2c03030b00d00941c081c0048 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 353582266 1250 353581016 353581031
    0x60f090a080f1204050a05090712020c0d0e0303070c09020a030e010204180c170103110f0d0b0105013002070609172503121d0115051f02120d110a03 65
    0x2904100791940b40c0160f440050204200d507aa414183c203084420503594000305480c0d49108641003800c0185081010340000f49072440743c880001d00c0091321601c0d5540300c06003845c4008240e184d102d034034000f8004410341e103810b102c2c04038103500604505902e820002814404005000d0998120b41d101c1800502c404045041e2005140203412000c4000d01e0420a0f9004000c010702c40d1310018080908890035891168040342c8a541c104410780c13034010030040300300965140018590109004c1e450001e42c1090443c2c030301d000100c5081c0290800f0800e100311848040d0319140094204040c244d071403545400c0c03000c0110386000c1c4c2d1441e40060b40400300d0358501c003241e01c402400c02d0038441c4130000c1c1e015680c074030007080d8403c42a0080050601c1c000c5814104861440c00c4480980704004195107860003d0741e0030031200c24804210f46050710185441e8070031800404940050046000141e0810320708042e001c43c2c0140141000c07248200001030410b2507810750310180d04801d02c69004070765141c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 353583516 1250 353582266 353582293
    0x31d120c0c01080402130504020f04090524070905010c020d0204050c0307030608210a09170c011103090f060304031211030114030a120e0a03020402030f061914060f090a08 75
    0xa05009640282010f40c464102175000c80da402c0442d1080b82080390f55100840d04556401c5a44e6142c0300c1c000f04144a140082d003081621106404208491186c0c0314142d80c06540ad0f041603203220724855102c00030103d03e0400152105120200202c5c0d10620b251540c0340140d4492103090700030100102e40039200d02c3e09810240032110b80d40c0090000b60301400f26407844600700b40a0110f80b11a15141075196443c100007521880030310741100c8031480e440c11018501800024418203910710036030b50206045400001c16489200b00d014050300040b040e451070000d41041001150828420314081c5089800b0001e204100d40b107010345408400d0740000104404105120341102001c8103c02500041c48507070384103508682c04094040600148003c200302c5552860001c03001150080d009540d00c0c9031000d203003d44844102c81e120300c0f6080310710031649079400444c5084183d8050428051382e120078101000120781000c03d034444074400c01c01007465107807598421742008029000c000c0403000d9204a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 353584766 1250 353583516 353583523
    0x3030e0a0b01051215041e05010f0e0c0405040c141210050103030905190e130203060103050a1a090601050402030a02160f03090902090112020a090806010b030405070603050f07031d120c 81
    0x28240c01c4c50340041c291002d840ca5461403d600154000741d42c5202e0034880d00c548942e840c0300c5c2d1014025510b400b09100100440703801a169110380e102c240c0e0031007501d91b0104021a03d08ad640681500f140c0342c000e1041c200041034400004400030201150b01d03004415031844c0004140c10301c5120ba44440c010001c0540000108020b411b080f0340008251003030180c541551525442510001c0b0001d801080d1103090480740055241d0b00030b000d0302d0056071681009c660701c003601c8000312042c40340c0802c03590880102c8401d5502891010001c1c01090b4039245c20440a500081c102210361542049401008003a454102c0c920718880c95081000801c10304024290604551149100500410200010341c0e8095a0b01a03003d940a40041c0c544503195001c40b6180e4094000c20310a20030b080000c0f500300a0700c0301a41c4994415403c80780001e0705c0b030404409441c42580d000e11030200b10b50201c0c440b40d010350001d11820720400d5041140c000030004880c49e0583c2a0003903040401c000481628a040a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 353586016 1250 353584766 353584789
    0x10902130c12020a081302060d1103090c0307050a030b0703060e04060509120903070302010c1a0c071205040f0303030b040e03031905061008180c0d03030c020d0207051c03030e0a0b0105 81
    0x1440440c1401c0404c0301c003a02e5100020003042c8000070740c843c018115920481622046240c10b0030400c0154070180d200c03c101d03801a41c0440c3c1900c6000441c404924000440c0382c26070700702415151035285141d56001e0702c85000b0302400c060645070440407031400580d44866100e03900440e400300b42410701c00780081c1800e100c020301800758801040505569180018040c044903820301e0201d0008030300b41088010450700c0442c9501e0b01e0441c5090045044c0310201412009008059522101002410590b240d01c254400d00c07140c1d1300e40b10010400700780a5404200480303000780001c10302c40034407c0c0303c5007143d2080310f42c042e0b2074240300300b85811340303110f441030940c40903058502005500d030328400540998001800b03d644030514400d00392071068240b0081284070806442c0d200300d000b1500e4084d020b442070854003401441549202221548002072040454501621980940303203013480f4052000f503144025400d0507110040c91074a100c0812900148a01900d04640154105010411b460902 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 353587266 1250 353586016 353586047
    0x16051b0906011d120f0d020a021c051f02210a060902040e0105061b010608030901120b01080a0b061c02211b1e0a080405011b20010902130c 61
    0x20940300c1c00b0079801c08035035082c150b0411070b5001c0102045030601171801c0c41000c49100140102d1803008002900010781c0c9401c503108444805a81004070302c0000168400070000c2c00d40e503c590240d0500c2d05040b100e00d0140841113901528040207500d115800f8100c4101c10440c50040d10200300c2902028803d001c0500340007070066150a10b4000202121003060003030070701c5071700c00103203070340841903054441034040d40000020701440790340e00c4869071240c000800c003c2c041400e4026045012046215092555605171124005912545219001080707207074941600001c1c100043c100010741580c1040c1e5500b1204c10260352119820321040d90810071800401204003001c05110002c1881305062180380070641203a030300c441ca010481c0c182c0f02c1114a003c4072021000400485d190b0744201d0081c8510f000760024090040d00280b200c2d044107142c2540c000288415140340c0d041c500b10b0700d46440c0d4911050010039001084d0f000261807141402051442d1681c03140d83d030020303036017049090f1841d0b802c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 353588516 1250 353587266 353587277
    0xd050f0117120f180904060b100f0f0807051e030612010501060807080408040506070803070206011e060815100f0206060102030702060d05040c031407030b090703080f16051b090601 79
    0x2d103240c540707103103000d4804180c0c0c5124000c01c40800310411084900704507040206414001d0819051000040000560700d40c0101c6c0c003805882407060160300ca0555030302c1140d8481320315603000c0004945030b00014000a0030440200003040401403000d80902800c100c003901c0f1340c0d41e8107102e820442080640441c100c0e00340d040200400c00e140c0c000301015880002428145410380c0d5610300401c1074401d40c0c002590010011410b4802e00403c0409107104100355000c0300d050381d880354030600d4500b440031038401015000400c2800074030320403000141c00001c40508030001003201c0001620071801000c24800243d01012602d03025039041110390380000080c0051841c0c001e10303802290240c13140318242d41c0710f252900041020031a450030050000c580082d03400303018200f010455512911548800d0318182710100c0800c880c40c0010500c0300480c1d6001c01510b00d0601c41c511b01c600740c1d0f00040340c030031810044849105c1c0440c038180180d0380c0801ca0140791694100d8071204004035140007900d20b504022 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 353589766 1250 353588516 353588533
    0x12020f060108300c03030c071a190e07090e160608101203020f151005010905060304120216090c120e0d11030702060706050403110d1d060d050f0117 65
    0xd4809021643c01c412140400d0b429101e0207a82c8a2032040054004084c0701c00402c00c40044540e0020b40075091107055402071030f54207034070200c804400070b80d80c07030084811034a03000c0c00e4603006070301c03500d400312490090b1210320b42e8400e80c001c1268040300c481005c5402040e0780640450806c0e07002c40103421107050408031400d00700603c1d02016940c1c02074500f660845c010640070706000b0406842034012a034202c1d0700c810f4004d1000048910166124240044080408200e560080d01c5000c01d40d10003910650541d9566112520009201c845100541c050f0340d516040761b040144410028107400301021510804c0340c10300a207003140e086242501c8a19101103400c1c1c03800c000c91071030794403962407401c010a8104501203909500ca030b140020341c00940018104200b00c10b9800281c4070343d01075203a0044040c000003006856640c00c075804800038a5186602400c1c00905a5000c0c1c83d400c007810301410150000c4c051011141e00b0f0750700550309101c031001081080040d6461a4410180c03102405155 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 353591016 1250 353589766 353589793
    0x50a0b1c030e100522051e0906090c12070509031c1b05070f03110310090f080a0c080304030302070210110a0611070c030309180902060a030507030912020f060108 71
    0x8000c1c110348640d48280c21420894441c0094401d17040501c01e00b04040c89403018410300110440c4607a0340940f07c1c2c0b40845000a030603d600c59118040074054180903915582003104200c0010201c01804d842032003800c00e03000325170300f09922075005502d881e0341d0b0b07403a441c04240c50300282900da01030755510f41c8841441c90b540203140f151403180d083c2c42e08603003403c14606a810700704540c01240c0e08520448001050003011441080c031054198240c07100c4100c1c458041c41503d0001d00c0145c1201009845400091920001892150303094030f010b200c3c0c0750140c1e1b50b00c210380c2e10540d0180c000913000b150041c01e5180004815080604504040520245200c40280c5440080402a140c0c980c2c0390003a0003001603180407070345c1445e80b00e110320b00c0c81c684034600034082081074010550001080074850b20325070058852410040e400500440c181281d030b43c0200c01601004204404164803940000000380d501125100c1c010b15a40152880042c440126403500805030701c140120743c400320304503194 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 353592266 1250 353591016 353591027
    0x7090614060403080a11160303080a1b0c1a0f040b13050c010528050319021309020702040b1e1002030f09010e0604180f0c031b1b06050a0b1c03 63
    0x4813135004070a942c94034241d580c11b5905400d40050084540280a0b07150710b0100001c40b41d0054a100c5e880304403807526802030314000c1390a604111566040c8005d85c03a4141d902482d046d2584610a412041c03200e0f00c0c011080c59058000e58401300c100c203074001400200000c003000d456000d00020b204146640c0c0d0344c0c545c1a554214102d025051090000f07216195400482003c4004011450b41c03400016407445e009085510844089102c0c0960ba210390a450050340202c0d5601125200c0c1c0281c03040c1465907040c000c0d0721003d01240d00c95500e40c0302c484113131034012070b00010b200d4a60104000c030420390280050004201503110840d00304102c0110090085400d03036010820070703e841c001075107007580801e12621468214148012589510000c5810260882000c2c000389400502c901460010281e09a4190b1992007484008900004140e42d100d1405010700800c400c0d600d14041459403902c500312101912048407180d02e0b2007003881603080440203840071a100101a8a90080940f0300601 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 353593516 1250 353592266 353592269
    0xf0c0206040c031b091811031f0f0f050f04032c271f0803130b0c07051201050a1104050904030305060609041401050a1d01060509010e0901060e010e030d020d050706060e0702070906140604 82
    0x14000e41d0ac0b005802e80703144940c090ba40002030100308000500340086c560301d089404580c210000307440314010f002d041c2a10840c0008403107405074489641d40e444010072480740c20500c4200f040070b04114582000700075003a29a0700640f40c083c440010070341a00c8000500c4110341d04955041d030700803c40c4075142d5480390895001c950801d001640c80c5d180301045941800301c00e500460717005540240442410300c043d40700ca801500c0600307013084030207039a0030010880e006500c24654849920000203000c80d02039040340e039008800800692a096406000604543c9040c2910070f540e42600014005030400e01440d8003d0120000e003a00c4417007408040d00714015050060004004002c1030b12042640150080c20400c0d000030410381940d81c4415000f85000d0a80f030202e0300044900c190303a45c40d800c000c52400f06540e030365409420440c0015a040ea9030b64060321044420b55a1000000340700700c000040d0704c0c0a0101d0b9406410385906d000104800c1da400c5402040001e5100c03220080d036956440d08840 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 353594766 1250 353593516 353593573
    0x102090a14030a080a18060903110402090409080d02071506030807030c0303020f03010e0a1d032505030d06080f070b0306010c060b040c030f0c0206040c031b09181103 73
    0x4803074885030800b007814500e1191008190301400b180300154603801010080601300305c28101e404440d03035100102c41f02002c40c4000b414580c400307030301c18805061a030010306441c00d0140000c1214550303030b6141c54407075008072036680b4020360115680d000c1102c00040d0316400b2895a000f0b01125040d0b44414840303100308040201403044040e9084105402078040d19410f01c1c1c60300303001d501c96a4076030101c5403000d01110030855040ca820403031080c01c8903c025404a200c026001181069090808140c60103280d4240041c4214034400c07400c0000c00810007007040c51005440482d809181480891401c0c0c41250b8012180e0003d4406100ea001083c003580d921020900c0c00c14800852030030054000d211002c112034010b400d0188602c441900341c1c002c10702d00b06040400304154003003400f00320b8444800396401403010841c9c0340d040000c1342c1d80c3d24a6003211b0b82e07220041c5e41c80790340da41c40e8641114200404051002c41280140c414030040b19040c020440c070681c041c1c20301c0c2e0448598003021014250190 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 353596016 1250 353594766 353594789
    0x605091206251b111002011401050f01020a0204110a0905010503190c050c0a0309030c1215050603010b0307030302011410060f03050903091509040501080f0d081e15040e0102090a 78
    0x40c080b0030300c688012400745180c4840302d10f890380641411030305503000540807030284450502d44035640b48148030303c00e410050340f01300841c6a400d10301088065141c1e1052281148600e50038840980c0c0c41d480b4045806101c404c41039070ba1030100d03d015140d0845903100e1414050103004021000c0240750180c00407149044000503030410081041c1d8460003240000d02903441a0512001090f400241c0c042c1a2800b442c080c1419656500660032249101440145072030a100b203600c1071a10260449a082003000b000400c82c078843c0070210b840c4c02000da00a40050303455070013071044035580a00d0740360028a0b0510301440c443c240f40c4064485c207140700c410810581e8840004490603024410358080e0140180119207040d149060840b294020420b124030a0746804000240d480000444040340c003500070240080881f00d000030f440c03c900003040c000711150b003141e503005501e2090034400e20400242e19030b5074070314001405110031a0100d0086081e41c0e0700c10042401c483c1c0d5003844c008111504103220 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 353597122 1106 353596016 353596081
    0xb042d05010b0f01090909231b010f08070f02160902090906030f250504050c0403140109030801050f06041a040315020711040f02130605091206 63
    0x80c08110445e20803c10000650009a90680189503201c140400001050540b440030080c44881d41c00880c0500344660003e04842c603442d50a18010305011520728000c1c100443c0034181000b030000451014684603c2001042c0c0342c20542c0b098030000c02d40d0391300e281020390080b200c064801c1011100284103800c00180c06031089968a0043c0340c4202041252041c6a80b68100b02e66556905500440c1a8403103024082c01152640c2c01156102d156050645403c580c01a81c44204d0b418580703024007182e4031280150540f50b00312140200c02000d030700015081e10403135101511181401040c020902028800391045034040e03011140c80813180542c4008070f00c10750000401040c1c0d0400190850708080c1d002e00245222600010300d0240301600030120b007209075001e44001580000c44401c00c0c100856182150302400340205043d013040c7e4030b940810300254601d5081072068002c1d = true := by decide +kernel

theorem cover : BRFrame.Cov 353417266 353597122 := by
  have h0 := BRFrame.cov_init 353417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 353417266 ≤ n) (h2 : n < 353597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
