-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3725
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:30:19.849824+00:00
-- url     : https://prove2.me/submissions/d8cc46e2-9fe5-4b5f-b323-b3d1c4ab5c22

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 669784172 ≤ n < 669964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 669785422 1250 669784172 669784183
    0x90607030f140d14012301181a220f051309060203150103200405060f040308040303080f0f06300102071209081f0f020d050711010b0a030b0f0603 64
    0x2d481490282e126281d2605840c040c02c00101040340000c0305400101d41039080502c500c00d03400c5101c080d81d111603201c0e00190365040c102403d014015244080000700460b035209400768030f40d00c50710156102c0000d076102c40d01800c6041204000b0a0948805106500e5a211040c0444008031111a1790220390035464000b05014034000e08231364000010070480c241074140c110354206082e68100024895111512610ac0301c1e00415400c0f50f2040100300b0883c81c00c84082d1071168650700826140540c0e1759114046588070341d00403004a0b18407410008805031390580680d000540381c034400568a059000200700031502d80952143c040c51100c00310107007128032444042d100280008555904040c01c0078091040441c0120700061480701c0003042c0354a0104062020141050041f0b00101203400c05e42c000e090b603030b070031090501e50a02000d0401c1c801d23400703054000d59468503802294401c42d0a80c078251403444540034001c6503240320820004081a0110750f02120000076812a5228100001d0601 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 669786672 1250 669785422 669785447
    0xe0103022b1203061703071707080f0a030902090105060c070306150e090606120d08071b080d0b0306070903050a080c0f0601061e030e0a030f030227031002090607030f 73
    0x18803455042d00b0680d6096400f8500752400a0280c200c60008008034540d2849020f500074520b01c90f0762049054400c2110140c10814801c907603450410140c8002800690032205409000984404905065041c07600b002400b624050714100e14044010811507581c0170300d0b1100501d002c0e5507502e08580054542c40e5803000e040900da007803032a41050007025584003000c3c2c400d20320840b0f18144401c031500000800e120144103e4403481a1561000c5c1d0071380300c0f20014410b01c40c407035903540007100001e035035000100010012500c00240c03032019481418604400204100c081c80000b20007480402c2c00043d00e40704a80c0d210154030381d24034a4050150400e440c00c00700400c02c0c42000000704580fa00007541d00308000f00030024007800c850003041282a201000128000c6030810b1907010701181c4541c9540c10703c101942001b5140105030503600361014281420001040b00c130801480d2140b0b1709000403031840c00039440550404a11f400014824841c1101c003c051050300031300072840e103000b074100f100710 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 669787922 1250 669786672 669786683
    0xa120e030a050c0607020c011d010306091b0906080c120c07051911040c050412060b0901120309080d0915020c06070b0f280b06090307060302070c0e0103022b 69
    0x441c1070114016100740c111400e01265030013070a0024418034070021b032900642c80140c0d101c410481039030f15407503602c400700e070041e030304260319040d000c1040100c03030064074441c40500a8501107400300600c004c05490203900b21800b00510f0301c0512040c0d003140f60541d80002c0450000244644032100344d41c0d01441880c4000b000ca002340d6a19a14044101201490b03140c0a40074207040588204204030031100d5401962001c6001884188a071007141000100c10500c12500010f0ba10025000605070308800d80c06912070001d408140e00405510101143c01405080c2c001c0c402ca044400d0003a04007960750150169407524900c000c01c000b032080100000d500c002525840d980e02503401d0840b46501c0c01c44401d90001d01d28008240e405000480d51607c0c102e91a031040705201c560303000740f405821440c401590210b0103105103105589c09003c800010991a1001603a800d214a000104405c5550000e011004840d00401c00b50301d130a80c00da040c001c0d030030321034100000c5100690403001000c000c01404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 669789172 1250 669787922 669787927
    0x605090a1703092106190902040e030a0201061a03010512070b21130b04200312030a1415061606150305011121090f030712080a02040b0a120e03 63
    0x10100400700043c200b120007034444512952441800442c095145440e0880c240e0251000075400340000300e04d02c0c0781482c03050011440403215000501503901904070301c6e002d80c00000d80d09d40c0e01602441003200034442c6c2145048103c101d03500c146d5950005104250040c0000000a00804018400d8802078403900c20f8103074036003e020280070102c0e481041002100310242c030204682c00506c103115200e140d4030030124600ca640e0340c0d4992051a00c4034a19055034640702054030083e5030144001005158140a06900c5e446c003440404240c60f0344260400d042003803041440b50210035100030b41c248030403c0e108203540d40301560f10700d4000704415030301400340f03031074000403440b861580e400c441c00b100d004000910070030640300c0844050b0711a5840e00384072004000c1403070000b410f4490703120303922440050980300800c0e0b000120506562000400300d0b00c5d84980ca0080c0c1c105608622015004442d2660850034282800000141c034072a00c40340c1403e218004c8240c0301c0040482d000440d692a043c4140c4e40c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 669790422 1250 669789172 669789209
    0x3040e070e0a05010905130906020d060605030916050612150604090b010305060a060512091513060c1b060218040204060201140a0e0309150f03040c1418010605090a 72
    0x182401407108040303110300300c800000100e66200311500fa060b41e000401e8050284052401e41004000070303501203804030307020310001d0360300600c5215000060074035488450390f0340f0b0510704403400c0c980c3e04800d0222074051200d0a00c4603840d9030041c1c400108454400101d503031205000750f115003148a81d8103520220004011501400030707045684948802c0e2030500403522140c080000700a0140242000140140030300c851340701c910030603542c03c44215800d46114101c0f008120700d150740d04941d1840302000302102441000660310502d502c1000600d0301c04140d40c038004400c1081550024040e20341c50300400e10000c10499008181c0b11020700902c01c5595540c0c0b07940180c081d0a04089000c80f0329100c0d0005406c06441d401444120070504000d18075114031034040100c021241424410012000d0242070001004d540045004a00070004000a54a40f0311000220313071200b04401e00441160000b0540351100051960544219052407a11851544089074003114103601000c1d500003458a8907 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 669791672 1250 669790422 669790427
    0x1a04030509030111070b280c0302070206120108100603120c03020114160311030103020f040c0c1b050a061b29010311150c0c010822120f26040503040e07 67
    0x1000111301c1901c4840c4071f60340d850324000c10000d06400202c4881940100f109070b0300040e42c8102d101172140d081c014100703402600440c0742500444801c90407103031440c0042c49410802c00c480040fa40740800c050090b9800d69884a41d90010301c80d01405204e030410749001014001c0d003201c1440c58403616112168075008a036090040c1e01c107070400b404a860521f040c0368948541c400c580c1600d4010f401103440409c003405010080003541c035a40100158211000005101e03481c40c80c4507108040888e40d50203081070b081003c65041a40040144010298041450002448030300e61903034004820a0008a0800da6440c05140700c0f41c03103182c400c0c000700012080002030144180c0110b016260380c0c5550b0702c401100006403117070504c7e4000941c401c03c0c02100710b42c45640001ea20220314950000001c01b00e81500380f261560100c1240c4018003072220380c251583c840f402c040020211300d0032171961034540000c4403045903213002c61011480a14001024440d0030421a0f00810002902e02101d14060400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 669792922 1250 669791672 669791677
    0xc0705090a0e2e0b1c141603020405060604050f090702070b0a050c1203010e010311010c02041d1b13020714070f170a0b180c121e0303041a04030509030111 68
    0x10f20701031440001c41e904000e040303480341c08020b8a014000c00c3c0c1c0301030101042c5c108103030a2001140d00034109003000d00031200500505120761910307400c145855045204100a2b200010042c5000b0740041c0410012659101090400950700f600c4a026640f5219401c9044c500d07150480c1400b42c400046481115a206005085543c845002d5883e2035100c43c07512900383c40280700e281d421408500041c0041002602801c010840c1410008460701d480e6001c00d058600341c100d003100044c1148400e400308241413200080d020f40401190404c0c210650005110051810840742c0c0d90364080303804000c110320000101c0c000b64031070b411a00b105642c0e000c5580740365414015003140c014128801c5404a1001501c40c5407903a019a0000c041e03a07410607200c07843c4545000d0714009128010054006898907214040d980d4031085c0906241240c403181700b6007810044105800e1944104104400316803099182c0c00000d0340b1803146c1099443c1d9040407a414081c0c10452030f0703d5403034120401186c0c0f02c1c4c0d000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 669794172 1250 669792922 669792973
    0x201062c011401020c01050d1401030305070506070206011a160605040f02121209010e0127210f030f050705010f0f0c050c0a03181a070c08030c0705090a0e 68
    0x4018100d80e8884220303407000d12010440740d000d68403410b4056040d41c00780005c0c0085400c09800050880d03007408800c0e01120003a4020b5010900004407201071060510046920050900080c00103524200d581c101304211341e00c14030506440807a4400141480111302032100c0d81000e8140000e00b4a0b0604480c9020f90b0301c012881000c10b00158070103090003054178852260340d10710341e50a20a20748015100740f0040310100d41040068007046600351402d11003036080928640105085a00300400b01d02181843c02d944011060f000d0010b2000420748122040c040d6414038000002c10b0240a050310140240b00d0028299400d04040700e090404546c031640881245035000d01100000c071200792001e110300364a020854000350f81840c00b090103940c10403c80c014070301c81001a642d860300582c0c0e04074640401e44401002c0010300c641442480d58001d000343c103400000d1441d048003061001e94508940c410ba501a05009001a41045d4103901c2208180020026924801c0c04c03840009001e140300302 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 669795422 1250 669794172 669794249
    0x5030a0809150a0b06160b041412031f0f0902070302070509010806070c05030f0c0c03101b0c1b03060f1a030703080d15030323130302040c020106 64
    0x1001070780101c03002520282c000035054628030180c95240044000d0042c0c80c41d031a8011508210710381e800f04840c00d500d03201502030b01007041582410301d44010703603408106a00886510404000c2510f1142c0360807a50070046000014201c604200c0507107a2003180c0e64070a41030004011800208028150020591148a070f402d80c0c0c7c005403504104880444280588103e5034060070004100b82e0262545013070300c9000300201ca0800c81a060401c040d03904c800c47c3c18900360000c880b0700000d8181000411091003110400340700c443c03000007082c840000c94164080820501e4403c40050004072440c0341603c08040c0c60035030300c0b5600d03400c01e2005480900c0b4111403c0b031030500c071314400c80724890001115480060280c0f110301d00c1c54591001e20340011030707400850b5594140201c110011700c008031004500c02d0b21808240310207000c442c544034068440304858401c2c03c010400e41508803400d40002c0d641d0407034001524268008003240144002c0d00301c00388804401d21000f40c42007058805140c51035090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 669796672 1250 669795422 669795437
    0xb0906060a0302131e030c06090f090b030703140c0109080c01230f0a0302031f05011d01120f0c080a05010807151101050a151a030c1e031312020c0f040507020106090203010305030a 79
    0x2218201c81418562041414140ac81e04d000e1200c2c0840d43c020050042c001000c40c1c4a0f02c0d01c0f625180d1204006004000701544401da42030499600090308800a000200141020a440000107481010560030000f030001c4010110310b05005464140c0f43c00420788641c0b2519403880c50301c00b4009500507a00940e0080c5021580b00d50309168205010035209d06a40f00e0403081144900440b914200c02c12080c180404501d100300c0d10b4138140b1a150038400c5003070303000c1082c2803114405442d030103025001403040350515005006402e0f001a140085aa0a003110382e43c9101001044a40000564440c042d55003000e01388481c00c0b006400c03c0c0601d150307101144c28000e41d2181d008541840701020403030304003010700010b80f4418500c400740900511440c410f04800c030346090f030841b003644120744054905810060b040300f404007204111004140078001027400d0b01c2d40381c00140307000100041e101c0c0b085031900001800b06200307401a40040c03251840c15500e950b12842c0c050703100d80001c0300b00310000d44103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 669797922 1250 669796672 669796679
    0x1005040b030a12051b0a0c140904050a0305030a110315010e060c060f090a0203060a0501030303060e07050d0f06150206041403040f060507052a040b0906060a0302131e030c 75
    0x80b488000070756009084010706400d40034251402e4014041034100d00560b02c040202d0550248100c0d8142ea21550700740320814100384070401c0102480141c68098184ca00c00c100018100040050304150107040c5152291740c0c00a030b00010708000300030300c02040340120620040144550350359221800036200d1212171103183c0144405401000440a902e42c024004205103900035420303141c001e8a9481a03d49045076030b00030a241010550750410340558410040086c541d040c40340318042c200090408615040810004001d80034010490100a03501c9400c1d407445c80c0e0580c0460010100702c250301000f050b102d00080d4840c9022641580c4205200720180d21b031070004000c64007502d6a168003035a44504050702207615402c900d030101c9462045545803480d07201d0a400342d89404c0103014410070076201940500c400c0e15203100009000780c001340140085c940d194010358040e800e06140040e1240e000070581d40c40c54000b644036403c1c0d0f48900c004101c500100d07200c1d40382640d02900750b040f2003a64 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 669799172 1250 669797922 669797929
    0x105061201020a0e150405060a05180609150d060305060108031b0f07180f2a020a080901120b09160216030203060a02030702010e010e0c0321030c0c0a0b1005040b 71
    0x3c2c24042c04006481c46400340b14038034080b4200d140181c030006106060035102c4001c101d1720f50000684002290010501e4840e8910005d01c0038120002500d10f10300f8010800c020984201c0e404413521114600410a282601d030b940d80448010350300401180c50559465100680b240e200300e103080d40413004a4079204000c0c20001d19141c0c0702d0f44030070040403032619141ca0140c650712041c000c4000a6201d04c5081401220342c0140c4001040c22504001c10844442c40001441c415006410543d0400031003040811400c40c1503d21250082c00d01c0c200301c1000149080080c00800201a1711020300424462400c10140744c4c2c0840c1c40440c4c00300d9001d010900010f204031011880000d606500c24000114005a01d0b0061a00400f950002090240c0c2c0b90301c009080d15030a4051035041c1e4800003148080b4541040046002d481064085a11100068500c1d406101c001d00781485258005164080c160081240b00b00843e00b28045603d02e0034001c01c59140a01c19200da903200758103110032403c10b4034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 669800422 1250 669799172 669799177
    0xe040b010302040e0408030615042319170f03030a090b102102040212040b09120a08160e0603070306050a1d0412023f0408031204080417010506120102 66
    0x1601501c952039a40d49661b1802d4213a807000300100e801071404a40c950788121001d000e00041c0102047c008a40000200d00c0314200c0d0013500c034a0f100c0c02264405211005c00c8002d01004d0340c181c0c0c0800c44164201e042511b181048851056030b15110003c10000802c0c0c1795409241d5943c40b8800f03480781074071909112075030716109004004001e40d60100840c5e51901d14040c20100d03d04c00b400150521201c080032000c0c0080490f42661a20f031070368208900280144244610100c1000f03445040030a40706c0c00414420b00100492444600015650f026034010a603100b0884801021030362349140002c0300501a00092140c180140c4000c20081800f41089800148064890039807125a40d40ca48840b000e844a840303150041d80591080d44c403c0c109424150082c944001d0180c0500d40312401c0c8006082004180018904d0001e01003800100000700031524410a09240350740d1540341da06007460b03030788915402098251a0070705505504001034129030f01c00c0d85d040b20a8851101d1a2104500340e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 669801672 1250 669800422 669800429
    0x5130b010207090b040b0a06030b012706050d060e13061a0d200306070c050f0c030607211b02010b040b0109120c03170705070b12010b091f0e040b01030204 68
    0x1070b00004802e009034a956404180005002400800c40380b03914030109007100b450341c001c000042e881d03810038070465070810f001d401c484a494220303640e0700c00e4001c4559030550880c0154010003900040d135403420607158014801804080d00480746900303110450045e16000c80004955150800041400c030b00d0700740c024004c180030042e01400c8050001d664410307821060980c0d10441a00148030b02c03200b0f40342004002c1c483c0d4244e031211a514040c0d03041451a140c402c980c0c0d50b1056220001122040e03e012400681011560411054682c030081079484010010420420300b81e1914000d003e11815000010303003581381640081100941e0341c4240801d440200c0d045078089000360001f00b00e202040d407403120f0b02c0c40c041c40802c14101c1e100e070b95003028000001e001081c094804114481481014401034000340740f482c120343d190194201800e41c41c40014422803503010004200c0c0034040e1280e035240700e83c0754481c07098150100c841440203000072052600260050745041c080100300d50091003101c040c2c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 669802922 1250 669801672 669801677
    0x90d020a0b0f04390506041d1e0f06040c030e060606160b040b0a15150c02010c0803070809060601030603051b0103061701060e0a110a0c11030d030605130b01 69
    0x15a40c4072030b106407150016008494240d982c80b41c0c0102c00d00041c025209030400344003015121822030313400c8010160b503900102c1c420381d0704000c104400c07405520003010007001c45804180c0f0b903680c2ca9a80c0310130544000d0300e01c40000014104065018100111031050100b04e80030866036840010403400c03a0085401d08000b07a05c0300001c10340303034613140b00500041c2d498030346585d144131116a10780b1200e62090340d0841d10402c0180610555541c90300400211404680c440c80b4007034504441c125409444c60041c1c0244a0919a80e1080d64859007060b0441504890095036a04008800a0050754111012401401040b002c07481546c400d01072001280d0b08103005111160074414039004058140b1580c40c14160784000018203500c5c1c5c6030904411070404070001540e240b0b0001d04500d00540100750758007440c076050303002c0307518900001550b18000e500d280440705506c440c903000b0342c1d004503000c88540c11310840c00d03940c0310b850f0300d078000380151403050342c0c810000000c055803101600e940b601558007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 669804172 1250 669802922 669802943
    0xc0d080906040b2a0304062304082203080d0b0f0102070b030c040905091f06030206120403020a02280f05030d0807020a02040606110607410d05090d020a 67
    0x41018141d80a801840c0c4281910794079418001c0040c0b8048403130703e5480b66480c00300800051012510900300c04843d001e4864014050100c0344109040c00104000e20405002c81d812022802c000c0350401100707051a1241c13512a00c07410164030641101145522a82c2845917048090404041485030404180c00034407005062540d102181e0f04010800c0c4031303e90003400001090328190044030b000e440014064865400d030101c03455880e1942c0c00c1d06d000081e04203181000180c46040444203c840701c020790400d41e440d00c1c941207082002200b4040e42c42041448140b0040107000c0218021004101c0031350000360350303080c0c038060300803252280607450740000c600340b1000303030207090001c0d80801d81d841504d02c12034070f42d0300141c110b032a940c12040000720700002d4181000d82c00c100c1150410300034244004d1a20300200300302e06505401c0858020120b2425240440c107000640102550307401010094580b10406a00d0009203003c44014410348941c8088030740080c004140542c40503040340040c10f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 669805422 1250 669804172 669804181
    0x140f09010b0f0402090414042909030d0c020309030703150e0105060904020603090a0b160e1c03032403150c110c0d0f05030d05012d1503020f0a050c0d080906 69
    0xf00a401002d0410380190300c405031129021b410307098981c400ea00c50800d229001403c0d40240b5003241e145403801c1c6180c0c0a80301808030b45c150000030740d00e2107040300b00040340410014804a0460146031007054051181e82800b20410000078864084440d55280400c8181c900c541000c0c02c0e1071050780d441390000921000700700581841c1008503481030103801100c440c48690b0ba03500f0410780313003140c113280242c8074145410551644100f124680c0070b01101d0007421800710003040380081034040001001d141e07803400100b41c041c07144156901030340340d104e0071113044a0346c07401d104032842e041008107030045280c2070301c444d0b40d24082c99401d0203541c086c0c001020241d502c80b040c4201684c03501e005a403081e01f040c50000010b0001c0005200400303026401181552506420401d003005100c020341d601d61448100314450024444c10b0030894120301c048140030680540140d000340b01e2940c601040d00c200241d98400d454000e80140f076802c948000301c0310005040c000450f182e15050321403180c075421180106 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 669806672 1250 669805422 669805429
    0x906030c0e0913021c050a02010801050915130b060c0307060e06010e012c07170114011205060a091817120103020d05120c07181b0f02030409140f09010b0f 68
    0x1039103252010744071080411509514511445c031148089565074040c0d05a1421075038421075140c01408182ea003210b171410b2924680e011040c611030070034060b0b039010344d00700c4c00c0b410b082c3c00010f20034402a015640d18000040c01c280c1380e07844107100707a5006080040c20044071100040e4241203070800e00b2019056420001c1c0d0b0701f110030090b060002d039450000c40b10301c4248149458140a00840d882c0c2c0050803a9061225481100590150b4014104800780c1c0c21640d030040c04454030108004000201d682d664400075465a215401c0002e41d10310348120070381c0003e1100c000308401409041c0ca04186290300d900c0c0d801c581b0a01c21901495692a401000107050602136080807511901c1622003200114511441c1030304010580b0388070381d00142c0d04110b8140a21a202c0d10410480e6044c095040758000b0803004000c40402d500c10004210000c0f06080e10074810344001e171030130b482c05000540c4035039040c01c81e0310401e0752649428030500c004a6018030052103600201d0102921006e000e1180b01c042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 669807922 1250 669806672 669806701
    0x31d0904080a2c0a150509061c061202041b05092e0306031505010303050a030e03090904050705041a030c01080c0d0603030518180a0221010b190f021f060801020a0906030c0e09 77
    0x4603482d022400001185010050041100bd8280940240403a001c0d5004010503545841c1d07514145100b141504030342d0980c4041113490290058031100407000045c44841500d1074265482c010900b13801d001040315030f0745a04840d080324000e45000100144201c9407801b00c40080c44000d0200d079040203141e10647c02a04841d21100c000c20030340f810b040c503020100b4100300080382c00b200c0d188c1001700d0a00c034518292158444c041a00e54190900c40307a500d0100c0e40e230343c004500c1c82e41404118400503d01d030203058115001e6840d200c00c240200c0341d4034175001e4120341010708104680d0a84082c076443c28108107591a081c4000f4140c215070036207489007448000e6200203540c10314100c0d40d02014141d4040d54dc140b0f070003440c50b2502265142c00700300e006400c0343d242180000400c04043c078134448166000400034490110210402c18840300c0f58110801845650b008030b00d1940081901034800790042d9000c01140e010ba14203000d124201d80085496070b2482c0b9205070b1100b090400710300340f803132000d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 669809172 1250 669807922 669807937
    0x20f0f0a0b1009021303021002030f0f07060b03100606080c090d030f03020f0a0206190212041416140906091b092704031d0904080a2c0a15050906 64
    0x5502c0c0703402c0d440f040d03101c00380c1e80045403104031000141010021800c04004156070b0700494405541030441115080e4483c4c414180032214120012038002c040c80002d41c440007840d0001401c4032041e203c1107803040040d100034803c48001c210390307000040d40c0b984280216285c1c500c0c0100100010340c5243d6056610401300c082200405a01f40030401d403500300741008001d0044285c000380101e10b81140c0300111040114024010b00e40184001c3d10314801c00d2000f07581080d413145d40754421084006003d483d02c0d150714109655100c88040010303031624035108005100c902564a000e441d81c03034170103200350600181c4100108466031004107040301e86050103050030001c010140c01008440101040380300801e140f0704000c0c5030000303040c4001c140d007003083c2d03030b61600d0781560001480d1079042c0003030025130000384050582e000000703204c40c1603442030910081c003610006880310002d81c0e6411030070720b0f5a030030031599000304104800410005110400b01c1c3c1c602d68203680d030300d103000801e10611210307412200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 669810422 1250 669809172 669809191
    0x702010c0f05010b030f070e0901110a260c030609070201050f1308040b031008070f08070b0a030207060606090911090d1211010e01050601030f090506010303031e060e07020f0f0a0b 79
    0x50b000c000b1541d0034020a00b41240c0035008021082c20a400c4032080031001d44900380c28be241a6514040b40d101c1c00c15111011030a0401c0b1040000311816442000c9100e0b080090840f040000c02c54124040005540541400e940420241e5030703001003039080341c800b43c1d51000000c490400042c0c0f1300050110700c55610f0b2044585505281c0d0f113040d445107940081d581c00c000204074080601068108004480c001e180111103500d20600d40100541c40c2c00c0036014003050383c000004c401d40054069011105a039034880320170000d242d82c42600811000780e0780100c0c4406410000c0c04850700036040e0540340409c030028001e06110031141e407a00220340509101c41c040c4801d402501c05d03c0b05083c4182c034404030381c81d4004034a40c51304800040840d000c0341113030340d855458801c401c80450000a260760540754181000211429003500f54001c0082c5084010099420814042829140c43e411140140d8030f40c2c0031100c040450b81c44044d03d0305014030240d10540e100b40949804143c400c420541c00400a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 669811672 1250 669810422 669810431
    0xd17160c1e0212060403080c12070302030711030c160b04030c0509090c18090d03060b090d1e08070b060a051513120305070c0e01081b03030d14010e0c0702010c0f0501 73
    0x42d0b0104581181040c09008543c000c9002c01003819040b04051ba813060314568114589451a031070342040443c0035000700c08041d03001c800512141d015140b090509071503030084036200e05c160304c25160340e4040f14039101ca500070144030001f000004813080d60107aaa101a520a000d400d100c144502004001d240706254031580d1b100810a454214181d03420850300d00030b08005140c89038804d443c1c030385040a01802c040c500201007000d00e41c1c45041c0c43c030303101c02181e039800c003007550b030400c40919608055003480800140881c0310400c034081009140303035842001120120b0784d80c00708000301681d103403003000e800a00400c1010740042000c030040a0550800b2079020146444d10030140c4a0014403c088012070710014418007488803510b1040b00904410030514417640c14180348907120910391107240e03601c0c030300020650603d0b50305200369200c0081d05c02d82005000c400c60302880b0701020a204200d00740c0b100002080348649803c044505940d01a101c16503c11308523907490340d18007102401a110b039582e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 669812922 1250 669811672 669811733
    0x4050618040e0d08071d0405070c12020706120b06041a04080102040f261b01031e0603021302070305270a090f1802030c010c080c0d17160c 61
    0x110310420000584103402840343c403c8035440500940c00140070310084c404c04036140c0909244d244481460f408040d2000b00710341c2c44c1d401c1c0036076100c0b510140080c0720804001ca0030b2040d41d030018007002120150f81d1203107405001b1504d00c200b1504200409038002004201c00d200011425070181e11030420354140d0351a01c2e0380c500d02d80d0308a0b0059004200780002c00c00c41044403294183c0c0c00c031544628990381000a200c003010040d074850744d006c031041500d0b1504c20880b41e580e0280e071200e0310020100d1002c0c00e0398a0701031340d518006d0219000891290351800071040c0000014802c1e0342d1659032540f14546028a14610610300e20f01d000718624400034101c00400071034036803001d104000c21b034044020070314035043d02d446001d44d0030b500407490032040303034101d0140503a40000c0c982644040c282402c5d81c12b9001401e20407603610900d42d0308062440307002c200420341c5a114550001590b02000d00d502251036541c4180f01000c00a1000720002e00410014008a103d04001050419a07071820000b607004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 669814172 1250 669812922 669812929
    0xc0408030a050327060f060f041a101404062d0314011401050915070b0708061302090f0135041707121101063201020105090304050618 59
    0x300c240740d0000340002c010b00407014104103071402070b9070240d050130741d00240242d015070351000d00402c3e030044402514041041c80d16030100a901c03801001d04280080c0e104807203014201136040c1c00301400352060380b14410100d84142c0d030600035210a1000c40307140c0744c41d100c41180c00b19007113403c0040540710500040c2d00c0780e00f0b00320307114408506170304d000c260f05c1c800009a84d03074100143d020200c100325601141d40b180e03034031004403002d604045440b40382680c5150100c2d03c89006001004100451550620803519041521a4450441101c00427008a07584090704140d010b001009908941008540f0200e907008070031807240e0903000381020b45400711900c5140c1d22240d900200340c04580f48942444180200e9002d140030540d983d100b558542140b55550240031f004c80b640c82c50800c0b42c0d9070109503d05200b9005240104840e50160302d030140003080340c110200c8014600100494400959019035006004051060b2071000c00303141050325010602c9002d074084030340500c07100c250741e4001d182a034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 669815422 1250 669814172 669814177
    0xf17071403032a010509030c0705130b04141f0f0314011b0f090503031e0f09210d0201111605030f0d0204031202010216140a0f0b06010e190e0c040803 66
    0x5043d89901e280e640c20012a86086407006041801c00d40c104001d4040e2a190010f4090f080310320503280324200a88604070403009012036071409912600300244003480f103066510540c020703251031040c0004818a0320340e0101101440c45080ca030806a0001000455034907184071075000318403000400c02c217000c4100a80005c40c0740443c1c0002c40c0318869215903541d4010300f90409040c080d4011f61034a21098002e00f0300d01810310615292030000148120000a440241c40c0c003130602900421030050405544107180144c192165198400d03980c00d01c038010310500030440c11980c0400017a1a0503c40c1c2c51668500d416110281c400c0d00c4100030b100c100301c90b010010034560110580050f01c4504520300007410301c02a040007801c581c01448211a0701d07111102e56002c560780801c00101000c4031070005400c112036040040c00081043d40075605000180004900c2410260b179040000180c91007000030207040e00003480c5150032100e50030710004a00b00d00458000040112075400c0071780d00c4071010700c0c40c0e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 669816672 1250 669815422 669815467
    0x402010215090d0e04020304050c0409050a17040e060f0a0612020c0a0803040b010f1809020a03020301091506211211030d0e010b04050712050402040f11040f1707140303 74
    0x10743c003240110b04002c0d4402e800490380f00c0101d074154130794246901c42561319409100c40510441d910002801001010451143c01030b038040c54070745c10381008448a00d0160420300c500c0c03661805041c0028a40c1c07504c1c1c0141110300b0300040440c1095810400c0441c1c244001c03d60040700c1981c00c000c0007020060400158504a114100300e0b59245410300d040700c80000c040e400441c4c1e5219050013805007550407007a80701140f404500000703082555000003202004a6440650554a4802e082c0c1c180070b00703082c03991603450741c02c6c40502c400382e543c600d0204940c0b450760900403680820301c034050000b80580c1d4141c40074000c0c1c0c42e1070064150100c1c0c640c0e00790b81c00b10002c00d01039aa184e00341c604108084c05000300200302120104010300d00502c0c0a001104841c100701e826035541c100290455469a000b035880c2c05000a04220a024182040420b076000b400b80c106400c26001e00094106502852070010548000141150760b290003c1101240310446040b941400300b44221075070b48000307074140c0b402c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 669817922 1250 669816672 669816691
    0x1104060b12090d03150614040f090504020a14060906030901020c0715030c09030c05092502030a110304050a03150b060703050304060b03070b03010b0a0306050d030810090203040b0403080402010215 86
    0x2410b00300d140394648000b6400c0d075000d1605003954600c0344645500450300725982410401102c02ca03060300c549140c420764200507911207981602286440140e400300e0303c1244203031078841c4c1c015200c00046121505107044283e1121041229042e42d042000140d03130481d1034800050304264410365660f0411905422281c258104d06200000b950703418003800c06400b00c141050130049045481d8507c400700c00f4054503002c1e003d0080807030b07030040740d000f0b9103002141c00b02c3d40078000c1c60007c0c5009440e03500c829000e100040e00d091402811507008000c8030201c5500a00e0307910020701d940d6411441800d0220b13150566940c0e07081980d182d450319001000130512981d525a03880c5005c0c41c0c11310441e150f100c200d034020780c440141400781e00b03020350440341501d1000450b16199132404001b100a0030702a003205410030400341071001095004282305010f0141c58842d20031060301d591501e000c0b8001200c0c0509401e00000109002c80d001e240c16a41243c01071043da4884c1e1382e1005251100b40701924800d84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 669819172 1250 669817922 669817957
    0x204050a05061f05070602071a040302030a090e10090b06071b03020418020d0b060d150212090a0305070b1e0f0f061509040509160b09040614030a1104060b 68
    0x551820040b4821021000075807030500e42d40343c1000a003103004844005201640c005040414001e02c06121000c500c20304500842074513091400a403690001c2e0b01100201d00501c001043c2252084403041c0b084004803008101d01d0710303200b4018098005a459550040401c01600740450f008010b010340d1506401d0341c00e1490b0380340d80b0503c400ca5112460a1040c6a80180d1880c0142d8489040d01d1070240c00c090b200100782c031440001141d00c564141c3c010300b607415405005a0340c54082d0041e10421040d01c02d04035055494052490700c2d48204c4400900003001084000001244c400385150454401c09a0300c0c0c640500c0048520916000c1c0c8426840550250070070203504005c0b000b0035407100e0103454000e078038041c050405800b070084800d010322468541c800580301400030080c98044c0340001c1100b12041da6602003d10f01d43c1e02860003a80a241082c5012440d8500f20050080608002d0000c2411445545610f2052040075004991068035602e000460f03040550181107200c904449503203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 669820422 1250 669819172 669819181
    0x70609060917060612030c010f0506190b0a180e070201020714031305130b06120103060c0e09040308070c140d0305182a130c020607032009010c0204050a05 68
    0x6100101542c4444626140b440700a070380c1c09008208160031180c1560102c00c03100003001914158007510070480a80d6182031110080401d10350482d40c0a944d0943e5040209140386407261024400ca000d1104a48420000f00c11420301c21910b007078264100422600806455040c0c40c803600700151610300060f9004103800d820700001c80c0034101c210340700000640c900304c00038059030001780c600e1140301d21a0700001c841d6a080c6100d80c124801a107002441d99640e10303510480b04016040031301041c1e030380f43c1c581400540d100b4010360f070140c00d1071002001041595503940c0c0450780c960008000c07170100f05100e4800b1002903031b505e0b800352050702c1900c0034006020b90414001e003119030040144140c80180d107803080b0134010200d101200b00002ca1041d4009204541c070415280c4c4a06040c80d1704241c84040301103d0761a01c0e0701461402da0140d007a01d54036203d03810200c05039040e4412000d0071529900094000c0404207008040701401070401c07440314403468000030129102201c08100540c0c5910401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 669821672 1250 669820422 669820427
    0xc060f05072c012001090803010e0f0703110f160f0506090c0a0b160503040f0305010606120509060f100803030408030f07050408070302060306060d0513050c0103020901020c101107060906 82
    0x2106200607010540100c4510340c000204001c01d01c191150f0b8400130100410000c00c02900240041030300864210360306c1d41d459941901d00c002c21141201100038120100740303103038400e00640311205417022043e8240042003494103201e40c442d0020183c2822a5104907000903001052136000f94012006044541341c181610750510b818052524400c1028070400d009440c5da24040d1400d00e0714280c001c425820042c64442c0c55481141c00c02e032800058484000300b048015007001003604d0701c43d80c0d20010400710344c030001c09860b81a600c54015410500024055003080d00c40d82d5880034081c0c0302046070b2503076026100d046034415282074031043e10000400c5001d00700c10701c19942000c150b00d40301d031400d403910740160340f103103460300000388612030000109200f40d40300e0f4240c948505000504108038203003072490107102c1c9c10714001250075016010b48010690700a02c20303924580d1041c0c016040d00da03500b00c00c00c203c01c8151441d0300709001c9941d2144072000d10401c8007a005c3c22294507091305850402801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 669822922 1250 669821672 669821717
    0x703021c090e060f13091e03090b0c01151e0b07031205060f060c1b0a030b07030e011b030207060f2f070c0e07080604050c0d180b1009110711010c060f0507 68
    0x44540b84647c801c000c00001d900a51042c200d071012210380b0385540c6402640c0e07014200250308c15004180c020b0000c10782509106480009080400b004e1601d030703640b00030304503c500a41c940980402c41010f60038140b2800b90700b0550340440010040d5065000d003c0020720160000125030880c0d512010804044050104000c0107094003182d5624685243d030356078411b130210080003c0c2c10503844d030784880000542500401042d07000c100c10381002c8900010010001d4000c44404d40708a81000c4a001c91200c581c0714a14100e039001412026040700c02428941c840340054524140d14820098000450340300e024080c05400102e00244c503500303001c01c008001d0607028120504c111700e80001e02041740d46480031541c1d011811030002c5048926803404600300a0b01c0c19001e46054040801c1003503040810981e642a00d00c00e030401c03c0100c0040e507603441107000d2003000a007040320042c55500c6940c001c80c4036101c05840380c9000304400000310b9116003543c605070b860b4004540790501c0d00206003440c041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 669824172 1250 669822922 669822953
    0x40b09071d12030307111204030f0302100c0e04090816120f05030f01060e12060106050a0f210b060c190b0601020102090f12010609110703021c090e060f1309 69
    0x34000c07001c105050b03005441e4072000d0712603803c3c0220b103031000f40307100402c0c02102c000341a10302c07003da1a1a560f09107a21501d800d400214014054411300c0c2c0030302d1201d03101d40310048030360f81c0d40e5880101420342880003d010403070042e110f40030180111049440503a594690840c0729071031048502c001034202400c4c3d40044500007090110038001c00c0020380f01c3d112202d045940074940340380076200c0310000c1060081c1c8071610340518055030001081040e080302c02050701101c01e50f9809501c0c285814203c0740e1400903c400034491940840c082580f0142c2d4002022024004150030f00e00400e18204a1a101511113a800c848402d14045001e205200c1c01483d804502030000398901701a07800012240c207403003d1507510a0f110700c2c0081304119800d6001d038020f8403550600304041d03255441403d8440e00140802c030014400d007400c200380d8844d42c014031101d040ea180c480d441c4103410040f41c0761800c00028010358005c54205030707689040e9a4000c03190f161900a100010701c400781c5044c011f130055207100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 669825422 1250 669824172 669824179
    0x60b0603010e130c09020c01090c06020f1e010e07080f1605130507020c0402070b0907060c05030a03050a090602031905011406250f150608210702040b09071d 69
    0x4101a0729070401107a4440f0111080d501c3c803800c185801c00c02c2e94580d801403180f080c4003091521618070154803041c540707405201c851542035500c00c82243c0e15500f040c0521400d402c22a1040380b840c4450002d40c0d1134500890005ca01d807150091582d1604c107241e84140081d9103c1c103009003420005002046021100b492003105d041e0a15002c19128101d181d84040d0342d603030750000176000620030f10100d098000010400e540c2c42400342031410401005031445550b6001d0008002410b030701030104580c540380d01038003450030582e00e001c1c00d400030b000c01400d00240c1c03a01d5a190200148a6100075407058942184140f59290300d0310740401210340c141c0100b2042c0702e200d105410141d445006490300c2d182c000e290b00c0780b1039881104854000b072810200528031034081c8003000821445010118035600c45010401400ea5901d8030559101150b240703010702401414000b0001921000081c000310740041d10200720380442c00c0200d038860904855210004550001400c4001c0800c0220300044001700d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 669826672 1250 669825422 669825427
    0x1101020303010f030b072106090501090b0a150507050d050d0e0c0609130b0312030f0906041a0703020712020c0f1509091b0414130513170c060103050a060b06 69
    0x140d1864400f5550002034400c0d01e818000543d09480b1340c46c8441d20102c001e4015880f4062000828080d1015000c0c001f0400d003071130004524055584203686180000500001c0c02625205000700e602c0b01480348c01040000401505011940420031215010810380d241c0d07075501c6030103510104549920132a9003850b00280d0b18940f482ea143d0050368a42003086425011102d0304106e0a00288400641e4a03014000d4030b185900c03412109000e98800e51540000402135584d030480303192500001c440050045501041619441d0300714140258081014280185011082c0d110707401e45d03500340011500140e0080d0842c88150810000250b111007080e55140d03034081c1c0c4060041064001d0001045c02080b41400161950301d003000e5002120824103c0d255644d5252080c0424444803c02c6c41c5d0301030800f1071048000301034076202d0a032103000441d28601c6603070300a50300c035500b166070319040340c09040c0b090000310b055820901c88140210b00c0b6800030220309482d46000000c1c1e40051580510800c800e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 669827922 1250 669826672 669826679
    0xc0501020a0216050d0312110918090d080910050a02121005010915140903010603080301090203041112061f091e0f060b07030f090902030c0c101803120e0f0a110102030301 75
    0x440b018058080084008c074520081180706d2409001c2e100040340e0060a07109450040c9510a041d18050600002602d240219000064640103c02e50382307028542c0c42042100410704490303100c1600520804800352411005401e981001c10040e00d03011051286804100120740e08100203400230700e0081e102a59074a039a500c09040c280c0100b4540d6400c0c00c1c00030301d0042d0b6590079400352001d035a000026540301e50715041014000d40080b2021244140c1d500080c0e40d0342c2c60107601c281040c2c000300004000c55a01d10b4800650300c034241066101000b2802070208400b0348a00a40d8003111407904c640b03000e8084030000074280d07666000e18511151424100303104c451004021220180c0c0c02d401c024914014005007241e51070202d0303000d1649148044203000300e03c806c441c024541c08248004803020300344a104942c08030390140400c101c80260146022001030b008241c10502002002000540007000a1020b03040c804444001440b503081011707201d04004101d0650300001200384002c5040d50705 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 669829172 1250 669827922 669827927
    0x71e060507020f0622020604090e0304080c03070b030408070c05060c0a03030f060812030910060b1c050105010e0d02040603060c020105060306240d2f01110a081204030c0501020a0216050d03 83
    0x8260301c43c58400c2483c10700f005d080d52107080c1283d0003811083ea08000c45000380d0045501d940080c040c510031402986000d000c0e915000450109031600d0b00c21003440c6403a0350355540c107a40c1c41403600b101d5540b071010f40021603a9501026010003009040a03052001040c80d000f030440d21248071005400d86049400c3c0300584001501070403c0c00309140040d503a4540c820424034001f601d43d244041c840c02c01d8400304690f20140082d2222610000182090b09944120f44098940034003030781f40010a1420011001d240100c406980c690016100003041da4503078581d2015201d41e102d00c400540c1d129024420340d414100240c5a1002c082c80402e008041e00320661031001c10f010034000e10900c040300c041c0c42841741d070110181502074409441040303413042e242c0c0300b443d80c1400b40d851070128482c03201000a020000c80c100c505641c0c0045c1203403403e0b1190190459182c03002d0010b404100d0346040000001c3d400340b00800d0320401035001440012510000c56028000301e0700301c070f405018a1880900000d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 669830422 1250 669829172 669829201
    0x70f111e0f030a0c0c0509090d03050a02040506120402011b15090c05091008010608010c09050d03230c01050c07020d03080a1b030608010f0504020a0308071e060507020f06 75
    0x1010840322409040002848900d0407080c102000c0300c0d4003001505402107604040c0d41105248110903046080ea907500401c59460011228462582c00410769400d101e0702c03e80c403641c1c0c0061040401800c2c01d444201049894002c1d40703120105d0104101440199a0052450b0440c00364000d00e000c0c0d10300b070565840c941d031005d03041c0c10b0301d0343c0da21426190b080282078120503000c1c2401030148402e03441d000010b0500c00c85548100a1554604607010912030010b00030060800c081c0d4440102144c03421051201031072140700182d040180000c15800424082e0f402031a080300c1e203548003900c491010410700e003103500140c10707460a900200103a50058030380b1408075042c90f415040250a40d600c4a6065002c0c0100c074419800c02c0c50f1060440c4149501a445503040d502444001c10000030035100000440740c040e0b802070b6100078074410400000d98410000d003180c0388035503c254481400340c1e03603555945210a40449002d0303118420002156810000718042c1e42d006001043c40c0c3c100b0070462105003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 669831672 1250 669830422 669830443
    0x5060f01090c2c0409081209010204050a0b07060e160f090c0806010c0c0306050c0705190b0402060315150a08100e01090e0f030307020106031b270e0d020105070f11 72
    0x140c50703e0903210803000c9030507000070051402410500c400001c525150904d513000d8100211181000d8000c2034020f041482514140d80f0b000e440d07050240d040403170301d0540d90481b1808880d007a07240c1d40340221850007801142c074001c8000c154980c08500701b2110b200201656003208100074a0000040741d0a075014502c160032500038202150f00101d942014031012075a90805454103042a0502031400071600c02845140e0044040e60900700c1c600901744030400d4000740c040e207a84254008107025203130400003907800001c4842801c4404580c030000c00c07103814422103294180030012498200e0b054100c05180c0d4403243c0d041044510381d0030040c201001d904103000340510940d03512144420003a040021b0300302c1025440c01c90b174491a06020081c082c00c01d80c0030481d07803101c043c040d0085003038010506505542c030010008030054000f010302d0150340d102c01250800e117038031039000d442c00040a01240c00e4068031940081168900001d014286841c4220308000b04250f000d8400d1101c0804550105003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 669832922 1250 669831672 669831707
    0x3240601120b030a03020606040f02030108060106080702100501120b0f06211212250e04050a2a0216120803090703020a080102040e010e0906070c05031605060f01090c 73
    0x20404407840080c010101e036541c4079014130491905105260300001d03514070810048605101c44400e20f654001640828422801c19a0120006000c4e460240b15800d5100c080c41c8101c070240c002c1d00c41200240c0340c0a034481404146a062880d00f44145a0501c40d840056920b100c607aa0804030041298611340c404000501e00703850764903200802050250103c25550740c0328860719201184c11941010324180c50400704100075480150035040c2c07a800b0603c1e110007a44075001440420400d100140c540180399580d065a1140c12020340c000b50314250807030303554004401d042101c04c0c0001070b1500295041e0b03284208040c03441003140951002515940d9580602c000d5140d8607070150343c0c2c3c80c04405410003503000302080d00c0030ae2001d0055001d0011207100c49500300c420399070fa42003660142c505880c440c0c0245c000200003251640540d1903010f08900c40c90849140c40407800e04107040300121982198143c2102c0c1c1489070300080c04801a0140903980d030100a2400304075400740c51a81c82411003a41c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 669834172 1250 669832922 669832937
    0x16050c04090b1f26010b0d050615060f0c010207020f0103150b130f03150b040b06090f010c02040c030e0c0306060a2306040e0103050613050d0c021c0303050603240601 73
    0x803d01600c140c1000030007260149016200c4051100d8025003071480c82c00d43d040d0b103089808a118030300029117162064205000d0320003a1110076005043d05070391242c283d000380c801c100075401c21000e9401445080422400161214a2441005480940600664100740c1042c08070b02541c1407a10510f07049a050f803a145a44076003d116008070950b19900000c45000500000802d0204406000107403001d90341c010000c0e0201c0004002c21682c07405841c0340c0151091103480f0090924000e05503c2c120141000384a20f641da07400a8261140904d20b0301c00217807504d554841e0901c04000300c0201d80070071405465945840720106295154a02c0b881c0d980b80180842c0b95494801c602d02c011140d1000b8141e00da40d1030320744081c002480d2082c03004644900c04d501c002038540070401105420694880c0240c191400b091100303c403400080303501680d0002555408482c048007502148100c40d02c02d40300802d452503e030341094203040342403403d040f13004040c0203509040d02c8209241580320909090401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 669835422 1250 669834172 669834211
    0xd1b050d0902011b2307060e0609010e04050a1e1802040c11030d021b0a02010f2a0f02010e06162d11040b041109131116050c04090b 58
    0x1c444d582d070301030041001000002004184555101c000003480d2210307002803552010300c403000d0b940350480c4c07003003200140c082c40a02c100c6240503001003250000524280101d0f48a2000040c00c54030192024129036590364110544d03400c4203500700c001d035040b66104002180c2c1d51265040d001da50074500038420341d562944124454003072242c1105d80340c00c1100b00d030380307400102030300c20002d62203401c0e0010020011000b034101c64200251803441180c0c1a0741e110a02c0401001c16100301501417401840d4090340c900e10f0755044614642c003219580160a05040d2801e940000f60101c10005400750041e001000061400151b4241144240e41c1c032442464000c01e1003984243c016480c074440da0f03038400c1d0380316210043c0545a9007108843e0400c96042229554070742c100001c40c3e1178003105040881040c071069030945440448810b21190152001c142540120f5102c241907100c03141544440050030203480502000304440c10f204901681e042007841c40c1600e424042250041030803890320540000b05 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 669836672 1250 669835422 669835427
    0xe0d0b0114030f0307030e010813030e1504080a0804050a08010203041e020a030f0b0403020c0910061809020408060708480a0906110a03050a081b0a050d1b050d090201 73
    0x1903c09081601c2600e403141a94900105224820489140008c8407030012803003004c040007030078502c940c1c50f0b10741002c240103940c140208440040030f0008201c2042c400021111400d101d0014120300c254600d941d0740342010100255550142c1219803540e105008000010f0102d038034909418515050f0481d400c00c1c40e1000407001000c5801c001e012460780d0321a1002c00c105080458050f83c0b0039005c0d905182c0c400700520800420442c0c2003c2c64206050080002c03501540c9044d807030400500a04c56040c0c6c84420b0f5105a07405030f4002200e41d031107103003045140780c3d20820440d001803040b031140d400f4050300410381020801c3c101c0148800c48101d12000b1a10340303a800c28844d414040b80a058031a844800c002d4281d02d5640f1400b004549140c0d1031a007502c9002c42d03400b54159040e154181001c003c4c01c4116440b1400a080d0310103c4000c5000004140514000d008012056614543d44618120308401960420b00710348000c05e0040d0502c0660503001020b460000c6545180040c1c00d20490004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 669837922 1250 669836672 669836683
    0x190803043219031208150102011a0d06110c0a0b010e011401030f0b12010b01020c181501023a020a051203070c0204050408030105280b030601090902030709060e0d0b011403 75
    0x2c1454000d185421013407500003650500c60314005c480f0f18607111490005900381c5200500341e1120003540d00300c000052034007902c0418894003694000820002d0100750030913591000700c4004150b0b20103a24070082044c00d404440c0034059400f8100b400b540340079240c20f103425145507014141520f54030001901e0000c0e038026588600010003044c0380102503a00d05000300864014540140107066a44240c2d0618044174422034090245030b8107550703141c00544a0701d1805402980c11070151003151409000100e15906c0c003800c440030f4080742c0c0c50a5440c881d000c590780c03517561030554021070000004104085801d0000803c03140c1c415603256141c1c44100c03414404903d0007584540350400340700501441101440c1038840558404113010002c2d81c224086100e003030705070f401c01d00c0204400d000c1c079075010000d5038100806052800c0410f1f10b400b990b1041c0e810444540002401c12842041080d0707001c0d64800700383c0b1041c1c0300c4c010740d01c04548030300c108000d05000341c1d01a120285008012501c08120 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 669839172 1250 669837922 669837929
    0x2070b041a1912110a05040e0a110a0509031b030a030e0a0803071110050c0a110409060203070f170106020706140c07060906030e0102040b1602190803043219 69
    0x1c0a0030340400200014010f505820281201c0d10720b40b454626556241408482c0d03a0015074035060b0030f040c038049001c694000010b120a110300c0c1c603142d000071000182030191582c02c141d0b4440d40d80300ca131520181032400c41d05020340d281b8107000102c82070054802150000c00181c15260183c006aa0003001c03c0c1c04c1c000a9000e12150f100001d070f15400d10070f5100b0000c405050444a21407481403c1808131420b018041050328960400d0543d00000790b211004000d03080d20103070001c01d82c05003e4a0b40c07022038000700c50400107e640104449070b804d034481f0000020a101c000011425410040c0081d80c0c0d507021700403001440030500f00c0c0950b1003040360544d01e803165400100c0d0b84d001d855140c0103010040502c1f440001c642841c49802c07810806000340c40640d1041c00d41c141c1010b942000b5070788408602c400c1680c202502c248042c500380030301d204442c0642806070017141d4680c549160b0040320400c481601c40940c524044807225a40b2140403500f812038211803c241e07000c414030b14140c00980651 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 669840422 1250 669839172 669839197
    0x1505060417070e0603070e0406090209160e030a03091203110f03042c04020d1b1712030f0c070c1716092d020c0102041403060702070b041a 61
    0x1400602480c00840303640050041d103098520303256441505409554041d00e54960680000d041400a4008209401d5200f40964000300e4110410f401144079540155810501e4601c80900f00e84d03d1600700720422541e07901a0010980180d9903200141408654000c80422060801c264002d0512818000501e0189035098860300a01500e10560f00d510511902c114410713030b0b0300300e9240d0108501e100000d047c607910b20310030f041e41c0b190f0800c200780c00100c00481e01c10819900c0030405180703444142d400340207517110461030640305c0710a00c0c0c0f401c4444004030708490310801c100403010324204102600216100e8010f80c84400c0c40c03a00d02511b42c401c3c1c20900d884070314410540b1900d01c0000300c45107203007000b000c40140c464560707031428281c810101c040c8560740720f01d01c01000400c0140946800c4c0000720000142000000d00425081e6400f42d40507032000d65032000307000c107546002c6c040c0a40000d1203000030722202e071414504a03140e0040e403250b009004840d0904441c0c4100d10401c4a10003078060 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 669841672 1250 669840422 669840427
    0x150c0b06010e03030c1b0108070f030c120e071406070f060b040902060a0201090b0c030c09010807020c03070b0403210f03181e031e0909090206120403080114040207080d150506 77
    0x1034400ba6903000701b010540100308107084003c3c440d4010082c07a800785605a071071084010340000c007940030307089000c883d84c1040890001c10441c14182e1040d8160203500e440030b0300c01745144c102214114000048218810441000f4140c0010380350300d20b5240056000c0008207500f421040050001e044a84020b0b400040019041c580c4560650060000520030261260543c88011511b00a404111f5660030307052010006c4001c99801218007951100c00e51044a11170105880400e041c07100c1544000c8000c0c50106091040080380e802d200d00602000c4694800d82d6000309005244001d0b9810170018541c0c0c512201010018080301074403043c0d0441c07074800340211022551001c80407124002d4002a41c14041d010701405c0302c916501c160010b03a55810701942c100b0020130010302e01020300701e034007040800c90b003900c2140e03130101d903480346010780c40e800c03c60741c54060398200c0ca50306c5055a600c1188101302030f074001400f81066507104010184001804561072845a100118030f402141d88800c0c003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 669842922 1250 669841672 669841687
    0x60e01030f050706030903092936010206040b04210801051306030209160315080a050d0e0a2102030105010806060112140c130902030403020d0306150c0b06010e0303 72
    0x44400080010b8071071000ca45200350340d0482101201c061700802000200e1284e0100079000c00001c107007507141c503503030102c021803c40b6031403604e002d42c002c4098241c00710f1007001c646142600601815104121058215241000740c1d0000352a00300090005012203103190100701440a0700c29145901d09912844080040521b00d0103002c6039004d100b0244035074411403441030481a14019001126806850810191114074114030680001c036564810507aa8824101400d8880207421000307040c440042c11b0300c21881d0030b1a80c00d0001d500031400c241301c1c0c441e0b101003040d02c9190701c060445032055003104034480000b00c0c00c000030b4109800a541036003407000105d2142c901180d1180511000d13211620080c2440ca50101a10940c25046001c14409800144010382d07003002414108a200156400261142c00d10380407a0001c0e101038006a0020faa80302c0810341511a00001d4a03000c2d410712078454107824000c102090b0540000c1c4504092030129409900682440d01c0080b0000c095a031220380c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 669844172 1250 669842922 669842933
    0x70507050a1506090e07090b0105091306240206070309020f060a030f050114061c0615090509010e150f0102031309051b12181507180b0901050d0f060e0103 68
    0x281020b01440d05107084070008000c130f494410020303400403010103011906d1501c140f1030004e2880c007a8440c14401c04021700f1640340c0d02c1042032042480b1140d0005075007418906041030f011045442c3c50b9415080c1d4100400c0385400065159103e0f1840c6408200424107102003800500074501554000c030000c94042502501078004800c2ea1650760000c015681e40c5a200c1b11150b44240401504420208060340c010110703900c81c4054901c3c14540418500d54840300f20700c81480d011004400100090003e00c107038640140310700d0042000e1030285a250420180304003c0420f040380540c0305011000c0e0f82075990b4003c0c01515460110348500e48203d41e552000580545411201d11505035101c81c0800200003070311054401061318845a1300b550354501d0000d049101502c05481021301c20521040c00812001c6641c51248210396252405a10304d001c410260039001e82108200c1d441c140701207110790744c1c05810303100d00c1c03005180c002c41e550180c0c0517688003c01064205400092648002005016 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 669845422 1250 669844172 669844193
    0xe032a220b150715020f03090d03051e0c07021503010b210108071707030807060e061305061603021b07050102060a0209060409050403200709141905070507050a 70
    0x24036400e001060014081004441d2020142481d4450620111000c590140242c82003848214001031070f2640c400361003034642e0002c8401038010f41c0302c0318880010662500880707420044900c078410700d440d4016002641068010310b00b11217504045891802e6598500001c055010320f00700280e80c070350716084044100c0e0320414a85600d0346291407402d0b501116141114100d40c810f07409020090b050021034441e65081680100a43c0b00b801c8010000c200c500000b458100e100d10000030302103e400002604180000b0319104601030241110008600e0100d240c1d40d104070120000415021030940a6000340a191807a0011880301ca003203143c08000020b04100352803098007150516a030320304820050340300c2c41c400950000c42c140400c00180c562a0405a0814032a0a1140c5203002c050018000c2448a11056029600c00ca03c00c00100309907214800d516080c140c2c0d85901460108980c03041c41c04010280014150b413a000203101c0c905c078405a0702900d030b211099442110b00c0e42490303401d10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 669846672 1250 669845422 669845479
    0x80a0207020d2a0b0d0506121b12010903020d0f02070305070f09061e03080a090b030a06051306052214091b09040f020d0602091309060b010e032a 64
    0xf110805041c45510502d40703c504858600c004503280c09a029401030141801518031a0410442d0258119186040c00041c0c02e1658884008860b00c1001d01007100c0d8992010009040380d14101c801004aa8041241c0f16400300a00704221404003032102289130258580c406400d80c007d520010960010411148048484190301800710303075150b2030454200c04a0012030201400103510820003c3c81e40d01c09001c0d0740b21a81402d5244c540c0d280c19154113a442220324000b1607035225001d10191610a030180040c9000440070031815040001080c0c00c0804c0001d1049244035040810042c406640c0140c0c0d101109401c50103a02c0c00c0130b005181d9a4503110a81f2000b20040da00d09500c00e0601d002e84030310858005034290710a071640c1c2c09004d01d0349141d20302920210307004c011000c42d9031610000c0e406d0702a42078100240361103680c1400812a194000030b141008082050b1040c0350354002062102224044840c0b180440400d01c454070403004003040b1900006028200040e86582d600c00080d00b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 669847922 1250 669846672 669846713
    0x3070e010302091f33050703021519090c0504020f030f0f06100f020c04020f040302190f05191a030a05090d080c090d051c1d0303030403080a0207020d 66
    0x507034450340c5440000c0784803451071404151042100f0040780d809900481c2010180602c52030f040c5c01003400301c0c280f181881e40f100003c21000a0340a0401d0b0381003080e0071605062100f644154241554444101443d110384001c0841d10b4100c0042400300c40b0343d2990050000400440d929410b81d02590000c0d04100e544090780300c49440040c002c0802000014800d40009041c10403070034041c041a2203000c0a12513807030031031060541324075a0751075510040074944692180103843d14a0340c810000d41d904d4003469003d017a29481020001c41c5001c075410010358404807400c170214050903905552007001644580c05c0d83c0345240c01c109070242140000d60082c0020402403226541e90049565503240e010b500c0070004d060074001542c0c0700c4011002d41500303d0000d251070030b0140140c0f1303400e20b001142c81261614108140f11102e80d150000c644c030070b6040844550306c851500c40c2c4c00080d100e010050000d01440800c100090210182e41e048585295004050708840c08880c10304048000a1510130000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 669849172 1250 669847922 669847939
    0x5130213080a1a04080d050a0f05091e010b090703020c0f030d0b0f0619030216050319090608100504050c0d09050705030f0307210e0303030c09190803030703051503070e010302 77
    0x983d581000214899500308407080e190142000f00300b001003400404038103801d6138a000c9000028600d014182c0103280031401071068824190949488600c224443c04003070b031500d041c0c01d03455103914403000d91040d182e050058403803800e90300403801d0246407255811035000008000398502021342c420f4448410907141202410540801d0040c903104028111440345801202100c0701e6201b034004281c15101060184a4950030307a4425140d80c00c0400da9401c1160803d00820030300ba44010304a005090078a0040c001c3c0c00e122a504840e240103016441c0610f844100140c9540029011640b850300792200c104a010010705113140c0312803031802014401d00038950b0030b440c0c0d09400015584400d402c00082d81b406100310003205a05151200c1d600113001c40d40030780c0a6565000e20195106c2c5101d034616590310703540403082140d0900001c0c0340200c00109030000780424000041903944c4040c807030034000b40035114010700610b040303051405c469042c4541e0002099900d112007a1504903403081e01c3c080ca = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 669850422 1250 669849172 669849203
    0x14011710060f1b0b150604060302091e06070602030702330106020601060e09060a26070f0f0b090118061112090609130e010c0c050c0102010c0905130213080a 69
    0x39490100c14100451003c0203140d61404034002048098000c02d02d14080810800d001c8003007400c540003030340080d0119501050b600d916003032201d1401c9100c40c0050540e010025982c0001d0014025807001030100c542c00b000007a000d0340200300c030161640380401c01d0340c00d40304040074117007142000600072902431040000000b0118000035007141610b41d6900c40114960808003441005c40004000542c01a803198000446460440d500c080c10458985400d03180c03241c103c0c0345440c1822030390100b03407407100c1d01904211aa0303c090343c41040d200038031001c540d94454140100d82054078291808140c0d51480400140070340c01a0700403084040c81d9040c1c40980d01c00c10700003c0079000d5654882e81003e01000801d51501c0c22141c01146000d80c100d000a541d413880d046642101c001c502420041810a4820300601034104036403400d12100b4070080c003142640c1d802c000e110403601d11409001d6260400420b505004540640780c42c10003810702305103482d41e0f500d490342d5030b440c41c082c058403002074812450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 669851672 1250 669850422 669850427
    0xb52030506240702130603020a06110c0f030a05060a2903030d02070503040909060903030e0c0f0907020f030d1d03070308011806080a141c0914011710060f 68
    0x2288240e07001031500c1e0307904000c490350b80051615007180e00300d020001c00c09100141d070781002c10414000a400001105800d43c8107101b13104005401282c1130107101d18000901c0c0d0390003d90083c50403020383e00d82d20b4103040d1101181c03818110560040031802070400304068035140342e101061a013110751203401a80b0065040440074034001900b04e401d904200940301c5c220f00701c0c0d0007d24509120b43e08a03450965242603001c115040803030704a40752b0b41c654410340289a03240c020000c483d00380902805541c1c2d200c00000320120000042603005a20342000240014003c2c00000d0b5070450182c00c2d44d03900c2030720140e0540100862410350716403c1c00d0707a0107207001703020010581c0d038440e41c59103034908264241040100e02d00d060500044445403031384808038201c0010310010100324441c0d01e00d503031200d0507160100d090000180e0390070220107403d111100f10701d511841640846990320f0400350480399010040340c452600c40500c4804030008000d01c10007040b056158000c0f901c0c140d40310400841140b904 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 669852922 1250 669851672 669851681
    0x1030c020c0402071a101a03010e0a050a0f02071b08030a120f02040b0c0d030c0e0d141216172701020c191a03040b5203 53
    0x104005034840070701074000d41042e42c002c000042c007400f0a00700b0b501c4444079141d450700c0100c03040c9441c0f0903240d408021404030450149903600610031028110340c18015000941f103001442c01401a03241c40c00310f030b4840d80661241400040d039540540d5158a54140041da00c0b1241a0480c8000800342001440c22401700548400d0440ca41c0c40e21030f0003002c1996000900484a114a4410343c200b02c000344e40d9038400c00400e201c000080150840c4d000c607420142c1107552651541c401d0100d80c1304c0780380055584c51413407219254407580340c44809840c014610329204030810388204040c40051034440c40301d443c90040072450300c03880c4281c02351094146240b0040c001c510f07104011510741400c4040c03400c4184c680411075030701841101c060102101c0054000300082c0701d249038030100c1c0c020501944416040e001007510340402214514200750382d48011354103009201c407544801b420401d05c104080c51140c9100c2022500c5900d060340d15041c240010300b0700700d03407444418410700b40c212102603001c1e002c2c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 669854172 1250 669852922 669852941
    0x19272c040f020904110a0f0303030c2f011d0106050913081222140706090b040302010516050f061504090b01270203010902030a1103090303060d0f050d030905010b0103 73
    0x241c0100c031040e99080c44041c00c4003500888240c1c20a82c8465496100c04080500070130780d002e034160740b40745141030207012601840301102c20844407440320300c8480182440001090007520b02d440580030b8540103070740144183c4a10740700880513995540c45440d41508884241c0340c04507144030035900c441c0300b44c0000380d0b0b4030340f40145456002c2c803803e164400d03904841540b040c0900c5a05482910b181011400d46440c0d0700d0450317121050908500c01402c040265030050007990814080850034101599147e00542c4002030411000094200c5c0d285103260380c07506269485411504000b401d500003a80f07400d0100d40c80c4052118017850b80426103058016600410b41007585050030364244024036403202841c85240f80e0401001c0c200c41030040c01c40c0b000714003c21113100c1c0107131641005a0030701c0c1500c5108480550031003061060101d6401e020048030342000c02140c13441030b2960749144c410104816000040d10a003c1c840d800031505401da001016a28070801c002c00000c00810015402ca07480d204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 669855422 1250 669854172 669854183
    0x90501141308030403030603050109050f0c012102090105040f06022a10080702033c0309030a0c110904031710080d08060310060605040303080a0219272c04 68
    0x201d4020031002001503030424020f01c3c0110f5141d4407512500d00352455144125025404550194119002400b02c1000c030700c000d00c0d014940d0442040d0b02d50300c50420030407059841d58001040300503603008000300c400070414150001c40741c0340c0c0e80d900030303454502084510412407000000c410b000062560342c04c2014500070008800c0c07040031841181d454100800b502c0a5102c20031601d1034a0b115885100170070b074041200310151182e0019010b0501e030340c00ca4001000b900504c03e0080d4403002200b43c40b59020700b0715000310400c600d42010340b1103410b010803642d00960fa44081c002030590250105400c50403c3c151140192600000d2030905419031140380c0e2076030004c01c000c000c00c41c85204602e400c41c800504950030400484c031003508490156102101140001504104060f000541c660b40300c0d04a80782113060200d00034806103c1100030003e00c04201c14180a85002e580401482c00d10f855a0005008140d840e121442c80c15008607800b0703c200741d16140000300d25801904994882d81c1d004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 669856672 1250 669855422 669855451
    0x5070e01091403070306020309031b0307082b140702010e07030c150908070b0909090c030d0c02060d06080d1409030304050d020a09020a051803010c022509050a09050114 74
    0x91009103002c44180005030305004012002001c02c0c5140065802043c4800c095695400034180c2000010448001205203070018040322000c42e42e10001c2d51101489001d04c1c070700030402080d4401480140c0480742242515110704080042c5510507154400c0016070020040309046900d16940d0701501d10000307001c000c0d030f8030003880801e610441c80200000320b0300b00b00039410b440c0c505030760030a180382e001003004a0002c00c04c5070b1140303860240c10717400064803000b030700e8505001c5000c01d40754060220b508040c046e04c0f1050004540b07549044400824000c841041083c3d240c10790719440d106000c900b24000341d0740d5401c85038002803010454510000c014002c604d031a03e0601170111112103058181da010900d441c0006034000c481c002010b49011a907034556a030074003124a001a1602c4402e40c5001740e1419072060807943e0000703031303100000700401c402c08040c0019a0171811380382c0c03a94001641c600d0506050001d00c041c65080a0f014901c01c10003403200d001c071000405c2e04020201e540800070340c1c4a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 669857922 1250 669856672 669856679
    0x339090f150f0414060307051507082a0a0210030c021f090f0506071d03031c06080106080f0601081603031407080a120c09060c060213030f03050d05070e0109 69
    0x96080600754071401400e103442440742030001400711015030800004100700741040140714642480700401a1034116000d5030f00d81c182e801e8041c007900402e10f0003041c9801c0003c44007025040c04021102e4040010303d50900c034280041d034140c07070b0218001c0890182c0107064840c03072403034081d00400b01030b0301d01075008001100c00300c05514070341205505074541140e80d9551101c0414154100e04804c10701800c02808175080c2042d0081201c46010b00725402c05420b0380fa030380c0c0595404000c4800a44100c00300c0d01031814006542d0006080a82c4400140d600c3c08000003000b40010034003039441d800394429101242c1e615007a294072340c0079000a404030310082640900000b4007401891080487e224407150521415540d5800950320406802c4086070240022000e204601d0040e801c4050207490980a003915020020304403030b9150b07000400050700840c04103601100c0c1c8a3300c40045800c6414012140030360308020748070780d0100340d4550300e00f4200400907180c50b010744565407030400107a540c00f02ca14503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 669859172 1250 669857922 669857941
    0xc04020c0a21020d1412091e0a0f02010c020109090e1e01060e1308040305100e100903050d0b12010912090602010c090608070201020c0f0721110f0339090f 68
    0x3070740c10078625841c018480106440c1b0b0303100060f4800c05100b001000e43c1e090803200049100c0446071603445035401220030800083c0305410094000b5820b0a040304070007668030058809030325035040490214684001c00001c000002070b2920b03a598605002c20000300e80c10b95103826142799019044843d0303852804500d4106010b0185501d45000c4c15510703007080d450340c5d20035090401d00f490800d440d649039014085060410b0080d000c0c02d05031a20200440605a90302a210f401091200a6010b65900e4500d00725202e0800552424030000d001b04019625440c06900d41d0b401c84c40407400283c00b900010580600511892089040300d4543d001c902d441c4c000700b1249250020000c00455400340000800e64800b000b501403201400c4c0b01030148079040002e00c1001c010f51150651602e66444005070125201966148280c001a14081f07450301808021038603011080d1140911400c14902200c5000701c3e210040136045180126082c0701040d40040045221043e1004d0003d008450041205200d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 669860422 1250 669859172 669859187
    0x6060a021e01050714031b0c01060e01030609140613110d0f0b04031202040b16050c0d0b01030507050d0317040c0807030c15020102030c0a0c050c04020c0a21020d 71
    0x45104480d10790010300d103400a00001c800040025a444105001a00750031205410820403140c80f110300310301c3e00c1c0340d400c00b1032600c0b543d11100d43c8100003840303c1d1501080d04088098400c40e16000901e5a4901d000d00c000d04224805031841d079100c1051b000211000300b0014001c20006010441401b4152034602c411040da00c0401e60081c3c4400400000030b0a00c107150308164001d081640d614505810b02034007444100e1580001588100000c2c007000d01143c050354804209815040340c80700d25803070030918110b0507411440d0700c0300e0992100000c002d0002c4416041e01e10071016950469616001c0c440d010518030801008141184d0345444081c0a018980e42d104d8000c2c440241c1060f138415415045c04e4543d00180c071030030712244003408204903440035110109824402145145002244000f01e401445804020428000812002c0c08420400c0f4541900020411540c888920703103515603c449889080710080e048009591300e115607a80541c6450002c0d40103820502c0c80c00c0c0303003221442c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 669861672 1250 669860422 669860437
    0x114010c0b04290702030306030c030106050d110d0c180c0f0503041e0210020a030206090d020303061302040f0b2d09040e010609090506010e0f07050a030e0f1501050a1d0606 76
    0x3543c001c0b15003081c4210f4030900e140161480e40281d583d0f42041820301d8180131070105602d000e681040020009034131496001e42020350481c61140a000c510070000700c0b10000458041d010742c44000010030381b0103c00d030801e1520710701da071010030080d1003211007620700701102c0142001061003880007401190b8032081c1018130001c261b648181054044c0d001401d114101e400e070000607030045803440300700b640402c0502c1d08075940100500c59054400b00081d034a2000800050080040c540040154486d0341c054402420241c046541c0c19600d031980e16915070440c1203110340140b51240f030b4000c1d0b0b4600451715500b0071000e208240c0341142c024107001c050000c42c2089400d644d600c54000481202c00d11075044402d100b600940074951500742107c1540b00090f0001409200c403109100400d90020304480d9425854103011135044000108103090902480c0d0a190a0044800400603652801500c506a540031074200159a49440b0081181800001121a032405c3c80000c1131092074000c1c05480403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 669862922 1250 669861672 669861713
    0x31e02030c0f071a03060f040e1c0e040c0503060a0501110309030a0602190915080406140a14130203120702060702061605060f071e050d0e03030114010c0b04 69
    0x10694410710381c03407030452200140e40d000e401404051001c6401091640d48404415040900f1401c0400c0010070810b040240d0724859640c2d014200382d4640d050040000260003a0181d0b4a100fa100301d0280c94070300985e00041c8035601e0410281692030040c002e9074000da0010b4090080141020f006458100c10030303110088a10061054018a603010000503801d1441b40c8005a11042413900501d045103010040c1000e00030820703024003003001440c1385c1c050711105d1858030403611b8480d81051002003100790300c0229588010030401030b8211098010300c6000e400700704076520940d1100010140c42c43d0b1104002c2d80b50b04007003440d001e41c14020000c1c0203150300081c446841c009040d400600726901c10140340d4403010340c0c402c6010900a091160300e9101180000c21031980c42e00301c0c3c0013080d600884013024140503218081d4a5014452000c1d034120525a03042000310202009420f5500d8009109001a13464420039211300c65100d091703c200402c0d441302c03000086403030700c3d640c0444809004406940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 669864172 1250 669862922 669862927
    0x61409090d2d1e03060303020a1e020a062c060405120705040203090d080c0310030602031b18211e030904180312090803150d05330103031e0203 63
    0x140c48046a81c1c641042d0026261030000301c04201c140346001c501c52403088203152820004202180d00030409281040d0300003143d4004038a8041e0042c1c1d501141d10019410044886005c0f44083c0c0200e2400c4a81502002c0e4418580e070407504440c1c94041030200582041c81400100484d00702841800b034096440c105030b6650301c0d1a0700c0031030100d8104491078040c81d0712440c001c010007508800d005030421150a0a02e256207084200120711b440030344002401e859000000484501a014200041c405244c0d003290b52000e6070340b9802d1120840c0c185a07449007600c0c02d035000b04408480200700364940c140010301240307607550425103400100701c06180260f010800c10486155102d1240740c2c0c02c541ea080c03803100245d102c3c0c10010030034401801c0c1d19014601c3e0070a2030020401240650358011544148180810b101002042412000c03510052840c0b2902c0310340b480b441404503090b00032030f42070601034000107603c00c074501841c1001e00c0044d001c82d91045096290101040d82d80541e2603045c01100d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 669865422 1250 669864172 669864227
    0x301060305120a090527070906020a2409060e072102010f0c0c06050403110306090c1c0f050a0501140f31030206070e010509090c091210061409090d 65
    0xd440204602a50000e15031035151b4428054482c420140c000c83d03213151070109135040c0040a560380c2c0c000a030251900b04014040c4c0c03100440004101540c03852107c052120780454039100c00a401d40114480f0305005094012072946031000e100c0c1302c0d80d088044529510307280e41d0019150300500306028006c008140d000d101c00305141103440f10040486982c0e041c1c0c0e40d851428950a140b503011003040c4a6040b0000344501882c0029141c00407040c200c80068079a002600b5580e50740715043e20081031014440c82c4201404070126811188902403c000c1c040700320618505441500100c540b100c5d12642540801d078509081406a036a06911140041507015103103513040207000c0c04442200140c0c058410003660640c00004821807075003c0c04e10500301550303400060101e0700f000308206151000072556070b001d039a60407800080302040c1001d030780d9100452003800018283e14007610448405d855030414550515401d294810b400540c05070482032901202114020036074500425020305c42901d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 669866672 1250 669865422 669865429
    0x40501060b0301030f1509080912010e07120c063002040b1614060907031506090c09030b01060806060f07020d020604080c0102060112080f030405010f1103010905060301060305120a0905 81
    0xb140a5030049900c2c081030551443c007003808a10021012403d02c0c01c0140702030001d2000380580d50608000c0ba001054407e04940250041100d2100071a0500c5241000690030352401040481140940304101c20961144025143e44000743c064049480106180980c082e4592080b541c02d150301881c09883c0c00d07907036805081c142e00104640d1301070501d00146d403000c02c00c10401086c1e01e05c010300040d2506290600a29031201158803018085c540c629000001042c45603205c0b070068040268100414141484d00403c442014003044030200422000481c942e800340c403026124000c010581450403070541c1e40209684c010342c10407a0003201c00702005005a40b1200600301820358540102000c8910000081c6000010b92120f03640314464543d11010440400885080c40c01d0288625600e0b00c07545841401082007003000c0320860703d092003040c0c0c041c8529000394121809a0010312940d2500d500b01805c0b01c1136031000402d9940038031a83c2244810440c09000e542000c1e0070701032f100703943e200d011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 669867922 1250 669866672 669866677
    0x8120c150c040819080307030c030608030706090c170a02040f0b0909030a03060e06031510030b0901140603150f070306050301060801021902030301150c080f0c060105010e010e18040501060b 83
    0x4814010744082403d0084400410901c4803690750061400d15140e00ca80b0f803014981320180030ba06c03c068944120f248414000d401a4000300041000c03603a55107401e0400000604100320110b0307035440b074041c0001e0100d124960304100c45c143e000282c0b2018944d6820400105524103440c506181c85500c2d105450780c5031a405445005d041000d580d492403500c60090841d4401c0c2c0103001c9810f00035041c08180e40b80012810800703181203c031001140c9452114240700e002c1d507400200701040c1c800411074440019000043d10803540c0500e800192104010141c80713042103814080c498074214002088046401020f0307400890904001500741c2e20780c00400d09540c11904220490380d000500704120700d40c2c1081500b05845940b01540c00c6504129401c0030010000f2030b0081008100c08911050000141c1110384808080ca501c2d13588120100e603071034075000c09124a502249448a41000950146042241108008016010305586035058484007000608103441ea9980c4400100f03010404000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 669869172 1250 669867922 669867931
    0x50c03120a0f09260606060a0c080d060e07020f01060608010e0a0c1407060905100603020a152a0c0504060b2a121c091221110903061008120c15 63
    0x18041d013403415000642c900b040c084c020a000365401c01440c0602c940c402000040749510002c0540d8540381c0c8811000a407495801491102103083c00b400300c0b003078001601960155442000f4400036a5611040c0e82403907003482450303441c511450001c1c40700e0710250b02820781c5040500304858a640500134490094202c03085c02c40301030781e40e01103c0c0d040c0442048201c100d146072410a012180c25036001c13903481d80c4d00c0c0c0704070301d552981311102c100014010054160030759028024104102c50481d16940180d030606030980303404522140101d401d003007901a000070713100301c884180d1400100c1410381217204060079140c40745a10054031008010b40500070344040d04500b44500c0e45584030300307018003140d40880190704906072511004070005020007410710507441702c500300b54900f80000403131004101c0d840d5412040a9180c820402054000ca20180020800c01d404a50443c0d07584480c10300f12400f503014012079a403050840070f070141820001840030901c400203542040d90030941c4402c0301d0780b0071355 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 669870422 1250 669869172 669869219
    0x10807020a1202030d06080a03020d0807090e1005010e013b06040605030f0709030f062304030302030a0b03010207050601050909070315020714012c010e19050c03120a0f09 75
    0x340030582a499401b50a020f422400c001d01101001640d0103985d0720400c51000c01407003c0e95001070036060060b404031000700000c5151045510706080300095100303d6000302070200308000100010f55121740d8951504a000141101982d07d80c400c0f01112140c1d1046001c03a4150500980d11980e101c581c0904010b1080740c03126a124201902e40c04c2c0e09440c02800641048400380082000c903d401e46100186074000c035001841c0080c100b540041c2045459500310144130040500c002c045d456030042d03206a210300401c1000000310000c140c2030b440b6825014015030710401c01448a0719002642c01e80003820581100d030b850307580c0da0707a00d80c0c800900449240d070540e012441d40c050084440038500213045201c020444d80c0e03110068460307405001019864080030450031540c004c1800d43c03001c0c45132080031044581c0007542c101c0c80786000002c908122182d00485101c00c425090000d40b428101c01c1180700641020b05180044400c12850354201080080943c000115042001094a10010105c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 669871672 1250 669870422 669870427
    0x4051512010503031e0f0f16020102160f0b0c0f0a0c0e0106030207080d0b01123e040b0702040b0d0311060907061b02130606051b03040b09010807020a120203 69
    0x4418618040320141e1100e40aa0400c012011445044600650610b404c1c00c00c5039840d00d00340e002000d014043c107480c080c01c0c180300165003143d201041c01640740c0103200364204c4900320521050720300000040d104080030010811030501c841c200310070103014002d5281046580820900b0507180c54101120006d88001c4400c100900004044001c1d039405416142803d518103101c541c0c1d80921032041001c070014140da950a07a4400f0303071103020014401a04c0b104c060240c400c0d1074a008075148690000380f040ba0400c00c2e107043d507140c00e84900e02d4012642083d160308003480e1100c4003890303620007c001c0340d0095403042170001558410300c0444280c3e0080e558140701c036000038106881e207140034041c00440e5001e200100503181d44071401504260a000300f840703a5004d40d20104170010031000115007850305084020a41d103034060058885c012040c50042a00101a9811901ca03c1039003d034928045d01000f4204a55005101c101d8004c030451040300c00045554645903054060714203180d0068000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 669872922 1250 669871672 669871687
    0x40204090803011215140f28060816030309050105030c04120f0b071106060f040f02040b03100b03061509120a0813081f0903091212080f10031403040515 67
    0x1010011440e9055809080020324008900ca5100e1003000b8980c800c540703851000900c0910010100034514410321648c1c042602940c500c02c0084d0519000d06002c038442d010100171459030721461202140d40544a80e03801c80e00b400c0044a0940c80109014003164040000090080100c01008121800b40c00c00340c1c21081700c1d186c07015003514041c02140402250700442c440110340411503640000d41240d4205c10380340c003d00800c024148904100f400039201003000625182e845000714403808031900da207107186031109401c0072240401c0d1010b54105080191010825503041c2c01000800c400500c0100c5022800801e01d2410b907110300b040b20f07444800306200d6145502c6400300c1e0302900e00d40d809051412030502d804403a1854100d01103000e00c1d03e800070042850301514416001d8409003240409200042c01c12820644110515100003076202001a1012012410701402030b1100317503800030454616280c280c00c1040803580d000481c0401c100004156a1703499040d043c03020f003d05020340302e0b41d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 669874172 1250 669872922 669872933
    0x8010b040c0302090f0616020a0e0402012c04020d0908070501090c05100e10090510051c060b0a031e090c030615080d08091c030f0509030c12030402040908030112 71
    0x103404070001c0c540180b29240b8660340303098415240240580c0c540ea190016030611000000c210300007e0f4000a4402010441d14080e07900c540c4502c0c000c0e282e0790701d00848460002a250001c0f81403210072881d5107500021494190010b00414042010100b001c0107140c40f64041340d40004401c0f12540e54950003542004500c3c10000d000300000c40e1100d0f080d81c80000040c00716a1044100c034460a5001d410401d074500804215003d050090000001e0895501015095900c803281540a011a8120150b0940402d0141d0000d543e04244841e060440002d4103034090100107200c500400140b040c0e0004d001c220788030380c0a0302400b42034401495403440c20f0134401c951003a050901410002c1a060260480c0000c0c03040d500c9120b4600303450640d035008030345828403409901d01100d010300548036005e900c1c0c2c580c01c281c15135410044200004d0300c0e04908184d60344200804548903800a039441c4403144400c60103140d01a0010b440070821003000c0c0e0f03428141c2c0d80260050890021160740315000e111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 669875422 1250 669874172 669874181
    0x703030e06070c14150f07020105210c181009050f0d06050a091109012105150c120a0504020a05040911040e01151208090d03111515090f04080f0f0408010b04 69
    0x300110450745404880d6901e11443e1003000006414800001001041903000f03642044c942d095241c0030001e0740c1006030140330984e200485001c5032500d0700300f1400c014501200004c0c0d0700d44085e1a01005c26107820180b00c16500303c2c82841e0390086141d081d010104130180600d920900842c1d0300000d009600e441c0003503240700c016010038060345581e001440226102c0740d030300404505a4000307090707018403890104c3c0380c07100d111046030414002d4414046041c07809400b4050007498200385070207550f1040d001e8011140101d074040d40c00941c94a0030400c508195014801150280c05181c8075148a00082401d03901101c041c407001b40c2d990124820b52082000c0c2c440c003d0110100700c0d000701c06a42c0c03a0070b50300d03002c1c9662181c89491070b1101d0004043c09100954010364014064603c0050072880c8401072000032a0001c1d400c10780d0f45d03a00f00207403801d41f041a00c1100c506940503090380311030700c4c2d0401d5900300b40344604002e541008001d00e1008440050801007040380008180c00000c00700703100a45 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 669876672 1250 669875422 669875449
    0x10f051005030d1418030f0f060103031103120103060c030207020406031b08030a0c02063f09030903120714070e092e0b060409090f140f0703030e06070c14 68
    0x3110303031445146124544c200c51101980c2441c0503440301100700003070b04251480c00440302c1c0e0711440806440409020030b80314101d0340039848400c3e00c0003500c445141c59110b00002c030032240070940300500c0020305aa005107a04d500030b240c0107092420f194086021504a608142c0d05d0301c0030403030020801c0116981c1d4402070304083d13010f107041c40d940310f10143c2803a110034002407140c0c42c04102840b4612090080b01c4801d0904e05030070740219411121754048984007060304800005c2e950000d1099100041210320041c005001041415000702d9503840f00e40000038111352a0903a003440b42201c05041000e4009001c4d020210170315403e0041c002c42ca40446010f1940c00314808160f40013540f1100b000310b030341082032001e020074810100300004400d4482c3e604410a2145800d001c54203225110001400c0a4802c903120148403600a4510355160200c284031034940c1c0c01070b001400001c2c03042d019442044400360045040a172176540d218040195500480610348004600740880c0c544401800e481 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 669877922 1250 669876672 669876677
    0x1f060c021905180a0207150203100602160506030406060302060f12090604030507140c04020301080a02011106131202030d140f1303021c0905060d02031905010b04120302010f051005030d 81
    0x50600d0321011500c40d10b01c1d040100f010801000000f144803e0a80454104941c4a040b900100c00310400150081d002540d40e19050300d40801d0201d0464000a0300c24000c5e050800640c0034140340c80c00300b00d1240c0c0700400c01c45405441d61f10000058440101030300d004040f0070340c03d0752603880c10510f40c0204031006185507055400342c1e042c4008a9004401c50710310640003c1082400c071113000003a40381c0308003058181c0e0824400400062010004a00b41c01058804da07a441e4151491408240d525602600c038861045010000c40b000110002007044041d01c076801520309211b09500c846040702d4119940d003010086820400159450703003c003107940f001d10729903040071511554500a503580c0d03503030425590800040b40c040d100c0e42c1c083c0c0715820080c5001840d0598a01401da00700010750025901c40c0502411100541c0c800945402120b05880c000d01c8890300301480d00328400c80e0b401c000304056065550321810320848491078007a0314841c440004510072018545414903280001194001c000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 669879172 1250 669877922 669877969
    0xc050418090f0c06260a18020904080a0f08060a05010c240b0a0501030911040b1c0c08060f01030f020f01031d060f2d0403051c050108060a180b1f060c02 67
    0x801c1d2000c412441c0c000b01ea544c0009241d81c1411f1705441c02e2149020040c0d44a080d210802c4104040500107019961f81561100d6800035040d400313554080c1c003505d1243d40049050402d000a500c504041c1c100703207004200d0302030000c07041c40f9015410010100c000316895100c061317140103420104400402031100f031034204080d101c9c41d2641040c1810551115208a4403000d030710100b0b555402c03403901c21890784c20014050300c03814680111a100c140c81405051300601c070004142c0440000c600b4100c0f900500e04c903050050325400c0000d0401607294940c18950f42c1c50b50100310401641c104e040c04140d41c801401e450038070004040900b04002c02c2c4000345402140912801c10804410325040341e548001000740d03403500d00d03041c0c590f4064814074001c40c085181210420440541205048030840c606891258541c8400c1d0003d0701c0d085044448446401c204140000d44992440759000c00320204103042c031011413104c0c01c1400a90340c02100007540c01d1f2050700641c03502040e840e040d400540c18024 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 669880422 1250 669879172 669879227
    0x302010306140609191505130509010621140103030c0201030b040c1209080c01110d050906010f14120d09030507053322180c050418090f0c06 62
    0x2070482c80344d0500e1a0194000d83e003441c0b2003402964402018103040700c0001e01d4481139100042250300f01101d1164444044607000801d400c2840d00c2c2030603280c2030380c0c5810303203220701d8400a0084440c80c01044c9034981c0d120071101d24840c0f1484124080e5100c0c2e40c0b54048138250b800010103488001d801d840c1304514000714000c0540e0002201c030700e01c40144801058406c018180f1130300e02d002d9849080704c15424115082d040c21243d500910309005030500420054803000c64a660307500b024060010314003000075041c8201c07405151030940101c0014045038600000ca1244c504000541103407502103100c40c1401e2040210600a003001b401054601c0c0d01e03220420324182064181543c0c0c00e855034407000000680d9003581c070046620752a000703d1506940381c501e03c040240c1c22194031030010340c140420003030a0300d401a8000c0b440d100c501540c0d164142420600e030b07050002c3d0071032000d954091303443c6e000e1400a8660082c01141c640500d200d407410747d20b0440058548042c5400108900604c6104035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 669881672 1250 669880422 669880429
    0x2010e030318010905030307050915030103020d081b0d03200715111303050304030308071d0f060405030a080a200a0f030309020306090d02011a0a12060204031209030201030614 77
    0x225404001040b140c000d4102500c100c1d8010009450301400c90b00001080110741900324000b088055000c1d14885001c540000049196020a000095121101c0842c21021481160151100c0e6001844240c40044a08260381c07503c1d10044151001c20348640c00d000d0383d980511002e88203084100c0140345441c606607a035001e0440b13802c0c482d80b02a40d880456400c4c080c0003038251500013004c3e401e14980c0340e84900380300f40d0300c3c0c01c180300c1200024401400900c00030b1040e00b0111240301e1000392800c0d001d0300c82d410001c4140500c800190040d0062000050503034042000d103100c1801340310040d03922610080028041184115402d4050403801c060140d03040000402d610721503007020003000e81141e1854110081c1003d581d01039072510a880c18400170020210724041c1c40100b035002040302c000d99660920350369200814465009047c0c00c410070101c88032408481d0070701e1103680010325180e03c03980c0c0d440c9403041080104c00058103c200a0085580510031380d0702500fa0306071801d8030303850300340c000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 669882922 1250 669881672 669881677
    0x30615090315181a0c0a05030f0c190302041502030703080a0e030d1b0306060905061209030f04030c031101021f0e01060510050d0501090b09040209070c210f02010e03 73
    0x1000c00e40740180e1400081d1059004840c164516903507100c0039032003410300d0b1340724031100300d65003801c0c030f0594000c80c42c41403410f42113410002076a1035450456460004400c01240c0080800021410410a40403403030104220344d81c0c0242a5180144c40c2d5090144000c0542d1a0440134000d540c030030008d42012076045004580c0c0601a1500801d00b1506010141d00f140501c04507020a6810b0209400c03080495003440140b60070700780e50070080c0b15901c06045a542d210780c800e032500b2460400004a400100c0c0e80c200c0c2e40441d481c1e00b280e2618240d201e861300c2c1c540c001c0e030064484460f0070101340104403200210b640c142209100420850b219003c04480601409015155113a90b90300a19840c4c40e00303400c800000d141c010143c9250210b1454094440d074407403201142040d240c040040b0f6001850703c0352400b5004040c0400c5185d075516828480f500c039000d0081000c3c4005c1800000008014040b80c90300004001d00030f10818140000c080d14031390000d02d002d800d69040017003403120504000305 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 669884172 1250 669882922 669882929
    0x236010e0d060915050f06090103080a030207050705091f090e0304172d0f010e0a080304020d060c12050906090a0b28050103050705060403030801060e0f1f03061509 72
    0x4aa072400c14032442c0000003060b030510003c0c01d18820022490112036182e000d070348540258260641156219410000d08503024000280241c0c824030202448030302c60744c00390881501c16000c0b120815154000100503040490303140300f48042031961072041404180f04134008082c900750501c051000c030100703641c980c000ca00950300c0b00b0150406901c40c0b0b49003000300211b1001000b140c841461f001900c1e41c1c0d5400004407803d2510721403d00c4020041e081485581c0301c000301d04028000c0081d1704d5803410800d62003e081668040c58018001d404280305108500b8180a00c0d100e0f0b10184a0380002c00303060b968000e02ca5083c5401c0f00082200c0140d002c160804807941c4403c044200740d48011b4044883d0040e440b480c0d901203506880030003200c446900c00c5060300e0184044640702e599600420680e803040d80401030014010350010082d4a0290303e0140311000000d22000001e2200300101d101c100e056031403080524242e0004c04000c83d050b128000107401c5902c0e441d039038980c43d604041c01103a981d10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 669885422 1250 669884172 669884179
    0x50d15020306040b0d050d11030a021203271b0604120f02120118020f030610060f09030b1f0b0406020c0108090f0111070312050712021305040236010e 66
    0x1c00074959a0300c0d90f00481c080a07000748051096161801c00994034400e40d0b05d0321000c07480685040304c0300c0c000001a101060b00302e5005080040104060300401d400161580420859541f40111403860030504406d040085030001e01d201000140350391030840401c4401400764204201c01d0007440c4103c007803040e4158001044003603010551020440d11364107051a405076518204c604081200e800c40700d02c0010f8000c41c0e10b03604240c800010103494071700560308100313004800c10080200c507001c1c4c01c080b2205030050034000714840c0e60743c0314181c1020080b551410505404400c0d11811301580354084040c22801001c0c50606080450180d552441c240d0080c1c140004140000c01d100c108000180b42018440000e00900820320981942904043c06c22004036130b819000000c100c8851180034421383c0f0590720000d484598442000007540701c07040014255290f1840803440b030721940014502c0030f600b8100320061a055542c003890b00325603104031400d41d8840a0002c401c40c0e0340302c26640d501e02e4048 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 669886672 1250 669885422 669885427
    0x50c0f0f090411060c070509061e0d110409060c110a050705041a03100903080c1206010e0414010e070f0c02030607050f0d0e0d090603330b0301080313050d1502 70
    0x5007018000180643d00c80c07507020000003202915203802041c000c080700d9041e20841060f40343c0004105000c214000042c00014504000000350301d000343d00701d4242030103680401604d402a202140a81c0c003d4235054500765120091080c1d0799500034011003403403070304402400c40f00c40e4035a203c684a0f40c1c148101b507c281c1d00c1d4501c0614494407110a00d244000040446150350364008200c07014002524055011070810340000d0b008803400000c44140703804440b10401c1a030b0303844d8010345182c040e04480540040d030740d20342c0300c005200107403109010740001d40c1a01c81524001000510407054010b0610410040180500058600140458010b20b180c10069141c0940c14040318280c05590180c4414504214032158070100101d102d01c1c0c041c0b200d9444a0303903191166416002c0d102d41c8401c102e403005080c0c1e21182120705000e00c003e180c00d0410f02d1320048503510450b95142e07810a80104900760000a101c0080f084560700f400002c20301a2400411013100d0b4881207034481e801421410b41c0c6400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 669887922 1250 669886672 669886681
    0xa09060f090303210608010c0206010b181512070c0203070504090b0f1305030403081e091f020708070f05120c010f031806060b09030c030616030b0315010b07050c0f0f09 74
    0x71004e02510101d101c010800541e680d5071540740c0a0401e404191002d0300492002140b001b8000040b50344121a9000220082010708c06111030030755424200c41c1c0a03001400003003c0021520161800381c6900e42d03c00064807603c0c01054105007065001903c00c920300a00d01340003491715000c3d5581303c03030301c50b803000c240b66104003032110381e951040701c0145240000a808000c0051030740241c015090010300e0b2151a249a21021040c1c2c49588252684030401c0c00c080c0240300c250401101c510300030b601c10348800642c1c039002e06141080c075800107124001444010b104034102401591b4003125528000c000d0381280000180184c42040417a0b020543c94010580d14910182c10905000e5481079041200c80c2e40c60031483c3c1e09c6d81108484902c20b014ad4641c852031842c0020303041c1d00a000d8a1070715241420110410b030020102d8100d07540d014001d903140805152080105580244540e2003156692807091801130304260b240c0070450b10440e10142880d0b84ca450715100020401070549103034190340c44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 669889172 1250 669887922 669887957
    0xe0409080409060f080111130b0304060b10020708011505101b050d0e030d21090f05060f160f1b05011b050913180b0415020f0a09060f090303 62
    0x441c0c10410311103090203c0020141c407501a5481100c181c02c1c000c112171080710780005894803841e00700240714101c0c0f28040c400f0f801e40c50020340c0c00c00e106040004c0c031002c1e0398021a510744802083e9001680002c42d0800c80c0344400e00440c4000085071301000c8003281400c00254800301e5000b49441080b6a03e220010345946032008230201c90303000011102081c0305c43e000140540000c0302c00c80c0c0a4040e0201c80503c8600500800d90380714968000710b14440c02c0607040c64003c204d804e00c20b0340c50232050010748010503020700a15000754000701001c6801e14100815007021200c4000c0d4404000d03c40d001a1342803030740020584a030300e9104411070281e12460801a0140203480410814070000040341e0710420f80220003848520030644aa100d50103800d001c0101322015107503078403829511030b40c2150005404549041c0e20601c1040c1024404201280d000100d0f00580188044014005070201e1400d030400071340c4e0000c0000b480c214081c072181d005c0080c40d0800e144802418406400078240c0da030f60 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 669890422 1250 669889172 669889177
    0xa080403050d060905011502150115140c0114090601120f080403230129060c1f0506090c03150909010b1c0b0702160e070203040e041109070f0e040908 66
    0x100c03020602c43c0980b00c03441100100707000e04c41e0206250110710036402c2540089111084009000021600c0d1383c64180303010210803404070716800b0403055019900c003400010380600b041e0130b440e000000741024490200141c0c2c1e00050720040050340311000402400d1850a00808859800074101002c0748c0b83e46040c2185000c2c1e604010201599180112860b4621048603c00075100000a000a510403114404d10b8005400012841d0350045260221410504001c0a980c60b0800440b200c40c01c8580c850b600d2170056150060081d61544248034003442e24807821904004200d00300c0c2e00c5d5090001c03810b02d99000c3d149440e0301454903100002e0704906e00703501c6420110009080709078824003a034401a200c85013541d007212403e690802090746070380b00149545180414a03200b200d01400c110080d6401c071002405542181710400021036907810b400c040500403071042c01e5130f15821a4510400c40b04070b90003025101040443c02e14600003550004d08038045c3c000c25103000031440c0c164104802c0c6803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 669891672 1250 669890422 669890437
    0x2040b0d090c0f08060f0708151903050715020d0f1218200112060b0a0c150c03141501080a0f090203060f070f0809030711040219120c0503010503030a08040305 70
    0x3c400306207000030080c0c40460301c184212001690101265505034096030202e006503800c64000850740300420316400c1281d6002a0200f0070710012000307039603d41d074242c9010000e03040000c60500c07400454080c25010800c3e0306541e1840e0810764120290082c0003042e800e11810f00c551241d031614440b4070403508580003507000c9070308020100e8a400114025182c9191035158a600144101c0030600350060a0700c101415144070104480ca000e4100904580d07010381d0345410303100840804070301e02e082c0c5498428030001c4442d0b81c4002c2101d00585d01d0404900d6001032103043c01d20464500392400b81c0e480801aa40007000c0d460000700d200480d6003550080024810080d018860301044c41110a402d00c000b901c00c0c10326588030050b08122420440d440d04041d01e040346150b05c140901c500280c010b45030304800d008050300041c1480001008801c0d240001009100801c0342c1b200b500308a034125010781201f48c0b00c1030610b41c2c030b903500d420007290342d910444070340300700300a46807001c2000c06206030211003c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 669892922 1250 669891672 669891689
    0xf09130504030302040512010513080703110d0206010e010b19050c01020705120306031c08060f01260702010b0303070507030813053d0f03090c0f03150f02040b0d090c 73
    0x41e18141c6000f070002d5100d0300685114160796018005220703414065507104507070b000f5009504e1420343d56900144e801c40d440440600582d2222001c21010400100440003029070050556514200c159454454103801450310300a0400103500d21041101003400260b100d403401e25a1103175803500342c038028050520300405902a0101865000c1090009140034220841c20350316035084405c0c00d20f692000c81044a0040b920100001c1c100f07103049040c0340303944c4106040440c8040c0da43d0f600d070703a4200ea40c1180da043c010301540034008140ea0900c1403292000003030303009500e00340d0f10ba29019900c0d513040c44010051000040d0b03404100f584d01d003240d401007002400c1420f444c40304e542001c15511200000401c48280300150304e864140f0494012828111030300e40c00b8983c01d6030001180680001201600d140c2e0030b0f041d0026070040070080d002c005600401c00f02c400405071110700d4066411b002072200e4042d00501c014401c44140004541c2c205c16a03240000f038031803003441d000c4065246584007444 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 669894172 1250 669892922 669892931
    0xf02090912040902072a090504151404030201060609080c06030a0209060c37110109030206131d010b22030614010602210d0b0d020909010914030f0f0913 67
    0x21004400c0c0c001e4217459100c3d1465900130300918045c3c81c0d9038186d8440018407440851000c020002850780841d40190045500400d040d42c4aa0703083d055410b441024440441e002d41044141582032103048007402042c03504420b05c03440d02c150301d55a1501c0e5031289102c1d006c00000f154403400c60394121030a060b805840503840e800c0c0c400019868000074045144512112092980f244030001c410800049621040145c012403545074200072035070703180304d01c0d050110041010002d6520726001e41050800305900040090410b420205507504010890a0144400c0d0051100c40c07148800c0d10f039a01b91554a0951481c144113643c08007481e203900c05040b091410344510500e001c0ba000c0795041e901a9001c0715001c00b0000d224041d400408408039070100b10612440010318180c6d04403486031071004061584585542d00091a00785003525860020b80d9030b00010340c100a03248940b806241140030103503042c4031001c0381c02001c61148076074240c00c00741c0004404140c3e64640501c4d01c0307200c01c4c0340070801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 669895422 1250 669894172 669894179
    0x90210021c050c06041e17030a060b0712030c02071a0a0f1d01030c02030403020603150a1703030406200307180503010e0a1106090d050a0209130f0209091204 69
    0x1d44480c03065281c158101c1020201e20207482c040c2048440030040030f00281070740d6507642c4404100e00080701e4869510707480602d4003c08500340314540c0d03400c7c00e60046803641d607081c48000c0004175001c903409050001000e00182c80400d1080304007071401400e504000c02c0054107a1002c82c00c0100341c0d0030408600242c0700e4080314000ca580040c01f50250952184002a00440402d540407541e0011140b40e41c4c14107001c540095200b5000303202017440c02d004607401d00d5101d500190641d00101c42d21400c1c1c6124030b603107402903d032106101d00100300700c42e203080b9404d42e03200045403248002040641072603110340ca8942480205444200080c5551a1040d01c1c5c0c2400e460090402c500d224400d4032034450120045020300c0c2c18450b25600d07011505c010040e082d0941c0d14160030700c160034076aa61100c401d02025010b5200ca0000b0980c80d817040010f4200056103104025003160098883c0414180c003002ca48001640841c00d05ca5094044400080513511294994a00030b482000b003050f8040c00704000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 669896672 1250 669895422 669895427
    0x12021e120a0f0902060a12060906081b0f0105070816021201021806030105030a39090c081605070215180f060a08161b1113050603060712090210 63
    0x281d025000e044024080c2c010000400015615a424040e510410802000c45628042c0c0b0000300000810315001ca10107540320120000c8403042d5000034850380162600400c050600e0300960900b42c000c0340d03907000c680900301c0000c00e01d005401c4028241400040d4652aa946080c00b842c03a186e4000d01d003a40c01132010096501079004020f84240c000f50200000c015841c02c0400e4034143d82d03000c0d005001c089400c0d10b03100c0046c2c3d007202880455211b0000300c00040303403100d410340f04d20440708098545500d2401d0741c01c4080351800b8001404220725030007408050ba003803021540d01c50719070303280250f2641041e000141750403e04400c0b042e40c1910000300080d0580220300010814041124001140d07001407040c40000d01c9805480ca0000366008005002d030307124804200048101403400c440715080b851804003406521890076140007594406807040341c0f51400e06002c404005203c1440181091400f20b90350301e202505010074030110a003104207540c03066102c0c0d0701d460b40042061b681c00725540c101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 669897922 1250 669896672 669896707
    0x507081612030504051009020109050d030906021005040c0b0c160e010807080a050c09131b171b04180203010603081801091401050f0c0f0606190612021e 67
    0x1240e1107400440403041d01070281c8a0a880b45400002400f500d102c0d0150700001403180f204101d041c0500c3c1030000c40e10344c4501c501c03031100e103200340c030780e5080181440c0f0007a16188444035844800381c1008100400140100a00380465008800d91500d038910400d0450610501001007486d000ca186000111a800c0d9a0320781e040700c0524094840c0d02d910b843e49591a40c0c010000a011580070100400e110b00301907104980c01000c205002d56113450a0751800404208070b4040f0740040c224080c18014100d1000b15080261100d20040c00c1d502d4030801100701ca00c24503810148126070302d040100440000c0c10010300c00c00d90040013002100e86070b08d083c0103950407200c0030210210326242ea41e4055401350600106551101e821a0703c50b8808400441c1e0581c000b807940f4445c62004e100590080340100704180800d04000040c0959140004c03c1c00f070a500d080741081d40c030b0013503141c007049000c0e000f207503a10b6003404002000d030b61000702607840c44520084014034084030700d00140910f046220002d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 669899172 1250 669897922 669897967
    0x915110102181003020a09051c0f0506040209070e18070203090604031a0c0909040f051c020a0b06041509050c0f13030b0622090609051e01110325050708 67
    0xb414042c075015007801320220b00a0a880d40007198070940d00b48668a000d03020000200c0800f2824a819443c80d55002c03034010a00f0400c40c0c2c07550001091004614064a8059020700d0914007083d01d16400d10000314204541c4203041207071600d21000c50040c0d882481281c2c2218006003d0540e40d85d9245485a0039200c80c7d00d1007410703440361001050742d55000b0000c90b512400018135007049a00c4039190403a08018001c8111240c0c42114442221009841105001040f90380c014042c4942d69080400700880d009041c94480c915112010452070b20484040301924201040061035655040300b090491188040702c1c104e01402040c00403041c500300c806e280035248108010307001c40d00ca100601c1032940613040c0000b150703070241d0400304e0300c1038050b4072007889140109008601031207a40c0340e40c0d0404042d8941035030042d8030615000d6010303d003401020390380c0b07503003640d070320315615200c5000840044042ea802c00010003210b4180320301403051003500c000740e0704140202d070741e0800381448058007408584d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 669900422 1250 669899172 669899179
    0x1608070602010e0f150c041221030b0901210510020a091203080a020921071d01031e050f0106060504061b111909050c120f07091511010218 61
    0xc202d00e05008020849007242c440712401031514507649180c21031801c05c02020421150018440001c10030700c03000140e9081400b074070f0240301d040040c0c18010301004110b00203100b85810728101c1c08141d201c0b41c081b1811140d945440510040d0702c2d141c01e06144600040c090003d100310060f000840c5030795402003c00c41c000351920101c1650381c8807807080c0e041034041c016021400020028417221615001000c1101d0024418404800c00341041030344646400d19040342580025004d2080303811207031040c82c4400105018500a615591b200c81c20f40b00b910740f51200103d6500c2101c1c0800604020a800441440b07009103c4151111402425034200d0300c2103800052030403104045403049010014412717074000c00c03140040036401c81030004490000b054a0100d0101c0700d0000b461070124400e141c061820a4181c942e15034107005107100b01480a010424007441100a000b04c5503000482c40d0304032030200804420310245020140d0340180540310ba8211540002000040300140351450303600b007141107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 669901672 1250 669900422 669900431
    0x203160c0f08060907180603150b0f2d120604260403150b130c180b04060f0e0301020702040507020c0301060b0f090609030f01090b01080106050405070c0206070203160807060201 78
    0x1031001c20b5646509464030410b9030805d440600c2224501c0039143d403814820701000c12403654035500c4444683c2919940d0703940e56a20055001d4903c1e14968014200c802111a210040140317192402c0700b4031200109581229130300c0f9160303403541b0f5012404044191342c2d002c0d1002c0b880c050074111640095a41070929045100f00c006848441802c191001d8941203209420402600c41c8200018007244039281e612071090b050307010300c440442c0100341310b1200075030700ca101d48803501403a050710311140c1e08204c0000f241400103002c2240d001100b441c40800c589043d203205075408000c68020300c107501019411600f040100501c02d034000458150f0004150000c0041584c0c9003513101150254520f1494411001c2040441515024024141a40c4002d0a559101900c000c800d400c44182c3c1c0300c212000d0030313420010001d141082c841c0f42c0092909580601c01d9142c6200020b02418036807200038400c5a007c030794801552030800046045200089041c90b000b901c0320400d941d168031503c0b8080066081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 669902922 1250 669901672 669901679
    0x50f0d15030515090a03092c0a0209030f0a03020d081305120711010801050f0f04230402270106032c0318120705010c03120f1508060f04020f010203160c0f 68
    0x6848043d1a01682c80e41807840c00d040c58140b4030310323220505e11850207021118503d4000c02e91701d460301580e4102e0b00140d070340c10030b2014103040c5200c900e410308003904085802008a5004986403003003640d20300e44a11241d44890704890203820001e000b400340d1091040b26858041c050004064141c094500301c1c40c4ca085c00307401100d0b110b001340191600210180c0d0080f20509080034110072649000b030000c00c446100d040391492036900c03542134918104001080c001541009412800c1c58405804403000000311820f00040090301031051034101582d800100e1003044d802c250600d551a100c40031415060000c0b524541c0d03a8022071182c0b90050b0043c907c6280900d0030002010388841804050180c4506d020011748202050070310079018000802e10900500c115803059420b1f094402400103612540e80801646405454206001c1c1e54018400c0c03220380d000c2c81079495440340c0d040741c00701c0c010041c0a00407070450080b50b585000c0c000caa044014208402001d41d58145d55540c3c103000185640c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 669904172 1250 669902922 669902941
    0x19050c0109110f0904171c2a0c030503072d0201091506030f02040b01030219050712170402040906060503070315110406050712030603080d050910020a050f0d15030515 73
    0x600740c178000c04186802040c000941100d00c041c1c1200089409841c0640400146500c1592502203028040c010305a1002a05038000340710142d0011b01031602840d944083d0707401400500c07026090600b40040000c810041e000b03050142c400d801080001156490020394001c0d01030804860201ca41c51041207a80004458911454040342c0c1c0000c462004803000740c007031000030034038081d255040680800828070340203418201561903600d281d507807a035030740e060341030189c00c2d51030003100c4804010f100c0b440300b1168040c2c09101a080b0340c04542c0011940f045161600040505070301c616018001d00c20000144101c92342c20580d5401c000e0410f11110031890b03c4440a0301c09c902440010400c24884000801c1510504465800301400d0009100740c41e82c842021a801c01d0b4500f40700191a4000c10078581d1040c4074114a81c86611019801e04282d0440070f0080d0048000108501c000416000341c17282d40e07034114070100c44e400c01c1c00c00d804079100d0803c6500d491110340801700300c89015020449039030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 669905422 1250 669904172 669904189
    0x320070b07060b031b0a0e0604020c0d1115010f0b09030114090a060b09060102030301261c0e01090b0a0302070c12050106050312120a050a020c1507031107020619050c0109110f 77
    0x550080040344113901f0304405441c0140054442c07034003d030b424030410100420410064181c1700035910b502c0444900c1c0b82425280c000c800c08032110209210300100170403445d601030142a6445922902d80315200100400c2c01030004940003550030b85070600b440751540c400314480c81001d015075810f2112465540612210301d0081c0c0349280180e10402c010403061040a00019440001c0d6003e8100d8190108480303182018030501c010300031003a1090000b02cde541141c40910081820300701818007910740684408580a541034480c141600055481304001c0440010340280c0603000500c04044000c0c200203008003000c0c050140248504c01c400c440740f40c40d0728151068442d0910440c140b40c0d440a1001c400340c50041c114000c040d80a010440c1002020302140000d2484c138680007500f403a107070b43c0c01015a0309000c807881c6400c00c10800c820141c2c40e50070440d0b00740740c0490202c0031000c0740c07608100c5691154101d851f00c07a5280c0b0300c5000400c51841b01190004004462000c1c01492400c01c001c02903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 669906672 1250 669905422 669905473
    0xd0602090a032117010e04050703060e0d080f0f04061112040c0302150c06070513030b0f0406050604060b2a1501060801171c02121c0c0c0320070b07060b03 68
    0x104c803400401c043d01c3c0402d031050f4400d00c60800d884c80540d580d03a68a00fa580d0f04095919542c0119000448140d0310404641c0c0c414078a6492441c142032200a5000182014102510041d16498080fa8084801c801c5489008038000301d1501e0349424100098903480a0004a21030041d0711488905c1c8141501030f0f950044101000d49003d40352400103032403135800b91160000680100c2c4001003c0f405060415110340d8000700441a03500e890b29003041141e1004080c144210b04d816802e0141e144240255125034100040102c1c0d00c14400c0c0d041d0f14400c8075950944080d11403901024411911036a0340c81c103c580d9a203482803281d88501c40212180340c90310038100b03152b11040b90705103003109490123840301201e41d006031108500480000c0d42140d12002d1a5070406103594042e8100c3c1d4014030903200034683e43d20308801c16900d9541c00800c5a80700740f440380300704200e1015412a1400c14800400100501d07941607079211560b2a000b80035102101d04581303c0d000d2810700b100a8031401ca500000c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 669907922 1250 669906672 669906707
    0xf0506011e1e030b0a080102041203050c2b0f0e010804081c05072106030b1602070b120106021b0604090c0e030a0819090302060304020d0602090a0321 66
    0x1806032111109200451041c100c004100c19412404214112a00c841e10b5031001039030082000c00d200700c148a4060860b51000d251a8410030041003544142d504003000c40354189000e540d5481c40c8081946020480c0d4022042181150081ca2450240e0f8401e2003010700143c03910042007010030010b80d14480410006804203520744001000174a003240104001c02e03540450900742c600b01060784040b03c900711070f42c501127100c460340e0b0b8901e8070803051440d0350200621801d0140c60b007595105030a440c00a4031440c000c1e0f1440441220380ca00900520020b8074102c3c07849903c8545d080e0aa800703d100a121769001b6000f10070108043c0084911203420581e805442070780f80500e03243c01c01c40202115600d1100f0454141c828514aa80138030064082500419283d80c072034620310511a030050003544103c0501c034007241c0820047c1c990005507640207804542e88103140a983c1811406482042101076120141e01e00c0841000441c42407034460a108010000c86400708403001c2c0c0e00114080f102400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 669909172 1250 669907922 669907937
    0x7030807080603150c041e230a15180902120c0309070506130603050105090907050f270f011e0e06121605030c0a06080f0601030b13020304060f050601 66
    0x80180100319181c0c11042c080c0444042d105070000c41c1d01840c030203a40344545900c00040401500d181055101100c0320100d00100b2640e1404122035040c242d28040c0702c505040e4250650398030340e11840c80d00010302510f100710064040d50324000b031481c000684031400c0c000c110080803881481600c01d552020030000e01c000394a0320751000074107940d08001c00740344c1c0c903105c0c4400c042100c1d12004040c3c0480d01d003800c030f101c5042d42001006000c0d2501600300d54004c1103040304020b4039150000b1170303a08850003541c00860020303540e00403520038000d0016003045412001e100c03098040311812064851140c412043c41b2a9803105107031310841e9840c01c48901e81601009043c490342480911150308002c00401104500c0c0304000381602703110304801100c2c0b400d40468002c1055081c1808000610581110385260203403d150000d030201501820b1040c41e14282000940f81c0e900941c000e42d4505802808143c0000468a00034060342c000c9808580950070207440e0540d4410714055180600360507107a400c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 669910422 1250 669909172 669909181
    0x130b0d0c110a030e0301150311120a0302300406120606031e02160b0709080114041703090a0204020408030c010b0a0819050c0a0905011e030521071505041403070308 72
    0x440c071383e1580740d2099040d540c1b1250040141c7d1001599801076204030407007008203026000700100302d240f521144180d41c110400d41d5000039404118844402a10310b0342120400300301c602140c0c0715500e104181c1a4000008003c29802d0300844410220440350b401400007a07199030048043c0c4000d18401044500c030184100b41c800c0c00c80e000381001c4441e007449548ad41415444138013840c03038191044070105264000c2408180b80a0140c41c020b012020210741c0c060420b940c84c7c2c42034410404d0080c0344502c02001181c102c0d88180040c4440c250010030030b54031030703844002e032603145da102080c803003829071900c3c40c604640c1c00c0c0612405e0440340f00001038429088035550150309001c0000c4111307071602502c0031002c8c0f142e1328440000081d01c510b00c4006010740c100322250f904025800765079030821a81910410005800249640c48804803101030700910502c1d600141d654001e00000501d00121814075500d00c0c03e103548201c3c822401514000d600064808103a6100c1c4038807100540022030201c0009d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 669911672 1250 669910422 669910427
    0x8010e15150612070908150c0a03050402040b0d0305041502010603080a0c1505040506040b0702011a190f030b060a0b12070e1804050a030e040c23130b0d0c110a03 71
    0x1841a41000ba100d1440d04820301e02802c04888101c44840c0843c16840003400030303400400a190310051a440000c85604005035110414082e1446103020980c030381000504645813a0401e60340794002a10b0040005290b29000e000c5070800c0c003842ca074402102070300075032451050003401c04a81e0482c440038a48800001c0444e1600b0014030169140704441d60700716208000d501c00c03039201e01c1c040e4001d0f15a5040c00e2030703d40c080703800c09041c0b0021a0304111000c80040c2a01554003052203044800b000e800100c1c203206000b1080c141c0c46106481405035001003032001c200541d5200f52004c440040d191500e401000700140258050140810001000035460900407100494205002030a4180201042800c486125800c49089030709800c80c4455008143c3c01c80f540080d0b8003000c40d800d00030242c812074003c3c890080c0189140d07803400305c0d10040c502401a0011901901d40a40d00d4006558940500c04950352003407102c500792914096201c42140e10580000841e01024000b51840c115651400c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 669912922 1250 669911672 669911701
    0x402040504090b252102190306080c0a06052205120303100f0b0444010f020412060f0b0a06170606180105071703070c1a0106050708030408190908010e15 67
    0x208030721701d9420010040e00107082014a1401e225a07940846d03141d0604141d0f90500c81003400450086113040018400c1039002402e86003081c40d904e1188140f0950041c00d460f02c00040c0d48040d0300b02c810045c0c0d100d00c45c28048019449400e0142e507084510395110b140200310f071200d216200188001740818004562045d14a0303401c01000b04074000c10b10205c51981030356004611490000c04001805900713913003000e0040881000e00c0c2a4218205032801d501c14244140703403c00280101d81c0c0d041c0d8044a0001d541c000241468050043c0e6925521100d004d440e80e840003c0d804035001d0342030005009480c03c1d000711041c00104100c886e0380c120160f4015112074028200417901000d175a000400b00001e4100a10f102d14415a81c40161602c9803c04040d400800c81d061402c2590300c00050044a4201c8200c2d20390b950300000d1107030390303998030304001e603e5000b201e41e003100c05400d55400c1030a055018408005482c800c400030020810710812650b90745245101103116a2610310004541c02c840c00c24 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 669914172 1250 669912922 669912977
    0x4200f130f2103140310081504020307060e01030906021b06010812071410050408030a151211130c0210110703021e03070c2312030f090402040504090b25 67
    0x40c003407602031101d050f0004c0358100312040b8401c80812401040100300402400c0182201410010b465040070f0300800d031224680d000f5003051240c064040c00701c60b4400c0d4801d004e0260000421502c40c0840d51491014411425440419200320400410800e2001c11801010000310f80040d00d0210a99145000c407100380c0b11594050240001203500c0a0050003450b1007113104003903c1c1e03a2403405140e040211a180354601c0214102c0c440d040c0010a2000c4412035a650410713005009000d46100058550010951243d201420008080302d256000035614024040b42d100078080b130f40f81c1241c00031341400f41003805401070340140c84041c20703200c000d1407045008800c2800c1e2846c203600c81d120441c02808542c05541c1c0d2101d000040d18580320140b10003200d9050850310386441038041d40d041303680c1c0d0003850f900380a03103000000c184c032130f69645504032002000c001c1e2051040c404981400d403042001255001a082d03104029501001149074485c403015516071518400040351100406000c1090f0a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 669915422 1250 669914172 669914177
    0x30506240f120118050f0a03090308031b070b0702060a02090906010e122a010206010b19020a12080403081006020a0803060d020409050307030f02030f070204200f130f2103 75
    0x591800c4180001c4c0940000302c20440b80012001c5400d00d00140384c05d0034199a590590022100c000010b41e0000c0ca1408494004101e07548079164000c0060900802101c0700740c2000d03000850300108403011100711310034001d035001c0d500e180e0386225104003a80b140502090b4024840d90000c0c122358018840f510314180094088980c1c0140c41038010302d0102c9071031544040060541c8002d8480e00545030030503090f10b00b84040e000a514000b01503406002c1c003100e000380044007486200c400f40c800c01c041c211080c1c00028210030030140c107802420341c41040d1340940000b0020400a0031030640d10800d08200d03606940100046850750b195400c40781c001038081a40a23001c1d440c080050303503c50007458030460180c00a9541c03110f01d4900a428075100088000c00e642003801240b02c0c020442c001d89107080e8040d10042031403403410f1410906407040003140700001a010078204000341b081384c040c00070040c440810b130300d1a035183c4076144200710141c4940100441c043e428020302070400b4810b15001c80c401d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 669916672 1250 669915422 669915439
    0x18040c0e1c0215070c03033501060305090d08060f0a0503240f010806040f03170c18030102040b03040303150f080a0309090b0d080f0c03070c030506240f 67
    0x18030000d038074100c00c5041140548101c1010000354074010300c10a100003c00c0302407074a42186503807611101701a52001030b06021040071603800180109188422480154114010b40c060b8405a80641c540078081d40c00003d1428001550320b440002c1d4844045655840700e22442d6503203020020445020f8842c41c0d00000f0002c0b000405480c1045413505801c4444844802e800c201d00c100c01c0d402c00010164000301c0351640040000030350110b1002c0c0c0054000c000c00130081c5890906613490000442d02a0141c200003080000b0311001c800035090803007010100000204000040509038007880c003e400408004001090009009912440b042094059001c0b8421303900c1c01003443c8a80b0642c0f02c00001e800c0720303011008042e401603071030740940b07103500c0d08200340300c0c1500118001d020813003001400c0c100c0006000304009110001e0b80c490120003411280e07142c1c42072518120041132480b00700c507680300b0940400c1120503041001c0900f913140501c0008025458400c000e00300340705501d016040b8214 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 669917922 1250 669916672 669916697
    0x209030f030d061d0415020d1103100510030213120c080703082d0901110c0a0611010e0d120f14042f010f05030901060b0a020609070b18040c 62
    0x1d0000d00989200c00c0000902c092034000c00503082146803c51140c0301c051202008001603514002a4210411900040e00e40070003150190041040d0900017171001008401c1042124241522000b524001c0c0ea6454032198050000c0d401c2c2c2c05020240c0c0075980130310b001842464404d0282e418014040e8400c459059518612203080180a4106641c1104000780585008000788814100c0002d10303c031010020391030200d5451140100344005042003aa0010310317801e200e042006003a1004001d2461040a41c1d5140161900c0400011074145500b0b105100c1d441c40310118121665021a441e140d210700582d021030310003040c4030000442096580c40043ca030000306846094800c03403140709003c992850425800d0107214003189401b030041c00c9034200950740e03640101d0781c2c00c03510704030700306191070341c90342c030b200601608071034000f00219800860620704040e40024058003801040d01656092626406118403d1090681440d941c550420b11002c0509182d8010411004a40742c0003084522 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 669919172 1250 669917922 669917953
    0x305090a0f0c030b160f0203090105090d030915020a02011d010c03140f1303020f1e040f0e0a0303091a07021e1903020c0f03150a0e0a0b0c04031e05060109020903 71
    0x10780e2000301407174202d04120281c3d500f00501c0d14440c3c0e1107000039410903036240c000810900ca0340000e9405150f105007881e0403d8051002d88018084000c00780c0d100c0c41c20306000950742d80d071495080e03000a5402c000f0a42200910030200b25842c811794940c2e5404101c1e46080e605100a800f003282c0c9100304000c941c0f40412110302410145090319039104000e45103004201a1141044c4020b00c42d000360303040c0c518100340c0030168074509241030700d02040300304100d034081005100081001c10f06019035a06d1004169141d80481c80301c80c0304120040e040d48400c0c00508072241c0440d00704002d64008840410052900b608440b10a104802126010f50007503c1801d1040040c00013200581d1008056015500c1d01d502c4920740030380c0c01e8006003c00300001051000c5404040c00f07551403903a403200240001001400440501a0440e00724099405c0280b0400e02c0b40d4070034481540c50341d44c00d030709907010450707400009511035800c00001c00d00f40e401e200c100b00013580800c00050349172040402d2501080e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 669920422 1250 669919172 669919193
    0xd05130807030e0f0301020a1d0105040306020d06090e1b040207020f0316060207060f050d0b0333010509060d12030b032e05130f0611030108010b0a060305090a0f0c03 73
    0x10710903a5800c41c94012082444004d69a00076164400d9005100004440354004850a01c001c01042e03a04814408140161403d04c6260405040f07140005082a5076104a4001c1000c40e02450002c00100341c0030291103032550811166481d5544102021b41a5071402e60007030415103000800c14150b1030401c0d00001d151941c101c0d00480041d4007558200309498042c000c00c0010011070401988501302c000d002040d40c8600d21204004564a86040c032168a00b0007045603494401c0c0c1c1c07034040f11407100104900506148410314841c489800010456003031629016011364000741c1480f005401e03565514a0800c0d09100090805076104504081590108407030300d920000204c821156040300f01c94007249017003c03624611700500340020300110741c01c0ea003601c50865070405404030280d40c3c079151802c05440c2c42022045c14410120011401c2001940642d0b0b00084c1152040da006603154010340075140102c0e00480284c028030001004100745048841c6100d02c07031441448099100e51b204202d11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 669921672 1250 669920422 669920437
    0xb1504060909030e04061521110418090c0608060301291c02030303040b07090504050709170d080c1308010207060c02070f080303190902040e030a03200d051308 70
    0x1252605107400503d0303040f01c070580a5460683c0c0510a49081c041116000300d220318244041100d182d0110100001d04824400143c2505038144800c1110103114003145e00180503014213040911441000008a8420f507802e07158030400c00d0013040d15101c0181c4181000900c0c040d01552a65821801115034444000556034070f00203034807070a42c21106101103d4603580f615200b00d030b03003110b00b0703005641c0010541c1e0307011341e1100301410107603a4448100c46088140d07100c5ca42003420710041c8910030b60060400015200302c902c1c02c42e0b051038850b9000b03942c0c0d01e2000c101c4000c61503a2011640d00701c40e403401041c000d88050b91a100c2981d03540031541c00c81e48204c2007921041c0d520320394214015418040390b00140040f440070312201d82009500c0b5100c3c0f1020b010150b01640034092501c0722400f60b0013040e0b00079001882000504d85500c003050712a8072480c600c0300001d10301521800c80140d541c283c0e900b00501000c440b0300788030035030b01c0a0000b031101408046024511a040d5000292043c004100a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 669922922 1250 669921672 669921689
    0x8070c090c090b030402090c07020111010903050405010f02011514030f070b0c0705010203030103050d0305041a0907030605060607170705010209060c0a0b0a0515190906090501050907090b070b150406 87
    0x150020703603008040d10b100d0f0b0440d640000c0300300184809a640c44d47d160f40c0213001135a800380ea40e40c491005075034007141402003072919404c000c41306041c07540040190085400a8903441e10752311001204a01701d4800c2e1a2042c01441260018003680c480160a90103018018084800104a6100071854810160711443c0351000020b42031514110901154004140c280019400c0d941543d07034041c3c8a083c192064410141d40d600010300303203c010808d162507140200b64110203400c01c0b0018548a5510b070000380d030405e0a000200c2e132507003007010881c1c0c041c5410681c02c8401d00c613201b0280740f0652000005039255902409404c2041c0c6d0b481d0010281c94545c1e40c010f1891b00c034a890520420100184680d903d1403420041100a034850980c440425208403214070390031410490080300070141d038210100583c641030020810080560019041c0d80044038a41c400f45e980d00c0b130881e0800356034059140080c03c2840050000380609403441c0e04904822060070100c4905000700b81100c440354002d003072 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 669924172 1250 669922922 669922931
    0x20c010b0a120308220c060804050601170a0b0c1209030a0e0402090607020609030111030709060809060606041e030f03080402040f1103150616050c10020d1b08070c09 73
    0x340741141c00c00303008003110489088a070741161005004103c0040000a1165401240c2d100340d8513000d0b03050200701d034400c207040c1d85030fa00c84400400c1403a04440894240c0300d0400003040504201c4241c00c20514044000c0581d000e1035558840080301c05086a000b41c00140b1041511100008081340325407030340c400035031b100c00141c2e41c01010440700c1010f240c0038034810480d841c400c0d1a041304070fa101d140c050765240e0361030303181c072000c80c2c010144444405903522002c800d00c1105988400984119100c540d01c244840e201e00c2019902c600c02607c2040e0f20010801c010042c50408000440150345080c2e0301006099880d103807000360102c1d11308103c000030100070410045151511900040c0c00c540342080240c00100712503d0010710001d0b28203c0c3c008000c500a600076512030007158440e1101112685010b0564a451592100480303a11441307840765402e0741640d00d00c0003541c044600032581c1d030000444d8000782d62a0340e44a2440040c1c6610700704110100101d0200f10f140c0300182180c81d03000a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 669925422 1250 669924172 669924191
    0x90307151e05091e18040c151103121b0406020a03092c060609040228080f010510111f0f09020609061b0607020d0201050c0903210409020c01 62
    0x1004448044969014882c0601c0481c2c40c64440141e080c03405040240400860b941d440d0001348213003100b0005480240700c0b82c040004110031034070007804032016034103109070070140f1030001d0f18514600d8640f20303219401408221800ca039100022508201c41c8072070003c0081c00700644501c2c035480307500000d02503400084030000300369008803010000c1c80f100500d510462589024420300e0742c07101681c4c00982408002060302c6aa5840c111108190002d0085580d13442c1200c004540101107840c00b00e42c0c8251080541c1d42502a24090b48100004007224001c1c0e030804e41085101c1080d00b030042c0c10070001466049070740e0010040070040c05105013078020202c0f0307180108001d0f1121161400c03046810320503542c006032120001d840d41c01104540d0a0303200c020300c005a071419890300d91203541e144513044c00d0007020390b0041050442080790b0360090160b50b440d6044e140840c4203804480f9003546c0510400b0303c40c185603000d1080b21000c5040d1f2a0300d0b00b03503030340d41e050b0598008100400841e5560040b03031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 669926672 1250 669925422 669925457
    0x209010e01080108060403032703020a02030106080d120507032310060504050a0603050a0e19050c18010b0d090615050118060f0f030908040605040e090604050d0509030715 75
    0x140503009103800605907041590b80e07900c0706806000101815203d400040903003050b5400d001644964036a0814540450b0400940e14420004103a0280d4a00013001c05c0400c40882d01f6526080c0c1c07922210402009011004c005020050808041596412812900e2210041c2d07621b400250507101c1030241c10541e880e000c0580c1309074410428058200420040d80d03c2d0702d0498801c503001410001056900c1e150240c0c00383c20800d80ca240c640c029402e507503540310914010082e120f4002d00850303290900200c20300102c04040900da07041c0c2090700e4010006004c0107401020720304203e400101d0f400001da55030702e09480340c80350b0421513042c1c003910500c42c80d40d00c028880348260381460014046454034074003074504107422034a102049450044005554000e8000c401e000343d00102030756460340e40b0034006000350060700a10b0f59032404880070a08603040026414025a00703c0c0117400401d8102005071125170204081c00d405015030500000c000524014000604040343c0701c902145000036107030f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 669927922 1250 669926672 669926687
    0x1c020a0803040807060506090f27070b361528021b090f060d05120a0305070c02010207150e030102120a05071e080604020c010c0f141204020405060a05030a06020901 72
    0x2090184107420104420150b0038040306400c84d14581c0c000174100742b0304903003c0c50004480108429486010400180c145c4000020020100d051455512042500803000c08030308074400c9043c101c5244811080b1a4071b820300d234080c907003c1d41c1c1807031a00e00280b00d4242d492080703540d00c094480c0d030701d0200b040280b0340c0c0500140a004995200d042141c5401e000021040507002d41240200d07070701180042c1d000d0311040520010708bc0c022003201c96000c1005141541a404201c1c0c0d000064200713004030f1206402134146041d8a98140c024144a40c01c088104d0841004030645070204100c008150000342c40030b01c01820203030200c0000c141d05152043c010030542d0780180a240c20824580400c0441c20158100b05000c0302403894a0100c607156240045c3c00b83c040d170120401c1552a10308403c3c1601d80110240341008001c0c1c6030a50000808015410036005103000d401032000848005401450070368403070340d842a4002c0010740144d4440e40804d01d40400342c44110b0311a58002100c14031036800810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 669929172 1250 669927922 669927931
    0xc041806031401140a0207050724030c1e14090604080f010b0111120d110d0b1f090b031008060c120a090c0b162111030c1c020a08030408070605 63
    0x2841144c070003c00e403900c4c003007004100c1c0e8642070303000c1856800c009060103090001d044910310803c3c44016280078008425149401102003442e25000c00708003030042c45540400d50f200071600c00541141841138869401010a00e00d0003641040081125911040608050501c01c0c0044c0071680950000c01c0c01c41d0b0b2480085411f00a114114140c1c0210001d1045602c00d6030f1500180c0741c01c01091200c003c4e140e65440c0407094040440d980d80441415880081c003100201c0d4407441d45075000a94100106074003042c1c0c2c0016a42034400e001c000c640c000219046001c031f1801500b01a514200582041e10a641c6940312a0001400c01444007501c101d542d086110040e0801400d9543e54948107510070601c039a420040b0007048111580c262202c1c006112034004461000a0004c821a6000d1030301c2c5100c20008910065610410103000205071540103640c0780041031046500c00c1d00c81d444020009540c0114440d440070880011542c102560203540300e02031035034489440d0710300300303054420041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 669930422 1250 669929172 669929213
    0x240105040b0a0312050f070609031d01050a14090d0308010806090c030303060405060409051204051e0d02151306050405040c11070e0a0e030403050c041b05040b030c04180603 76
    0x3250700351640e559046a1048a50103c004c40b24421503030741c1603d090140c00d072201e6491202081030b605000054002a055074820b6540d10509100c014650001000304000c490010380306104203001640151071090205102820450400001c0300000f020b400344c0c0d50741200018000c00041140307030301c10001c103900a0290000b8040880381280420381c0d0f400001c2002c2c2c4a2512000032810580b40c607806140315540110039511901d00c400c0e820b0741b65902501c1002d005200c0b244001c80b80341036071082e001c0d0b0ba4400400c0004620304640820642c02104d002210845404002c122142810243c04c54000d00b01916015241ca00d1b205c10002190110fa0510081c8088031444201013400402c2800940d4910010b00e2059210039074000000c08801480c41c0152000203804000d004000800d200d070148111000d11040c540080da030803855100404401c00f194003440f060001c1034101020b182e120102040c41c50801c0c0e40c421060300507042e411194151540e42d800c00b8000c2c014100110028421103e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 669931672 1250 669930422 669930431
    0xb1e0d0f050f07020a08090a150206070f11030f03220b0610090e0f07030204120507141219080d060b0a181a0d020f130f0504050c0a0305130524010504 66
    0x40f0002c1e44508403c0802851044009001c40c22661840c82140242000301c100000c03040c03800e04080d58440b010b0f1a0000412b0052a030710488622805511000154038005036003030148440c62860340da0406440361440c00a4032a088280903100341c401015240901111400fa09184042c41602e80f03000d2040c0040242c0c03060144504000000010b4000d0301080450b592650f40500880c024043c2d80c0101c4400c1c1811042c1e0420301100007081000e54800c04c47c24203180001c042044101c8040c4145031003550801c0601c21000c41c0d0b949241450913000e45d0b50316103843c1801c520030048440c181c01c9150480d402150032880c80c3e51010500000c403402c280e900300518105007000340301c020440c0641c0c0c004440010060131018050701a186a0304a510300140c9801c0385202d0000c2048584c0204070030040481800182c6203031602a0a0044c0e541c205201d00c1c5c040c12081c00c5010303203002410660024003070010600000c20420640c82c5d40d00705026000000109080d460300c0080b41a0300c5144140c0c1003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 669932922 1250 669931672 669931681
    0x1c1113240503060c120402030c060c010605010905060c06070f0c0209072601030b061309060606020606030d1d0622091d01060503060604021b011113050d0c0b1e0d0f050f 74
    0x1340c400320b5510b845610440b089030b56407440064600200141c3c00d40c1c1060000c90605100401500820300740c0d0300036207544445a072150203120040c0500324410a0039800180454503d90056240c1c03000b100203817812a00e507841d550080703400c0d010281d070118000380001d021417042c00600700000c148942d2003070300700f411540f5503100c500348142e000d09201e00c00c80c21204508103400320780d4802c2d0240b03036200070300f805242e503203c8021751280307404c071102c500078094007079102002032180c0001c1d20b03001c45001000c04c04003291000c0c04420340243d041200c1c1c0c1c0c0d041d10885400c0460122454000b004242801b00383c0c0360141180c0c14987d8440c00c912a110380c140642480f007030b540420f0440d030114094900503102c2103d001ca4080030001c460100040394686030803455000107100c0105503848002c8a0369a100c4e03130301c40034031010710100c442c06000030100350018007005908100503d00418001c68005803d59140d410450960043d10f8101c00c080d03454003004a4403405000b6281e00202c018a90101480d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 669934172 1250 669932922 669932941
    0x7050306030a120512150909070e1f05040e0c12070e1f0e090a03090b0a050723010f0e010609052415040914061c111324050306 56
    0x2000303801041c52000c1620b510403d44035200391307131004480a00211079170804a1095000f00e0402c84e145000702c0102d4001008204006241011101210903400c01540d92801c1c40d50014140401ca00c0600c82c802000942981c071170040800758140c0b0301c0907011007404642007009466a001d075820306908410b0f010000380e103d18204640c092002900749100e040d0079004003450900300d07080b00640b0b44c0003405102481c0386c0041c03044e10207442522140c041585030120089580140002c03030000a40402015000a441300c01e81068000300c1c80c001f140f100103c40c0c3c2c2d10b01b1340b445a1900480140d0b00e02c0b8110f0b98070402d0250070020080c1c0803041100d82416500e1090400400b685400030180100141401e5241d21440e6051441208011030b104c80d11414840c014011402a40741e03050600c02c04501e0b2854003001c00401c98881e81a51040101c107651030701500501040c0b800da0201814003808504807083c0240c403044049010792503144001e1020210716011241c2200d40650300002c2040300018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 669935422 1250 669934172 669934183
    0x5040515071d19081501060f0305040b040f1a18100c0206010e100509160e180117010605100903030f0f1209020f042a08040807140f070605030406050705030603 70
    0xb0010f07a00108074408100d2107402c2003600e9072040e03542d0f1207034058150700c43d610f50036058144c0c0c001e6a03d0350820074506508034242e8005580183c000701140e0007207400955032002c0406403610400c0e04512001c1c0142c1c0c0000228030850f03113115403031545440301184040911805982142c4480c0810070320010402c003d40c1d03800140031b00304046101c46e002c581903411184284008100c014003040440c03a0420300342c01c10301d03000b1040401003645403040c05218980580d80a4007551180d80c829450ba2811204144868261201c13581555032150007048589650289545400050300c1e40842e061a41c980206a0380e1007800540402c01ea0080401e442540700a914900c4504000d011032690000d00000e2026054412066405444d16910008030403d4408854003070f07100c4240d19202d04880389094400c5c41c4200d4005020304410056000058844500d1312140d50098041b100b90707252034400075140030080c0c0c0081012460100400c403c1100d10300444c0d40c0326101e4684282141058404681d40c0d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 669936672 1250 669935422 669935477
    0x60e060c1207140a06021305100c02100912050309010906020304121106300a0b09180127110f1e060f041202090f131101120504051507 59
    0x40c0c50000302c02e01448507071010745a07090031103000d450f111845460140006c0d070100c03005410484003400005240d02d80482c030400400010b4884550055240d400c11001c0031204000c00107102e0081000709442111410700580144078000440d941c001410014000c0c0d00154003d0046601c108400d000d01d00540301a0f0145030f07845816501200031110003e083ca00400c94000d10040c40840c510aa054192118411001c035a50481403542ca0301030000b4103444401210a82100f140740100350480c051603003e200f000d40c4a0000036840342c100b50605a01c19110001c0a450b07242d218100041c4152100e01e02d007900c004698001300001010003080b0440c44d016498455425400c48190541e2201812a0b00303500c030181646a0f12a00d884950031109100c00043c0e0003003e200001806a01c00f4464480c0964010301c81c0d5a40205190b03544c20b02030310031600c018108002c120103080e00c3c03200350140300e0090344a90043c003802501042440d6480d000182040e0070000110341c1c10000e02d200c1080e80161 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 669937922 1250 669936672 669936703
    0x4170606090f16050d110a05031f050d030e061605030a0e0910060f11030a0c060f020313140f0a201f0e2701030302070b0c0c01030504050c19060e060c 66
    0x85481d004841002004030b155005c200ba10005100354071740303a00c540212b10400b044200c174a05440300340c03100c22980c0c1c068001d807900800028195400b01e8003425110610010081c581c03071a007030030749400505220f20303c8404c48240d400480d035401003503080030304124580c8060b030391900741d0b02d001f40d00164030001c07a12038001032203444443e4168091184004002d11103070701003181e60710b4510200040c103002e5404404c0e03030220b1030b150001c2c542c14424002c503401000e000041130794001803621420054200a42c10036917912a0041400007624280101315281c0c1c0100d01d084111100c03003021000405404000502c01c5408040c441a0703240ca41c41c04c038801c09803510b444d8401ea600741e00481daa45d9100109581d052442c20340c482e5008807201c00c41416a440f03682030356141c0740d440100c04468001c401a6080640040380281c0942d44030f54402d03944280107100300e50310840a600400d4005080c5107003a800040249410700419400945010710514252061460110b06141c80c40c4c81707840e0301000002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 669939172 1250 669937922 669937927
    0x26040602090319052a03030405060a021507030b0a0b0306011421010806090f030a0c08070602040519030507080a0302060a051f0602031201060309030e0d060204170606090f1605 77
    0x99480401c1200040454502d1240b010191410815601c40b40e0707809141d02e03252590b170110150090703141c06035500400036004508003414101080081e41000710204210310a03c90315904000303608042d207014110139200050408100c0050180c0003903590000c5010307100c1002400860307644425008507074043c4807041601d61111080c6843c10710110400c02c0c80101d0803400114010780040b803518050a1a01d040760409298441c60580328081d003600000030a80094510010540b010010041a03114090042c03505407220001040c044000c40c4950261030b8560092007001010062140640700344001031050140c03603a0300943d1810010b20784130045403210086005039040e0044020715644d2410300344441070f244d0200075941d8100f444513028004001c40002a507501034462144c0c500d070980e40f490210404201400240002034000f294010f41c2000001f5000da80025810080722010700944064107052081148109008d0b21030000c540c0000e00340700300042c489203011210130450130f241c1e4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 669940422 1250 669939172 669939187
    0x20612040203072d061b0b071419030b0f1509060702031c030b1008010905090723091f1a13030c03031e0e0120030406030204050126040602 61
    0xc0c102119640280c102c40044040e651403162400149446a540b4600f010a0207980350402c46622822410040081c6c684e481003c0c0801e080c8082c90354840481e0500c0c84000c4800c4400d036189902c248023058030b522071450f6055580340d140c06004410354045800302048401d0100160050f928100c4c4000403c070000359200340398031a0415144142c0d0002c00707a031400704404211030b016082d103d5540c0d00081c40d2441c001080d00d4940d1000c1101300d039541e22081560709110090b00104006415450135208010700000c081040c0c5001d103005018460092780380c44100400e0246881001d07004944041445101c0104010310310a0f14003220b0b5502d0032681d280c03e006016a00d140f00c2c2c5910700c0c0e4404812080401800205d18115044034072a0f80c3e14210300c4180c2c500741c40c001e42c142128200103003421200448a40c032a008040102031044562445401e414103440e24580c09648070f200841e07004241084a50382080c2c0340e56410680d041240a05100c642e850030403603c0082c00140010390104415 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 669941672 1250 669940422 669940429
    0x606090d1a010306090b01080a0506072d02010f1a030c010305060643120305060a0f090c020706140412061116061a1509030f0d050304030e06070206120402 68
    0xc54019a403224001e2a03961241081400382284800640e4030355205000094800ca0008200741d0b081d4208010344410f0b2140c202c01c0342d0752200d10131800051906421010300601080ca10702425a0442e0000070701c40c4210003000702540c07030214099071540710441407040c4c591404100c405410000b460000f0325075840c41d00051050055440d1400003c1c100782d031200300402003070320704280005500641c0768810381c581601c240c5009959001800c08052481c24008240250001c542104c0002c00034074946445080300c08080d1101e50000c140d041d2203d01030301c0b0140d01846240701411851401123044000300207819401e00c5148034910f101c846107003941062001b5a0700040308400095501a40d07108000e980d074050041c1000243d60341c46c070344a0b00007480700100c0b000c030019400c0500725003101c0008203070141c00e0360450440e451f0180284008842e480d00d051100c003100121644a030b84d201d041604005041c2d0341c006040e980500302c10000080541da030072040e154810842400880300f9901c51021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 669942922 1250 669941672 669941693
    0x11030a0f020c0712150528110a0e0f06040302010f05031009021b1203090a030c1103071d07050a080a1d0601180e0303010e01050d03091a0301090e01050606090d 70
    0x2c0d04090040141c040340d184803c00003030f4801c0c0d0044084040428900746080c00300d9105071140320010013043c13088080c49007195440e540307840c4841d1002900f0716980d070302c020301036111340c0240d00040e5080c1d203011290f103010766849000c03510981781d2074285410b42d070002c3e20034144111603405000c1e0100014510100c00c1c00c0c030f2000740500101c195242d1140300e95400001c0b101ea0025026401290800138503401c0030401e40b8800c2c00b00b40004c1c275424100ea14142c03100d20020380180e50301c074005070b224002924204494402000741985072886050410b01c0f81c80d02841c003800b40700030843d00300100c0400a45c0303c1c003034a4000011170382c0090b09045002e403100d0061041054103800c0d0050400004990a00d0500c0105812550310140180e40306a500b0503160700c800d01551428010110041c011810b1446038100c0c00da00c24149042c40c5500d6050406803140c03808080c642075034000005000401050150068814910000340305a0801302c0c0014450701030028014040c5182031103003018090102c06 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 669944172 1250 669942922 669942937
    0xf1e0c030d05042d0915090603230a030804061d0106030321020906160309120f02010e010815220e0a0314130b0904090212011b0311030a0f02 62
    0x1101e60850105101400b42d810034803500000411030040f1070302d20748010442c1e61505441c032600003111030030303c1e0107440207050b45010704541058444000c20040301c0361080001a600511a41c0d481002d1164030f9031100c124040061200d400c90001eaa0000b41c1003503586400981c000404503846490500381c2d03003c55461f1050304404e42c20311800000341074104040e650348004d00c0d00134800d070500300d5103200c0c187c1c07180072240703038001d0810003180352503aa100c00d07506980c5c0d02c0791500f03291981da19031005032254000075081da508141c1d009094115a0009a5018964020708010b00c451810091011641d03040300b50311401106048030201c0081c0e00400f5480c0d100000f40320411602600701042580c0d0b42d000340c812400300d948281300001c0750214105507002c45000410022a00d41402101c0101d50080103419400684441900006a6622040c49428a00400001403954a0044007440d61850700c9124003450320f041011030055017420f007103d0b030000c0d2515001ca08482c0084e2110000e100d21030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 669945422 1250 669944172 669944179
    0x236150904020a200a170306040b030319081008100c1110050114032a0a120f11090907030803100321090e0c07030f111605040e0f1e0c 59
    0x1803120061604010520302d41c1a022161900c0544c2c100d03d9103a0701c4191240c05003406e40a81c049011040a9400031a40800050004148211154003007440c5412074401c1c210003103280141d02212941c00000345a01031211186208032918011255488035003111032014100d440d0401044034601880b10320450401410403140b40e18544c0c000301c40104005e0148a0842180346098031442c900010700d07a169000c44561068003075a06140095040031002d5404d4001e1901d00c1d00090600b061070700481424014082c41d4007d40440ca000071100c481410079600c10484e5000b03102c1061000100c0c04240ca90003000e6540c6ca840d0002c0e0302a100700e19901c0180040c460b0700740c210b44020208030b00040d1406545440704019102d801407107080344101e5003081039130f000b80038000110740700c4c40495408055071301b84070003985015600c9605043c0034600000250003014070410041c2890712540001d41c10380c0020300301d110804d12106840d022124201103003d126007000701c80c1c0060611240c001d10381c004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 669946672 1250 669945422 669945427
    0x30603070b03090307020126180f010f0c080901140105150706050106020309100309030f0f0315080607110307231006080a0c0509150907030f0f023615090402 69
    0x460f0b100e44d40340d000000807800210102092a48000400d40c640300390350001d645116a0740e9020820600d07a103242c5071240300c0d40304032005511055400c3c45001d616605420010400b144160302c0501200f074060411015a85040142408a4aa07010141c1550350460740401c4842d00014649282e0058103005030005c2c0c0f501c0000580282c00100405080000380d4910103803503600e2000b075046603c044c0002d00410340084520500b14400e001c140314007211400c0c00201e005d5041030048414486801c405072581c0b102c001d224880746c00c40302040c0401d031104000c0d85891400d42d03e030702c140340c5410520001c801c001c03002c00500c0c003070500c008415944088000c100c0b0551300c0c0301d600d5a81d000007000380c41401c104c1a0206860911a11151040130704c101c1918440c00ca02c010301c2400c49004007d10209070359020b04585103491f07406031280a0380503540158841291403041074009045644100c610044118000050503846011000040d800c80d980d11040790520403980040c071030303082c0303095029100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 669947922 1250 669946672 669946681
    0x8040803091f0c0f0c0c090209010c080a030501080c0a030305040504020c030c061006080f042402190c02030105010b1e181518061c0911030601080a050d020303041205030603070b03 79
    0x2554003c1c030500d44940e40740c200c410303440382e4252103441c00840054003a0790704403001d001058090300181013414040c54070f240400f031161210b101c0e5030000c84600000907203c10040202d04000c1200101c401c2041340c080788114a0350703034050920310503441540c1c0a40e401144034040d411084c01500c0c00a41d1007001e0b50700c20703c2e1406410685a00368024800860385e9180441c41c1c602d1104405886907501100500c03040901107a0f4100c031017039480720342c070155400f04245246d400079040b513800f03003c150f80c41d800c0c10303070f800d034410942503070f40503086552002d20900c882c1c103100d101010110300c101401450345985213000380d4807420f1404a800c840e50040c0b2100d50403903a0318007010051a20039960120110801d0200d810049a445031a905040d40f002d9050316213250310003a03010f64403e0340b0a010404012110380042030071320600340d201c5e00141e004004914288102840041d182240e00d101861440c0341c10342c9e40c6008070100081d448208800440021320b10b4a0811010700a40210300e009a202d180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 669949172 1250 669947922 669947983
    0x50d030807180e0105011809021908060303070302060c0f04091802040c03060e01091a03012307170106140c120901030b010302071a070c12030b040501150804080309 72
    0x8003520000700081204141c40c1240c100e25003000705541c0754007446810f59181100468180304400380c80b403600401c8282c00168003000e03100034403900d01c5412400384200461100580140001001640039400030450030002030b5011490360b80c0502100a995241d1400d0f65005000d030041d0341000150780c0c40d000f02400030500b42414107030034a200f00c0e01403250807401c03a01181520064425101014200e0700180508074040d08428007640f501004810050100c0000a0945090140d8800104004a03082c060701c0500305542c1d5108140742424040b641903030203a090490b00500c103007000c01c0380b2191407404030708501e400c403004a11a5070866405095002003811150b1210103101e0210303241072035084455010b402591840350f08035110551507103a003101004520401000e0900f044003002107800069102e10000c4c10309a05c40c3d070b00007032141020060104440c0180c00151654401840000c0d02c2c55126050071786c4241c0c800122622030315091328691529a11500752085241d00e40e0f0b14220038803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 669950422 1250 669949172 669949187
    0x190503070c0f0e070203193f0b0a03030e01200a0b060a0f0b16020109030203060a0b040b040621051903030e1624092c07020609030403110a050d03 64
    0x5000f011071074015141d609050380e0b24464680151140c003842c0d9074507220715002d00b4004080b180002c034070300c183e20303009000224141c408004076a00c41c0d05001d040e0281d03001d6482444c24580c010399441001c142180c4000d000080816410bc1c1040060a020301548484141c0580140c5c10340c011074155080038544911241d01c12105d1601800365030714000b5404150008080440714414503491074288442034407a01c1346403418041c2e05200c280b0f1000001a00d08024541c0301e4103402000147c040c901504020a48944e0104107100d68100001844800c0c004007004810300f0380c4280369034181c006468841c1c18954000c42c1d0050701821000081e0034141c01d03402c000c8181d01e800c0140c41c1c1c5940b41d03c107103101251a45c064505001042445140c0004203c00b105070010b03003038142a0029580c40b02c03034120018980c40c0d803440008410b4900c1c440180000a01a0001c4860014000500e05840c01171360324004d520000d0f240107000c0d440e040d800c3d180d9072201005400d0282400d0031000b1242030140580 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 669951672 1250 669950422 669950429
    0x613020408240106140d1416020f150106081f140306160c0b0912030c0702041802011d060c010507020a0506010b040b030106030c020c040c110c060c190503070c0f 71
    0x2c420030080340300008611440c14140c4106895402881c104524a03948503085102e03204825039403841214420140401b0251068a0036202244582e00000e002030400801c8019210a580119130244c80d40300a1520281900e416182c05101540d803058039044984c952143d11415418401e004a030f4003114010705600600282c0499032240c1340c030803a90854600c503d24800028450b600c445c2c000400ea450982c0e003250bc2c0b6401c40e40c01e4502d18400901690066660240ca4140002c44108508190060112401440b66810110703c0c0d40c6c3c00207070455402c038001c5c031010f210b16040344200359034502c1515848164070b4002c20a82c900900c0107555280d40d0b241c1516980b048000005111240c0c070229003d59448158090469203448802c0c0d002e002403071044002e40c02000e2203110251968800d101d9400201c0d914840c40000340c0401505150802e00346600540c401c12580380800b000203851050900424207809041c0d0850904c41e045000d8000000c207401151207002031029009504201136 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 669952922 1250 669951672 669951703
    0x2a020c090c1b070e1302010908011401060306060815100c1a010f171f090b040507030309090c0c080a0201091505010f12231011030f2d0613020408 64
    0x4a520010342d4a40d20195072007140781102c41a0002400610442da194041c03600c10b041070400181c4400d012805e480118802d1601d08100030010031807513a1501a0400900f01c50030601441d0412030980da023a49031030301c4818000d40600704980c21840c0310b00307022941c16030042c501e0901842c03221030100c9039850a104248040355900720108800c0512200328208240e040000c1c0300d5a00300c03041c5640701c0c175007400580030205e966461080100d0f00d58042d2510861183c4090314849056280142445100e5042141031170300e0980d10042040d04407040200098001a0080d00c94107540d10403800b400c85110004d144c01d000701c51016100c1400d030400350686066822050b071203a20703104581d82030242141c0240a40410000c80e05908500c0c004244134070425405960096094001c0c0e501500e0184800c40d186d10000020400e0320070610541c00c0d00484030011850f0741611030503040c2ca89401c1e603054941216074a101082150f03840c074180441202100c181551104e9440c001e0680700c04028014500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 669954172 1250 669952922 669952957
    0x203240105040606020102030910180c0e0916120803040c0902271c0605131202070335032206050406141006030c140d060611012a020c090c 61
    0x4c00310700600035030340302c0e240940081c50b6941e0501400400360031041c401070141804402500041740255003070201418840e80b100c02542411080d9618040e41c41c201d501640c40122000c3c440d2094100c0c0c5604003d03080303030809490361210b0034040756140003a840700348228400916116900c031441e2150000048289590b42d003402d5410a2081040c1c0c0c01030200c0c0c4003020400b4140000e030701d643c0116001300c2d02c00e031040191003256079948484a2003122403405644411400c02c10440d552410242c001e0b4110400c40e42c0d0b2110401000c00d102824840c001d010f00048002074500341804070400a00b42c5540c0d0700c94118000d410040010304094406858450610415504c070b90000862103000d01d0100c17000f00d4000b4900341c0203c0080c18009003500401502d4040d140f03005011401405841384a074000140a5250070009031654002842a801d1641002454010000311442c20f400040240080c2440741d0f034208412030070411148460341e403003061803040c00800b40d5500301400041030071180015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 669955422 1250 669954172 669954179
    0x30e0307140303070201050f13180c020f0613030c0b010e0106081302030c01050d02040906090e19081e0415080f010f0806062713020f040605091302032401050406 71
    0x1501c00394080e40c0160168000c0008600551203034004000e00048554402c0c00c0922019403c0c401540c2503002301c444041a012040c0c0c0d0001d01d1040943c41d0540e80003c09500031105115034492030018002100050852156420f0501400003512181c3d440700d0000c48545e111042801108000c0c09108000740300c0e207002820984400d5043c0700c14a800800404c400144280111030b103901031018544440c2e001c0c4000544810305010300d4010b030000e840d000c6440340703003202c04c9490800c07280c905080d0350360504170807400310f40044210f58ac60260a0841500852046ca258065102e03035403210500312080d107015108140d002c098a0701540e000f4402d040e5030390b4ac5140d06081e01e803140c00307904015080710000c2201032400aa8080b007604000742124110843c0a0124480c060308807000040c580307440201303100b14605541035284425003110300b00301007030428020071b2459800500d003440f0303040c0c81c0300071702c0641d41e0821080003d0302244029008002581d81080f955581c2885002c1c02141803d0010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 669956672 1250 669955422 669955439
    0x60414010b031e070c020904060e0109080d1113031509140a0512030717180312010807091e0f0b0306150a0f240905100305340c05010f0504030e0307 65
    0x3c83c09401a5a105503502649400304410101c0280081b504665280f04520100384207002d4071070098040e5006c280c661b060300450806540d804e0441401c082c0040143d5000c3d0000d002000094a030040d100e03485603c040f5080800500308035101034001c035107184010208103000038050b00c00341d2260054662048103008000311500080e03640201140030301c043d40610030000c4160302d074800380c2921184480c00714031070341e00c1c110340c002d034849032a941c500340040c410818100150001004680c01c2040f4220188009580c0300e1010081d9182254951040c04be502603650441c10302100001c05490b1517080500e0a000c0180c1e011001d130317028841d01800052000154100d04d01184c1b80d403001e200303c110391780300d4070601802540ea441041c0090101c1c0030030140c441e00c00c0340302c8200c05031320000780908110444d407041044002100c500080011290143c2c9291518610041c240c6410160700082070b81c03411901410f035524800440519080421082c141c0c841e90012840a055003a10072203521500b04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 669957922 1250 669956672 669956731
    0x80f0714011406060d0b060c010c0206010608090318180901060503150919020a03060207030306140301021c0506011209060606080702160b0307051909090c0906090905060414010b03 79
    0x540003091060b100051003414110f000700440300c80360b00b0004a0300040b00000d4266040310210f000b00360b54a01205a4481e010082d00740981507500b0041c2041c6040c504169883c85007504091a88541c0e280e0a419a101c0204909600349007007011000c1d131420b0810180200f0301441007a10900c00c3e24028203071041401c541500420244000c2d00200400c45e900c212641a0f030803040381c1041180340008041406031016141e501d1181e500030441d10b02d400c6c194010040e04000c80c61090748100142d08003079010402c1c4a0200459200c0810369540b0040140c2e11079240c081000042407c0810b64400c01860754403d0040d11a40c0d10f038402c5585801400b00d90f600d078424120542e464060350700b8049414031700051a8003d9040c41c0003441c11103503401740d10600c840c1c08074050104286600070f01000f001405002d0780102a03250144841d440c01a0050903600c2d20b00c034032410103079154081000c5480d01d0300044d424040024444000d56500d904805880d0310841d5071104906114804030501c16000e2079 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 669959172 1250 669957922 669957941
    0x30c0219110432060102120910031a041805010c2c0d081207080609100611010204050901030305070b0c041503050702161e0e09061303020109080f071401 67
    0x24681200c074200c0500004054103211021030b8415200600f03851036101d0401c80c1c03c01d1081850051a0400e007002902d041075030010040c0494041c040123100e03483c0c0c0c440040207140030b4500843c1d01c898000700e5001c1c0840550316150464140102203482e403208040f81c1180b41e100d08005c02055200100031660100165802d516040c401099040420200c031910050148001d01008100794507036114030703160b4022090150403000c500100803c90790003031001c543c03240080d0740c00000303483d100510030600c0070140505001e100c40c440409510802c2503040e10702070b080141c5202c2a83d43c580c00c0c05085500f04000403100d004c2040009070024001c0c00980c1e0480d071002307002141e1014070100c02d50140000805034403c51242c100405002003090a59100a004521102c4c014403101035000c0c108050030303004070909280d03070f40501c1032400000400550000c51407032000040b00c3c4600d41280944510003018003024804507038200d00300078000050400700d00c15025803a00e00d1440720142d0a0728045034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 669960422 1250 669959172 669959183
    0x30203191703011406030405030f070b010518060303041e050a0e0f0a02090d0f030c020d081801081012030c0c0b0901111f0e010605040204140f1806040c110d030c0219 73
    0x2d041642810040055900700d231043c011350341071426405803160385801288060f034500703001000401403070a081d41103c203c1070765040081043c4c40c101005c42da49200b58482c54400030b40151820614240c04d01d4450040d000c01011102c003da40d82c8030b00702c400d0100741d4000304111132604c00b16592070010b00c203c40c0c00720406403410700084070588507500150555442601441000c07280240180e450b8800c880e003030344c0305441840e20b80e01d09ca40248550300740c0c41c4c05241440340b41010f00102d06c0f11500458201e9002002c1070703038241410b18040354043da04020003060440146008581e01c44008082e1140041c01e130713100e0080c503c08041c100d035212607040c00c03042950714080b091703184a003145d0040d4401d00c0410001003541c60341d89000c2003c0703901c43d034040307800c00036005284c8010380340044044240c501e01304c410100381d00841c4403980e40004003038049442103960744140942c1324003462440c01c20402e840252001040d440c0d20103805000d10700303402c0005014409a42c44002d11030200c900d003a60700708 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 669961672 1250 669960422 669960449
    0x903020d090e0c090d1212050a02250303110c0601081912111c0905040f02040807060c0203100e2d07060e0301151205070e06010503070e0a03020319170301 68
    0x43da040580d0398042c1a02c190002c1d54615100003045025184446c507104075601c0c0340078482c01d06061011a030000e440e8501040c0100300f02680d040b02070481036410240030f041144400001d04d4154020514280b4126039107002207186a200c06000c94414120b074219020303104014010840050502c80341003006220443e000403890f10240b00e082040801c002c40011070b100402c0e42c0c101007692001d4024a40c0028401c4e803400d10213402c19000b081100c0410507000d50071301d418520792644600c8035015040400801044500540d40c08000196004a080784200001c0345507424050326445000541c0c00d1241a00d000707941b04494210309410584000d1010b0450582008011619020000300c6503074950340b14010303410400030b0440d40400900789000030354000c402078078186080c81c0b020b501c48552002010100304042c3d8120003202d1b030100052404112180714407000803487c4401c0d07000a501440b80401070300404001031064000302e4003131615603040c844070401c282c00ba0b00c42401011181d20f0007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 669962922 1250 669961672 669961681
    0xa060b1c0e0a06060b0a14091c11040f06150206010302030607050c030c1617060f0a1107051506120109050a1209080a0c050f04090c0302060f09130903020d090e 70
    0x1140e0001c1c06480c0e000040d80d0b041035460b11540251210381c0c00c91009400700146812105400c442c2c5c00c0400c162990119007490503100c00200100070364801800c0b0101400156805c004400040e00703411103000340104910000c001d521001071005000d9080f4406c4034041e91148140006145412a64000c008042503520b02200700d40d130350040c000c24020382c0710034040c101d49060280300c114500c1204140180d82d01e854180f10a00f2840c1c1585a00d8864000b2003d11040c2280e0103149640b01e041704501003009045071070175080500c1035800146ca6805505150aa007591a0003050300500b401c950300141d840c81481081e007240d040f100c000384140c0c00411035800051440484445400752070030000441c0d580c1d802d020303080024440c5c3c21105120302c2d09081c800703880c111404540c0e400d010b503070410a40210760b0760403007507076102e0101920554002c902640c144000e0402c50b0000e090242c00f075240040c14a00032405419030440480150203200a2040c205116425500c00c45030318007800d200ea5100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 669964028 1106 669962922 669962977
    0x115050a150e0d0602070c06081620070f120b01090b0108040f08040906030602091e06030703090303060f060c060c0207061d0f0d0503030a060b 63
    0x2504000d2040e1400d941d41d07a0301c12046401c02030020095070001440b290050440100342c1400002c0440800213500e11003030840790242c0380c0d5461910382031443c5044541d4080050006240b003c0d0b00c2e805200303200f60400c00444a00140c480741c13034940040f1030b50b10440350070446141c008585030718200700c035000110b80184100300382004011600c0000800c15200600081c21040e825440403050010300c104442c01409501c500b004019581d1600348040d401c8000d0203840b0b0040701c500c2c07a02540703c0d240c2400c008900108040e1a540d240da006a008000100d0242e04059481e4000702d03031650031160540140c8040c1e00e6032000300d2100d16010701030700c000f00524021508601c0d0200300c0140c00c0080304034644036054124040c8810b04000c210b481c0c0c0445040703503002c00c0c2100c10b00188040480190b02803c05030100307000254039000329041c90302c03480d010900399035100f03500c81242d0700 = true := by decide +kernel

theorem cover : BRFrame.Cov 669784172 669964028 := by
  have h0 := BRFrame.cov_init 669784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 669784172 ≤ n) (h2 : n < 669964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
