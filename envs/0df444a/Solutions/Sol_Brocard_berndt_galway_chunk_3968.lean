-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3968
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:11:43.196253+00:00
-- url     : https://prove2.me/submissions/2414cd90-73c8-42a2-bc85-48fe31780dec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 713489208 ≤ n < 713669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 713490458 1250 713489208 713489213
    0x2150708120f191508030a05070b0a05070f0f090e0907030b0f040f0314120415200a1206030b04060b03150615090d1506140d050a0f050f030304080913090c03 69
    0x80c050100a100700c07440e041c0d40101794844244081d00081001e41e44254030348405040100a09401410280c5003610305024000641d5008032082c0556105041044c048000c7e0603046075240240da02c00c40301c5030002c0c0c05000110760041442401c9900170500c1405503103c021046044003801e84000b0b1020010440400000c2e006a80105800180b40358403402c00e4100c03042040c100004503012035a108846400d41130703964031352081c0201c0c402102d001403501030480105400074418006500240200d1107807110302c07481140c00c0f590145502100d8002642441e18080b0081c061700b80520348240580394942505101d12032034640b04038070081410303070080c10f0340d0310707507d10340d4442c00d5096000400400300f0008264800110002420100400110245400c0407810360362203c60074944a40348101d03c84010503400030703070200c1d50354210f0404a502d11951030711038a84030400c68400441d00002c401c000038041440041c0041a4061700c41268031484405007a04841002070014403820500c0014000b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 713491708 1250 713490458 713490461
    0xb010e13050405030c0609060109240308030a0603050115091409031905070b04050601060206160801050f0a080d12050a0902010c06240e100f06021902150708120f19 72
    0xc02c030b40580107591804480e1001507003000301c200e0b40c400b0543d100400402c0031200394800d80000f0f086070510b120119020010151042e1344034403010381080c00100204002da1002c5e0b002c2c0d402903510400130448800c040303094210780782e02407040810740b52034190324103150031518034050b210744482000346152a04200380da03900070340c4003540d00e42045810b05c8240c0001c0c0e6031440e550700481c019001042d0a614100d00245007504c010a106042c00c1d028018401da1178220aa00c0e066480499140f829000d100010456801040e44109082d1144a0120842c2500000e055141e41c443d4401406250303100244842078641d1110000e001a04809110000c02d0b280d9110800c0310808510502c4104220520708100d144213411442c0441103030340500000703205610001000f0a00f00591054031403400501945a0161742c019071050500c103101d14045549440a05e425914010001500c52003981000c10041d00071440380c400c1c1c00340e4a0042004d030014007034054401c455001d242e0a80140c1c1451110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 713492958 1250 713491708 713491711
    0xf06062d030b060304140124172b020d0c020609060304060f0f0b1801031a04080c06270a080901050c03070204140412141b0c09010906090b010e1305 65
    0x4140d40c0305052855640c90500440c02940a01406c241d808420403816085038844082885d50300d01031040c074018490309082c00d4044400b100c0c515994020b070764a90038203110240b44410311641542c110a40200d050000402107000e09034219055007803d89401da0700f0359503084010b588a001409088000d107040c030000c0d54002d220384008600300504030405001e440065105401164a9014030600350a03c140b248079040c81004a032040c651551b100c4141003a241c80780c1c4054000c50500260034040e000080b1401400700d0003c641702840e160240b03404000e010f4071440468040d91180070b01c680400203e2155440e0050f1403145000305050055809610803c003071040b900061200e40051b035076038400c1c6160ba40c068844880d60f03103807034035101181800c01d0108800b400a42c1c40500d1741740c080c860a44241c04c084119601d0808481c0358203c0c6400c0d40c0b28001135100403000c00204034000260800c00c11200e40d0a01800220320000042d1a42c001c00600160010480c1c1100725521009070000ca = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 713494208 1250 713492958 713493047
    0x50f0d0819021b0c01031505060406050a0c0c0305010605010e061e1305030106080606040e071404050604020415232704060f0b090307120b06010c0212030703030f0606 73
    0x10b1078a802c0c1e83d81a005038440302a444283c1e0071508128a0a58040c0103020071884036081c8070404030f0408000494602990103079004210300415425a0280101c00100d00307290020304601826070703240741c0f0303034003826a50107950300240d4144412080c5042170016a80c3c01c0f8100564200341c6402102c0d0402540c20404004003046007000000905032420b1080d80f02404020024100c40d140800902065800103001d0510b41d41c8100820003205100d411440c56035082203402040a0725000c000402902454101c4041401c040003440103007504044443c9503d1841c015446003288030006014450182422111031540480055550319821f099842e00c1200003c02c0000c1054440503c000c00c000141c02c0100c3e903c03000a2500d600f0f1400704031540090506142c9110001c49a98075050402e50103081c06050003c140f903c0811076490054074030040c0014030849440300b01e00d04000300501043d100071104a07250201c0403821900c510210100c0442207018501d80e071000c05d00d0300f10600781400301e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 713495458 1250 713494208 713494211
    0x405040b090c0313031e09140a03031706060d022805041211040f1d0106150c06020d0b030d0e0127172b170121080c030d09050f0d0819 59
    0x1815050401c03e6081e010b1b180e450740d280000310341010324030004c951340d0020b03c40c45013040402c2000084c0d40000314055440301001d03043da05480e1040858064009e00783c6c002c1b504c03400442c0000000c0c08a4006861824121240c00d54001803050300b91403d01c01c9005d80c2c651002041085008a4001c058041030984080d00c00121003500f08000ca040700c0003033341802b00c025030600c20403015181c00d00409019080c00704410306a403c9402c4051b0607a0020340000300002e8011440543c81c9101d588100308044000c0d050300d0f8000040000200b500d00d5405c0d81702d020800002511680125694101203203a046040c40c080750703030802d5481c0d0107080d0341c016400010300c02c3c0254080c1d070341b4014542c0301e0054004520441c980c045602d01400c004e5072141990f000141004c01040840c1c0c00d4504101480c041c0d0703c00b210028201e0400a0b0240700c0c0351251a038a12001075502592140f507400076404600440c252902000e079003844580340e607151080000029513080110705500c00c40820380810080c034910 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 713496708 1250 713495458 713495477
    0x7050c0402030106110601090c0e010c06020d110405041112011e0305010606051201150905040209010c050601030c260d050a0309120c030201061703070b0a02040b03040501020405040b090c031303 85
    0x40c141c0c0d000741c100000040c409240031a201008118550140603900010310520410040040241c1c03041900681003041100b00b00e403d1041d036904660040e4030011045c440c0d9668103009000c2c59120f44101c0703000b90b10342565100101850000e0382c080c580c0030003045240740d192540c0032000085a103403030b103032041030400000000b4038244038107030080c2103540307582d03880c0ca401c1d0990740710300b4030140d00071680c201030f0492407561540d1001100041d00c04c1102c0c0180c642c140031004176103074000d2550051103841002c002000344285007500e0f20840b41d0303040a4003d01681d0000e204038015003107100d6100d5900503d40a4403560044000d0a000103942c0b40000380e0003619150410f80801002140c000700b00c03040900414942d080c0a444c0150072020040255800394000d5180c1d284190a0060444490301d00401c3d5031022580407980103101c8880c840d501d1781407030b00780036000358000e101d845d10072890305020f91081c0c03c00c200704a101c1c01030b18192034150b40d81c400c1c00b201011801c6208500b0800d103001c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 713497958 1250 713496708 713496733
    0x3090b070804050904200d03081605190203030a0b0406050607060506032a0909010e03070201210501170c040504030e2e030c0806030a0209190603051b0906010e060904020705 76
    0x60a11890144030b40c500100d44842804101c8030701b44d40203501a000c00c020300d8001c01c0e0404c0001d60003400414609840d213450000031a024094964a0301d82c0c50801100c02c080036074000091405000b0604082107190b40c100c040208a5000c3c0c858150840c2007808a4000304500d03a119950000010b819200700c103040740c0c020040b09403031a540b1440012401202c08443c1000c1c00300c40c2e40810410000c101107416484002d9490049680090401c08092406280190003008a500c0d20304070f1030091040d542c5880810301410000d20050200f44164020030382140f0301342c0203580c01a078045d201c002082c0301b40070a00c1a4400503060401055205084000c007c1c41c2540e0580c107082055a00001c80000700701c8001d15030340b4040c15443c0303c0d9014108140140e600c4011242d00000d002c800c40241000f40010b00c0050308076a440039200d406003407041c182d43c00481c188000f41010499981e17015035200f000548103080900103041c0c02100510080c0d031103007000c0d4020010a801481101d48290142 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 713499208 1250 713497958 713497969
    0x4080604080a030b03280606090c0908100203070c0f020d0f03030218010c0203030f071406070504030605090f0d1d090108150603120d05070e0402030406140a0903090b07080405 77
    0x2a241121200000510140619450b1051303441050044010b841415265401000c1080c050200c58600b202e6000f0700c0300c20050550300600050680101c180030b01402c00e80058050180780c07085c8081d03800341d10104d480440d0f0f18800c90784902c03a04c0c1c0f10030510a1307aa40b919002030702001c0307040303800004518040c4045401e14850401840c4250340160703036854401a160761035070318034201c3ca05101140e002940141d0300030090711a4000c0c000081515601702c1d0a00c564031440b40300d1082c1d4140564000c0c014071640c010000d20a890141e8001e2009441da040b1080e41c03400011030604540e00280e11555820f4814801195451480e84000c480b10116100260702228281c0c050700440d031004051171860703001100c01aa01c04000c401400030100c4411044030203105041560004650303460014031800e0080015186002001d00115220329103494144014100d84100e211045aa000000c481000c0341c007441140c0b1790b05956130020a4502310401280d508030240c204c03450141404003013030035200d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 713500458 1250 713499208 713499211
    0xb0d030c080307050f03180c010f0c15021c0509010c08090a0308091606091d0f01030b070306090f050f0603031e090619050403030306090203061f0c06050711070906080d050d02040806 80
    0x500c0700100b0801e14092250b00d0b0040714442a41408140340c080308865070041140c10b071142c0c004042e22048180c3303400c414001c1c85284000711b0030404c006100c81e110b00c0c613035000d02e20a05003400200503076408030006480b002812180001c07158405964003002910400c816a0025946009c0303e089113071404030261032500a400880016116a07070070415007080e540c61400c1407140c0d8a9011032428075100020b6414814080030341080c451f035010540f200d10a42c05040108220f0b04208443c004c0b40d5200700240405580e05004001c140e40801c07080e05c1c000c801c84105406030b00240c100020110203007580c941045007580c1d80580d090000d0024001e94010b02c5a1310162540c60304c1d83c0d02d0441c6005001c503021600402040c3d03105004200c882c2d111030104010010340c0e0141d29620003040701c4121400d001076a03005140904080603c101660040b41d00712030103403102d05641800f5205c0d070100c821102d00780b0a02034158044102d11480c140200001d0540302050f400151819881e000c1082c81c0110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 713501708 1250 713500458 713500471
    0x3090b07051201150906110c2709070e06130914030c12070201090e060303090409111008040c05010c0f1a220b0a0f0605040f0f0b0d030c080307050f03 66
    0x100080b0200da6004441d885405440f407140c4115100e011507070300812844907406039009101c10340311800001881004080308440d0020100600c406038040c0b101c1c001c40300f070a0f401c521301c551003022800104000c100c2c1010385443c8142d03d4580c3d070b00c1d2401c010b14804d404881c51170383e6546480d10400b0a0801103142030248030b003001903944070001300036a46408011428443d195a0501907800141c0e070240703001003220010f03802c2941030388903000003904502c1000180c542c0139160100f504100147d141201c61209011a003c100700c0c05411030584208a041b1801450800034400502280d8010400c00e0b0849004811003802045284d0394849241d0b181900c44002150300010002d0140c1c1204110b03080d43c9602c81c20100712645503540701f510040c06800c1c4070b0000d403101c00c00360340c0c0c00c80e941c010340c01007000038001c2c4400541006600020000190000585414000068050f0a108917191240c99155403034141044080d2074035079072500060040780030020100040c2490003010800703140500b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 713502958 1250 713501708 713501717
    0x3010905030316080403021504060e1c12020f0304120908030307030204030c050f0108180c04090c0e060105090603040b04021906170a051603020d021308060403121e0b0103090b07 78
    0x281540700c1d041c0c0b54070010100f801c00402c0c00820000075400300703010441c0851400f241c038041e01d42d85402d9000d40480c440304441440358118030300d5160000820508201d54039210b802d207400c0404290400c1c0c0c490070000c5150030740100045030010b40c11901d001c40d0b113001c0b407400820194031b030350f11641158030070703110407000030b4012032b050003401103d0310000010b00d811514280b9501441c00003800021000340179141354191318a0110b544402440800c1e0030080042c410803040511b46011030029065001e60000302092000041c03465015030304075025810000c000e641103640e140d58003441020003c0c4101d8019410700382e04a034140c68511060050000781d103400107940c5120000188407407005040c096564244824024001018a140c25070440d46180140c2d640e0110041c3d10007030300c0b5072120713501c900b0703e1500c00113a040c00c0850141e006a21a50310280789a1002045130140d90b481c0d225515000c041082c1000b07090181c0d400814400e0060501203424040ca840e0406142800c4500c1c5000c43e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 713504208 1250 713502958 713502961
    0x7050a12060507020102090f0f0a08100903080901050411060d14131109060604051017010e160906020c100c0f060b011b0519021801060203130608040302060c0f0405030109050303 78
    0x20380c2c1c01415808000d0f88021818104040e0000d4501801590100d0080c0744205510034142c81e140c05400290071044104e502c8903440480e000000c22554100340e00280c4c101e070104001e000103005090280f5004100b11500c104003800300b10441c0d016101c194025540d90311840c2d1840d8054012074819590750a24040203501030801000f0807c1080792a172003100c0400c00c01c1425a80d80050702e06039003080d00c041000c10321046007039840074601c1c91100d000602c00c00000aa1020504480b8861110007415035402c001d000c80640c0c000b04c40e03004032070140e041480041d0540c140209018075203e00744ca0300c800e00070516180c000c0d4244000b00107407041c680707600700f11030f80d0750b08000304020030950703040301105141140e181c00f40c64180050b212120050084406400d550b83e820101001d00a48a6510860750791641c002c0d54030b50041002d04512030001000045450080600354070454241d0060040c1360754096500d821640010310f00d001403581480003281c2502c0910820a0043c4a0401141d59 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 713505458 1250 713504208 713504213
    0x1b16060605150715050c090306040609060e0a210e1c030806011815050708030108060103050606150d0c120c0306050901050d030203070803150d030f0f0518060c07050a12 74
    0x2128142000b140000e2020410700c000903601c0000d00b5914000064000b50503240e0b511011042e101c4c0242d5503503d482854140701c203010329503002d11101c600c030350010802401c6100e44161601c0c040c60000d440b6074280342114035074445481050040340748914010341403c0d208c40008181040004080c40c0c590800f0108034101608480d40b141c01200900705000c845c41d82906400f005076050040b404a400ac910b90120b00c41c0c0030304187c030ad0741e560081c0495100d60312482c200da60b60409103c165210302c00c1402059040c02e012401550311480760075602d00d071409000840c00075258034548401040700248190281203200c0c4202085c0900956021450038600030401000c41410b03000f00c3c1c4600201c40045c1700090300001141e21855000d14041d03100d5440c4160314040120202d049034001c5a448170f941c04050340100c6014010b0847e0701c0714540b586000304200c03a2402001020f202d604040120301140d0301c1c00901a126110322002140d5903240c0b1900883d0070444980c0c0641141c84091044604 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 713506708 1250 713505458 713505469
    0x1203100e16030b06092103041205060907090507270b21061002030405011409040507111006060813050307060e060405191e081e131d1b16060605 63
    0x6000101300c90f641e090045160000c0d034181d103d0b00043c040d40c80310171111240d85a051040d0b0f8010f00b100d440004503008242025a183d280c00c68810a450041c1303600030903000c00500c9070a0080c16696165000150b03100c030301c00b2603095102032442c03555820342c500107000d44140c00104685140e44030150350051055240217464840036050300e110b1010f10445041c00d65002007920125682445c081c0343d1403408450300402d40c410001e9941d0814100380400c070300144c1000d10f600b032400b96001150406003003415000201c62440c024000050885000704684071601c40d050456240a4402d50385804941ea58101c1101c011251241841d0845030811007400000e2080c20381c10a0344050400d900b8001390780d40201a000420711405021102c80c4038001d1001c08410360741e240f6002c00d6911111a0490f04900d03103038010302880300c0712448454010640208201c06809000300c0d41a0028042e101c40c841c3c81c100c0345000c00501c9200c03d05200c0190310700d894481e007c3c6030768001c060010f40755080c00c06022 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 713507958 1250 713506708 713506721
    0x3071b060f1109060d1e0608030a0f110604111203040e07091a030105190504180c0b07050a020d020301021306080108060c03091e010f02180415081203100e1603 70
    0x400382d01040c0050030264603168216814003890385000244007210380ba6180c0c004580f804c900503000d20b820008140700c20008018a0350f035009450768070401500c1c0c00100c03001590b09c015030304c41d80c100c200803c0001d2036018460350089801080403c001c00291506803554010b80d01c58003000703400205000721590031001c16005050802d102c4407035500300e001410704600c03040c402c140c062600940c1d860340010249a002c0d01400c0003d2091103800300110311504282c4a90009807440c500352040018210307031420441d4110303035000d0060101c0481c680c00f0080001c48410b81a80c1654080140700030740d000c141000d401804960716a04d61319414aa1000c1c90074800918014603040c04005203c12107100141000d40110050711425118400c0707284035001d4841c0f10720503600702d4000b24031440c10309070068024601c03400660b41005214504420080101d950303100c1d0031019082101403602407044031000b50341c4481d00e0014039188130b43c0c9122001524000722200402400d03285949006560706003c1e01c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 713509208 1250 713507958 713507981
    0x161b06020606010504030b060d08041401030f0c0f12023a0225023115050f1c120509040b0a14010c0312060f030c080105010b070803071b060f 62
    0x700420314241002818a01c1240006420703840c40c200050015512190820140d650000304551600da07a03140d10070381d00d144a421240400d06019828140b00d17024441c00300b0700000c81c1c1d0354000d0300d0b40b00b40341500c82588103441101c2182e000c000e034100035000586018582601c05191152030381100106061103660038404504080c010000c00707038100705031900ca000c9183c080004010410a43c400103601c4141788000000100c5d041411050050103d03030300f0003046801c5841400706541c0c20503007850b240181d000f0650f01943c01c0469510600705680701c808903034080040c0303c41c90642601c40b40f80c003250000000340050000a10710a581c10030b401807866220040d558048000d04101c001d40c8510310107070382d0f541000b07a0b00090b00e060502c91401c0c0103143c0c0460b8010484c05841d1504110740b11200e010a803882c0c141c0840c0000c6511052080a040b5003450851074104603041e034030020290310260817102000915110f9171080020400d000b91200c0c031502d4001042020300080c0c800381d80c0c2e0038611 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 713510458 1250 713509208 713509213
    0x7150605060d0f330603110d020a0909090b1b12390307180f05060f0d05070809060601052104060e0303040803040302160305030a0c020303161b0602 65
    0x401680d1540c106450040d880d001c0e0128900d01c2080340ba100030120941d01800e13070f650907107140c0c50350348195214612071248441c032805020703291001a01070b210801c07501c0c80c205204000500c0350301e070305070f020f001d21600620300440e903543c0d101d600c0701c19140d581d001500c0e0142c8100a000e144840c1c040041c01d1002003860181c06e002400c0514615176000400a100f02c07144250038008002c0400038030b40542c40110380c03a95288500240c0313030905030000c84508001c9803c5400b0082d11000151402085843d0740c542e14030b14904080030b0101035008804010021182031000340141c02103400303a98454451a0780342c0d2028501800c519207814000b0381020305011041060400c101c5030120101482000700e040358840340c4961038080c00804481207400000d010100a20003002031100045010300d00075401c65440030382d103841c011001002407100074295441040551040c42c003801c0c105030180d00060039241000c815a8030b40c02d919209105c21142c075441480003802d1140160080703405800503100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 713511708 1250 713510458 713510471
    0x513030203030403080612010f020c10020301051c0507090c0804020102100204050f0105090a0b19090806060904150f020406050d060b12040f0507050316170d14091c05030715 76
    0x18065141e1002074000342c1040031100018182c1c0c0c45880655060f80c090744020044128107443c6e0303030005e41004216601c0c0340540304e2041710000050003a203043e203400a11903201500c158540100c0ca0041000440c0c2c940100e09002030a81001d1042498100850710350403601d2030684002410306505414041445105010501080e1941c1e000c44030b4912084c20500c0e552580c0c01c002514014240c1d00031080d005000652001d40c0c02007106045113000749445089c15a600c0e141d1281d25035500303d40c000d41202110340020702050209803440201c2211801c0024a0207070001600140c6e403040c3c0200740030070740014000c0310350f00f5940318035401086050303601804d054032403005600716803001d000a0607030101444a40c0070300005000090040c50018100c440300d0840c1220490942c0031440f400c1d558005d2018007848005021400c040180304eaaa1903004d844070280f130900c510340041d243c0b80d41154800400d003142c5100b51004038501400740d030085449480c50f1822101030045202d03086c1d1303058204139 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 713512958 1250 713511708 713511713
    0x20109210e09041101050a0c0b0a02070c1d0f0a091416270228091401020319120b0a0306241203050f160b0702060a09022d06040306020d0513 62
    0x360009584c00240303400d45d0346a800d0301c011a03540c050303104040c21241ca19010700140980c00d0703008001e118400d00380c801c60140d82c0c0c0f180341740440030302c1c03071800c8000840d0001a01200b081035a80c2d500c070010300b000140d40e0310543c0300c61000115203241510380d5442005a403200e10150101d4400070181c1d524554030b2115105c40e908058a4032100400303005801182604e80c81c101c40e140403015002e43c207100f04160b03040407001846402144150010320403041c21001c9103502c0442102c840041c02c0100c0340c0e10004e5134100302c0d60003c1e10811060140d60351101c041d09640c58682c0000218003900020400500c0c2241e091460480842d2000c0e026819a104200750780307005510380d02d840c2e0181080b03902c1e0b0000f01c1004045100d405c414488000c0e1050000c400c000c0341c01d031207074010040ea9007102c40c15510b225003401105c10003200070390311103034012000200e220303140300824480b81c4030b030f080a12600c1c2c0440807883c07981168000b1105581c0210340030445000034400d1b103a2200030b010003031710001003a4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 713514208 1250 713512958 713512973
    0x50708100b0a0b03070918050406060f14130b0616050c010216270c050c0c040c0c02041d160e070203070b0106122409050105060304110d03020109210e0904 68
    0x500c151000f190000c00080ca0080c094090390004004488500e403000020082c0c0c42c008280844088941c030b0310340341004c00ca42410a00001c1505c0318201a59107400210042240c940d000780c480b24100d5403140104d41c3d90f500c1d03074800b034400702060303008072a1760100301d00d00541002c0019600604540c0451118480300da0190301c07110072240e02c00c482c01c2201003044407040804c03220704805a0014104000c0c9840150b0200040050300e42800c10768440c01290010003082e0340a140c003080005c1c4440c2d40c3d50000d072070568402c0c80251190340c04080c48001d2508480e00f41030030001e4881e82c5005414040001c3e080c020b418a41c0440c1500c007a40c0b52002a036034024041006000e07141c10032004989001505060390300c50320f00600c14000106150300c10030501c0f080071142c1d0003260009400d200000406041c4181624007850340868000c4880b02d500382400b0703900480741010741c115074070b60004501007500c29001038003039074a50981c4080c1c02840680035280d0070b10119158003520141d010131021030200d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 713515458 1250 713514208 713514229
    0x1110c1005071e0b0402090708150103270f1b05090f0a200301080106050d020d030311070602030a0203061c03020d0f02030906030f09251a0412050708100b 68
    0x101d0421070388400050602411201080c02d81c101c10b007283d40d070b0b81c07010301854020b118403a5100f100d421000b03030384201b4100d69882041e64500654400b818003849258040d4020842040c8a60005000c180003108040b4021190700015240300c25500b0040c000d004040b0580035001c4625001c0b00061480d200102e071211302c0081036802442e20a07070200b42c0e000240d800c000300c0000441050201000c0b4140104040d80c800c0c4644201c540c03800d0400280e83c203280c44185500c0e03400500f02e4448050548041e03000c1d10304544528070b51402000054001003da04c0614010003481c0c10060701d030710b00381c400c0c005003200c0c21004c1c0b0300480e502c00e10b03940041d900150114140c0d4441ca0081c1e2480f03099241070b4610300a50120710b40c004008801c01608a0f8946460380c070900c800001ca4440c401c194810700141c40303071a40207190700781441900b80490001046541d52020005e0341c01032805542d0200d051019403121401c50b416006001c041002e41400c114540c44074000c04c4041000d2800c950004191860 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 713516708 1250 713515458 713515489
    0x1a010c0503071b0305030a02100b0f030a0f03090b030a0207171215220b0a050603090a08160f12030506040b030c120c040e071a04140f0415060201090201110c 69
    0x35262403d1180e01900d42c0e5a005550203021a5202c8911200c00394807190a01c180390000ca103031803d4480545802c16100c040c100f4040d02a214881003501c6030a41d6a40d449400d034103010070104005451008800210720400e1070020058441c8420f14103078000311080400880c0c010000d100041d07101c03a000038010340140c4440504509808854081668815840710390708100482c1092136102d0f001035044030351502030803612000981d031640108002d80c0429038a5400c140c0c030604809000035000f200400324002d51010b14004900c583d5203030341c2c40315255041140d00700039400000d2040e6815009041cbc00c000125402c0c41040480e07004031366a00042c0f00002c1c0b050040d40c1242d884186c007440010300c0c40754060014000d405000404540c7d9200d203100765540540641036070091807024009032002c0c1d60a0300588041880303480c08018049800203000e80c0d1082c0d4501c00d03507502c605007102a0313000340040d40010a6400b207600006d0001c0c6408102002641c004084e42c107155660318411040c3c026 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 713517958 1250 713516708 713516723
    0x1608010f06230f04150504110f19170103030f020f06060609100e0409060207021003111215030105040507050312040b030f04080706060801140903090f120a080d1a010c050307 76
    0x40002d00050050120010080d4000385804540482e814480d80600c0c01c0d03a0040d142804448003100c600c1e5110b10a811307648840d94428441071011810039035600c0700903199890802e6025007100c60140c5851001e030300c1180400c580550905031a9012f01c140d40c0100301e01c07800350610385084c1000c11180e1103000c0400b4401c00307107480110030782c42c002d810003483c144001d070040103000c0d00303031030188000e41c0722100c20b911a028030a00001482c0c440d00509059001c00d084145c180304e00c1262000d0100c1d009800d58049402c4140c00c1802610248a42c030300c07a074000c0d0b00500c1e82d580380406150a000c0c0e00c0c110480450402c1100340000790060003140d4000354100c103024030703a070b4803802e00e0307012401240310044c052428032400145100301500b080c80d002018560040d03080e101c0f140500c0d42c0b840703241900354121221801810382403803c80641d803110a42c403801e9034282c0071981c0c2c80700d0041d88803075aa4158aa81e803102c0540c030f0719030500728a102070030a08040f05500c050b51201d603900e000e000d00040005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 713519208 1250 713517958 713518019
    0x2115010e240d2406030509060c04090203190c0201150b2a0f0703030905040507050403051504020f180411040c120b03011d0321060109180e1608010f06 66
    0xc402d1607001400c201c0556414a07505a0008401c4489168034400e0400090801d800b00360207450106e0440d005003010f400c0d5504c4c142c44c0c424210040d400083c549202c50003051105010302020740948212a44194000104109110402141c82c036264000c00e00325007040c020302640e44907040012400103040c4a40c0c801520b04071680500d008180311001c4920b001d082e000104060f006a0b103902601d108070b80512440d5106c40b411907140c06036210181070380e80a00e0081f91011a0a0801a04240094103601601c0c0207800800c7c004071a04e000e120440002d00200024041c0700003108032004005c550034082d80c2003e0000074990084801c140070010b0388e40381e120040342c0c0d09500044070001b2151000c0460031014070b0f030b04e859401060062610013680144404c4203150f145041e489041e050312501c10880c140758445090b04c03082800304941c140d0321400a14100c20401c07080300405005401012a14101a483d03425281d1800b80000a10304100701071101140508002e0301559000c034500018 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 713520458 1250 713519208 713519227
    0x40911271309050c1206040b070305070e1e150d0b03010216030f0207030f030f1e0206011a070219060f051201060c0602210601090f0503070306022115010e24 69
    0x44c0b80700e1480042d440944441e02025440003c101c1500c142d0003200710325900c0d514030300c00f80d060b100b0448001000402c0006005a5860300c0301e4205c0c051100712844541c803140e00390100d00f42d0071010a10380c00d02040841c049010200307602400701002400d03070096081a0280c0d200c1c120013100d0f0b80d401024000d09010303044040e03100b082890021904400402c08549a908010b046400d200c2900c10004459500515042d0341e40d01e50700710001195801058030b6840d240c1c40600a031a489000c8000500800c10103015070350340c1766050501505071804031140e0b46082e102403c030300c44c2d4582c40b00501c001800600b0948864110445c11100b083c14031400218007858500002e100307220a82c6191703800170541401c6080c2850415106103000e8a0b006400780d180c0223010040300d201d200f140d0781648a150140b000500c5600500019903140c6100700a4110b0044c41d0301000d18116035100001082459403111907074000100600e022043e10003d91a41c2a5444842820f002094032000b076240000c01810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 713521708 1250 713520458 713520463
    0xa240503251a070b0c0304060c0f090e060114070b0f010e010f05090402130c0e090604060305100c030b03030d05070e0402070302030d15051903020406060206060319050304091127130905 81
    0xb036a9601036600c62145c0340c400c1c012002900240c1d4252000b5280518040d8014010025401c1040445d107910b41c0c03003031402d58003400c5840010140c904100c03072900d01e100d01c03c02400281144601c640111401ca14083c1c07061401042d059110400c07056080e8010401c4160458014068400581d141006aa11400030982020b02c54500d2240640f600e0f80742c001c8e0036803004846400702401c07a401310b001c0e00e46500700030070344205000c0640345070050500c080c0c5484580d03102c0702040d03d2900700414005a101d00007400e6421801580040c0d946840411501d143d01ca16030300c1c194103045030110304142650710000d61701d000c0c0304c810761002c690782c1e0f1000c0c4c01d00a6050b040d9004040085c5010310700d00036024022140d240f40d100480c010340c01c0074070116040c3e00200310a8415a00a4000c002455140d41200c90343c1c4410700c1c0581d42d0340820400490040c3c06400340e2090b010818504540e181e0001150442000d8420f03a07840e03014102d09006000c03175a40e428042015440c1c608046007030303081c1b81852030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 713522958 1250 713521708 713521717
    0x1210c031d0d020c121005090c030d17090706090e040f080c030d1b0206061005130605040302100e0604050d0204111809010603150e0a240503251a 64
    0x14641c1c0c580300418031003510001080d01950101d035080ea82c0f01c0101c0341c01d1110300d00503201065100d030007812900100c40902d40c001c0d984660000308950b20038408102180c00c20500003d207600048a0000c600311b840b410400081d00440c4660007450864500800104451424015800301c02202000310b024001009414200c5542001d0600da540810450880c0d8a43c003103041c1d513003640d0074600e0070b2020703210001c0200d02c401900d4010342000d503183c20810411024070340c59001030100900964040702c1c0104030b1003001e4103103a01e500d540d0710d041d40100400382c4a522243c0080040d00343c0300c64a591076507010f80d000c954080c0c8500490350594170016000c3c196040340300c01050070203d80030840c00100c002c40f40129006854a4240d80d803100011015280042d00c41d241d0b2002d201820045103d480c181141d01442c01200090000040c081c1001d8811440340603514020710800e0504c041d280602070a003d1102c0340508504a040203c502810101c65228040d5040340b0384012000c02075803981107a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 713524208 1250 713522958 713522981
    0x30c090406080313060e0a0605090607050627030a170c0c0303090607030e150705071509240204240e1305041112031801021603030903060b01210c03 65
    0x20311141d9200d00e90b055981d0040264406043c501460000d00f00b80a02c0c00180003c2010300810101401c000342a152988103000e1070360041010460880403440c00e0200a015204510010080c90301c2c00b144400910182c44541400307801c00c0021064154022511103a444c521000461031503036280e00c50516406900030080c0c4500000080120003100030400e907204103000e480801014010381e111659a401d10130081000300c00210206074405c0c082c1010300211481801c014549442020180f425110068811a0030348403d00004000c030310083c00b04080366400d41c8086003014a4502d903400e8044140b0071884000b09100c1411481c40e215051285180b40d01420100c00c180444c8084001000c0840307042c0c031074680c003444c080c1140c640100012000d00b00e0000039401c02d1040301002c48880c0e94502e516056100f200144030540e0390340313a004401940240c942600081c0b031810010705a9111300d4002d410816900001c5240704119442d41021070314182d80003886050040341a001071014200d003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 713525458 1250 713524208 713524211
    0x8060601091a193c02011103010e0415060909210e0d02030a0b0903030714071a09070e0a020d0501080106080303012d0f090b041116030c060e03070b0f070f05030c0904 73
    0x11031650541c1da100d1a02c026920f203e20410f25003002c0405c034202d9650041d03407001d80404000405c440284032000e02d800078080d48229031684103103a484c0048520540c8403001e415200d1400b042807201004c649800e440c134030403802c440c0d140888402441e00d00c01503e0b00703225426034108581507445c10000c0c6042c595200070303600980d0034006900c41d030344c2d00304807481c0d0001039801c03215443c088102c400b55900349504c280600701343c0c3c10b01c036a100220030707000340312628a1081120010321210305070000b500602c03444030010782d248036a01c0242e0070f61354143c2110340580c0c140041000019400401c684c115508109401d105994100094a01504141c0c07a070a05030340c505004510300d0b0180d44030508484400404200ca2807101c03007803106484140581c400c10004c28880181c3c100b0041c0c001030004d6200c1d00e0078491000c100c0c1d070b5070f00490340c010312801c855900c0411071038100042c404240350440b1002c5201d00d00c1e03145c4a10002d01c0900014800003c0203c0070010500d02d40034401a9a00ba5400920 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 713526708 1250 713525458 713525507
    0x40906091b033806030c04050c04090e0613021210050f071e0c060b0409080d0203040507080312060f0f030f010c080601030b0f0616020a08060601091a19 67
    0xc0300300401c419070000352489890500195140c00c4602c211844003040c0844408060300d00343d1203286484070041c5080e41500680e4000c0106648900c00d86100c2c81288003483d86450800c3e41c080d089a140e040c0501c1c2540c0880184100340180700d48580304181d044980b0790416100c00d1440c0e00f490b00d00703000c42e05018104010712080391410300449204107900c2d5200d02244400c101b00b800640f41c0243c6500101d44158103407004070b42c0d2034200e0140c180740604046100a20380d5910300c080d5200c0d035a000d0b100c0340d000c014001086000e004407001082c40728000e600741002800c880c0b10380c1e0800b800962280c07002080b2180c407911943e2115a48a00c0141035070310800e1500d0810703010300f2031346d95240009040e440008005602034400e100e074404014224450700c0d0278410a0195a502032114144003080c80341104006950b0700210801500360500541a98140f0100140c16410b0310b0304800414107050011220020801040d80d41a681c2c4103520400910246800c1c1c45d0140c54840d56481c400c20340300f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 713527958 1250 713526708 713526743
    0x1503090503120109110301150e0301021b010912020f030d0207020f0907020105160f0c0201081801020712022e02030421020a14210f04051305010617060a0504090609 72
    0x266a94101c0780c01c0d00c801e00101c5c41e2402481c040380700900880400c00c08494034500440d114032200c0c03000c440060001454104004600e004910340f03071010104a85d1214001d0040202240000442528500042680034181011140c0f24021080c0c81c10005501041ca07a003076650f0b51250601e5040050724114840c1040d81000f40601f0089410a4224800d20541d81c00c031481740b482031285070704980d510126010241c0c0115070008001d4480751803078610100c9008001420300c000e1481d248121a8540d6105180f080642444810110b0309507181c60298081c800c4025103010f4121054445030040e62940c0340e190240100d580458540070002034210421160f030b40000c0e07809280c90082e040003481c1402c2c40c0003560364203180d03038108030310300d003880360714840f0085440140062520341a4002d041689460110b8034040000200181050310b4500400080b44c103c7c003090290003030714944100314a40310000c0382464140f88140f41c0203980e42c00107034043c0450b5602092840d03621040706d015550007032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 713529208 1250 713527958 713527987
    0x4060308090f19171005090303010501120608030306100c0b010605090a0f0b0708070201020a0506090102040e0109050417090109030b041209051008040b04081207020105010f0602030a02071503090503 87
    0x140c070100c0c010148905a4009890315000c1c000d0703c40082c092452a00d4140100c40301204501d100080283c443c0100301c5d04600e0942c05401d201d0181e240041d0b03100d6150100040c099002441d43c01d018924004c0280480d09010003200d40c011010341304400c05806454080350051061207000d825510008008074503140d200c0c0090803282412607020f0710301a107542d0b024103003030000c3c81640035480c400c000520000320611b0151141c0740c0140143c66258005403980c50415900300d0714070a40d42d5002405002c049001e03071703201c1d02425151000300501c1c9416a195509088a9a680d1114003404100c5c0035141e0300ca00300c4507000d190300c0070000e03100c1c0c1018038180a9040c184191500410071101000c00c042c1040c0040d60040001a40d91a04c3d50700d49803a0703d68004c1014200341c0f0303003c4c000c010342100c4140303103000396004500550000505614000d0310705001d80d015000341046400821a07520110f50000e048420740d0400300e28040408070580c4140d00800e01364100501ca4000031030802c04d41c0030f03203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 713530458 1250 713529208 713529217
    0xb070533040f2406140d0f081c14150102150a290301050f1e06031e21040b0a050c0c0409080a1404150509030a140a021302130513060504060308 63
    0x100c3d00500c4420b0f2640e401c00c070b0300700380010460303045803160480d180818917400e88001c80341d000b0261b040c0b030034400d51807070a42000702c0c0104c032030f80e15190f056072320004040b29055503108601411341d0810021500000b92120031604200e00303035140000102e80c02800f107512000c403088081c0218042da5101d086e030000c40280c035444080c030951811000a0f0030301100b00f16140329210010315561000485100040d40c444060800d60700743c8201045444100c0014543e40a080d20460080284101309000c10501c460660021004d81e00c0074041004103d04d684180d8003858114103120f92140c501c80f0f6505d14040c00c1a03c0954410f082c409000300303100642000741942400d617a1221000700c2c0380007000c0c1041c41948107070414031320b03411981d45400d8420000351116280040580b421280b158039100784840040e00011201e8201c4070508046150414042c04800072102083d42018141101c04140e10f500788a0340d405040b0480200110708400c0d408100030303240041040007100c0c0c50f401c000070960030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 713531708 1250 713530458 713530523
    0x908160f0b030105091314010c0804020f011106180a05190308010608040510020706140c04060906080919083a1e20040b070533040f 58
    0x1502030041881031400084030f0680f80301420f003d002d0f403240c0322944121122150160741d42014446906805507081c010030307403800d05607a9420403d04090040140540d401500b05060254980a60b00304000208003540e008244207003071710800c0d8000c07681038201402d1040080a0780990242d40140552a04071484091300a55072415142e8070350b50b05513130003030040d13602519640c0100c40030340320000e003074000b0801c02d88100340104100c800c0c00d41000200e807040e40c803284901c6000c6401e122550b44020100001c0007103103000f200c00d0030074401c2d160301c46001860f036402441ca40c441c80428026040f007115120325641c02d030039200e10300c0d0034481000303400244050740c00e0034064003c0400010b03a0b406403100c07501004a4901001125a0159005080c2540a4403501c06c2c0a071480560a400300c1c0900010140c00100599540c1c403803512506000b070849001c61022018441c071000340c85001c5444442c900e0441d0f08001d203484a050441003a408140c0c01820040c904c0c960800340a01a00310850380d00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 713532958 1250 713531708 713531729
    0x110c0624090403210b120c0103050606040e0a0b0a031713052d010e041103040c05010c080708180d030e030610060225050306280b0906040507090816 65
    0x80c800d0801c582604159000303000509075144583c148940540c041e01031003100200060310128031030114900e1850b00b0101292a00715008600c05544c040c00b896501440445406290a007481a00e1030428001380801c43c50b00e540711090b580355201c9030341c018080e41e08008041a100781c492401c00c083c0e484201044042d02e00303840005031904180340da04003085180b08490729514100140350380d0030801c0760803603410006121070201041c0c807107100b6107214455202a80d0740e039107001c2c20000c0600c6842e03880241000840c18902010549503801e40d0603040d8040300d450b40d50980640c182011010f40d0001d01d9205008031a044101504400b90103038032002581130303c0355680c0c0c050420208603000c1c8507031000f50700701c0504070000c06214044082c000600c080c0101016443d40d0100f0b190003012240290b0010b89103103007589120404110b015404000141070028420b404040342d000a80900032a02854039480850003c90180300340c45c0140014900302d500354898003842c8481c0c14103600c0fa00704411f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 713534208 1250 713532958 713533021
    0x3040c0f051c08071704090f180f02091009180b0a090819110a0b22020d03050306040e151f03120c0c03050102040f060f03051306110c06 60
    0xc0c2040e125020392641d884a0012081d00951510f901a41c814a03080700c1c1c02c01c8007005515081c03a050050806001400400a000880400080304681c0d40d9001500484001c24221002800e0359544192159042c1c41460080c0c8400c2e4466074141902c1d0010705641e4101801c7c03a10b0315544000c100e0180e4020381c01c0380c0031074460803400f0003184c0c042003001d8180c0404002080c00c40f205040380402a054502d440050032910100290030100e440300100e8040c0340760b07400d0007000f00050254030380c044820785000051810a40c00200d5601c00100000c2c00d0044c0840003440380c3d80c8981c003000303541c882c81054500043d0280411403111404950840380340c0c2c0604281c1d0046900f0790440001c1e60360100c1421444901c500c020740d00c1c080c0c0307400103c84004042001000040082c00980006c240c51640c80c0b051038285900904030740b8441101d001014034003400c0001010000340c00068045e04a003000a24001920b500203d5100b00c03180301c15144111000d02450040825108801c41c0044c248000701 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 713535458 1250 713534208 713534219
    0x10c140f1e191e090b1e0706020403050d0819050711031605060a09170711131b05270423010f09020301060f08070c1205030907081617100203040c0f 65
    0x111070303020032500b00151906100744580c1c17038601c000f4079001d0b103418403044a824160f40151142d0f8441c040849446801080800400900b001201031102e100d003443d8660745400c0d04500c0381800c00c0c942850001d41c44a021401140c000e82c452001600c0120076299281c01414103003801400c40c94084503103100301030024104008900ca40d4414541c00301c0500650000c4142e0702459400080094441c2840741c0748918440c0e40e03d1501c8040c4900039480415002c40d540326061514514604000030f0203801c00044c41c17084403520b992400924511010381d200002d803c0450020110110b0000030407a09041c240089054681da0b68125032102546000c40c6481d40e5418050740000c0c07140c50003055010320500302103400b4070a9690b0102c074603d0118601445500c030414036031440d0b0a00ba010450000c01c0c040c1900301849500e014201c184028001d4032958124030f416440c152081036548203600c0c45010580354240820502c00e40c0f454400d645a04250030640d100b1040c41c40b8609d94494500000681d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 713536708 1250 713535458 713535497
    0x71b0608100605040f140f120d080603120d150e09070509090106030c03120c0804030c03021e030717010e03030702060108160e010b1b010c020609010c140f1e19 70
    0x6a0b00070081a0096070f02e00304d9034051b1040342d007203450783c0240c0e01e81d0700300020b0720b8101020848801d50b2000b8200005140e002819460002d48118003d0b04041e48281144030540115594840305510010f01015604000c400036402d642042c90554110310520499040c0000c1400507514100c506640030380741c0034036030340c200c8103a80f0004140da8240e100c02c102040b1440180e400301c520604240e4400e4000303540e0000d196004c1c3c0c0040301e1250002c1c205109605000040c40c4400100d01d2805841c1800c0c2c0c00020368840161044240e036000b07580c0b200910080a400c181d90301d20386441200e8503070034132000103500d030700007401035000c98403403a0190100c011000720140100c90861039800b0550b404c0c446054200c0d40040041c0c84c1fa0303541410181100d510902c2007000121065001c2e0645061500f41c40e401e450030224103404100e01c0303208010600a40800711814510403007521917680d6002942070800a20419a540f0602004648207140d03c40490701200e40103c150303a24400c14007440040348 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 713537958 1250 713536708 713536717
    0x30f01060f06020a0b0a20041212030212010e1f120506070c030503070311040302030d0e09010b0421020a12300c0215130303090f0e04031202071b0608100605 69
    0x900c244045d10205200c03020742e5004000d460034602c62034440c0403514600641e1a0b0095000203520b000d800703580d0301404265101d108000040e032405502d44411b130080407480480600600c07481c0315214010034455103050194207052411600c041e0b00d81a81d1b800080a5001c1c403640030341d0f032030003624005090107100c4d00c1c4001009074152102d80c2035440b0b01400710010920100e00d580500002c000101c0541d50030401c1c0d110320185a43c603441c0b240424418030658440607403000b4212074062006200441d020050741c180081c110310643c00c00c50f86400000c200908903171045444010750941581405a491468900d503031480f0000e089006e21509001450202251114005140c8141410040c50a00c10001c103500c0071000300c5091a05847d0b80c103940081c0ca500480104900030000c100e01c00000242c1801416003c507242018600341c0c501030b2100381002e0240b64440e41c0051301c0410071119021120181000e500140703440f0361202400b034001c51060324a29050410510f000461310b06c01c40072034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 713539208 1250 713537958 713537963
    0x140105010e13030c050a0c03110a14130f090206122203140c0111030c0705010f0e0d0503100308030103061e050415020a091505040303110c06040e04030e030f01060f06020a 75
    0xd5000b100d52800c45101640740d00480700c2d80500c2d0083e001181c0c208a01c100607501450b00c0008604101003004012111139211010080d401c50501410780c0e240d40c5501800c4000300c0002c50310740c517107035050f00c0180001e80b0020350044020440c2d20321118000019403283c24064039174088450880419040c91110002c005c00013018500c6a02086052001420392803502000115030b813030140d003562900350412940031030300b407001150400a0040900a40104031b001210030000400540001506c0e803d07a446890107004000011911491020241200840d00310350700680704d5840b031502c02d01400f07820b2041d81c100700448048010150342c42c81024011b81e400051982035180d001032040c00b940060781c0903402d0040d12040040e0000d5000d801c9801c4080c0c65071243d80c0d0300c0c1103141c007411300c030038001d030f02407031a031004609640545400c801c403400d40d030b517020241449980d0b0f464102d8908400d401c2c1150540529144102c0d18a01500500700340c0345160340403040c1c5500c80320126591145d0b20000b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 713540458 1250 713539208 713539231
    0x50f0907090e1c181a0d02160c140a0605030c1b0a12030f11030613050903120f010303020607090e0604182f0d02010203090613030c081b010f020309090a18140105010e 73
    0x1545c20803c07141c0d0048c1401e200840c014400c11405880d41d154480041d1f100008603000c00c0f04500e264542045504040c01140c10700505505210807010030b40d00498000c07034101114409807500700c140c01c20064503411380c0001e0241e20402100401009405002c00030145139043c0002e1030006840c0e0402d80340714480142007203c040384c00881c42d0001c1e1001500c003280714041000580c41884c0440c44580c400c007100f071442d04a6500d10302d4000d15080d0010071110400c401d00205002190345c48100503003005007101c0224280200700100012804054001064003c00c81c1c20300c0c089502815034405c60302d400142e005080e050314400e002e8411894180280103030401c1042591510300400541040c2d016412200e20302c030b4803590364002010b01c03a042104960310440740c0c8c0c1542008604001c0c0040800c0c80e00700e02c1c500340710401030b40d28001c039680f06228218881c0040d03820b20181e071100c420072441d10703042941034100d420100b030411004400705586500740340010980700c0c4140403090092005080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 713541708 1250 713540458 713540467
    0x220e0604050601091503140f06090c1e030106021e0f030a1101060e1905070c0341070c090b012f0a080c01050f0907090e1c181a 56
    0x3000020403000700304506000e02c02d080031502c910700100c19070703400305541c078002020000300c5e0b4541c2c09110002e0540e500d41002408108640d00d50340c100f95040b10044006603107802002c58140380303880c12864400c2203500c0200c00007840039400208031981c1c0c031004044000c00440c1c000036584405481c0007118081d40f01700083c03002a482146140c8200ea80d12000050650310751507504148030043d105410700c100081003101c9403111030f108054000e5054100420010510364024101151044030003068060f10b40c0c0307500c502c035104045900804402000b0483d01c86120b07600d44069003054405480f1036500440104e20800c40d8840c140702000140c60305001a54011450010700710742050240310f00d49201c030800b004420070019021124881c01c0342603107c01002e0400d038215100200383c95450034101040c043d0040021903a5819900802070206810070450142407401803181c44414010749a04045415254414900015032510310504084941d071039819120010000c0d090b040002c0d030800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 713542958 1250 713541708 713541721
    0x302091e060d0206091f1101050f07050c0c210f030f030a02070804080a0b0114180a0c14190201060e09150a0f020c1609020a0203071101090302090c220e 67
    0x2003004120301d1004040a1905d025240818024840b044000841e40001044480315907001200c0151000b8241c0c0200118074001d008100185c501406d1641404400509010314040a126600c980000545045200c4038510300c1001440c4240f04094528014194001d02e00751001c02118091203801b4080c0d801c2d40c50f40c10121009512540c0100c0c0c0c0c07503008000008040109100d0504801c1c0640c054408540c9416880c0e942c2903202100540300d0310880746552050019064002d8000a202000040d000e50601043da01c4404e5070001a02c00d000c08a0401300c4004540102080a01c0c141d0081c09940d035110031030b10030b40005803403211140d040644075400b10720342c480401d40e0081280e880800c804c595150640102d0344194021516900450902c0300501f080345c00e404001e200074041180340401e182d42c001d440380103048000704001070491003c03200342c1c4030b4070340b800c05550000c009410034140450b102110ba030051f10000c6880c9140d0904944c01440c1600910494403800024410b0fa41c501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 713544208 1250 713542958 713542969
    0x160206190219020307020a05040b1011030405030304080105061f0906080903090a030501090b060f06040b092e0201150b070b0702011b0507030e0901050604121502130302091e06 77
    0x9038891804207500740300c40e00e480e1625000a0401400070340185130342d01100e005100014405420060249042010800036515002840c0c1d1441c65645030114060418000c1c036811441107a024640c144000700b000701c0c5591040d403000e40075103011140740c070680e0400c2c200712031070a00d004401c81c00301c1c1d107030001001502c2c090003403607030b1100c400410782e843c1580300c10018a0302c10305500146e5036a90354a0000c410882da4598981c3c000d1401c0b00c4503100303000c2031000603901c1c1c4102e001d202010070011507818015190000307990b5a0309013081a05041d02c1040500c40c081c1e48545d545c203c010b60802e111400c07030141c040c0c440002c1d01c0ca0a010b10b498085940c03603562500501822403001c566859091200d6003a140b0424541c0494994400340c0e1490b160500070040c009001c9030ba48038030082e1004120694403e003c44c2c084440200503030716808038504010b403290040b016502200350002402e00d803c0229401002c0c10f0341d00c09c43d20484c02d5201d11400000b0384a25401c80506000c0c09070101d505403800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 713545458 1250 713544208 713544241
    0x30c0512101103010623030a0911061b2a0d050a020904240216030c0f0812010306050f040507030b060a08070e0105010207171b150c06070305160206 65
    0x8140884020740d50801d140300480312998814400040040018041c0d0380e448a4449942007070303801036000801020300b045400e032001921011f50183d466004100300f000003e100d0070007080c0144043d842e11910407881a0200d40e01e02d11026a000307042e610041003190903411085038032004182e440070440380c4144003103a1030b05802581c0b144521f50070040103968550189100e03502c1307240c400d02c024040c502858030300c21014400380161401400040309102090006070105901440d0221255000342007000c0508424800504400d5000586503580301504a2f058104d80c07241004110654882c6084110880309940007440c9405c88141007022800560540d9000701c0c00412002005965042d100c3c80c0208035408064581140001000f07a0742e0180301ea10020b00d04031040d07090501e60440c4141c2c44034842444101988002414040b46498a01c0720340c0c013203071001d8515940c81301030406440e44c075a4204c0360000082c0c20680002e00480b0b641d180e044a00005400402c6a52910014908003071070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 713546708 1250 713545458 713545489
    0x1120b03070522151737052b0c02030303041712011401080a020306010c1527050f060606040e190903031509060b0a0c1103060f040c050103060e07032d020a0315030c05 73
    0x9481b440000850b0061120341c00a510303d214540c0ba98140301c0512100900324101c800034489041d9503d4050780b0040100c0e0360060b40060814200b098130300007d01c003030040d400901800440c0c0d200104180c41ca03041c600c0681c6000b601c40d800c0640d507202c45407040c1d101c126800c0e400a81c40a8110f400500890f1900010801620010a44000248000035096030040705141ca5101c800c100c102404024003050100011400240901c0d10300100824041c0c481c0e40305680031070903074000290201c410482e5148203816030401c24030607215181002405003500b80d66254518051140000d11403d9901c41c840441d0f56039100241407030180e0f1015510001580300503604520102d54202d1140da043c4040b40c8900c0314006002072074103103818540c5004400c2e8100c0c0b4141440c1c881c1c1440300710540700c13401d42d0048291801048200c081050f9408c0c15881440003034800c4a043c544d84924445500034141c15203440d40c00300138000e40340c050400c4d1802248005400048844814441030410300c0e01701c0c04600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 713547958 1250 713546708 713546803
    0x10e030106051c11030601030f08210f01080631110d0b0414060f010509040302100908030a0c1809021e120601120b030705221517 57
    0x1581c0e840803a9580d6029265488250841c03001c0c44200100f40448807241c13001074004001030346c1160b88400045408007800b81682601040050700f04041c0c01540f42001002c2441c0c84881c188940c88000342c400078060f00e2224041c520006006180b1180701d260807212000146070707080c82aa1040c0101070645c00141c494010b40450460300307840380300412814030b100311070360003003032030b05051400b80c0300c50b1590742c4607143c2c03c0501440f2046025517580740c1914400c43d09642151503c6ca02a8a008042d185200409050200300c0050140b00e00140d07106289010042c0010500c004044450f41e1249501c44000001c40c3c20600440301191701a1052210001c5000803580920a83c1c1d510764120041d03070f10000640004200880d40c0c0721550049401c11050141f102420b8140040e844231aa402442e001d01004e17814081517418600501c42d000c451503034200911080588620f00a03203c034052144084422000034642010004e1361420040900034888049120442900710420f810400a03100d070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 713549208 1250 713547958 713547971
    0xa020c010906023c0307050321070e040b2e14040810050702190f05070e04150902060d18020307050a06021203070302070b01060f0e040e0706050d020c061008071e05010e0301 76
    0x20302040005084160040e0008c585540191000000000c90040720078100050710040c0140c541d0011300c01c00900d20101c034040381251002e408203040c00b002001100c1e83e111307195030aa400c8040c141a0b0301400e10b40e940ea2441c1d0a8413500c20410030b00c03451003140066800b1110381001c0d05040c0d0701403a0007204a105548240e40518200c0f0980c0700155000e03164610340c803060104005081190a000740039240c8012041e240645a051407548201c02082175645c5032800c800440d61428100e8410004190303003008008c400b048080d0007040f055104030700034440c851000c101c0d0702d840c7c1c05a40c2190071580c01007a148408000c21300551300b0280850080c07540900101e000900ea100e0000d029122035038641082040c0844001e040202400500b0301030307460451a088150404580c1c070084c0c1d0703c10300b4403940e5250340ca1402d200910444411801c1800b42c00140069003081d5500c0303c04840012003100d4089444006070302c441ca5020141c03044001c201c40c070800103540181c9440070a00320003000020903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 713550458 1250 713549208 713549323
    0x70506090d08130305030f12060301050103080403060e10050a06500a0312031d0d0507030e06040305010b090a0204081c1e0201230f010504021e0a020c01090602 70
    0x31a00b0103c108207c808002c80d550584244482d98136a00150450003800154510348810b04144907d00002d40080d40302c03001081950010010509550060b0300104554076241d954003006210307500070b010540d004003c45024104228130340d050940e9404991040c17405c000310362944001d444040001085004508000065456411080c000d50068604a118504083c4001d08603400c007440c0c1d01000701699000003080e90000359640f100400c50500030741e1100c040c107040e28409810b19145074001000039000c001c2010641240150100130f1b104d0451b80d883e540d11040c00d0780541c0c0525007065014510400c40c020518148031650007403414000d05900c400d04001540f0a4030072000b00c0940e454410044d054806009036528201070042c2102c51414038442c805603180041c800c45129940224107004054409000e044c46880311404003951000125006074542508442581c0402c904000008000f400865940010405180c002c40c5220044a60903e101207292100454100b95803a1611 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 713551708 1250 713550458 713550463
    0x30c13180f0b0a11280909020403080a02070501080f041101140a080f010f06080f0a0e16060e04020f0904051909080d0f02090307140301020d020d0905070506090d08130305 75
    0x41041c02100484810300e88030442100f81d60100181465030401040001d8290002c82c5020440e4017641c41049032441342c2040840701d15400b9042600984c0c80010000100a08000100700d656920307000d4900301c940d1880150f50703070710045840505005492000030005003000500c407023080e00505001c1608036440760301f4a16a0030400001000c02c4105d800d200d040c10400140500410000074240409030070994018502c01028109008270a52080420030a00d01c40e0414060300b400c1c0d038219412803680d10850030a001c0103115070750101310307090000e13801c60030306008440c00b942520b400b4901e0941c0100c188801030200400d20503070b164540900c40c1110520307015028860303006102294a0b491200e4682e002c03500c200c035840c91018070400110800303460100d000021599210704403200065190b01203800783c8030304141d1800d89880000c032003461045076030040a2046c0030700200c4005942303601c1440040d215031101c80d076200041c90220390010f40b0000003070550f140c6407580c42a400b0703a03e958032803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 713552958 1250 713551708 713551733
    0x3070e0703090807051b031b0d08041220010207030b060607020411030a0204170105151002070905101401142205030604081902010b0d060f021216030b030c1318 70
    0x160a5003207403286411038018070004046c0324000f1400f408200000e860580c0109200040282c01004641108010b01000380103903802416850204555461103161400032a14a480034942da0300802c020342009510000c0c4100a8035442940251582ca580c0b08000150700103000c200da215031101c025600880840380910301a1012000c05030f00d96007054040350305841000c42c14083e90b8501810444141d441e0144404140c2c03040d0b0710004110310244040782003004035040309181c00e04103824041e412110030700301c1d0111401c1420500040c07445000441e40c0e05a450603c4944000510805000c030508150b0803030a8170058440141141e580c80c0480d0070301c1030840c1c2c145c41e40a40822801010311000e103c11180e41c50390f2000700492080000000c0c10164103c0c0007910300c2e651010003c11440d240c0d4115104d116000c544d03070360300d8504031840313501c619411054000081e0030041040280c1c2000102e501502e1801041d1121010060025000500c00040110011108440040d020650185116 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 713554208 1250 713552958 713552963
    0x402030604060b19170d0e06091c0501051006090e0405060115110601030506040b16090b0a05120f0910110f0c011803260601051606060f060302071704030203070e0703090807 76
    0xa00140940282d070a0800090364005814804038500b14030781941da603230498404840881e201000420b1222103403040c1894540000d0856283c601402000e0043c2d050075412184a50350391607015844000c0265403042c1582c1c001d089038002001800341c3c250b4500340700e0060106280c00c420078618000000e1031702c1802c0e441601d254100728107100601c17860200301d9501c200019480c0183e01c184400c000c01040310352044006048000c188002c1d658840c1c2c00311080010b0b83d0141c10014144820182010002a1b9202465205040390070780c0419030360040e107200c03100c00c1d01d41906003554403101200341d9100040722070b07195503074800465240344030042d4020950b0096454500e1501900c0c21401c941ea26050790045002107141002030580e80802180c035800500c242e0040030221a240002c003070242c94004200c44034a40c600400e9481c0d2641c080e11401d03000350f402903900c1c0b0842d42e0620f12803095000180d09a00070140c240260b141c05208603030040060b00d40014500b09a4480c1c004a40007038004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 713555458 1250 713554208 713554229
    0xf030a0809010b0f0114090f0409060209040b091b03040212030c0f0705010804230a05030c0f06060d0f08030408090d110906092a04031a010611060402030604060b19 72
    0x1407021402003446286902e000544101e40a0802e0301c001070700803180c43c00d020301109000904100c82e80c48200c0300f4030200c800540700f48280380c048d240800203900000301d064001c6290040900d868540150740074059810720f50400032280000c2170140719940010801d981085011240060543c001c1000700400c016800140101c40010301101c2d050800e554011410801500c0a02001c5103415082a11503090f50744542524021900080d051500050740034080780404034803940552008070703e403802900705505503009940e8040400640b2030750790380080c10124003a0f22030f500141d4540300079500304d8010484139040019800002c0c41d155040c43e402c46820340c8180c80840c039800e05840702904001c04540d04170040c80c00160040c0c800d820b070501071501c241d00112040c00b60185800321406903803c0900500c01c0b528000198001d02800e1041ea40010f041209518101201045450280754010050802e80d151501c0d03040280c0011180d00c0d510100100303691016540c0f588160300204a0082d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 713556708 1250 713555458 713555461
    0x827060c010c30090f02030f0303181207020121090c050a08030a0e1905031e070807060507062714060601090b09091b04080703060b0f031e0f030a08 65
    0x80007824110f8861444400075840d08000e001d5160102400900710604100002d0ba11010300b4008012481c00300041e4050141d52641c03076600c04d021006520440b01010030840c030818403d41039680d041c428a200c076203d030003030044200540c4600000300303011500205800300c100410b55050300316213810b641218a4100d494040225041040c810341c000c1407414051418501002c0003e001503c1400c403240c4640541101d1000711028031560350040c210180c100c4081c20010b120200001e008100160254450701000290140c40040c42d282030321000d0341c7da03604011655441c1409819400b01c0c15003091528518961003e100603400c4080c2c80c000c0d8450800820014a054202607015025904002c07441c0c2c03050050040c050111001c9460998241e0016580d11030419200e410320403183c2c11064000900041901e400140441903e01404003084103107001810080c2c00040f20040e140c064000803003118040a007983c0e84e0704003240540a884072408245a100c2c25603001d9001c0102081c034540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 713557958 1250 713556708 713556731
    0xa051b071e0510122003090c060a09060503090a0b040308060f010e0d1403040e130c09050106090504180204020a0f03112a0109021503041104090827060c01 68
    0x8a1205101486514003460404011803c4146100500018820070345002e903001d803400e80c0098008103600030100301d2041c0362405c000362a0301c140d40c1001d00b8400d1010b600714500d0600e0440780c25004589070f2000e40ca16121301515680c200802c80020b038090315007848007003000d00e01030300e01c82d07846560f911280c0d25043c010400b82400c4108410304105a00000f04504e03115010f103030030241e0304001c41d02c3d5964840001c4c907165100d6500188100400c000510400300340010f00c0307086d582d20800124076003d80b221009000c4510074420640005c906002c20401402c1944c00441d81d10140880300800a02540100703080e41d0010100b6400a401c5a0f100c1890369032501c02e81c803040038840e5006280218201e014a0080050f0400f0042e50100048fe00703140e20007540010115a400780c840d240d000e0850003201420740040302c1c1a5200544142c060641d0318007441042907696202101d82d040401c00031040040e40c20482c43c40040c030041050008060b601e82003c0d0500682900c00828030000d00d2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 713559208 1250 713557958 713557979
    0x3120702041a1003090f0525140a05060a05070c0b031503030403020d0809011b03030203072007031419050303010911271f02070807051002120a051b07 66
    0x411030341c1c000d0b0000c2c0d20144800d40d550404034400700030514000ca0380601e2814004101a01000c00130020710940510040d4002d96050000700d00000034540c0f000d1a41d07c00aa203440d4803901c80c010f40c0030003840300a005900d8480042c01c1d80020300d02d011800c0c0307480c69a6403c103100d415080483c441a0100802030040305103440c038004040d055002d941050303c1c550105840c00c0d6000001040a4404100005981d00c00c01d94610344074444400b119540c4920304000c1c000703500a490031000103484c4240610b107100c1c1c045800c145416000300900000b1324603118034442052114808040f4054601468851070b4a40b0419607210300a20166a99500d0700c6400011200c41442050600400780a000c1c4072200c5421805007030540d40100c4003100d0074420005210042d0403181886c030110142c0c014004540c0016442c083da040a401c98a80580b208200300f20810100f128400690040140c3d2045c400540d010340094406420518201304401000765000e45020207040d01d9580080000c000e043e400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 713560458 1250 713559208 713559221
    0x20f0c0952080a0b0f0a03060b0315071704060b03010c05130f18050601020c060304210801121407031212110f04090e0a051b13020331020312070204 65
    0x21100300903100c9040d00d000b0300100d034000d040c40700050b5581d0b200041038941244900084100400741d6021944030700d80100100005035075280070344280200803000f058200b4540380100081c1d2511144854030010168000c01d000b0000c80c1d800c0c0d125145d6101d944c44c00d010380e0600344816164551210545102445d100450754810980e04070304c40010440a40b100349001d00903442030030045800e507510801030b89040038044169800920020400040c0000403031118801c554040e049915030314842804c0350441c10a002d42000a4100d10150700041e03c0843e050704004140402d407801d84d5a2a00d902c42034445e0b04c4a00d41c04201d09c4400e8407a254400c2c42901c41c0c8041004819007414114000c80039640114091a8012079403404082c02c907000030803800b1151940081110f00d48038010821800d555011030000f4000c2414004000611b03001d40262071042c05110b000108448d0784546420410030b00c41c3d40041401e10003010440545c5040c8522408034003a20f42069440701c00b0b01c11700089812 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 713561708 1250 713560458 713560591
    0x240501022401061d150c0120090d17030403021c050a05040b160b01080717010e030724060602011a040b090105060d0204171507020f0c09 60
    0x500d1414901114a0450700c9055070024684080300002501503050f81d159010111980318102010005d091848000149489501940248001880400c80403d145554440b03003200500030310101201d030406440300c0503c140160400c0c168000b14901001280d0300c00d64040c2c0058000e000c3c24a410200c0c2640c0340c030a07818034949680390941c1c0e020010640d0103a4003514015640005240c0710554810210b512050b811414007052035075500050399641741d05220314078010307a01d00d00c5000c8880b0107106200c24440c4440146182420710790350403012040c0b5980190703c0300000060144422594031a41000e013402d900001141c0c2c0c140100c1100200c1c4018003544a0390500803403030480d480d0710004030304507541130310300a071135800c813400c00c402a000710782003d80046040c58005820001c0001c40310041402c402d98058540c85421040f616a10b031403144c1040c135801068071a40380c2c205041c04580c071038481c20307044004250616200410000c0005a00d0130505c0c03072141440543c03014050b149500c03c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 713562958 1250 713561708 713561743
    0x20106050306041104020307050c030c0c03060702030a08180102040305030a03060302010e0d151509150f0b160f0614010801050603060108210715050709030605090a08030114010324050102 82
    0xb83c5681c800340749402d13440e400c9010b1034010010407405801402950180000041a29112101c040d4019550702e40c203a020380c070074420900455019400841110844129035960200e6550743d4a0482941d07640d090040c2c1e402d40d800c210004c04240140090008540c4a0380e0200d107039450350000500c422402851103100d0881060402c0c0041c1904401703038032894110030042030031034101185400d070111940c0105051400c1c0f540d40c0400c41c40c01c6000760160342c0213890b001d8101c0d8072030550f5413107800b582e402e10f02d161002000103070104282980070211184a0300700420800c02c0c82910782c02d14171082c0d210480a0391038109108503864140000d5001d004107100a019003008485100800c550414540350b1036400003803000148518000d031034038081c06156051129007444500104000c02030700c01500e10740c0c1341c80b001c039510710000705021040c56001085c160940e42450125050600c88045c014189980e4442004515400105e0241802400411400c610703107803100180c2406a40251030071800d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 713564208 1250 713562958 713562961
    0x1c060c090e0f010e0402010e033d0b03150c041211030d03090804060c0302030c070815011203021b010507061406010f09050a14130510090f05130201032712020106050306 74
    0x848820203071394441e40905e41a11408c505502003410070002e000c10300407180c8000140d034102100001610421000030301000314031a0f03481c001c03900303c840d82d0b038080c1c0d4960400e10061600209142140390003000041c107240c0307095070f5140c4001484000c00400c650402d50207509401c0c5260030701120f9103030919400c0c28820901540e9404056101d603015510a001c0c0038143c0034103140c030030015507a084a0f80340c21218150340740c021031a600c0a40d0445000400c80d144004120000201d40a40c1030035410740040011100900040c400000d0b009000b60410000b8800760707011601c07034015420881d805070380402550400740001004010081460000c0c451500b20800003a19403002c4401254410110900441d40750000110721205585250458605200510070700d0701c0014032071000c841b00c4a404000301c0103a0341c0000280e4504480c5020402d0f94007100700301550003a008103041910360496402403007103d034120100c2440740c3d001585c207981203a42d2004410b40900c241409007004074014002c1e07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 713565458 1250 713564208 713564219
    0x1270902010c060e01060911181f0311071b1802040513050408091003061e06120507111911151b031207050d0f06141c060c090e0f01 58
    0x1d0b00035044006102d43e568103000b544d4510291302901c0030b4913026400b44030b4248100110a60b50300f02042040307000484000b220721920342003000c10070315080d50744d1607c264002d5401c15401000b0054074030b07210382c50810907640050440311a140c829890341000d0038025080500781240b10020581c0c0340c0b0040d10400052140d6074030106070407a50280303410081131558a5240003011801980c0b60a0f800c4242008040840b0f905600f00d041a41e4030300d11008207410035503030030000000e0f140c883c5e0808038107041c40b204901511904619403110b11824090307150318000140e1407030103c10038060300b5025402d084c0340c420021240c0d52400000402c0392114207a204510070481984100d02815898102d40d0300181c4031940c0520542d1700140c000402042c852409030746c003904680c02030720580c01d014070300f007203080c682c00080c8035000030b07110128202107074840800c0611030181840d0302d14a9107100e008603170702c0004d44503000b510f851302c0c0e407540c0e42120245400ea81c0140700c180a040080008807140041c000f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 713566708 1250 713565458 713565467
    0x50105010207080a26130e1f0312021606090e0a0b03031629150d03020606060d02040b041203120506010c3324051c05150127090201 58
    0x180740c10000081c0d90640308405200302c4002810301c19400d000205603c21140c582c486d1590460b403407120f81c2e017146e6032040c4226042015541007400b00c00b203100700c148040f0b000401131040803210350045480329030003014030300000e00069000e01d00140360040240068024214520b4110a0202d4140302c4228150002604c03401040781d02d41c4086c0d4603140100a0003002130000302c02049401040032651105c80c0035000c600e0048420036041d03905a400761025091000c1c5010390507416902801003031316801d0800000f940103402241a00e9001d000124141d12071000a20042c220701c0b201681c0c03041149005440e100340d500c03078007105c41c1c60041040f02a1342c01107484c007002a44403103d558a4400100d8501c5001d007001d141081e020301c03040e04111040416030241d1100c100104440020300044000700c4043e1400c1e0207455000011124421411403543c02d072084614411030035a400310203084911114650f090380709860665008410302141d46902030101c0c00c015501e482400100c0d00703500082c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 713567958 1250 713566708 713566723
    0x50a060503100b04080d031103040f020f01023a08040c090518100f060503010c09120303060e1302090a0b060313080c0304031110020c01080a0c02010b12030a0305010501020708 77
    0x1414000300000081c0e072644a1000c000290455000464949848a00b150740d950310007801c00002c6494407003008051000182505c0c0f089500c60b6502d8034240c5d542d824080304003910080c15065100d540006143c0e40d50807030403038443c10f540307640c0f40c10b1990080c3c0260380400109520442400700000a00000c035003411112802e41340e0300c04000c14203848801282d090009000c2c4540013501816010b0040c03508542c004e0703560754082190500071142c48604050807a4081d00c0281e0100308401410040703241e110403601d90560003800c0001d60749a03a030034102c8500e80c0c1100d240c0361102c4007101c44000c51400048058100d50425002c1214181200c01700300c0d0361001a00c1f681c00354071106045400c0043c1c05044400b264480d84c1943d03101c958a207464010810030b0010184245408043c0b104854030000b001d074040340059481507071984581040500a000c1d41400c40d045540301c031641203954070340e40101c3d070460807210001c40d56207440c0c0f02c00904031601030b0800d0f0b045400252040280180016070710 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 713569208 1250 713567958 713567969
    0x150e0604051507080f061504060f03060f0f050f0402070804030302030a0f020102030f0f040c0f09230f060d0c0509070809100c0f050f1605010912032702120f010b0f0a050a 75
    0x111041c0c44400000e42c0d004400c2c1000070350387c4400900415455840100d040480d100c6490a12035141c4692201442140c4c0340900400d85060f031204211a1070195030a140206001d000189401c0307454481c0d0441c1d0b4003a80041d40960720005005076a1a808418903940c1003103071008504506204030203200340f800c080c0120082da5000c0c0085014440c194008400a185c01c1502d00c510395910110140949005240d4035010b00780e9105818006001c5000d4520031404580e105c60f0941c0c1d01000c100c3d8400e2050000d0300c1b11801480049109d07210036912b46d01a00e51610390701680d1510610145c9004412500c060b81030781404807400c0640d401c02d8081101070550300700540c58088042d001109070040402000200440308c41403000d010065106004190041101c200c100107160420380503121426840c0c2d824041e4460001500181251021a40362009140c039441d010030191031458000030750000043c60755103105d9030500c0c1c50021803980b03012500340c0386528023916000000b0362680d228441c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 713570458 1250 713569208 713569231
    0x7030203100b0a1206091a0d0503090d050715120b1801030305030c091e04061508070507020604050d0606051309020f0d05010b030706050703090509061c150e060405150708 75
    0x490a10500030700c40d090711013480074010405a60b0b03038404032006d0181d101000401070000140c50405050140ba90400d107034221004529100c42c8a041c007000100e0030b41c2c180c07110300a0100100300403101400400d07138010320780d840d00170030012082c1100c110b5602c00040c1d84200340d6038020002006001c0d00190440e034050400503100d0703585105010840c4100c144e031303e0b4407151104c14004008405245011256000d8070104245511451154000c032412640140400c10700800682000c8c40307078000f010800d2000d486c0034101591480030408100c00d8810894140d51600c0d01840f807814440f034140c00d020800039050162901c80d40100301c0000000c2c200c180038080442c411400c0c45804d42210404603809012265072641d200001000340e00038241c110300003200240d00141c585402401d40340103140c02840200c288030b9680c103213107d60140070710443d841a0321480c00c110300e801e184200600c00364020061704c41844c0030310b070040c100b075885900325015011280912500070781c80700459501c000800072 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 713571708 1250 713570458 713570467
    0x14150f01081f030302060a050606070221011e0b01030c0509010f08100503030309100c0c110d14010519060812120705041511010b0307061e050c01111207030203100b 72
    0x185426200600c2d007590008000c041d6002040540c0055000d00c25007071000c04000c1501c0380300800c0182e10500d04041e501028031100e500070700918056400440010100001d6a2922400c03040115860518400c400d0b95440b603221a0550700740c02000f41205a030b1030802d240800400000e00600c080600745d13010005007070002a00c2240c40306001c4080c10f801021240c60b45007440c152599036640c20103900d4514200228091043c0c0600180c800300355115201e40204075506050040c241d0f07180400360303a190500b030401000c500e4207101c0d40d0300814000c1c5444c0c0f101c124680c04101075035070720b6000c0c500340c1d800143c907113584241c100195505020074100c0811191649081241c440c02160400303a000c0f1512011f4050b459000741c0681c1c081044000203100024030a0105601d8081b54482c40010806160114001001000c0100050031080c00c0c1141400480040ba60846901c8518412a8100001c050038003000c16080d041e81f141e040e10742036165140031490440300c0700c43c5100d000f09010000c107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 713572958 1250 713571708 713571721
    0x1b0306061211120103050c0109080a03020c040c1b3f0c030207090f0605040c081509060d15020304031106010602070308031306020c06060f0d03090e071701080114150f0108 75
    0x20116035143c0080c03035142d40503584a0501741e441c5c06840c48071303030301294685500040f00107001c1201440340b509900546044076452041c0f0001d8800c060011040004000d0058114006a02e0f010a0103001d00c42110034860320942d24070401c01c042e4035005000410000240040510352508a20000945808403549146150076450b05900c2c0d00301c0d0469900b018a0b9a81d000c0095001c801103401c100c2d424080c9a080b40c1060311200020b50703500f82c4040540e919a107072410b0806041c0d41019014101d40b0303680318184c50f40c0410341100596900040d07000002e0000f455071262100c103075014a00d01501041d40b501201030f554003014800180042d07800300005902100101d031a001032600000c00355500c4224849a5403200706c200c514510400c0c3e42400116a401c01c51000702a4035459124180301c80e051042804200343d000b89890700f00000721440c04540380e0340b18101c600800ca01e5002140ea843c1218000043d10402019485041203100010b0116070302c3c0131243c0c2540c0d4003820001661340703c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 713574208 1250 713572958 713572991
    0x40e060d02040212160e0103090506060d140111071416030f1a090a0b0c0f0904050a06050324010e1e0703060807140306010e06030a02060f07020d061b03060612 70
    0x60300c0b20010581100c080180b812403580744181805125031b070790384030382c000f00c801582221010304001d0559404034002421504041401d50a018000c003140850707417400c40ca0f0349095940d06498510110f034046030103020041840c0b042565145480c01800c0060364050342c880f0070f41e9580c40003400b540c52448012044c404440248403112211380c0c1504494684099125540c00100d01c00f2500300d0010000100c15030684000c2d6111041c1c441005880c1611200400000d441d0140c4015811981e56400107140c1e03608002608560400d104200ba007520316a0710280d04080c141e06c80300100c08031004100d5032000584649180040c84c0c0383c640d0303151701e4007102100100324bc1c0d000078982d84543c4401060b100f42c850a06518500308800b214560381c1c83d40b0500641d4481501c0040c0c1542c005a0341c040149080d00c040c100c820900c039144d40c10000650002000002019004e644440d0f644020755001d003007681c0c2192900300213007424003205251410007401c16460150001249030346994100340b45200c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 713575458 1250 713574208 713574217
    0x114090c0a033c0c02030901050c01140711070603060b093f100204050d1421090a051c060b0a030b040c150c08032406121803040e060d020402 62
    0x1210400d001c49091030f6011080c2c1402c40d04071034010050034460503000c0560240c2000300794140d000d1340c1404100c800550b1076801c00c0d41e214002d5500c4100c039a001d605010755045c03103401d4a03a104000c11031040625401c02c0001d400c94410181012014440b50030307084201e81078031001791580442c4c101c56126009803603541100a064050701846184490a0303015401d40b480c0e04074805460704540914140f0040780b10300e2042c0f80e003000c104082403000c0381c401e9140b0054001d003c815241e40f050082810740280c2600c0b27100500d901000310b850149420f107034944c00054401aa44c000c0d80c4a01c641c2d0340c5600c2594040c0c01847c968480541a40c40d84070350400200559002004029600340791419038404d00b030324019a0740301e220104c0a0a9404e109040da0034285801100542c5551200040310b2003501021000c400703507010b13605503269952a2100107002c5272010101a181d6801c00c10b002c0c040c0c031110220701c45490f40c4244001c4c0004200c005071260440c3c0c085414005419481c030120f4041c1c0038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 713576708 1250 713575458 713575481
    0x91507080d0504030e01090f150314011d010e0112260d0501031412040e06030a300801150806120a0f0b0c030f01181508030a03050114090c0a03 63
    0xc04a814601c1207000c0c0c11950150340f10b9116840032150314001120542c996104d0701503031040b100c9041010740580c04020007c84a107140200c2c807000503001943d0051000e0348130580c0d050007541000a402c0c2d4815800d4050b2020240c8840b00e545000025980c40b440980c000d40400e8141d440e19003034000d0704440401e2030780c0d11050152107900d45002c1c02c00a041c2480103a4403211585920541044c0c040342c0240c4080341d025000d8200f0b810110070b040d11301c6000341199054800c011420f00442c1900742c3d601303080c01000b1450030302c440c0d80c02020b01614044011500a1280c100010311807040140e0395404a003c2920344909035a0b142d00c000f540d40d03040c020030040716005128001041c0401d40d000400c04602654001016840f405101e60f11848115003803c0020380000c0180b04281c403644051030314440304000807c5651500002080c426025031000150342d00001da030344811030301801560f00501c0114201e2082d901d1240c007040c403401c0d0052000c00d0402c1c001031a100c80c81d0081d84002d84d4000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 713577958 1250 713576708 713576723
    0x1080613061e080105090c030a0f0302010e07090218012102090103140a0903080c0918040503070204050c09010f02070f03020103111e0706050a020c1c02010e150a0b090c091507 77
    0x150302102c074001c00290207071201c19420403000130020f480001c0d845510b40e60280c014218038031a5201d030340342811140300860441d52100080f90040700b04116420150040150042c1d881080c002c03424014010b800c005414045407141a020090280078035a2041d0380c2e08101580e690020780048005044c5030041c41859203011081c025119410790107848190b01c00c0c1c8030b0311000d03201c0c200a00e6250050000c4280c0c0083d12182c50784500c81c5020400c0c2d0445d1140c0100d9052550710760004041c0e5104461480d9600400f1603031070340369079000355410004001c40c0040d20b40e4a01b412011215610781d800081e06154543c1004419129040f0865040310300042202c00c1c440e0b1070415290103a40020020b0354031f50304150105003022194403c490b0000a0140145041141240c460b90ba100548480c80c0555580c1e10148402080500202404c542d17003440d071081e14907103154444103c440030010700d40200421400c0080611003d070807220140000c03183c0c244130010013051482a44661b400090100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 713579208 1250 713577958 713577989
    0xc0901270509070302040b011d040c120c020c01020616020601090c0c120e03060f010e0f04060e07170f01060308250f050a061b09030f0c0e01080d030606020c0108061306 74
    0x10000403c254064a100729800e11418a8030001100c0300d00b6003403000c04245092007070120b05803800b070f030040c00703281c00c9410170444401486484c0307030407a480006a003003d40c0000ba04039031150b90500140e98020700c00003441241da0550700000f9940c800502902071140e40ea0b00501a049010300e80380c03c40954400d82c1e840c203550401c82d008048900c1005054040e05c210400b2508071080c140f4103034181c502e0340a5814041d40c80c20044a6003240203003050391015501c1203020b21501d03040c00b08a0141a24004907d405500300254600d400280b44640003164074000e0b082c40024206011901c04540c0500c01121190404400199802c3c56083c024200841030420008121010411040e150700a65040240c0004100000c2d0030b840e41c18005c0f0300041403404240300040042e031181d8015070042c440e1080c20364941c0d144d410a08001e0300b100303400d42e00c4030745442d0f420340d4180603502c040c00c40d510281520403410000a0070395500034050f907108040b14440b5040d0141c081c1e010400410070200c452642 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 713580458 1250 713579208 713579221
    0xf0606080f0a0b012c2e031e030e010810090207030e10112808040306092109060804081e030907060203071a09031e0d0c020c09012705 59
    0x101c21054100700c40f12140781d00001800c820004009941d01009400040c001d0901c03c102e4014074001401d02e0390305904800400541944c0e100b43c00c80306104000104c1c40c03030707046051480324001c800307900a40030607960b403d00300043e600c0404000390a0b82070800406076103a1414059820741242c1000c02040c1c8041070400c2496840410a50184e0060310f8580100d4203c10702101c540c1d80201d4001e21030b5110710014401c4c0e038819010034100301c8031900c0c600341400031559001502d5100b40e1090b40c015813103100700c8090085a21001115040e2941031840c83e07000450094004a13146c41364105101000e80043e0074001c507207003150200002d114201c40f411015170041c08040c3c10076034085c1078074850000041036050001048503121340d04003c603651101c0b496440d2500c00d09004012032040e00080c890f50030306c03801c0441005040b440300180682c44168600042e400c40b00008003220031503014980c16281e58451480d010306403032607010000c90082d0402c10107900e013285030005a240901c0c10081121 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 713581708 1250 713580458 713580463
    0x918080f0a0908030a0807110c03010e060402101b03030f02120405010c0f0212040b0d060b04090c0315060c030804020105160b0f01060206010503100c0207030b0c1e160f0606080f 78
    0xc1d104a5110207018644503c800395482c06050a2036001c00c03010000b19402a00074010026071302d51940c111686050a0000703e420b4070401d50403089940c1c840001d11045190050701401c882d00a8a04500c40c0341c02986003000045104d240903040c15607650b054207001c411030301140c10640b1145d50b101c10b2810140340450007040c1500000300042e4000c0740ea12019480070420000818151003950f0a00781000802e54041e80601c0a0300055030740d036480010800712800c0640008c00d0351080002c0c038142c0c40b11024054600c2014001c000c0542e90400740000d50b006580040d03400d4040c5028500b0b9556440107036034070300c02c8200d94031848007406404010400820310491140f4840c0b0500c81103640d0750351050340c0e01e940a000d6698940c2110861042c03c060551010790418024812190038607502d0300c80c441880e806580046094000182c604046080007118010551200c010107180880da420150718a02145000402d002c890302c58905c2441556042a0094403c4070b00f031300c06521950032101d6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 713582958 1250 713581708 713581717
    0x804031e061a040b06030c0d0b0621011809150c11010612140c15070515070e040b090c0912070905090102030f160206010e0403200c03190c0918080f 65
    0x14826070500b4003c500c0303030406109580c020080c508503141040e42c2c001601029003008081c2070b4012100303000814000c4490b0400bc640d5000b00c40f0b00382040d5040c0602e240d0304c00440f0f080108100c0c14800e8100c0064081a100e40307040811100c00a0542a0f40001711100c24000640315120741c00c01c1c0c0c0104543c000d0b20b101d50700f210300c40c1010302640442402565160008141c400d64013411704c039401800060380034020301d10a803041c3c0545000000800d0710000206d0252412070001c0c0d05817440d0340090804d4400c5030040c41080394543c0181c60500450f103828451000901c1c05070150005641d204201080a080a402c5040701401140303010242d5500079001100c0d5000d0b00c0d070019000c1149240c000700c0c0508041844d50141070139a080c800e9501c26040040e000304c04201c0e507170b8074904c03054607000c204414000b40040605503000c5048105450a10700c907a1080c415160039000304009106140c0540845400c0c07400802c40014800d42198000071102c006402c0340c100040450113a18890000d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 713584208 1250 713582958 713583011
    0x90a03030201060f091401140315040606030c171f0b04020d0b04051b190905330c0703150b0901030b100b18090405070b0a030504060b010c0804031e06 66
    0x401440e41d9174610000d8403030301303c101c003190384401005009481c60f00e142d008004030302804171222078405284901112004607410703a0303440d0340e030f01051080105481e068001821201d66044030b90200400c240e0302c444c4100110900700c1001100c44501c13891642203a03071200d0006100f15181e0320f4030660740026040360754041c1d101b18900400a40722000d4803404141126200065900748030b4005620505115140002401d03c03041440c00115540c5010014611401c144508c040392440004906c0100b2214816207203140e03810f0040c0c01820034002241021a0740020341480d0002c040c61040d40104507541405807c83c40020021041c404005103140c043c1c0740c80101c0d2901290f4031001a250740c024150b14a0396000c603407480c5000da01d05002a581c0245c0500c065900303056451a4004d1580d000904c0c480120307444004000c10706c401c1d80329640405c0804e0030422550802c0b5619110640300e1030100902c075402018480d1001406c0c540061000340d4000d004000000b500c540b4400d6440e16103001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 713585458 1250 713584208 713584229
    0xe0d020a230f06120f0a09020d120e0102010506010228120203130b030114132d0501090923150703020d0506030109021e0102010e0d050a021e06070f05090a0303020106 73
    0x2c0c00c1241010412101a401c010007800315607200c460841d99044005088070307101c00c4d201c0c0d510401582c1d9103502c2c00403481c4107441c0151301030030440000d420003018000030b5055924181c1041066600418003105002400c05804c03010029001c01c502d908024001c050b200803001150390805c0354000004103811100003980300703805542c0762038404182c80240036440d40c205488020200f1410a07100f42a010051400d022400b82e031000303140101c40600c42c42d0811950300040718001045081d1003452301400c4a45414441142140c030b0b5103050f510242e03070101d07107102064001c02030b0341070500200c2d43c4400801004101414801c1c0028083e412400c0c8402c3e5441c42c1c640428507030f150500c01d5007120350b409050022a01407440c03906481001811846055540341c80500b48128402e00014407156102e07241d840c3c85540c100c000074a4035100c1c0b441081d04010300508042c885c1d40018403281d010030103280c840e01540d5400d8080b03c0f940a250070391600607030303007040c04002c05806400c2002500c45002a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 713586708 1250 713585458 713585479
    0x80d0b040e1b0913170a110a081b0307020913020a120b0609150d0201050d02430503030f1008100e1c0e0f0303160b0109050106030207030e0d020a23 65
    0xe09190400c03d603401001d03c0d10380070721040c03070148610250000030207c0c2404104082c094170000c1c18000111700881e491040043c04c1a50942c5400e50788242c0030140005504000c05a404101e4949014000e881441d45401c00001199190000e1402418040409030003103001072a10000c008400d8038000d01c14031905000600c0003046170848603060030000d000c002e81e5503142d001510141d1041c440303074506580800c445500482100701c10303002044691402851002080b54a0b80070080e0b112038244051104039000b40492400404d482d044500401c0303c10079070b12102c0402e9220a03481c1d12900550117580d0035000e50460303550103039000104078402e40c1c50907501585c24250100f1540381540100d8111140314000341051111000705c6100641100e1400c2c10805100142054600c0308580e0440c6040040c050300d015401100c0c0104081d080c15810903150780d0f00640307807000003400c582c0540106c0c40c06070300795504c0f4841da070001d2009120305e052102c107060170441000d084800c2240a04501c11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 713587958 1250 713586708 713586721
    0x30302190807142d0c0f030106090c0905130203090a030305150a060809010b010f050412080d1b0e04020a050f0903120307020a03021b0907051b03040e0f13080d0b040e1b09 75
    0x104c04026015a000a00041040c910410490031140c070065038141d0340e80c000100b000e0a0600c64a8000c2d409519510221454582000490341c01010400212401441072118400700002d400341c03184c0c0c3c14140801c0701d58030350320040078240210000039441000b8038000582c2c1c1d41c000c040603016406010082c0441c040003401900c4010300c0f40031080c0025400c000c00c108440001461007030365031003140d800d4900132820001000352502d500317540e004003030b003901c40c0040039400070300605c043e1400355070541c1890303403901010b00703a8020005d54501d5141d001403103d03115581402180d1151199401058030307410904c01c000d50322205101c0032030140c4104c0d03060040c1c04083c00007018102e0320007002e1b044141d40d024000c0b511508500c0c1c102d0452600c1645124040d01c007440900041c0100b40f807088034515140c006109200f030003605540c0355210410030700d40810450001c036000324101100220b8400342c1c40c40460000c00444805018600503464219052220000001e0310420100c1364400c2546501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 713589208 1250 713587958 713588023
    0x91e0812040308010e160206130c0e04320c0409020d020405010603020301090b010905100f020a0c03080d1404120302030618090a020a05122806051807080703030219080714 75
    0x403111b91000d648400c3c00551000c0c03000308000c401510591a01c18207585e0b4105501e00c510003540e0444d80d0340004605814446810301000700c0985451030300745400400d000c84e450702c1d04000962140525100c0c0220819034481902d0708a00380e5000e0010130a942c2e543d41c00034000d4200380140418141004014a4150300c51000c1806542005084500407003d801d03082d120b180340d080020080d4044d40c942e020200c0c440740c48000003140038007030317444c1d0740c8550401c0074044882c1d50340210006030551050001089400303440160840e0340d030400582c1c94580344000b4188070705602d0412299080c0c2000c100032014003080110b070051098030521b03e0a511039041002003242c02ea201c1c2810352006845540c40c03030106c44190004000b0722703d032200b074080130307122601a55011943c10703142900c00940d00100200422034030004140d130310302074842e903421a540203481d151142000c003494200d8498850601a248045400d1140d0203030308241115002c1c01200c0e12404103100048010340925284d4075012180b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 713590458 1250 713589208 713589241
    0x24140313033015030f030c0302010513030807111f06050907020102120c13090207050c15090307030303052d19090c171e0109020f04091e0812040308010e 67
    0x4074142802c00300185075140000380405080b60305203403420500000441c4603002800b810500170f03510710034915840c0c203002e030a45402920004055242ca0307414408240d2218516820002d9864006031084440f101a40303001c0b126026424a0603001e1310074840d50b800f603444030084850958224100d81e0701c0c07000c1a402c03406107900e0f90500c0d000a10018064141c0400200205247c90b1626a12151103007400740807a00112000c40b078503840300c114510300b03103410a0302c1e40300541c14116252402002d400401d442d01c1c00c42c07000409254130340300454155258816160380020039650601c0d000c0410141207500da486c29100101c9480e00740c0303c030b01c00000d414060300440c10741010704c2000b0700e440c24840300c44480408441c0c0c01c4d00d008201580c080400500c0300180c3c4421880c0000c1840302180c010001220b6076405400c1c0b050b482c00c044280081c0c03042003078071640158941c1903001c2100318101080b051041c002e00c00c4820381c0d040100420507822400d81c0d4140c60f5098050081070741c6d41a44582803501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 713591708 1250 713590458 713590517
    0x424081213120c08100f14090d050a030b150703110c2d130c27090c0c0b011d0606160b0c0f1902010b0603012414031303 53
    0x45442403102c61a04840300c00503502c5440b694001a0b42c681e141da0821501408140c800c42d10b42020343c42040c482d0040d4401c51404034240c1c490b909192140e00d950740a001d81103020f00002180c2c0a03070180c0694020400c01402900340c0031002e80c40403d0203810740c841c10045000c03800071070780348408100010b0702c03a20681c0f0140106100d00d800026100c160f602100c48420341d07500c40c081c412110340b20204051400000401c0100304003050360030141004c84c003207900300c20208410200d0b440c90076000c0c011508403105408009840c0c484004120344004210300d0140c112807050000090450984a11100f1450341c1d014603051501c4082c00c00a8600c00c80c0302e00481c41d020030034080041444507003119002010b4800d00ca103000110b064602d0726401c03405001e42d0542e041241d50030181e80a00071307411005000c840940c0b40d90b04151440e00d812040030300b2100c0c6130480038076031382d174041c09144030304185249040360729103a1178074210070180c01c10140381c1140022485100202001c010b034030910030980c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 713592958 1250 713591708 713591737
    0xf04080706110903030a030615020a021503040f170705060f010506030a0b0406050301060e0603150c0f07030309021e0a080304080c01050c010b090108060103060b0d0305040302040b04240812 83
    0x1116840c1d000140c07a007500545030540041000600d039a13070810043c41104615140818010f250001c207200c4280508019010343d008460030100581c0c890392a90020010441166160b45407802c140c100c1000c40a4010543d80d0784c1c0d240c410150756110040c1081c50712880c2182c05a40d41c2c04480001d2000a01c03440385c1080c0240085032503040140c100840302040500001442a80c540000342035540f294490642c0c5140a024811142418070850a41c6e00f0305416006031410600c4901d0b041c0e118400e0b14a05c40c000110356841050300c650010341c42a0340003003500c004088280024403504030720350b40003482260b4004001034418800310aa038100c40d0150085c012803e0170000646240d4012082454107558554548440b40e0343c40c0796a50281085000404107036045103040d108459810754414411584401e40e50000717980b1104550035640c0c161004141c400c031480200d1b014114900402c0d10041100c3c43e41045440807c00702800c5070420400c131803c0000e1802013520078840c18401c680c2c0d15 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 713594208 1250 713592958 713592967
    0x9050112050c100813020411030c07030206010902090604030f0f02061c050732040306061706070e100c110901061e1d090705040e0106030207021f1d0f1e03060f0408 72
    0x80c4034920044902c5e40084e01c00700b640c2156004500640d402261206510f5001081c00400d06d5810400c003405003111940840c503002442c0700040040c05544001001244141040303020849100680e003030482d80a003d8a4450158000e07002007400180b45010701c0d14034004c00140fa10f8880d80c0d504140503170001245540c2044d0603086040120b0614490903421010440040021414420000200145110224065000e00c04e49040c0840034010008008072003880b000180d541d183d41742065840c90818022039400c0c0c5c5006c40c0b8400c43d02c0e8107203521410307000000030220303041040345254001011600c815200880320a40300441500d5400369803107900c04091045089c00c60340345410030782d541000c0e82050396441c0200c4000340309070440310001c1d40101d140c00460811401303030030840c20000810000005415401015100d030703074001440d540350f0a0712a5826440d84084400d003000050301065441001034080b00d480034440d0250340c060f00c60000003a20700d0114005441c020382d03000004a260 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 713595458 1250 713594208 713594221
    0x1202030a0c0204180b0f100f0e2214060a0f11040302040c02012a020c04050903121b070b060901080607080103061109100806040c030608070b07050709050112050c1008 73
    0x10080d603601a10400c03211101100491450105948a0801c070150b1400305d2904018101003200c81340d02c15235510390030aa052054158078016140d1100305a04c3c100782d41081c86072142d0074080200005001a0743c0c00c0c401000940c0c02140b410f1141c0c2c841c403424000000f081a03004116102c01c18110440b501c240828001071526400801c1240d0480c400420041500c18001c080300c4140002100100b07d0004c44101c03041d014020b280010000701d60130011454441c1c6402d49078440c0c8501100030b82d03c9031001809050001864500e40c144050758181c9504007841c000500d1134060f03411921508131280009000200007650910031a10342eaa100d6041c2d02c0c59495202900580d800c03415010801d00c4146c0141c1c840111403c0b200100d44d40e1801a800c0036014001141e0110b400c0c441094103084041c040c1031400900c5208580c114140540d031221503041642c1045416004451480c1c102000014098010103a100d600f0340a80161803480306d03000200803541441489040c045414000007511 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 713596708 1250 713595458 713595461
    0x71b08040e37050406200301080c09040b28060815130201021504060b040515100201060812070303060b0f030105120c0a051c1a071209080706020a050f070507031202030a0c0204 77
    0x421600c240170100d2182070000b400c0550100380c0700940a0080013100400c4440c0d0200036801e050401900e01c8400b0741442e407901e811065000b00340301600105400c00c000c410542c21400c40c14900e03110020001d03c1e40b121903190315203824041c20351f0400c1e0500c000c103440c0603640c09051226981600142000c524510002c607050100410684610350740da452074070a616075002c2c10344074501e500c4c0c041c109010050b04000c44c081244494004683c0341400900c0409030008400f8024011840c499840d040145406c8015101075000b403c0300c0d040c045010349030b00c880d4202441c1a140103c071600040303c080c00346181c0c1d9a9890105580c003a00c001740c200031a04206031200e0001c1c1c9070b6490341c0c100034100d880e030b0b008104104884500f400390039001c114085910402d040600c480d00c09090142c2412626082d4150040c1c0ca030151070241c1c006491010580aa0203c849103610b070703d130b401d0700c0740000d09040b41c07100454401525014681c1d806e0003405072000c0122121050a80c964000d40707595a000d200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 713597958 1250 713596708 713596711
    0x81501021c0810090608010638031503100c02120a0f030b060d0e0c0f0a0b0706020c0703051e1203010602191707061d0106080303071b08040e3705 64
    0x120b5400b55001c04922050304e070045001400309503002050481c50b20807031216803400c0c183d20304481400d41c000c1e880078901554a0802c80d40259071083e443e0744520186484501000d0b0b18950300d0300c2000c0c00400f019040b40c00110b0951425000c2e07443c0c000b45401a4103252041c050701500003180c844045214900a9010028001c405040386003481c01d150b81a400300c840b0300c0d405429a0340101c91000795031500c4001005c1e00042560300490306031604000440030300491400600c110b8001c103200c40d10030130800076040110341200445805011210b0900802144450340304010300400740d16a06401400c4222412203800e94000c0c00da16400c0f036280c0640c078040c1d2608450701407810781c85442603010000a0607031203020300400155004042d19185030402c03503100a007200d905140e02040004408420740381d0000715404c10070913405245581e1480090b41050003402520301060108000f95901d40716032044660900c044c802120420100000c1d034040d42064521b0322407014141d4502e410f0307800c900d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 713599208 1250 713597958 713597971
    0x150c0a080714030a1521021311030f0925050f01110313090f06080a02060304080c010515040c090b030a020a1103041712120402100e0d03081501021c08 66
    0x80c1002d000c4458201e06500641e041041e26444030703103950150f910850541e004055078040c2901c05400c0500880c0f089280e4100a4030800d544800c105d42d040868000a0008140035806541c900d011a281d010f031000907124901c6511421580c100440c0c410100c11680582482d09481d941f4034002c104039039080c1024603241088002154680280d00800c09010305440d00301215100504047c000c400329040c140d601804181082e03c10080c0c1d800110b88500000e8044c0e61895680d95281801e0320948a5207440ba841c0d51f10341000c01515001c0e100000106040c125010300001c2c42e0301c1802c0300c1d640001c0c05900d19a400410106079000f01aa0040400315402d08124441041040c003040c00c41c0c01c15400911303100440c281000160405200032006080852070240c101000b498541e1800903000b04001c0c080c1c54240b1070021a80c1c0500e054400700302005203458128815454011f10791001603072941e810060115419140c2e60012880c014166410301c44203001c146d11a0341111a0407002d45031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 713600458 1250 713599208 713599217
    0xa02040b070803130b0907170a1203020309191b0504020a1d010c05070e0108010e032701030608030a120c050f0306061605070b1e09061e0904021308150c0a0807 70
    0x6500024101100c001d109500440240900038640581000201c84508088c2d04c9904803030011400901c2400a00c000c00c100c038540141c5035528807030100e2506c09c05081c1d8200084442101e502000f80c010031200e00e035005003115034010340c1d590052009074010107014001041c415403070b20106020100103000c1040051606c0528011282c580b02d0503c140781c1c00c02144400640010f100c8880d09000d05100800100015480c4c02c8580051014501c0c00701c01171001104a0342d0101c07000d82c4607410130009041b0300c0303050f29603070720362800301910200e45405040c00c46800c0900d0107002600a030203071030b07404071400019880d40d84d4140420800c0c4c1c0c840c100644804503020807410128104106030740181184405580d074030003038001d0040c000712588801e0400c9001c2004583c209464a10548810340403015132000d4018045541c800c4d24068010480c0c0c105101107104100c07051010030b441c0484071313518140c07904102c8000c15901640340840e1b045203c294100140190a0711818145501c00c540f841d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 713601708 1250 713600458 713600491
    0x515160323061314040506060a052809060b03102304050901090f0503130f0605070201051c0e03090103050c030408041203021c050306011e090b0c030906070305120a02040b070803 78
    0x40f103204030749505040c912207100340c808000400104020041d041030013118445821803505001440c01c01484040d50b9030501030440003403800c0c42451501003e0712041c9001d1001d1500c401d12446550000c85032545d0750100d880000810108000013040b51a0010004416101c0500b0920025003006000c0d6241590b0350841107006c58203820b03c00042601c50340c0610398900d03404041c25440c0c0041d030418081289a0f01c010041c840d008001c49144c9642030820700d46401820740d54a15400b0310720002081d0500300040c00b01c3e082c20200c01003121034400d8030708226581f25030035095500d02040b80c2c01400036000304001e106007400e005109100503c24411106070100440240ca50800c140c07031410702145012050003d6580c0014100b60220454100b00ca41c6a5801a000340340318403900c01e001d0b42e91000034400380307036510a02c101c942c4503370302030700079a0348607210310300103011b035100004854000b402c003008142c0025040c000c0790704840c5c03048401707428003c0383d4442d0445640090042800e0f02d06401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 713602958 1250 713601708 713601739
    0x60b0a11030d090506190216021201020d1407090905011503020c07030c0603091707023f0304061b05120f040504090c030204060503010e0307060b0a03051516032306 72
    0x381822148101c3c0540740707070305010042006c4102d4011440081078010311000700e0007031030504140700e03144d01142c55400703604d0708031842c5009104403a40c116501c1e007804102c0c0000245090311500801c1c00b03550b47d00295680c2e15606044171828050300d01266002541d040780d051103a0090007a81c0b000e20150350030b10b907903580c7d0b10f80c4010f840c1e40b01c800400e8a030580f002c140803500300e1b040c03801036594001620f01a07060b400583d81440c03910440349404110407100c49240720220044044a02503041081034880411810b40c0d69001849500002410802021558807a08044242d620350142c010006059130260403009508a0202c90b401c540741030100098540d19400f0b00c0d00201d0040c00300d441040c0c1180103220a85403250000e90180c0c1c10000031000342e40000040b2011940c000e50005400b1514200054090300c0c1382e44050b10512405124840342107410b00c0030b50241a80d1111400f51030380e402c0042e0152148410000380035a00001d00079640052026150742c008802403417440071444e401e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 713604208 1250 713602958 713602961
    0x6060b030109050718030302060414010f0c0e13061206020a0e0a060c120315050f0f0603091005010602160e070c02040c052a030f3403020c04060b0a11030d 68
    0x342c1c04031140c2a2588240100b0a0300840b252a00008a03961070140c1c60860320040d50b02d01024100400001c859000c0ca44420002e5010b0407030002e003040705200040c06548020241d1001c6903009109000c540030110356141c8611a036011035039101404151010b203626181c0007904007800610600003410041c034107030303500c4100400c003803d034640b9641c0f48a0710b50301301020351062240c05402414a00100100d240c807582403450102c40d4100c414042d030b42d004101203400090340c84000c940103080803060003500e6101240f0f00512200d208000c100c40e07139032490101e0b030350017500c1484080030040305000d001850020102650240141c00c2c851400b52050380454210b4003481d000d01c00151000c2000e984004114003c1085025103a0309641c00c95400c0341c20035100d21232910280081140001d50383c000c4500ca070644400711580740900b20b000010003403201180006408100c0050040780d0f00b032811481d141c030400064400d00700c0d119003488003510b801e50f00c03804001507142c100d2000b4890381c2015103a0307 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 713605458 1250 713604208 713604211
    0x1526071b21020d082802090405010e1609120308090c0a091a0d120c030c170702090a051006180503030c010b030606011d091503150702100c02061306060b03 68
    0x700e401c00d20051240074001c2c248208540d45004000720101401400b44c10211018082c8207001c54800710310941d444542d000b403098a0107a0342180c00e00000140080e4076244080c4580d4460072030b00102c0068507802c4910880c03d00031561850414584000464410401eaa078405448821683d0078100c403800100b403a44207a0000c0031140e00d030488101c505480e2003c052113401c090380e100000f410300765500a0902003802d034030000c001d059122002403612402c0683c440075008489012541e00c0013044450030380c4680b205034020001a40410b95020903440741d0f0340700d0f42400048014042c01c0c031408503a815036040c648a51040b190070041031641e0f003800200101c0710b048000240c2d00b00c03040107050903c00d00420841c10b0000c200d96480c020700c120384c0d410724002070407605c10415541d100e80c014008958039586941501c07803110028449020745568034011003072602114401c04644401205482d01c01c1080d50050300700102082e21290110156009907206203404078a0603200c040c0c07208203400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 713606708 1250 713605458 713605493
    0x10f030f0215071b050102010903170406180807030306050a0302130b24040905010b03060102060c0f0d06120606170d1409060309071e03080a0e030f01061526071b 71
    0x43c0e1203081510600c180e2071340200f1080c0003e00c103114082d02d01a0040400070729020030401c1d00e100007004c2181c141d1004d40c4408554101c5541003816082a2405400803d0210082864500081640e203040c03050703101140d40c003d088840100048100313401420105071003d800c0744044e030320518a40440c1d00301d00255414000c1c05520342d403408852400340c86042c0d1094840013010001d0100c26603002c103541d9032180e610f4022300e565100c44100c851380c0748200001c41790014034005010416004800000c113056020f0001400102e071124442c00f070032000200340140580c010180c0301107950140d80490300e0a21036101c90342c10110803502292513035004440106150f084240f051008008031031035112110300b0740614011290565841400620a0074044000d04c24132180310986a82c00300400c28803001c00c01d0003400340c1c0f981c82120301038900c003504039500418118903503541c2e43c4001484000782d442407414501417507110420251444e49840300a198481d560b0550640030030080c0044009c40e11 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 713607958 1250 713606708 713606723
    0x10903060c0e031614091506030f01180b06041403070e0f10060c030c1112010c02061b12060613080a0804090c080420010c0b01080a02010e0306010f030f021507 70
    0x40c044400c040c20b00641d44c000002c1440c004106200c124075595000600300380640d410040390300c4180d01051100c0c000368203203600c41c00c00010846260b01020840b4129103100364080c0140100c030b03a2210a440b88841400c0d040fa0f000c0c07000700324056002020f040c1c40304000e4142c601050f144d40400d880396404a4411980310000414010303c468a14103e100500300c51608900c506030075075000f0705064074041c000e490f00503c1060b01c0030075510011203a140ba030b2548002c0100c23446c80c0e00083c1d25210200d50343c1950b41c4072981c00000050604003101c4965490380f000c2c1450741e85920410507584c05c80007542d00c0d404c1340e401c03021a00001c10894006924041e0701c50a44a52810740705000b03540074441c50508001099051100103201100780d41c1c00c01e040010303100703203401c0a8030040741c10550700b03c409030501c581100000741e000400700340442e2060003a40c034018125200001e0641c0c072a000c0c4220b1a00f101d22402c03c1000c20710107000644a503200a152111250038945140001c0d0024441a100760 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 713609208 1250 713607958 713607977
    0x8040905041a130b0703150f080d080c040612020d060e0405010b040507051c05091f020720030a170c0a060912020f0d0c030210020408010b011d0607030804050118141011030114010903060c 82
    0xc0b900400641e0380000cd21070820300e01070529000609010a02603680c000a401180d0074000000340d40144000d085020200d6485242c80d0600c0340c043d0041000700d40c020741c076120104545034407038011640701c2d19903a50810f4102c4c2c0070b200b0356802040010180303012406a003103c000b103040500451013010315503200c0541c0707800712420325a02c40d41c00100034140c001131034000703d801510046003502c0725581101003084505420b50480106218850103050903002e0301501c4820888658403001d100e50140c0907145415550f000c060b44d9504148407482003980c014600051031910400c51010498803a2050301e0f004040c05c3c020380140d800c00d0300080b030a651503e00380032107560320400b03244110140d541c040102d80c1411000c03442c90b01c14004051304010f000170015080c840c094004102400a52240c9030507102c260074010520215400c0001e903500600042036480003c03401040517140303000000d81e180d6481e0401003103a10a55107500d034188032070580004085940340c8507000d80e52100e0349a0587c071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 713610458 1250 713609208 713609233
    0xf0d0c18050108010b1f090902030a0c11030702010203090d0c050303040605030a0c0c11010e010e0613051804030806010e1207080d020d03060b04050d08040905041a130b0703150f08 79
    0x7522016000085140e00d0301c18508802c1d07441c0050021003050600302c007000d22003a008200c1305014290880e600d050700000c1402380c040e805503c00310107408107944045101d4001c650b1140c6034412001c0180c0164801e000019043c58034551002e2018459100c2072030380b0b50390720046402c43e081076100c180810004010004450700724003546002a400d441c0040255a1560724881104007150b022410080440340d1b9817011390203841c00382e102d900002c0101d034803603040704038a0641078003d02815000340b038a18005018807617148500c5001d90751607100c00310b2550340e90004682514074402030740e03070103144104106100c1c00b00b07202c807002034480e40020b40030740d0183c004040d1914018040c0d110402d841c2040402c0403805a01c1668140ca00458111386003403503600b03148207980540d40065640c41d00e4107040c0030400000035000444205481a110190b0380c415842c54a101d1282102400e010040c10000d0003c0340b1942c0031120850041f0188420300e525401a048003140b07a4201c03441a501940b2021003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 713611708 1250 713610458 713610461
    0x2318120a120f0324140109050a08210408030913110d0501050102240f060d0822050409020d1223040f090c050417010b130b0a0e090c0f0d0c18 62
    0x524400c0b41caa0342d0030001103007030840d030608624460b0780401c5e1040d0342d441d1001da200c0c8a0300c2d001040c00810041003d07448090720ba4517501d02c040c510f9000d03110050708042d03203d4500281c404039080300025504102d000c0c018842c8130002074601a0210f6905c000e00b101e0011810003a1055600103400021150704040000e40b40c0495842c5150349000454040b41040040e0300c5d9080d03216800c2c13900103481741c490b00003003039118441c1403000b005402d01180c600305140c0608000702e036004074074034003107403169950703041c0000c569807800082d4214140f0200c41005c1031f0300328503c1d5008125882d00381c00300b00606c0141c02c001c003984000080403450001d001c02c01c40034001100001f402486504108078400080701608510603845000d040c3d04d001640381d0f003094420350084000310750140041443e1010403041d040140846401d4178880c000c03000f00403c884000d03454007840f0364955001440c448400340e08020203907141c50b800c03079801060307040c1c80c400240061076010300401e046000b042c0682580100e030030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 713612958 1250 713611708 713611721
    0x105060103050c040501140708040612232202031603020117060901050d05030409020406030902030f0d051e130305060609070809071502030c0a032318120a120f03 71
    0x40c10542000207010100b003056044070100c450900700010320285410b420b200500401202501190000c9000509240c10042d6000d007440401810403d0001004012202c00440e05510142d110395100144498030408051700800a01340e01003010760800d640040d01c1e00c41d0304402d1001c40c0c50003007000c00c21540c011803170400c101001c440350080c40c5090400f052400005201d928481c644031480d01013880000e008036070141040d11401e41d0340b6030f02c07040043e0103032189042c200c0c041e100e0070020040c01c88000c200e034100b01e012a55014540113501140d400154298666107401d01c2c0f04102c18002d0fa410701052000540c8102d0281c4240d1070078100300a00c4c03071001004d4805100d58803040080803c00404d0f0042500e003000d01200000821510403442c2d8002c40541c035582d0705c6041810300500d60040006059106810502d080d15810226a20001c2c004c200514030341a42c4440c224905142c424104810b0b03401200458040e9503154039850322018500c42c00c4400b044203040d02c5102d0301d5050080c5d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 713614208 1250 713612958 713612971
    0xf020f070b04082116140a030f12090c051011070e010911040b090607151406031e1c020a0b040b0a0f0b011b020118080106170c010c1e020d050c01020105 67
    0x3160b00e4084d80000c0b580610403100c0c041030048240c50ba105c01c02404c070041c402402c501c502200c0b10344031207250290030610160044030214600918204040c2018060440e60a5200d04050740681c94001442444118a40711005100501c081002010030402c11500107042c5180c001815514080941c400c84030351403951031049404110521011001c94215040e0320700076500540c2d246c0321404c10104400070400361140c1c650505907805800240300c0321460054a00320141c984c0c4a024420b40c21042140989900301c50700700c8200f04417803202e00c1d401441c4200e510700680728180002d50303610149600c100d8040390120640c01c03d100103c101407180003c0100c000b1070820100e00180006081006c2e02054100d0000000c0c2d6201d0131a48a80c0c0b2074a104070003810394030070341500d442c9241c0c040c25030b074098a1003400c101043d100300c001001460301a400c1e0180c49004850f00030391100c6904208090403801c161045000c0600140c8952010700000d5025001424001390000f00081c00e64401a280c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 713615458 1250 713614208 713614243
    0xe0f13021b120304110d060f0504021807020a110d0b0709140402040506030c070204090803070c350a03020c0703030e012c12070b030705121f060f020f070b0408 70
    0x300303100b00d80c007001200e400c990030100f0480f01d413a45000081010307034003510007031509003421503a0308501003075045a03008d5403088541845821005690a0141034100c8038400168000580c100103d092000d880100c400090001e0b13030b07030a2580d140c00301b010000b0f88021000400c070881c100701100c04001d02e400c08550440d01540742600e49000540b040c0030107019102103c800040542c21583c2d02d50107880c800350701c03107042c075201d03d04000b025007070401c1e05206480c0e160320b003e002c000139440802c505007403900c10325601015140c050a90000d0ba001103c1c2c0f6414903900f0000716030980020040c0600861296488101c0c08081000044c09001d4040c1000301401c041c80d003844400c2e624601a941003070741031b940440c071080e49450540c07805140b40c0c49030011890000074040400c3d07000004003c2e44207480c00008450300c541c0d003852507512204074500090891032805100c0e4610819642c2a0300d0414811100c0c0001c0c03129031142408611390251023504030010301005013a8040c0841d410602c100c004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 713616708 1250 713615458 713615473
    0xc080117011a010815130515060309060f10031b0312020f06150a12060b10050c03030402060901140a030e0709020405033c0106031703160e0f13021b 65
    0x260400300c201c507031003410f001141c400202181d084202002c2d80c984001c1103101546c41a400e01c03002420242c840024030b1f0141c003c0c01d60241407c0f8122409440341a0041c605030380c900b40003150640014100040b4100501c200201240c402001c00722071486010300d00040038954900740909002d0210410b080d50000311805520440110f09039030321510381d02d40c610385500c2030000146202c1294110020419681580c43d090026560211074040ba01b81d5000015210182d0185c515026050684a55a004000140060910001070f1250b0041814070901e203451007400241e00341c120842c180c0009507030b6403d00c5c43c0d10703e08206507402130010340811403030070741403070003081e1961040d0001c000848050007a1900d400000c24035403086441080c058992250002105400707411035210540f00361201908888094501d003045034003846800142208031000540142c0b50341180c0b43e0110752200c0303032045482047d1900907512544001e90140141d545050b000d800088804111118031294001e88 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 713617958 1250 713616708 713616731
    0xb1b0609060f13020d031413061e02060408030106230c030a1d0102101d0111180906060d050403020a1e020a080706080f0c07060f02040e1305030d1e0c08011701 70
    0x1c0301c44900764240c03610012145600031f01104500c20155941081c02c504000010343e65031241003541800d07116003920034014010001243d079040269000b4101c01b5042004100d11401400d0300d06840366103076659041c9040c2003080b080c85402002005245410010707440303081903070080440300c43c00428448010302060400000396610710381c03805e003a41e80360b8414480000855014800c09603800c120002e02039000c09a9148c502074112002031001201c081000c00c400b480d01c00400361048102510060501c030002c905da10184c4006042601036001d4003c00101080c0c2c005041011b5016050030841700c0b039158814000c40e01c01c0d0380d02961003908410b10511400b54071400b41508215514541903203a1035801140c4600d10030040010725503403134074420b00d460007a40e4000d0000c071040400418250340d11007030403c03040350303840800824981003007000848000d40e80e4003424031513045410052400b041003258000301c41d02920404085042c4d8001009a012100240e05107064804000d01c010152340 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 713619208 1250 713617958 713617969
    0x40e070f06030b01030e010905030405090a05070509010e1f05040510030e0a02062208011d06150103020f0d15170d0518120607031a12070b1b0609060f1302 68
    0x5000341e0701055102d04400303038280c1c480d03000014404e010342c000308101105441c2c0607a0b26030252080d40c0c025051440003e0940301c4612a4520801003500c4103880d103ca01401142e5441d140080c46610905260681e0074010200f803003446040c09680f989a034440c18a0704000c9000c5100440c8800c15007041e0403260601404a04084500d50650b441501d807000301287c9003002e100802407a02c890403001c400600d1090540280495020710000000460701001441d52a02803c8501c0c2c10b140e05042000c010315442a40241000202148014280607500c0540c0c4133544482e280d80b1100c0696503001c0c0820507030032440c030820b40700e0000109210995800090910301656403004118441140d0710340040c0c49150042c03001d405c0d19815243c0b2403070100d802400402544014000341400010100480c2c18106071042002c40100c005040b03445c070303144600055520104902d82a0201014468040d0204200312800b071200040a0f0266140100481c418420001c1c80160124080e4401c000507072581c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 713620458 1250 713619208 713619239
    0x6050303090d1b08030c1006051507170f2d1e0309030f030c0c0106060e1503060a0503030a0c030f0314060409060e0316052109130f050408040302040e07 67
    0x11086416504a0803950f91540469940c850b103c01d02001950030200840450084100803541404101858440c4140306842c840c0f024401d0a000c0200846c0d00440e0b0014550120b02d43c0f00a8000e180c464000c0b50b0704941d400606c085e0480d08044542600c901d120f4002d1070320b941841002c000c0c107000040b07540b02e4018a05940d400214000000440e0940400303108484007540241c42e22940e1b410030920401d001d900407600800710354a070a41c08641d0900c01c40200714502d42c001c1c0203450b101d403244d1100c20325900c00350189070322442c0350100041d9900c0902c09407105913090744441401740e41038140a000f1809000c0258201460300c0796801d48c03150b07282500c580055055400191030300262a2010003401010704185641c03001140d840041452038282d10b2a19200c0c40645400c0014103007001d00000d8800145100000280a50307942400c0c4903982d140f00384001c0e0070100b0384d40745034446403003110340650b8151002c03400002c06009500300390180154841660004202243c0f51120b50141c0810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 713621708 1250 713620458 713620463
    0x114090105120a05011505102d11060a0203091203011505030405010f1103071d090103300f0f020307020f13090b010807090c0203041413060308180406050303090d 71
    0xb103004685000e880c003041080407940c1d0203402004914600c006141c401c20740780c8070301440307003220000810602d889900c035500d0446110015031070101c882c40c50180450b94107030301c0004100c410b012483d000038080020b68003d00b41081d0050b92810300300d4034a41450003100c5040b203000402c100400c28120f44010707484c03e40b10307a490b240d500c0c1d413902e14243d805030008410b0030400f0342c100114031400304901001103004101540712580805840c0020010b0419110400355110f20f1040041001c1042d0710224003103004420fa900c0000941c410f02d02d8910181441c5e5080021409003000e500980c21161000441500d400110301301840c13680019640340c1c840c58021f000b00003580d960100c2c0039a640005400c1580038900d40019a1623488195450745a407007040201070424143c0c400c564004412a0705403121f082c17401405418070014800e100c1003202c04030740340c07582e00c410000100c2c036900050811034250143d000c3c411b01d07036a8200b01c00c0d1410f0703801c41032203504100302c0f00c10170303a0704c2c203102c440e1070356 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 713622958 1250 713621708 713621719
    0xf08030a03020a112b090e04080706180308010819150b040b060d0207021801030f060203072001050f06061306361703071101030203060d12050705060114090105 70
    0x1041480704984900009411350403034032520b49200d031121240400011008a903418400c4a07034a14081122045020b01c03070f84080351848004500070440040050200038050600440d050b03603401c49030142900d2203003080c0d0004000c04011300507440e080c040540b2034510b04202c41e80e0b00c40303580c90748894035400b440403100721580d892402491741c4450b0040301d111a402848191213004017610f1402a5022007000c034071542c000d14600f502e003140005414180c9401001d007040d241c0040d91100000c1d4001b41801c0c083c00b40d4240b49449007041320000c3c07240c401a5000100d8030b814686400420548040c09841c803440f024001d040c1d01001540100c0b00f101c03000d00d0203c084201d1016000c8103030542e4a803201403090166000203030412880520740490301000036603180f201841c0b100030b45038060220010b0011840000343c1c3d02940c070139009140c002900501a071020109565040c1e44c820600809401082c404503021080c00001c4c41030f1801050350440840604540c040051030441c0140140b43c42070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 713624208 1250 713622958 713622967
    0xd140f060906010c0819170c040b1c050123040b030d0f1e0305090f010b1503040318063c0c03051312022806080a0b040207080a02070f08030a0302 64
    0x244c2c401d0418048560b000105103030fa80300d001e8002030000304041d280c0400700700303a1000c8010016003c48010311844d40400000d0a1500f051050340740d99126800c0810320801d054080080fa0820784605402400d516241140c10040212131080f54154429002e205a03c1e20340341040c2d640b80841c90000108880c0f8224404071a02c400075211508286001800083c036017642900349c54040d480301c0c1c041e54038003088030041e01c03461403100e0990302103041982e000102040608004c64003000a10380280c820708004500003419820125407180e264488800580040d101007100b000c42e10f010002c0f20722980d0142880114200303a4000b12400c81421010820b20000d008107151245c800d13200240c0c0059503004200e941c03440d03403080e030741703081002a4842c8912948420750241034240340d5000802581106442c980f07048810365030600c1c0103101800035a254460f403541a515440100520740c45440b4290326a20608402031902401e40c100c0c510300004c042050000d980c00000303540c112640ba14002d48d48 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 713625458 1250 713624208 713624221
    0x9010b0919020c010e06090610030f061d15270a080d1803031506080f130501150303050d050c040b030a0c0e1809120f0912031e0d140f0609 61
    0xf486031125420182d4a00704904441481c0030038441e0103040a0001c071051900d50904550704a403882c880242802001307005100080d8080c3c2054964088032520b031051000c4000040b0708004001c00094400c4501c08200a2032045901103040b2426843c4401c820118843c041d06030748108030707200030300310b130384040350545410019801002c0d4002a20350f44400021032464040c010303007904180304076015150800800c0a5208449152040d1007038003110009490f0752058403110342007120103540b2952140f294511404503c1d03030400007144603a07202c1d41d4685540c032828007210000790001c0e24600040008000d00114075058a40102c880e01300043e1202c41000c05036000c9a208031240c1c1c00800031a03c90303040d0072a10940c54411007049050b10102900812025003511504800c4001d2190a002c92030725414070300134600002456400306d900c1c0c240181b0b5102e4100e003419001225220001600c40c107044218020000030744e040c8084c500490905e462540e0340400c004010f64090300000b40000d80 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 713626708 1250 713625458 713625461
    0x1203140c09130f06030b09010501090504020a030b10090606111b090403081801060303030b0108060d03140a1206090b03070902030708070806061303080d14011d27031209010b0919 78
    0x500743d8065030410003190741e0f16000c2d02c3d449044556003415403800000189040c560300801e4422a4010309040690303003541c1d5003003880d076006452840e54090040020a0501051003071784040c21182d04c41e04880601192803620305030200180b0315900810316000f10040c0c5072108529007280d8581403811003641c60115600c2c0c68804c10311001031541c2445c800005044d0184d00000c81008282d030303045407581e03905090261091400700004c00199400d0065403072a8a0500901400d5010740341000c0f54072201e0b2012002d81e002d903001800c0c0390741e50345d92924040c901000020014040c665003542103103801d0002a01e40d21009140d038007844202c41c002542540c503c4106d03070301048c0301080111069228188954550442c56085008a10b40702c003100442d01c0e0350050504960001011840c0c08a0500d581882c1201c09010b040c1c03404856080e1040c407030310000503613040505810041d5110140b601004151040140a03507450741d140c0f140e500542c0d190f03101d02076801035607140c039030035412103280d000c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 713627958 1250 713626708 713626721
    0x70b0705220609030c0902090f060c010b0d2012030f0a03060e090106030c050612041b080d02100f0b0619090b0d02040f060e1003090501060e041203140c0913 69
    0x10144400c0c075404581c0d150404a1681540e008a0108034150b8503240b02401300d01c140c02070349a200c2c24007c2d020482c0d1500744000e2508821440c00071450701e158501103400800300c4803045500344041d1118161442030b40340c058002c103404490703015032443c4800c4442c0c0c480c0301c3d00b2504994030f040003c0100e00c0600035080000200704d6404000410710706420661f00a080d60301080f140c14100c0040010b017490200155554105100e12400854545903105580703401120340200510703040000c0003800c070009011401c40344d0050703000b914a24422440300c800702d50200c1201c507602440d00500600d01c3e1610000ea40703126070041050280c013110800180c0e03103c4101d40c0300010b11031000461070400c0103a60054030031600c1074174404070407548402d0192024804c0c00c6055420101780c4002c0c14545c0d220b034200c100c045000ea400014240c0d102c070f5190341a11401c44054411032121241b00940d581c0c58401c86800a90304140c040300c0d41041c0360b110201e4400c42c01c0e205d00c1501c0e4680240400000c0d0b80c00207 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 713629208 1250 713627958 713628007
    0x50c0906060a0c0f0b041218051e0406082d0613031b0c08010915110a05031312030e1b0913050c0a0620073002040507080907050303070b0705 62
    0x144082c0380907d0f24070052240a081c0344001280e05100c41129241846c4e50380a55000030861780380b10501e03000950302e940c8054000d0b50b105803a14030004030b509003440040860314034804007600328105040040c04850211030b016003168066010000300405080500a600c0c3c3e161410309a0030940710035154a2211600026080c0c1d5068500001c8007901503001c1c0300c4440c8030740c0d80c68107820204c100b10021074800128a90358080c3c20008266031600c54001951b000700910b03010100f42c045911000050280440c10f0303000700740d4600e620315400b402006140b40021904441782540074031480031a500000103044001583c90019203001000710a1081e001425005001c42d00e00541d1071500412a40103030030480b84420f24105440a01c000114815050ba4511115900c0c000c08620745018140d04100070016418140c00c0380380700580e1039018040c05008680e5400d015400c0c0100368a042940325032000b0300c00c0c2e0082104400150070403c900384d115040d070070721030346440420074109a0b00e8116001d0703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 713630458 1250 713629208 713629223
    0x915290c0313230102010e061503120304030e0103050604020910030b210601030c080d0e2e0801091b1416020d080403060b04090519020307050a030807050c0906060a0c0f 74
    0xc56403c910202030103e110052091400c05507100380103900302e505003920042250800c1000070000d448102c80c0c0301d0000405401c8464441c2000c44a4255030025601240001c400510300400356a05d07019a542010044404500c0d0105e0303500040c054801c000c403010145501d884084402d95070b500186908580c1c0098040161150b10a0041c2c5804c1d0034001143c1895048602240d9000000341d0f940f4110381b00d03100ca6980811500400c00b8042c0714088004102080b0000c80303450581c0d02520000030141c540704c0040e1541000c0c18441614803607200b06111150514000034110307800004130501e02c10640c0303650f50f92400d804540c41ca194094001a4200c40e03584907481c200841c0c4070061003120b0041e04100200380501307080100384c401c901d1000c0d205602056211103600c800d4450b00c441e1174402001c039510550358201081214085500c15907418402107001c0c0709206052040d0038102e00704589820a0349003d400041081c002d0341e19100030030030050440010001c2c994007100c20305400604 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 713631708 1250 713630458 713630497
    0x4020c101d0d0c060c020106270906060b0703031b0c08070206251a010b030606130509070909110304020105070f06020409091202150c04090f150915290c03 68
    0x2003d4076003001c9520846109103080200c2c607000b44180304000035100300180204070f205c4d0f0703107422640c900d08141000003419601d0900300c0001d00d5034890003008000c0c0304409902e4400c103080c00b0303045511300003188000f07a0030750880f0310459621010800107154802c0710036071a07020704d0000c5500303406a9201c80a10704862016448040030b01241c21000501c0f0b64050445000080540302040da820301c15081c08001c02d00110319185001e0307029001ca48000e02ca8044032550380e80009188e007800761011404514041c0042c0722241c1c0500074525114036090025141d0304140d40000c14034071400300c0180c401b0008584000c104034694046a009040000c0c09100c441c0c002d082c90110039000c0350a400162051001c180703880f40c8865020b61040c1000402c45040c2894903d201028241c1d40102c0654282e860304c48402c1c0b40c500b4400a009060011000034020149442c001040340070794001c900340c00c0c014018034080c2503000240b090a4411141c1742c82c3c0b1404030040b406e01d140145090310012841c0e80c0c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 713632958 1250 713631708 713631733
    0xc060507230a150c0503040311031624150512150f060a05010e03060a02090109031a040605070c050d050a0903140606011e0206150a03020a09020c060604020c101d 71
    0xb030084070042c014031000004400541c0004101c0c1c0c81c074003072400032171400d00010300480d0250b038401d00328034070940135280380485007100190b503450501c0d03045400031001404004800c00daa085046094509401000001044025100b00200e140f089511030442c1c89000140010305021b01c038400862803800c880c81c1e04005802d4086d400c421200d440c01610507500002d81507216010140090001502411441c0c890440038006544141c41050502200c00709c0000000c40a005140080410440105080c00d09240610940b2800350010040050002e00540031580100320303007038002410309116a0341c2d81c00010540c2c8030035090303001a01c20420b60b01c0319801d41c2c0012480030b125100981c2c8170309550500d4040011240d0101c003078000168001c60004c0d000041403400c01c1d045100050800050694a500103000360985802c40c1840b1a00820440104041008050f03040300c000c80d01541032403050701c10b450340d605800b4006040d40b526041d0040400e080c10321101d400c0424001a1102c015511 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 713634208 1250 713632958 713632963
    0x120f080c0102091e01080403030e0132070e0135010902070b1b041a09040e100506060a1238090604061a18040c0903110d0c06050723 58
    0xe04010f401010151071100140e08280f04c4000e04020513117580800307032036a4030210b008000310801440d03250340e83c8503221086e17035000c0007001a1000b1403990407401118500c2029190b04060030400074085010410510b90b83c01c854101d82462281c241d69201e02101d003d40200780c0403a100c501040340e44c280020928801c1a001049074900440444031141c564001004c801485a00f06c42d8007031000f0312050161811840c2c083e401a03207003681c1d03503050003031140024044602d0a0700305901540010400444420b6602172243c3c007060480329141056240d05020b025521483e10009180b641c4050b04031504201c5a688880b428014050400c0040b000004501e4804840c0d4407911808000d000a6051b2070310b40202020746011004a81454081148114060700410030003800307000308125004c0552158414020621001d42d211040589581004440100300f421001e00030015000d4403808255040d012000721001460607685d6003280382408005401c04000b14111005ca40c090a05070301c100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 713635458 1250 713634208 713634217
    0x50c030906070207051c0c0b040e01031b0503060a021b060c031b0306281a04090501150c020f01090f0e0901150608041e020d06140619120f080c0102 65
    0x1940304480c00398032612001e0380d8402c402d22880798000355160100044580d807140e620000303445030500404d840d8984000c8100e542258000140040484d40100217121402105925181410300507689160401c0013203502c0d4030009141e07481068001508140a559030004800782004010582d080380c1411600c84815510030b50723003c141e00450400d2610002e0804003200d00547c00107080c000c0400800803921100722920303c044c1841c1d03802a00002d51011802c4400a95030720b1541299550380c2811070403c00c4034010780000086030701145640c5205034102e010440215011500c014045030305500480e65041507412088000c0084800060860b040c508061702a114030700c0280301e0a6032800c2075503100d100c035200b82e000080c1c2c1d4801090110b6900107840743e14501034000e6201204880e0041f40580200d6901114150740d6003007014135842c0f102c140c082d0041c001302c2d06460307190f4040303103140d0007207955000d409a103200000c0d95100b04207400da00e034500035911500041e1680c41d0500100c1c002e421 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 713636708 1250 713635458 713635471
    0x141f0807030506040e060123030d0201060501020d090e0a1a040c05070605181f02040f0b120105040e0706110f0d180f03120f120528180209070210050c03 67
    0x3040c003c51180c2c9010300815054030800c40040c44030307078604031040c0e0291007041c2100d01d502d0201c00580340079443c1408035200b003250b55000460820300d00f2000901d03084030203a202c2c0c00c000080304107215203400407010a8220385108400f04010301c6100c41605400000111660b1251400d0b0130201e000d600280945052401442c0800496665826000300b54818040c0500030740c00c0b05400c660034040482c212101c2503011000142001e4480c11541e0769480c1541140c0210480484d06604451900c800c85001d000e09480603c8102c0d50201d042d580e0303035000c0c00384805100d410400004060800c11614060480320011143d004070f1340780703000e8511303460a200418511040e020202e1964502c1d01c206003243c1c0d0084a10b82d4000c035284080f103000c3c416194800c100101c0300004181d540b11400303510b011346080d4616801d401c2c55884000c0302400b001070240c00c01420060610807445454210544143d0199850086039075204012814100d107140a6403010337151100740450500f880010350b1282c80c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 713637958 1250 713636708 713636711
    0x303032a0c020307080c0d080318060709030b1515090105070c150212090303090405090c130203070f1b0f0212030309060f07050910270902071a070801141f080703 71
    0x1601c0b040c1891b16502000609a0070200010b48000000d500c40010342c0c1c800004401c032020f00c3c034019407050900406803a41d40010300030510500600000e1a4181e03040640511041352040840000c148851000c000f5150840da020030090b1180e406801160000340e030024900b011503403101145600c0101c00b1040b074005200d68600c00347d071102810304036003074100010001c504008980c4104409808020805c0e100c0c0d004a1541e540940c4a5242240c500031a4500150f00c929040b800200b12400c004181c4040050908440c0610340c200d040780400c80f500034002e0030140d030003800895444200100e00d0030b600e100020400101a00106840b40a400d140600341d0701c0340c86144003260240200c1442960105600c080c1241c04e0303000710302c1000004180c5038001c8164002341100700c00307014558022044150001586020000000341c003a0100000400c088080e0801c0180100149014010002411b0018822007070a59a0034200382036007070341c00960f2208001d40c0c44020104181a9440c01c0400e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 713639208 1250 713637958 713637973
    0x6071d0916142110080102191d22180c0312050304022d0607030905090115020615030a0b04060c03051513110c1905061605040303032a0c0203 62
    0x404060044410003c0200c00103486000b01c00c0d050ba00842002e030126898072852440054890020300142c02184070790340800c20303440350750724010b811041411100c0c2c50305d030f041c0552100141e440c0e607003402083c1180032030302ca640620402888000e03c2c18190006014019002c400304202c0e0000c900e60507644075801c079000725560071034140c2c0c07180020344009502c07640e42007900310072b40410000c0e03210240402a01d02d080100c10b002185203940006810784c0041d802007428845030920b81051030041400100000c03040500050013902d0700805440d4208030140c841032144181e90170051700380959004009030506050a1409900600b03c0b13080320030229043c440001c840f0380245400b0300281c003019060300c4200704600000c42c01042c07481d03042c424028090103846600b0108018a5403b04484070042c88050801d0601c4d61400c440100140b9000c444c09103100c0390503902605603012030341c1c9428046011410755807203481c04410000d004883c40c01e070031009c0c503100358488400d036005802a001d940d8003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 713640458 1250 713639208 713639237
    0x80709061202010e150409020a09080a080a0c03020309041a0102060a060308030606090a120f0b0c04080a02010e131a0f090618090f010e100606080906071d0916 70
    0x60318428815400806440081000035500441c3c0985101400524444501c4800030085c41d49030056008880041da011903008540f07038201307940030090981e0340000e004002c402c0d500c181d960300c01e03412480104240c081716001054000c005407140454003e000f0721851040f000c08202c851035249840e0300512554000c034107120358511900e02581e03003086000b072440c0e450000340452540410b50807600240d18860000300c22018184001e94140b01e0041e104182c60241005100a10702520615001c84200000c10007c2400114204410381c20309114940051880c00509240b141e500841d0030103051500c20b242849611020107400c440880d0440c00c1c500040b0140030000388203d642e240c00c50700840c000d50500c10041e40883e4001151000c07280790704010080e140c292003414031641a140e20108422480b070109000d07500203864203140010741c42c0f404d130341c0255841c40050302ca50306100090882c41010112200110072002018191030203a0505803080d50700c8405003030001001a03245445c60b840e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 713641708 1250 713640458 713640461
    0x70c06061509032607080c0d0918051512010c0f020114010e090f030a0207060e0607050303040318051c06050a020301050a031101030f0f050a05100810020d140f01080709 74
    0x920405079900c1c061036066940d83c0e0703895070004c1028000001032400203c0c03015210380c000d0181368442c50565031074a200d01007071407504111056950030300208217010302644074403212600c1c80c034000180218154a8a1440403604005580019003021294000049159054001c070b288542d155545c038800c0341002c42c040782240d909240c1c4400f2a62a0030040202c200d1001d01035821035200002d9418850078410440e10350b5104140c000e000d40c1049604010483d0000304003c0716034401e031001ea10f000081e0351041d86030312001b8801000d21a04545150111078076144600c0507000240601d000d040c0140c0380f1340750301085005c1c2100d41d24184800101040080d000341e0303041b51006466450100c0c103617074a02900040c041140d5041542e200303c07602c2e00750b0480c05440900303a11204d002484d400d00990347d0040e240b0081840242268401d0104450840029a0000901c8050300140c031500504200e40207172942c40007695805040c03400307200c00c0c83c11107030906040f2207800f2b0071520381640e200b40c00070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 713642958 1250 713641708 713641739
    0x5030316030c0f0c05070b0424020a170a18060512090f070b1e04060905010e0d0302071e090504141009020102030304080c2b0e03062418070c0606 64
    0x500003103180440e1400703140560b4540e80304a1040c81030314000790b101d500947d0160001d0340f061a007000c2e11420082420038140d1009103d007024409080c0200d695150300e07262031214605201c5180000541c600e0184c0701d860404514403030140302d840101c2d91034071f0040040d0000401c0340502101d0750081031081e800000c2801003005001c002e000400e20300a0000141d0708440c1600c01286240c08040407107060410050018040c03507110081c07a03505200c00103009000341d000c1035020701c401682000c04260000348240c04c4501c0420700c0081851250b015011810b455030000d8005800e00c4144010481c1c420004200528448100d90b0400045240b41083d126983c3c00a0b015800c2000410042490400100b8480c4c450204a60901a14080f8020f0030403c01c1d200e03103243c0c0e0822100b10402c540c02405800b003c40210010069030805654805414441d1341c1c0e0713074104405d003a04038070180e11025540303120342403c0c2843c0e800d031b841c141001402407a0010000c0300c183c1d241ca48049242000203076040e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 713644208 1250 713642958 713642981
    0x10090e25230d0f151508041707080706050103061d0604031706030a08040e010524040308090a050904032c01020c04091b030606241e0207080703031d031c0516020405040503031603 78
    0x8ca0b0007450080f41211942e00602060726122800c1011102165950041c1c1d4000c512400002441d0042c51804180c1d541181d0713221801ca4010005010101c0e038044008521a00740d6010500f464850000291400040b0036000741008400b242c0043c0800d0110100c0d8101c440980d540d40c401d130740100c002c400c502600d14005130107160a0000b031001c01d1404002c2d000022003e0030070481c442d00c0c0d80c0007540c20002214201c000400c0c06260080e0f1402c0b400749500d0410200d0109a06901c034280041c3d101c081700000d46000e184d0b9400000207021181d1380c441030795200000040c034500d07128140940600a5401402a03c6941c100c2075112080300c1541074000000c140c1d01c084001c1c13004140950124281c1020b201140b20340b8030f0118100405000b8200114800c3c1c4560030408907180040e07042041401c11144280c1011040b001d20b01d5603040b4040380d4544914000d035844c400c24400c00c083c42c40c2260042d401034541410002040000401580100520380503c40c4880100000324160303000920070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 713645458 1250 713644208 713644223
    0xf060f15120204181d01020301060f0c060914070303020d02032505010902040608010e0705120d0f020118060c080610090510090e25230d0f15150804 65
    0x3040c800510a451640203a0389506001d0300d06aa80c0d43e02407000c0d5003d004005100da9900380d500c4a12518000c035812680101000f54215850150040d00c4510710100410911521044600c2005216808400d11a42c030005140300443c100305015a205070720301080300588111302807640c1d950300000c107442030b241c0041066000000419041c2400c01c4a25004486940d00c52652074010ba6560003140054040040000744880e61081d401e4a800503075403240d405640c814616405c201d00205241c8100640ea041074240c4400c2004100e004211030b0000400001d070403041b00c010031880d5000103501140b2650b0b01070340d507143d4404110340032040f0b804030408194050020041803c0900414199203028107110101c10381d241507440754000111540c40f44420300099400e85190040b0440b11498111301d00006103071040c0000384030714041e0052402480c40c0100b41c41078030820ba5007180342c40341003424050060400201140c1a401c401d8042c030b04103010722001025056200c0d400340e82c07050390031820 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 713646708 1250 713645458 713645489
    0x3010f051c0b13020102011b180f15082a0405040f020307200f120c0610061b02121c02010606050a090909061107050c09010909050a030e060c0703060f060f 68
    0xe0283c0360ba00c1c44100302d06554943e400d00d07050006c1c540300f0381a075500176140c0c0300e84416208040301e514241764211a07440e210340c1000b80302080c40c03a44c0008005101d4280700d003450b1545260400e086800031807009008180c50406400c840380d460241c8116141079500740100c154846001c0e0030f038082102c013403002500c08940c42500540380f0303a00c1c1e1001d68032002516880552061709608120907407090b0407038020006048812260708000280e80311000000c01800c050409100924ac3c60b40702a440c03a051380341c014488190f584507031030190840e10020445214030411012482101c40e900300c1d50001d54a0f100380011494090021244208488c0da21401c0c0941410b003080000c090040d41554115615500d00380740d88000780c0289640c2c5d0007140101481c011401c00c0105030403058201d980c9060030040741100213840000e807041d009603d810140c00b119038441c081645401482c9124609214004001090140c02d030321031103802a08007014015152101100e40c12410346202b48200004040f4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 713647958 1250 713646708 713646721
    0x1404300f0b040309090609090c0f0f23040204030609031106010b0702090a020d090f050d1d090414060a020405031203010503030304150f0c050301080c0a0b030106050c0f010203010f051c0b 82
    0x300d03074081d109050900c3c0845e124510310003140d485030404045980d4946107042840368045400000f840304ea40d4699520b03040040d190000da0a501ca0030799541000c0781940740c1c00b0460207466a40400140c002c546603685c80c103146001e00310040068002c00d9401184040580002c0f07000d505841a504c0070307a25110880c0d0a04c4807180c5d0080455a0255090108034540c4e41c1c94020000c80e01d0140001102c035003200c0c281a414212140e45030418480800b0040c010080c041e1240c001c01d08044441004580d1503003400c40c0c203503a9803005000a07010b04010403541035220b5018005072082502110600080d4503e2541d50344800c1c05181ea26074002d00018002034400c48500003210036091011075222103105005056644030400007006c54070200051005c644200801058001c04495174203074a4600700c1480824403040c0210020400005900341c500282000959010065400215036a607959001001c1c01d0314503000300f505c00c144547c5507002031a16200c007680ea003500440a01140e880f0311 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 713649208 1250 713647958 713647973
    0x1107081c0528123605010501030c0e010914150607060606050d0c0e061b0f0a030c140610051009030c14100809030d09231005010603090f0b071404300f 66
    0x44404000b01210700d0298001170f00030b025045c020f520450340600c0e0242810040c4030544d1050b00001c102a14103040501d07200440a07107541c0248807441160f105000c140080f416134461640041d16483c03c0035000a004ea92140c010400217054080400c09980c40c080c4c1256400d085010403507101401340000c220441e0308440448040d02c0c043c084a000cae503006038180781810700d400030540c0421205403100d0180216154220310b1007070300101902291800440c0207080220902455005094100342c682d8282c0c003818000d0061604050622510790f5202400c1c3c0003101d00e0045a4060340219205000c6a4010306103e4041c86100780650b0629603d02503410007401d141c001600c0d46111141c135280c424010031040d4866602403405003841404842401054500c1a8080400c043ca880e4080d0b02160350680990b02da02c2c1d0007410200385490321702003200c07043c0314201c002e42e200c5030001e030015005103044180c0009000000b4201070f02c0080511889031062840f9000d000380b00c10100260004924 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 713650458 1250 713649208 713649281
    0x1d09010e0109050703060518100c020d08070c03081519050f0a060504031205120f06090c0c070605130308040e040b0a051e131b05011107081c052812 65
    0x230000101482051450200c0c6080045943c02100550351388035144170035414080c140c2c0c9a09607041460985c213000300c0040610702214405400c202c00313030303001c00c2130224100040814408020218982054a407c80541d2407407184030300d9100c0c0e40701009010b01402d11203a0042119203d458072802c0c9407030b5450300ca04030300201409500b006020059040c00b880403040e02801680d403036040225078903000040c403400354400780045440704814003104460a40010308903060714101e1612039100d8046100c148904113107030300000c03c0700b070012070003041c80038041c82e00d548154041c7d0070b010300e02d486082d40c2c502155029209a508081d000410b00032800880102942184641000101074002501c515403c2c1000d1404412003000844041045691290000c0d00d0312006201a148251400102c076179503155190b1807c80b03000e201e01241c201c0f03600a500f5100354411060210003011040001c100b001150169400e0100c0c0d6820652035603600030b84143d07105246c7e12401c42204da5142e45046e01181c05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 713651708 1250 713650458 713650471
    0x303151715160f110102070b06030c12100e0f03030a090314070507050f0f1e030c030102190e0112020a090f060c050a020415030f0c0302010305090a0f110a1d09010e01090507030605 79
    0x1300e500da0001c00503007480103042981c001c0c184c0104a0418404140c101525000c01510500b980a1841040d04020890006804c00450006400381404101500748820014900d00501000c410080007105c26005521075600c0b031382d220790b542d4590440016540c000c90a015003550301c040b500344401c0c100f0742c460002c17079280181a68400145000020750a88642410440c0806460480c0010f400c04011b20360301d80d40214001c1d406c0803602c1c0380850424542c20900d1081200040300d0202a03409131603010010503c03007009540e1000e5008004e0468410340c03045160640800e8400256036104541c0700e01d102e58041c010b090030b1030041d000c000117030a00b090b00c1860110300398000400a099002e6402103584920000842c1c90326600001d0700300c4000a10f45c141c19008001c00a0009508807400442a46e01c2481031f0780701d1000d00302182c082004d54101d00ca2800d010041e140c0c00c201a40301e9607102c3c8030380314001d02800a030702d00d0b051300382d40c0850801082d42d40500350034000524a5040a9840751 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 713652958 1250 713651708 713651717
    0x304051e040507020a4d030a11090105011e1409030f24040507031e021002011b02010e0d050903030d0c0504030b010e070504030305070303151715160f 66
    0xe6003200010219001036540b40c001d6400310315440100a40c210014a110111000c2c80e081d0b580f10503a031000081c03a2412185440803951199206c010b0410946c0164050242c03c64143d81c0d0340303203403030b503800700d00742c00c07810300c528000701c00010690310170740c0c103650b04100d11545022544503011042d01d2603e00600c0e4a03801880600203540651820090031100391084002045556071503000140c00c1c95041c0803d441d80d5a1100401c40450b8002070300b00d0880e42d1040c174400c901070070311483c1e008203600800001c0d8003e503021811040554150406103403a0410740f1079405900742e91805078200c801d002400001900b1000200752000d0040003c0c0c0031012001d000d45e440e140b82c40d0310340c0048400100271a000710700c001c0360a00500c02101a43e81c0502400400d01080307003030200d809000c40c0103e2200034108000080c104081520982200105800f10518501066103d034070409800c0b4503111450260306c50304080c03c001552000710240140001381408442114000d000c44141e000c000e0b8820910 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 713654208 1250 713652958 713653009
    0x50a050c0705060c0313090903140c030426060a0b0f150f0304050303010e13080304060207031211250b0c0a110601060f1403060a0506090f18061206010305030405 71
    0x1903c40f0300082004103550405582c0d0351810141501c158865901711101039494110402e000039000802030700001c08001c2c2042c1c548030702d84400d0b0303c1e51017150001400c2652090b21100c52160340007114501000701000d9407480e541d00000103040300c071001c2989038000c4101c40c0b100c0c2c1d241031003841c10151943c3c802030306180100035000010a640155000c8400383d1000004106010b900c80c0c1c4540c010207900c910440b041019280c0d80306a020140014100c00d80c00a40c01d02094003481941c005610011800d1080300414400980c0d2030300400908415810030103042c050a14001496084040d0f01c90145900c58850300e4080b21560066050301003400090446620218030800c01640200304903600c00c824480c1101004041014000400500d44004d00070310520756070f0085141d01780d49040e1903058460102c480041c25030750801c2c070000d07000020000c40f4404900341002c460f2150100b40c484044160582d00c03196502c100902c80504150014001404249005102110740c2001c150341400c20 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 713655458 1250 713654208 713654219
    0x919060506030f040314030405150c09030a120e010e130902010e09130c0608041e0501110a0224010e0a0b0a030c06080a0606050307140f0d090305030906060a0303050a050c07 76
    0x1954400c3c1d400f1914030081e0010002055480a03917214a440001c214a082d0708090390b80940e1f9001080400c004d00f201e01e0001903001b0500300540b445014020102d401c0b141550400c1e0800c607241c0c00c0309030002603d07100700400c194010808141c202c0c4024008034904c080c2e900101d0000c0c03c0c0c00740100d04102420800d41c1c0185d03103040d4100c0c060300070340f412054100904c0c80c140104808945c455018042180200008078440081002850007490100640050a40740c0b440c0101135240c1403504031800813540d2003c290f4001000c0e100d03084c51401d030029a00c003841741106251024419514543c1c04540022041d83e43d5070004101c40201600898040351640e50b004800c80c219042500010841400c02003092464003821004100d40e0402078614100310b603004000c0c030300c040840e240481001540404030341d2140111344d54081924020840c81350b41d850b00400725441990300030114401c10340402c460341b8200e10035408599040d201d0a190121011090340c9941102410703c600d0b01690070009003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 713656708 1250 713655458 713655469
    0x6060d0219030b0d110d030903021207081002180105071115030a2306060903120a0c2108010302012f0105090d08010b04050103020f0418140702060609190605 69
    0x8001d11210100d540003440703890020212003002c01520f100c3c40c9a19003002c0840d401900c100c51030002a2003400b244c070341038181a600b0290f1944000d401c1580d12940955002c008600d41c002d0300d040700d0648410b407411341c52050a82c02019480014106244814401d5600480091103000d205a8400212505900000b82a05600c5068140101e000000c00c4000c0e02c191085a00803200f04250f107481707050844400c540900010001d90003001c0c002a0b0014076030701041036200c07210b60040700350354074942c07028001c0008040b0603080798170b2015a0403002c80f0b4800c07218178956080146e40d031624160700e550011600145003041c04034103002040140c0840f03901d1140554021014003001107214141402c00038a403e600040703c00800910f00010312007070303842c5000c440403241c09280258540b004044600c0b480e10480d032001000d62004030380c15801391019000042218456049080704d95100003050380c8560040310600c3e40200410300156000e00c4840d00c200080c4011180086c078940c80f9001300c0e5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 713657958 1250 713656708 713656717
    0xc030a0e2202070312180816020a08010b01110307031205070c140a1b031e052806060e1512010213030b01080f0106080a0b0421051902030a0207090506060d02 69
    0x51400d07400140701024117401001d003290003081c01e07004009054420724041403059a038103000f442c101c1d000400e940c02c401081c0ca0744151a8008040c2d0a149070b40b05402070082c40c801600c0d9000c0369000142180c0403901001b03883c200c50f0140c840c4824090000c00e01c40003000010404c2d024054a0f0300818045100c981074001d030f16002d040200340c2d012240c03e00f40f25005c007440301c01260030035071441400003596140101811040c0400c4028a00030344c0d160440c10005681d003000c001c402d6243d1850003c00c1c0c01002200da1a0244000f000100d4031012705c0907805204489449580c2451803d511036810b04140920410306171100050618013280c0350f1006403c2c40c2d520070342c2c102c0001801480750300010b0041c200749078000e41c000c100003803034a01c400740c0392003074148090049510680000e06020342000c00324481004400d810034031603950078020f8490341013071040c0d882d2140b0705804030010750700020440d01e010110b40c0040c09018030340281c0e84082d0600405141d0084014003407001d44294900140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 713659208 1250 713657958 713658019
    0x1e02070809030c121911090f0106030b06090f22051311030d170a06091b030b0307081c0201020c12041701060612020a1115010504110c030a0e 62
    0x35512640281090302d89001651414404c111441001040b100001080c2120b00000030003440e0880040c1031034081846005542e68024020390108440b80d2403e4020b81c0c107880154804010001d25881444050301403402a240c00075009103a0b02e4140c9009660b60440340c00d010b0000c1c0d03101c2d0a000d02c1900740c90003a60b14203284600c144503041000084001c0600203041036009100300651800d00400d440ea0340d0407015803940d542c1012800200c05500184080d19045006000c0840c00b810700f0403852203201c54200c0024504103c21030309140108006007101c01043c014120a034042e800610042d2107000c01900350b6600f0008241100000e10a1030035500403960600d80325480c04020792207484140010741000e03403400b00184140c0750481013a42421400309030040c2c450810306803da403050b070041c628100c14420214580032140b5200b1200e0b0584000343c070144411990408984402c0c054106001803a800600407507042c10721031003010580c110010071041c01203c05910f200070f5030480e5181d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 713660458 1250 713659208 713659223
    0x607110310051602031c0203070c08030f0601110a02090f15091e09121c06050303031003140d0e0f15120103170901052b020f0409060e10091e0207 64
    0x401010240304840007000d10340f540090340c40d01d003070b030480030111400340d40489002a5000c070200d84440c1c819501d01c0e04243c1d001e244070b42d5a09007221a0502d1030310860b41c040c001504400309081c80040451038542c01d1354060140c10458035031854420340098000c0020180e07402c43d982d452078690721a100356004402e03c443c900000d402c4081c0748540c2c140b0003047c4001c0c2e50702640207401060f580c081141da1645000e42c00c2408030036410200f5000e8441540056850b10020003800000865940102e0481e40300e01e0000300603440400c62680c03503020058040010a4581140980c2828400010702c0050f00003802140703201c41d03224421010b6000040a901074450300d10050003044403d524503240301040b144500d04000040000030715521070340040880310700480344009001c00303101341c0d0469030780803240b0155100e030060510740e00240c01a100b80741c102402d007040001c401c100d800007075001703000b06100000424181b01d900005015200000f0315030000c0301000ba24884494805450514400c820 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 713661708 1250 713660458 713660461
    0x804020415060509090907060906050f1c051501090f09050402040b0a1e14151c020301090b010206061e060f0c030a0302220602061501110102070507051c020d02060711031005 76
    0x50100170b900060148070603500140e01800003e400c441030b030b0100c880c5803070950307030742d00391159110014098039404040c484c8800740e00c405869485e821140c8990464003112552140c0031b001103618000034864103500100711f070410b100e001c05940011364000d0000e000492040d00580c0403900c03444080d03011403500c0c58141100800700304942c1844004050803d401d10780c2001910000302d20001110222242043c00543c4e4460004c48000d0342e081c8c9041e840301103448ad80c2d1000510050640720982c1130060040c00c0009103d441e000c566096807034140044070035014038000500c282c540c4002c0611022010074848518039510820040811100341c0ea00941c9034056800a40f0190140205581034280c8a090a0140035130008015601c07030b8002039440200c40c45000140ca2a050404001e0055400062004107100c400503040040302e8094401030410858600c00d00d21002600c00000d522485000301074015103045000b40c541c00d40100c45900f203880f107410000c0d1814200d02c0e08100780c81d84410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 713662958 1250 713661708 713661727
    0xb0d02120a020c070603020d1805030c01060801060f090b030a0827100c06020a090b0d0905060c03100b030c220303030e031201171906020409110a0c020108040204150605 74
    0xc58030703400c992212425030600b503401c40c0564a60074180501010140d01180f00c00c41c6945642007068040e543e5450b0140500850500740d44035800700d02030901a60a0000c0080e4205c41440f0301c80490310076141003403050782054041c0d4094031003422415454400c400d5410702240c4442c004200c4100307480814680d00d001a882c1d41001c801c21580d42e441036400860038004190800d8081c0481980041e0041c0d480021075001d91301c0c3c1000f5000800d5899012400b184242c81030b52201240ba130054041300c1040e55031a4a0640034072044034403056000c10310300108032081d10000510380245c2081d040c0b5050070410341d100c10400340480715107800180b101800308103054140c40b80580c0391900801071481e0104211108854044c10f00c6482101803402c01170400c0d1450901c028081c00440303914a9a0700314403418802d01940241c051456492714080c074100d0391514410440b1005044c0f91100b51540140390015200100014816070300543c4984070103944180c02842c01c4081d10b86038485a07107403103220 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 713664208 1250 713662958 713662987
    0x3070c140609100b060334050904140702070e04031407030e1002070506040506030a09051606020c030a0b0a0f09290615190c060212070f170610090b0d02 67
    0xb030b0311951001d20700024040d07241c6601c8100d96222030b0b40401f05480e0081502154400e02003002248502d42c0030000624009910000801300f082c01100c05111a140700c1c09800900d020a44844000d40e10080e42040743d50b10010001d030344a8041d0800c540c00500c10200d1100692003510200d0028440c1d0904c089246842103180010b0b403150f1004150050400d000b01d80300384103e025651094402100040d125103454000080f11a444000d0703811403111010040b144107030502404015019910400d0a0b0381000074402c049543c0002d481909600c4400511004103001c80580c01200e1b191025000400e01419a45d0b201106401c580d000101c00d04806e4120b070003020f46040e2080c1002214065503645035400e440e44805c461100417840341da440402e8a99500c0c10100400c07071400071070b00c6102d000e41d4091031885050035481e8140e02001c5031808444c403108900460f442c40000101090950a041e152588103110909120000507142c010211158101801003260160006000c0b14200801c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 713665458 1250 713664208 713664223
    0x10303081612020912070b130801110306010509030a1202071a211f14094501020c062a040e0a0b06030709230a0b03070c140609 56
    0x2a40d21034421200302900003000c08038000c0d108400302e5004501801d880c0d0310301c070261000701001401c50b46881d9a503920b000c51500010840c1c148a810305800242448040c01448107950100300030302e1965681c00c0065555400c0110401d81500c96444068001641801c2400c2e2201c800e0300140505440c00c981495440c18044014052003030610104d00000400c00102c0700a90701c4000741142d0f40e448044154100304034220886401c5100500050055a02d0104041c021015251450b10fa980c040c5a055034000c4c00321300c00c030341030103901d07507a400e03080c001480350414290001e81072047c031102c680550036a08079007411201600181d06102141045601c2102c0519007111054280c1001d4a1007110a0185204420007081804000340d80c4041640c0240080d6100034071650301d83c1445240217010540d14090206440e4100300c041d030b20080d15100c44030400c003004000740c061904100500c00c4640028040000740440c03d5440c6001910000c250440103861034001d10301c1e8902607850341d10b0081c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 713666708 1250 713665458 713665471
    0x605040b030604150b060708120105010c02090f07020f160f0503070509041716050d02070905060a0504090212070e0919110402211e1e0615090a0e01030308 68
    0x180880c00021030310003107042d40e4440e40014040b00c500108401c0718000d80305610b040d540c410300004110b000c1113009406030415500902c0d214034161b0b215401540c103904044000b03940010b0707ea002494680d5501034050384803040784140c0d18042c2d030581c94245040b0324942d0003c2030300d00480050207080300403401600200400c4004090141c0380002041051801400207071603621180c40c40d80348443d018085610380e56144c0a0781d400700704103043c800c1d01c907165100c0210050099490009010105009540c02550001c01c80301145240900308001000c2900c41241c011100c0c10010480c11410300c019002401e5240300c000c080d1a0008a42e810488185000448120070003042e1000c40d0051552404042054600507501e94115072441110b403440f2607444620f005880410030440c0c03141c42e00e003184840280d4000a2030f100c404005407122038080429058003450400120586042c10368130780a50b0018400602d440c0e2854040741c444801c6030010078000020710010400c040e030000500380c0c0100d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 713667958 1250 713666708 713666711
    0x20a210501120311071a03090d030603080a1d18070f02061515090904080a18150f090b0705030406120b0d080c07081515061309020d06091e060504 64
    0x60411840d00808094044098100400c4e45003801540300d0030080003014094509026002400000c0c3c0c4040981c0203c5144800d8042c896905001a001e401403e040e242c0c0320554604203401620111800000004092a140e5800420003026243c0c00e905001015103030703101c62820b14101e00060078440140307a510f41190310030001c1041c01030782141c480d12442000c60f0032071203c03204c001c020550360089182d0035900c80c40403418403040106420081c4840c14068842e0001d0026800142101d034505105114a500d4066629100b29205074028400e882c2c4070f0800d0642d46031250601d081e01d80003008100e5403640005418042d2903005400701d01035203102202400b00e055020046004e580100310018281d20001c0b074642000c0c0380030702c10603011f0104501200c08491800d465041d00800581e81d00a071a001038101f03801c142011421035040c0004004000505441d0600d000020b5100c560425500c40e500c59001c20b0041c00d0b405242c0707540f24041001c13040c041c1c1e00b40143c412941141e01a81c401c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 713669064 1106 713667958 713667961
    0x60904140d080f0112030c060b061c0f0f06140906122a19060528080f010803040f090b060c060f0103030810050603180709020a2105 58
    0x2203000343d03840003413030f40d076596400c000c82c00300c0380042c0000700034041718808074a09400140d07107040d01420340c503d499620380c081184070241e401c0c2d03120041d0322002d061b40504120b0207081c11180030020100055842d140c1ca404420310300003005401003041e03c0020b0100e41d101d400f00c01c4001e01c2c42081d10b1000043e10703600c13180442c1017214108240031840c400969400c044000080120b581540082a00d00b4000195015042503095022450710030f90300c01c00c3d40c1000f00c103a00c00030f07290742c07200c58081c200307002445648001600030807519407080c4020030603503034a02070340e404607076210074001030800308803021610610608404034181c0c0309403018051411000e0016904030b038020382d1020801e85540c01503c0380052680320b0141e01403c14004600c070f0780c2407504011006940d04045401e250750310101f02c03040c0d801c1200810040780c1c42c403224060090700c83e40320004a07041204100420f = true := by decide +kernel

theorem cover : BRFrame.Cov 713489208 713669064 := by
  have h0 := BRFrame.cov_init 713489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 713489208 ≤ n) (h2 : n < 713669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
