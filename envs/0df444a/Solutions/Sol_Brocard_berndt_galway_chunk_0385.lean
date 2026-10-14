-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0385
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:32:26.053875+00:00
-- url     : https://prove2.me/submissions/c0929bb6-3198-4ab9-83d4-3ac7a4f72526

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 69064750 ≤ n < 69244606 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 69066000 1250 69064750 69064757
    0x71b0801230402060702180a06081c05120405070f0609090f060510121d06040c0e0403020303011a0d050c0909071409010c020f032407031a010c0614070f020f0706 71
    0xb0344554080040070341c40f41e5000c030307404403030352001c60341e40c001c0c16810034401d22800303500064041c90003c01d82d080000540d66140700300d01d4030a415a000c0e410206545000c20040c0c0f58007110343d51880d026142844d0f54100f54140c1c0c140f074000140543d405420042030b9455010b003400910580d00028041d03c220303000309a44442254400c45219108a5400540c01c083ca44041101c20020130b0025240000001545168000d40c040100307200700981c0c5a002040d00c180380d00418507283e2030003500e901042c001c2d4a0000504010000451444011380b8003111348880208418146a180340d025030740014401d500802d4524001401c0c1e901400b400e0b600c030508000414034000000e0300440b8200c1d09564102ea2140e41201001d400d6201040745c507001506940c411501522069484124001c000700550101400c1054032181052080803040f8806001e0070050010105840c1c520f001c1e0816142ca142005a19000c000f81294800a400800403294007a1010b140c0c21440c02904c8040074000d20011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 69067250 1250 69066000 69066071
    0xa051011040b0c160810150b0f0f040803030a0608010c080c0f090a120b1918060203040201260618010312050901020a0803070c031205061e06071b0801 66
    0x1140b5108014600300000805545150b8104030120b000c900841d04084525070106101c455001018403648000518040a5500862a180580e030f2a4403462800e8844400c0c04140500c50b01044800c2d140500684c50035039890380760180d10f2100910880c41a10410f60070420022001802900500d0044c146101c1180c5080c00401044010b036108007490f540000442c080051519410851003050034402c800250070342c207183c0c00000c0c0e070b0b40941c03020355652071400c0000c006081e03420340c8920368598000d0026899540d00d00041c0d90425160713002c412019550040c1e100f000c4800140b03035100302c004844008a20f581030003401c03011031090200030990000c21320002920b1340240050302890740c0520403680c05055075601c4a40399042a500b090124500c07121680030036070400c0c12100c070303202c020100b000710b842c050340003c6040101d0302001d100400d5001c103003085600c41c0c40171284d01c6a04a80b684c6c1c640b205280c0310784001020f034411104594a40a0b8100200801c2c625829400e03030039100b01c8030b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 69068500 1250 69067250 69067259
    0xa0503102301050c0a0503040902180a060512040206070b040c180207020306010915030c080609010f0207150510092a020606010807180314060702070603060807030b06030c040504050a05101104 84
    0x210f9070b00c1141d20340756501c6448595800920100000c001402480c980980c60700d81703544c400c60031100700703400841c4111201d6005024039503106c002d035002c00072200c940002e503884e21700100700c0b98403903240064440c0548000300700a00203106640011185545008240c5001c2c0e9000e00d0200d000e40d50009506030450401000f52070780a400c41c940010500405100b41d65482e0b45030701e1060450391200ca903c0c0c00c00b9007048540c1c0030a2045182c99003030490103500d080190380d16240058410414030aa803545c0300049207108068880c1c940140114490400c180d00c6101c51741c1400e44102040d10381c042c003121454000481c4046000d030b000d05c3c0182c550b16150303290040151001340300441d040b8034601c0d241c14004042101c200c000302000103450702402082c106210000d06001d1035070400c1c01814240841041038400001c0c0d00303000c4036082004405151280d0001034140940010070300e0307000b820301081c8020311401040ca49a4240f2400c00c41d000a00300c1001802030700d03901c800ca0303402d40b00705000070030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 69069750 1250 69068500 69068507
    0x303060112020c07050414010603051003030504090e0f0d1d04090b060112090204180308090a0506010506090109030c090212090a020306010b0706090506040809150f0d200a0503102301 80
    0x1144106003056443c6240c880c801b00e401c840344050014079150030f0307030010040180c143c42a15001410407120100e50307411600c0141c2184194410243c0d0303566034080c1842c0885080c40762103044a01941500d00401ca101002003503143d81c03500d10103410f440d103800b00d40145418450303128241c2e8050105810307a6521001965520301c44101030301000d80320414200103907203600c03c0c404038a4414203c034400f24568240109114001003911304564803aa0aa40100c0c10001c2d445044810844140e81d545200000481d100640c40c0c0c0000c0201c02c82c1400410b08a60130340103407248105200305a8055620801031603030b902c102c1c29029400d900204010f006030311200e4000c2445a015034004520f040980c0c0d203952404a040b2800d845c1c0d8140451490243d04e08642c40c070b100010340000050901c42400c1c183c6c0050300c503039803410b00c0803503585030722100108000e0b2401258651085d5003e0b00c9144c18ac2010707110b607004542e1400b14004986002c104203842460303181c1f00c2014101c055090403164001075 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 69071000 1250 69069750 69069757
    0x30303091b030304031502070b1806011418010f1a0a050403080306010903050303070f2c091008030315010306050a03080904050603030c011a0306070206010e04120e060703110609030306011202 84
    0xc54143c0810800170000c69048005031594480e442c4005a80d20118103101c1d514590142442059a000c4203441d214060006926415101da00650802e0071031000c002800d0b07440031080311444000e030300d0000188051113001000848988441e401c2d11f050f0a15840e40e81849991110808a002800140b000c550013038080c5600c410103041028403175071245c96080c83c640044580500052200d000204290ba01071080c10401c80202c0350040c200702a644864480018218a140521002d000040091300070b030600d00c00030705220342074907542d0a050313055807150000741106c0e038042401c7c8034000810341002c6840f00c0032260000302850074500802d0400000e007101401d046d901d03100900202003218020701c6407070340c1d191510403280d01003110705050504142000301450700f035410174001009090480c1c40d11031f5100c0d1b4031040400650100000036903182c240b400718203130010000303e030680406412110311540d405c03900080303444903511808080ea0b64801100e0403400110104020381c00c403030941c0c015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 69072250 1250 69071000 69071053
    0x9030b09010f09050c1302040b07030c0f1e030f05040b09040c0909050106030603020f0d050c01080a060f06050a031d03090d06020705010218090108010b03030a110c0901090608010b03030309 83
    0x4218000c0700041001583c0c2141419603d50b00541e50000c05881c000c61080742e0807000c2c110541c203151600851003680d0003030a07405010b10914030f0302d0304204845100e007021010b0b4001c40d102e480b03114502c2410641c08401400f20003181c4002540004ca0f03000d071066904545842190318a400060014171018103506141071303052000040e0040780018485c01018013800c0640e030001002c514500420407282d24801581c0c0c06010039009140c040750b0041448210b40d0000e08040c3d806480d02c1c3d48590040c496584155030122000c85c010400a074454001c2280b41007030354041c841000c4441300c1e0000818240b0819a0541c0b0810000800e070418080740b142e898018070005080c0101c40d00c0d01c0d82a80c0c007421340440c55034400d51401600d0318106045034050001038000f08181e10940001c02da0f24801c803004042407140c511101500d184003041603001c840c10203002c100d61940d50310705840107441140256a03d5500786500040c81e402d0001c1542d10410400000b0324400840003101c0e100240c00201 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 69073500 1250 69072250 69072253
    0x11d0a03060c0e04050403030506031002071208040305070807060b01030507023c010f020d1107030509010e0a03021c05010c1b02061b0f0309090604180b0c041e150f09030b09 76
    0x3803c00301a40c4520805224600984001c65039181c0041014107051403442c9080340d00744140800c40c041070040303441e078400c0d1001c0c0c142460583c886c0d05041e9698021080000e100038000940c0b61b040044d00c4d000407110404c2030300c00388a41d0f2650768042e84c4843c1c2d00052208038080080941423020040c0f03419030b0001c1e80340d00c410034140125110050950b1011a02c000c62030b500068602c005070928801d80b0100ba400050f0036003070480d1550010a948295150103040207003025120b80c0550b01c840b41c1038001d5034010041c000b2078070400c482c180f2141c0d84050a6a05518211038004043d004840d1034450f48828203007610400c59aa080003155003000c040c400f03040442e00c2a0011040c030400101031000000401503407035442d9041040010100185410b01a6040a0b406100700000191001d030b2240d001030a0003007503403044800c50140c00341d42d00100148280d90780da11071028416846005a41c0414141414a40c456809030703109800348131032000080440d48100041100c48411a800000540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 69074750 1250 69073500 69073517
    0x12080a0f030b03070816060201020408061602010f0905010c0314151201090b18070609050a0311041b201c080405240f060d02130c021e010506011d0a03060c 68
    0x100f894410103400502c05980704256606d0802c3e420010100103189030707c000d5140c68204859161600c001828058046d40418507010066000790001850b961012200b08156052420614040c0244c41c2444010a01c0e1104510110b0101c41000f8403030200d0400ca40000380204051010341c11500340c3c00d000c155070f2002000d0004400c080c00900038114500c240640c190b022550700d003407030300b5036000d1428415491020811030b2140e403010421660015421400d0741e440c940802e020300020152600d02075141c03406041150b40000028400d07c050241c1880411036407150765a0303803108480c0e15261000750107440c00c101482004116840351241c410b5859500648035102c8a0041300c4012410400c142c10401c1005818140026071020301200c44200c001826004102e900486900380049640c84585a80040d4020400103840c089030f03000181c0480c200d40c09642c02030034251181800120701c4003101042102051054a54500040c4846901d03490b5954000040180c1d8111109002c6000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 69076000 1250 69074750 69074771
    0x111e0906040311030d0e0901030b040302010e010e030309011404020d02060304020a09060801020a030506040921030b03030c0a05010c0f0509060a0e0d030c031407030c140106120804090612080a0f03 86
    0x40580002c500c107514010340d558040b8105402e00c5800c640b00b01c1000302d140004180c40e070f91445040e0440f90003a1070354849840f41e0404a01400b1191201d45056003482c0070714841d044000021442003030001c1c003c100c4042005040881c0d44030546000e98041c83c41c08185015140c0344c0f00031904940300900d84207056554120f039a060302c81580c419059a5404500034080d04d4041c01b580307038480d204803001c10441c40c082d544c80490350a0743c8600c05d000f004202c0c0c0000014003d9006001d00360b0000c0c12251166a00c6c03018540d542c05040c1d08651035400d100341c03500198010100d02086440c42d41720103040884010501c000b680080c4005004c000c410b0700c9100c0513440e55081c150049000303654803003144000b810050f04018000704800002c43e010485400400d6000c0380b1141615400f0851846404c24804d00030f025001c2500041d0428021807a00810480b20300020030480b075902030180005640c8144007100c031600d900c0050180c0d0810012044094410001305400c0641d42c100011594001e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 69077250 1250 69076000 69076009
    0x509060105160c240c03030f020904090b010f090b011b0501021e0c070b03190e0a0210020303011802040f0905060301061806050108090a03170c1903050708070201111e09 74
    0x1440e400f940c144441840601224182ca101d080701107805101c000b0107074090074401084c07071060290140405a454800300c4034020380d50100c0303840040c010700912103882a4200100c80d400c0c203200d103604802d0310b0071001510015a00070380c40d51080503110840c1a8144911000745c0c8061210200c0f0555820010004181005060003240c84100f600d00c5440d040b29005a610f072000c15001561149024800c00045c410141b851785c0030b034139202401255204040004c2c514001604200070362051380c04020004d4958000301540c12184c118a04050030103071012040100c3c803d90203408110b0505600c01c0c00b000040750001a0848030160001400380da40e01e40200078117446c4c0b0ad0341d071201910b94100308001d40e40117501f02d4000c140d120241203e55140d0b40c1c00f810344003450b44a50780d80b811340e10000f02d90f040c3c80811b6610f844007a0507000851481070b640200141000c848400108440c0000300da8124414421804505c800c400708034500340c00760408840000071403803004840c003010400003046494 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 69078500 1250 69077250 69077287
    0x1605030d061503060f17010e060f0720030301260d020705030c0402040f030b1306050a090605160207060e060705071d0117070306021b01020a0804020306011e0509060105 74
    0x6001030001406800c240c5002d8140d45050451020181014000e00c2402e8200742c0000c110f0b01d00c101c49010300c25041840340e0240c004040400b002d03000d6074080081c220440a14a0b110300d98542e111203100d01c442044401e240c100c0081030704035920600044c410a4582c82c2e001800d0f84084c110140c0019143e81c0051408181808602c0180c01115082040341410402107484603400c41c1c00750f04140c02c14a0480504041e40f0028011030b8084012540501d40d00100b082c1d042c0e04410203004502c0d00c489124081c000a00701280c416242400044280a140031044800540390b03002d0046c1d41d140c8502140d40f2400c0701c45042e4030200130440a00059010000340e8002c0004004800083e0040d40c400c9404500591190380e00c410000d0849001d148042015016654006d8005071520b00e2145120780d1845401c4818006603c000f44883e000d5400c10051340c030a40c421401c07683c06a8a411458103500c0e641c0380d041500c3c43c405181482a4a01100c1d000e90101043c5003140c00d054140b12801d00140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 69079750 1250 69078500 69078517
    0x1050c0d0e010908070515090402040e040b0412140307080603011b080f0f060d080c010609090501090b09010b0307031106090a06110d090303050a080a150b04050f0a0503060606160503 80
    0x19078006406000d960421001d40041014102030700c2c4a80c03508000c01d03041840700310080940384000501c400b10f075469505880162140300310051942c0381500d8035010000c015242a40c001d0307079064130f40005c0740c4642000e02c1d80d40000100356065480d0340100b41c2d0364000103000c82d6415521480e01c50f40c0050714060300e9141040c19a40d1042ca400c0107113041c150b840d000b07450513400503008010414a900d40c40d041d07186076a07020004903034a0403c100d03140d0040190380c100403415410002c409080c01815002036282500444138241c0607140c2076041822100d6030211140c00d60003480040012070030200ca09c41c042000a441b440c80d101c0c98800140c2c0381c00c9640c005402040b4007241f600103d100801503201e1519150910021860442e00c02500794041c0881c11344c1049030000c0056079401190304500d0b2242c0c00010030442c620307211a20701c42039070418050305004901c19941d1003400c0c40e1a90f1940704441025019044030b40b50b07070041c40302a500881c800d44144203c1c144900000d074003000100001c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 69081000 1250 69079750 69079757
    0x30c031002130915170319110115030b180a060e0a030908030301030f08030a0b0a08010c02010b0d0f02040c05120906010e0f070f0521090c0a0503030712080601050c0d 73
    0x1501010315422041c0050b03040114418600708a505550308100740070005c0c4d4140300b05c0c2c038000c03e0350408140d00d503200791920801c60048000320050302d2a040000840c98541c1c110080c424041381c03894506e43c0c501c5a20020f00300140c280042405608001c05001b42e00d103880c07040e43c1c50302c0741e6a2680001d0321000e400c820302c10b520403800b90042c1a800403005000c0c005142c091803031545151034a001c280341250000d400b250740000071070552011030340204500c41c0d0150840c5000b65841c0c20f040e008110602107080503500703000402d0424034094407800015680813041c12109019a001c0c80002c000c0912071406000302041225840d91040c4c1030385101d0059100204200d60506a20142c105005000c0402c2c1e40458001c2c001c1594201d4540d0000c2d1240d40340c00340e110f850040840300101518a0b03504421040c5405100d2a10350200e84e00070080310503203109030400d81e82c10a140d564413803404094104071310800c1c903000d02131181041513001391052422a060410150705142031040d00c05000c0d022 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 69082250 1250 69081000 69081007
    0x204140301050c0705031207091d010f05030a15110403080d09030201060e0402011209020a0b0c010212011d011202060d060b0a120c090e0604110301081018030518030c031002 76
    0x11032600b405403a03441410401100d00f01036040ea240c5503240a020260002d6981e03060000f010310b481141d1203002004040b9031442c000c1c44041000c4031064080c05015450201c9110104031f03402d00080032406a03a01000007500d4010110308803008200d102d08000f0541e5080000001088c820390140c4450141c1a0000803085c0d41e600e03019084a02030b500c203149000c0b0700b00030403000d43e8000e5030340d01400c21450000701381c0e8102d610019020a040d071300302c0e915483e408914020b4170300f03055001e0007402c10650031060f850303600d0b2620085503051074500341520200b240010700c8980c2c0c0341c240d8010241d101620310b5007403080e15a0b0100c02e850a542110301d01130b401044900f00c0c207901075500b0490b55807000d010403070000100c600512018140c0126200030a100300031840c43c1d00c0d0b5601c00401540c28012268032561034210854590324401c1545414508000a901c00a401c0d01c5240d2809981921101d181c032507192909282030710700f8000c5035450301811075889144e85040c030a01207508210080160f9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 69083500 1250 69082250 69082289
    0x5030406030609090b0612010e01020f0417060610140c0703200f090c0a0c020405010314150f060d02030a0c1e08010b060f13080d0206240f1003020403060204 69
    0x4507011503229000a509022007035003c0761106000300d1b00080c3c19182540404029181c2c18050814440001c800b90b200255488075900000c0103481641d007a411050090003200003a03a550b41401d40f05142d0100c1c0704200030102d00d0103150707002969000404880d003442201070310141072200950040d208091495110310100c5001700110709410310445c2d50f5850601000007048210380d00130706941c4581e04c009180c0300e5040c0984000348031942c1c020001e00c565a140d250040801e60151860b10322481080030540104510036040f40c42110b07d40c150000715a640c808010b4100401401030f41c041c022010300740302254080440c40c0c09044a0140100086140308200082407041d034062049070b4034140c0c114071207039a03000454068020480046884280c51344002009030344a503c0200380d4410f034a040c494007600403410910560350300d44450700b82d081212504050419142c1019070006d030103100e40b1690302d0701c400c035140100d400c0d01c1c0060406840381c0c1ca12080380d00a41080d90140802c450b4400c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 69084750 1250 69083500 69083507
    0x3070c02120d0206041a1303050903030d0906060608010e04031718030705010c020606060405010206062701060221071e03030e0706020102070c0618060305040515070804120f0210150f0305030406 85
    0x603d1703610906c0003400986480e10a0ba56041c00c0590000c04010b00000c0c1001d16580c02c0042d11540d200901c0104540904e07440d0400c01450305d84151b82c0480c1c0c0c4130000182c00b207084011103100c0d5415032980e407010300703041d0003108030f00400a1100084a500203000f029401081018000c0c0f54410000003545090008001c0d15200005161620405e030070441400942d0740422803a410440c117541659800404904840d03c202d1804140800c20911000001e0a40d03030000d0003e18400e0b1b07102a03400d61140140c0d16050328402c01034054201c82c0f40c4100c9046800102c0030064510b4001e16000818581112803a030400180d42d01820051f9000302e64102808460b103502130060a50f8289101d41c51404031a02020032a2407041320203042e039500015084c4038013440b0340d040c1410209540305a500d801c2c4005030402c0c50548040c4c40798038414401002c1c040c06903038100c019001680080c0340017109142140050020001c464086000c4910001f40412403120050080c6100e4070166803103508050006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 69086000 1250 69084750 69084773
    0x403080d090602121522020f04030807030c0c0504140f04020312160201120203010e01060c1118041514061e09040809010809010516030902120a0809121203070c02120d020604 76
    0x258442d8014400c1d441c4046c0d2a0701e0701625640042034050f803910502a110480c5009581c00642251800207104c003c1551103048281480c0c49114010f4007140c0344e100f030104503a040b414441690001c000800d010185007882140d010380700504403400c04144404401c05604403410f0f00d00b914007110140000c540c0c000c1c0e8070506c0704e001804118259850040688407100301841400244442d80c40d503101400a40f03054009040b40203410705281c078103006003044445504440c165480380d425130135494004110300550792070400114218040d92a480c040090321802c502902c014000341e81b2081e413183c1c880008152049000e0800709444100b510000b5208681c02016003590340d01d0001003000c2c1d280c503502d10f40e4483c0300d9840d0002c0c00c26080d1001c030b40380740d90b0304c10801e8052003442d84841c10018950014101980181c90340a0003107070104000f0381e5003902c01540c0f01000014000213141c2e034440ca0102404600090502c440e44c01c0140c040750038201c0034a40000160058000c0000780400d81281d07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 69087250 1250 69086000 69086041
    0x417031f091b020316060e070e040c180903170a090510020a0e01020712030e0409060509070f0b04080a0803060a1503020c0105010609030206030f040309090c051309110403080d09060212 81
    0x1d1482c00041c2e0140c4090407841080046c40f141d90342c040c9050b4803c1c204441c40142c06c41800903056401c0504010360445114410f030884552112928074800310180612070322181d0588444880841081c840e0061110080200c1c100c540e80c2c0741030350049001041810034030030810000503035400b00441d004040c1c008900c6c0c200d0640d800303494208882d0a011950395401c940518000d0285504100041d02406820074040c00c0036080c6070522814003004a01d0701d00319103000e60190081a90340e0f4004405001780c0c4a40c81a9401486001000c151540c00071a44100018a980310941e12601031300403a42e14162105c000a0b40403641895241d400d02c182c0d030240085041805406286030f0010303170103200003807990b0000c00c0070b00d0121f0201801080000c0c00b401c10040240110f0b0404880289903070410450704c103141ca5080d02c000303a00d855511a024261052000444c43d00f42141c0381e448041d440b0308004130880c0c0ea21248800401c0003480900f6010320443c648100030300302000700208207070856a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 69088500 1250 69087250 69087253
    0x10801050913110a0312020706082404150308130504150618080609030702031204050904031116090605040b04050105061c0612030201020c0706080417031f091b02 71
    0x522441c0c0d90702003000d80c0000003956850318998540381c800915250000200c0c0c1250f44c0714008820000e0400d445103000060b070b82280c040300d541d83c00c1111004004e48113161003e40101d061034081d0031043d09185c5000000d4000b00c3d841803000282203051078194020b0b11805c60124814184c2038030320035102d00902e8122018000c0d05003070f100100b0300480e1449a2000d1261030030081003100c50b0050150001c240e10030594206180001807035440b90300c600403c0780f190184030340044517522890107440548001030600030240d13403540d80540c0c4200c6140c000c2482d40c415a03a402044c441295000030280a6522000c0345141c03404c002d00c0b0540300015620f501c40ca003440010310081d15150155190101110504003104100002d5a4000d02658011451072408200c03103005064054000304413800344c0d0307000c50707802580c1c0c0e5004541561044c0d40003000030100740d11004810150202441e08480a0112a280c4624001c2c0120300d030000d80c2d002001c603035101c3c0080030000032450708450040b1521300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 69089750 1250 69088500 69088517
    0x8120108010b130515030d0806030c060414120709050c190c0f06180203010203090309100801080709020a1101150311040b090a09030207050d030507050d05040e040320030a17010501 79
    0x3400ca1110300164101c12559580001c503003205c07035a5502c02200000c1d090b1203040d092148000c01229003100c01c0f0740030b84900c29150403d0b05003c0308407022500c5d5611007140d5201c03140708210254402410b840820700c0b0715034000c12003103420b02c9681d001703103284c40e08180d030740b00364000d00c070500242940c0400921141014140101d407813040c1d00c100380740d80440001400682c081e2007800b0420200c0001e50150b2022040000c0c0081c00002804111811507501d03040c41e100040440d640c984c00d000380c2c0c4858000e89820007841e48590040c0031a503889044c080c1d100019190400d0841d907500c1c100054880c405c03442041800000d650324030000307005903003d122450240d0007040c07800c18003410015017170781c0d5103080c801403500c00d000a030041c0600030701d090143c04050800800541203604152158050136180b015030303038002d0040310100c8a401e07006014035510f80d241507071441300500ca0986580705030001c8040c6c005050000340f144d01400c4d21014a200d0190740040c04048050300814107015004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 69091000 1250 69089750 69089771
    0x150703060605160c0f0602102012040807020409030c2001020c1323010e070801060806060d0e030301080a05100204030203070b0f091509010201050901090309120f0b040812010801 78
    0xc1c01c4407501a40c0203c0902011014588035844000c59403000c03a84040480d808100140d0101c0c49040c880a40c04042c0300c2400c20344050007410448455110b207000040040d400c1d000c600130720840c1c0c4180118030003410842203401241c00d03200050022130004010350000401c11058503581c1c1d503440b1880c00108104d41803030300081d48e41d00c0100c6c001841094800b00e40101107070345800c5400e0440c40580821a1082c00200520500200780100c18900801c0400500041e11480890b41241d031190741d0000d070b544a59083c0485540403d105c54a016102e021000c2c1d01001080194000e19525004041c2d00026052035802d00c441d00d120001424010801000941d40c0003552030155120300300050b40d10075040002061500c00c0b0f0410782e40280f00d5007452120406080d02916041ca8281c00070701c0b01c4d913201d070080c1342202c103003d00040115031913202c144803c141101c0e94a070300d14410401c1020090341a1206078402d5000c80f01101c4030340b40004c040e459000307603c4081d0f0050010310000c1c0710300c5502 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 69092250 1250 69091000 69091007
    0x16050f0115180f020c010617010b1c0501091a0711010504020603040308090708010c0e0108070f0c110a0504050a060305010b0607050d0807051605071a040b04031112030c1507030606 79
    0x2103204410415200003001c1d64591901d50105041c03c0080741e045541d500400c1c82c00d4068940752190308100c1641303051508400b9410300a2103140003004141000030401d100018420160800082d00e95641c1c8558110020b860b15009510280f08101044050b00d0509002031081d030149814203900e9051105000043c0c03608010b07aa00564181880c1905580300d403417162802a40c2d62240b00c0310f40c01e06001c0703141d098001c1d0005041030700c280d031420500e985201c81607481b000098202c40020f502c081600020a629030903034140c1c014020f01480a60340d5480004058a00646900c2a1070303503075490420801c442442050000507054500e60f043c40503d4032103d88034a2049181030a219280d000625114403400071186000120030344070340c6800440c1421561a0032030b01640304803401c81d0049007140d0f56400b082d2000c0b034600d65a014030f090b0440d80c031100004200550a03400c03074101e1f0005817007558207102800440603800001c001031712040004203410180a80585c0516181c41400c0c0301c5585e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 69093500 1250 69092250 69092291
    0x314090309010543060501150e0d060b03150610090614030a0b090906070f0201021c02090d0b1e0105041505010c03171602100209030a02010c0602070816050f01 70
    0x12103039600300e014410143c0929840b651104c048080700c282c1c0c100e90b6940d000c54500455494001d035420805a0703260001c0d20341d502c2109003041c0c0400c2c02496444041d02d040904110450700c00c01c00402c031940c2e044003003842c160b1000c403201c01c02030b850010003629007070a01e00c4101c000d06600d0038052452030f200c0054501540340740c40e40c0c4140000000602136907070070f800808200034064070010311458119416a2038100546044000608064580c003e46105000b90349450b51081d00110003040d2101d01030009610000c1c0381504074001d1000c0d9004502c0f00700702a80304500c2d0307003201d18007401001110800110140c000e903103c0d070310300b860a083c06021100d4030000c0d07400a0034418820300443c242600e0b098485ca280c215035100c0e0740100402d0310500e116010300c3d44502e4080f0745407100c1002c0c40b43d0581c004d25000540680c0510b2040000d588150541c1030401e000d140010300d044410703150810385601011036580160030342c4805104001c402c00c031480c0d01000c0e0070000c200d858200c2440180303150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 69094750 1250 69093500 69093517
    0x306060d0b0a0603020607080c010b01210e0c040f02070b0a020403030c0204231008071d0c1e070b190b0a030311030d05011212081009110904090303140903090105 71
    0x50400003403010310b000e920010146800a00791915903d281c03070000303203d90002030801720355404c2200039002c03940a0340d00c04100b0321810b4075039030402c509c4000340001003040303c641180c94440c0c03210081c09510f0702d1052419410041901582e20801d50031701d2080014050004440780f403040000700302090f440182c18074201c1d0f0444010900b00030041a520501c0080c40c0352030400160301c070601c4003058a1102d01c40442e080750090360b10f40c55584000c3d400b4401e0b545009010084804d000030f9074400d4202c010105151410080d91034110000450b043c1604a040200d540700100001e02900b0301c1c012528552130003c13614180310a01c00c070408540720818a00c0f0042c1804506901e41d08008014820b030783d0034071010748003004590383d2542c02c8640319801c1402941c4e0280281d55280440b445030042074030a030380000c04001c0491528174940010402c107035005003a0b820034401210199070ba07000e09980c1d079000350b80c04208001132030f100c880d80d91000f0700800c11540c0200644511a40c01906648154 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 69096000 1250 69094750 69094763
    0x206090307031b2004061205060a05060a030b0c0418050601172206060504060b0f03040f0507090614040507030204080d0315050306100602060705072d1506080c0306060d 74
    0x902402c44000c15083c003220005000d2400c020101d0b4606610110b40380b0007a03012a0103214a55991444010b145020760025140350001800686180300c0c51308100d40083d400f6141080e0150740761500781d51284c003a91201e0138405c0015003004400c140034607618401c2e03c0c0c404100f241c3e042000001e0034007100c9442c0b115055181c84005038401f964a07040e6030b03070313401540001c27010005a85000b0000340001c3c002c291040345001000300d089100f03101a1140900240413852941e11562500c101d880d044103802c9826101c0c4003804503000110b400351800901c2e040c07408501803901c100400003680c2c2c004180700308040c41030200b04065080012104419a49400e001403540080308000c40200c0031500040e4140c406c1c54180000109c0f110142c6044829a03404c1da0015121014225503e01c1074100182c58845841c00c00000345441c0d601500c00c01e081000d010000e540340303a485440825582c8a050b0380e2641d5071604001c542c10a01080000800c1203014028515000d00010681c0c4904440500f05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 69097250 1250 69096000 69096017
    0x80601050301120c0b04090c020106080102070f201302030601020d020a0201050d1d010627020f0f160f030206010501021212180313090b01030b03010504051c05091507060507020609030703 82
    0x140078031045410007030710341700586540d0f6944452024002d80047c0c6102d90040d0300e814400211a9410f01c283c0b00420380c0700d10307540114107013500c03559401206e0004081d95510300c4020540d06981e2a406044070060760755003d0380782e10b002000641030050041543c015500480040d9005030380c020116401d046030800001070032010302154244c006015015040c580d8648540400c0b40c00314112000d040c40c0941c41701035500d005407240b000c1a4010340c1d00d0300010760010310000035001400405040c4d0514600e040700d44005c11174540c0920070615210540143e002036005210300d59042c04003100698201504c2480d2000c800f540c0444084014840541d500d046110824503a00500881c3c4650000d007054540356519401040001d15012820b11302182c40c03c8800c0d881800d060060611594100002e031171040002166500020b00d00c89151041001c02c00110005a484081c5140c580004d0304501c0e0701d42c01380e03280c20320440b44c000d0115015584070100b0040041800021203e0042e414a02103d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 69098500 1250 69097250 69097253
    0x30603060601051e030a1401050d03090605032d060103050a0903200a02130b03010b0103060608040f08130608010503060c040305250308030a020307020c041b181205060a060608060105030112 83
    0x2030510400c603800c4d80c400d400014010546001e421800b40030150719149002030f41d961081087c030070216003004003c1031007007108115581c040d6028652200c044601c1004c000c02c1503421105004180182a48408210040c050b05591512410f07910144400c8200b00050789038402a04000d22001192004d00c1851006400e080c0c0c24440010900d0380030300700c00c10007000c40c10303840040c01030182c4080c040e40c030b0a01b04068640c03003030040004840103030f20380c5030380340d04d65403503420802e5082c44054491040030441d0720034540001c107000005103100c1c0d036a500c0c65410901007604018000c0c1418500000500050011030300c003007a4150a00305c140c9070010b44441102040d00542c006910140c0a04404800c00c181c95006400440c420f44003a0300740e500c072107590701c2040200e40d6030100015010001d45521600386000e2403035050813000103684c0e01d041c90350b0b81541102d19030325880100d4054120760103008010845004a0010300000c0c1422259481d1100000b01035000510a05038240101c441050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 69099750 1250 69098500 69098527
    0x4030609110301020f03070807020601030201080403080603010b060a0207050102060c0301030c060815100917010e120a0905060c0d11030702010215070c060507093002010c021801030f0c05030303060306060105 91
    0xc02140010b0000c2d52907181040d620083d135042110600041511500043d285501c00710707015042c3c0382e05841780e51003500c841d10103c5801000506440d0150758454183c91360f40d441d036001d0320201465500901c0d0690514000904200010704582c00340c0009100500000306600c00203000e80c1d0992501103455690141c00d0a010351074a20880c0c2c000c501c0300080c03200070740d0014501c4191001006050610311505112074221044002c4003da0390b04500e401464030114040184512401403412015960321040050400d5000345500300c410340c450030340ca40e0802d80015404c036401000e1000303982002445d400107912452240203188480750860001075003103021302200c400054000c0e00412291610110291010211b40103410001e0074032820440800102c61100c40d24040c030307100c0075020181c7eaa00546411504001c1280d0200f14100402d040491441a141c0218025034150701104128200f21465100b90740005001e90401c0080020a841c00521180c2003802840c0032551500c401e408403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 69101000 1250 69099750 69099773
    0xf03051608040305360105180108060a080106140109230f010c1202010905060619030b0604140705090a061403060114090307030809090708060120030f030a090303060503060c04030609 80
    0x455a00c807450420205e0031070b600d442d451444000d4501407208114401500d481c0603900f0a09201c602540c03141060b075118030b01094004030b010f0005100a521030224600359250b03a0408a402e0580354290f01c015a03009901c280200310200600f1034681c40d1242c0710340074140a0030500d02a80306101c01400d00d034401c4d00462403007500240124003906482d0130080c040c120305101a80e25214540100303241e03107040c109407a000c00c0084003c50b032036451940d412103043c1d030041c01c41d81e01a40e10075010300503000c860388542c0b04551580d80c441c1e036082c6201c20007000b00882c2e046801006034441c600c108041c403900850f41c100009027002c11403d01926201625480742e24005601805800000410452070b5005020180021140b400c1503030750f596421154624119400b038005000c0c1104018800726880200050500040a5030300c1d00d0f143c0d50b0650300c40e51041c2d0340f030101d00750b4401d1030b601403541c50310516026210840143c24a401c00e40c807100134034007641c00040c0055a8814100c3d00b00b0000d6400e2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 69102250 1250 69101000 69101017
    0x417030d060806070f1b060f1506020d090806010e0720070f03021201020c0303160c020306070e090f100b13050a030804030b1302151b0601030b070f03051608040305 72
    0xa1119503110080c458491030113507028130110b043c0e00358060701079025004248140b01c4a50001c60450354035200e60000c1c1100c1d0f116510429503030700b031080712501880c1c514005440c00742c0040114801e0844010000e110075841040789400c0070b00107105810307035480640d070010031500d0542a00000001140d9404400035400a03144c4210000014444081c1c604642103038022540e10303100c2260304907042e0a034882c0c1c990840c5260004c00001c0d40e580e0001c00c03241024820744c90030620b02541039002c6890070206482c04000305203680440b180d98034205c00c0035680034020608a60f080e0a01495000302d500c024000e909500002090481501081c168070000034400201a42a8a50380e03050044107540240010385001390841c0000320a20001e403444000d06601401081e041550081070080325000403000c403041c51980000004580010401503001c2d41c00346514030450b0401d1080a892020000c20f840c00340341c24a000c1040380315084a0382d41100005080400203580d8620302126a84100d41c42c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 69103500 1250 69102250 69102277
    0x121905010801270803011e0b0c060a05243609010c0908060a1a0916030b0a05010c080703111009060f110306040b04061206020924041703 60
    0x1844107015044500f4103081020031070100303000c91020442d0b640150700042c2035090100010010072001b000c207901c2c2e900c40c0c1d0700d00d40c00c1c550300d81c0711208143e4403551824030690b000e0024001c07181540d114140c0c00c2030000c210801f845d541d4119210701c0500e40c410a511840b244407044190b14002003091808180c0800c6040c02035154824101c1c511400f607801941d15864801a4035085000707942e0601540c3d8490000d042d1641e50078110000381480c1240f090401c2c080a00e0217155441e0391008500410000195000240151500400f15844840301c50320031141c84004101c0307a43c020320701d5000180c202c1c21103130b510b0300d1034141a9940c0050b00000c242e40d10a110450b02c2e0300f101684248019449081d081c0078a00c0580c02c1001076448a00d40e450315080200082172a52402c0d0340304c0c03a60704001800100351241d40b81074601c003014818600342d80094001603452803518000a1090104601c0740646000850010243c0c140d40147c2c019410b1840e440d45480c401403400304183ca80030010541c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 69104750 1250 69103500 69103511
    0x130b01200a050c04091509030c0b0406140604020412060203180a050f01060902040605041202030c060a03021c02030c030606031003020306010314010b010c05031c02040b0c0c0907030e031219 83
    0xa44160741c5001c0782100303070303218021600042800c2c502030050781d5105800c02c41005c1e82100c902003110003404500421414400c0708840f8800044090b00c403a13110f50702580c800180ba0050f010462100d0b140181141c3c49548100018008001d0709462408c5081d0003060042e204e07565049404121241c0c28a4004a48030308080d040811000242e0349040c00c0b5810001d00200380d645524100707a009500076040425401e200501c81001c0c404440c036a220700003012212910200c002042c02507201086200000e60006200c0d030b0141101480d04015012400085246280c00c841d00c61081c000581203a200e2100000410804000c0d842c2c42e801a54004098444e81e5030340e41303042820483c04d035141c0040c950800102000b81c0d03004405001109401c4006146011201200b81c4070486c4040c24030710480d9400c5c003021403e03d409401408401501c1030080c102001c0c11002c001542c88020601c1303040608000c0300280340f4001000f601c07810740182c161118151111100b034140801951001c2a0451a10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 69106000 1250 69104750 69104807
    0xe0615011b0804060f02030301031110021c080702010b010e0a09021c0204090221060f010f200102070209092410030203010c08040b100308041a0f0c0a030906090302130b01 75
    0x80c2c0204201c6095854000b003200104409a0b00e0380424800648441c05001b030303a00232070038404010010b010051041d6075140030720070100510600f140090b07800141ca44010040c13659024480c01c0c50b03030a800d0801c00c465400361070008520007190700900b0009a001724212484018a044002c1d01e048180019500c2d40d86a0340040700a401c40d800043c1c90740040024606d180016880490140c1000b81142c80542c02e030200640304000048110801c1083c0300307a1382007035804e5000e020320581e03100800150327983c043c0f4010000d0301040504071440035049202e00c0d0891240300b1004503030301c4809080520540e51030442009140d519584003a4142d4280081061020742c0450002e2103036201f0b8800d50740c551100028018542050b020080c0341ca1740c200014003204142c41e040d4154104840c690340d00e00352010f4482107603608407000e4881260712031511030040640002c20742c40074009600d403200d03c0d03074510340004502d40c0b103112580c50360969170399407810103921900001100038041c20140c890300211 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 69107250 1250 69106000 69106013
    0x70302030706080f0c0405060a080727030605090705031f2c0622030c0c0305191101030b28030206400303110f1b03010c02010e0615011b 60
    0x101c0342540042c5091300020f4019072079034107407416a00058840c90601500880c10740f043c000260554050060b810b00c001c0d40081040c194485421a40303400c001c6261851400b1001e550b00a00040c0050f0402c900600103610002041406d000510100d0303070780320981e90181c46c01880d1080d00c2d086482c03c100c9002d40d02200000204264091b0702c812101c05540c3d200c0446483c2c00c48100210741440100e88103800309220b280d441103454065240c000b4480c0d0303a980d03420701c2d2590001001d33000d1401280a84148690f00420755401c0100703003410f00071110210005203500c03014103104401c00110300145617511101c4d41c3c242c005194050301140e5500c0581010040a541d021024089980383d080c0208014940050500e08032079011214040d4a0546e5803d4038041c02da0b20072485240300c1d000340c0e107088010030803070420b20b80400308865908070b15031004d050030344040d4501e1030196810002c440094140000b8004c1d030242c042019400d0031610080122650981110028524a450b0b07030b401061085 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 69108500 1250 69107250 69107267
    0x60f050f0411040e0c040b06040b0c010c1701050102030712020102120a0b15040f0b07080f03190525050310180203060109050909060411180a050910060f17070302030706 74
    0x405040b0b0301c0300c07106810042903401c5030b60411a2a0006003c500f20750030241c0108140703800c020011400d054461001d03002a4000c0000f100c021781d140c1c041c10a00c282c000c500d56500b0508030325842129030402c40040e580c0e114041c4001d010500c40d814103c0b03100c0c400c2d030641c4c40080e041d01910800d41041c000100191071110100b920544c2c81080c0380c0d481c042140304890498040300c60010000c0c3c9802203009007900040d8080e100c000d410071040600d81080030003584210350b051081c2d44a036400707001070022500010455400c403c464000b002c80042140e00906114003149010759995403090034000c045007066211011203c103006815400d001c00390091840341200707a80b004d1a0303940c0d440c01c00c07004800640e0341c010243c02482c0840c0c0820f818a43c04c0f900d41e100601a00b46546400700c00d420820011249120344982e41c400b400040c0c20b040c0300550200765046810300200b4145810350750201150702c2a07140400c001d0070b00062120080c0800c1c0c00942d0020309581036295a800c02814022 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 69109750 1250 69108500 69108503
    0xe041811040501060e1f090503070303120b040203060f0d02030c03030f07050606100903060c030908070501090b0a0b210708120301060801120b0c090109080105070c03110c100804060f050f04 83
    0x141810300228031244a01c543e2000b000006000541c40703c60f44059040072104141b0580c1040848217010503c0e480c02c02c0304a00079031091340c0b1a1201b0022228072400c441011014608c41e60040060000c0c56031541c2c40018920400c40308500645140d100180c07500030300c1907240b40c240c040802c610100c512400d010304900d90207082902c600c1d82d14841006081302d90b041034103000c207540c3c86042c03020602036809260141e03243c1c20006003603100343d22045250303003043c401250507079100e90601c800c102e1210002c9402c619140b205000e0205400e0000c1c0240c0182898503040c200d402d201b035401c0300000c008041c01803031000700741c0d01c2d00815000410038642c8240900e6020448031000080d24200d0110040e442c0dd0b080042c181781511107a0b0320788070300d502c01c10f0282d042180c0321401295203c02032003141e010351034949a82440b070a5900e000703001120030be842c000e8903030070901400c01c03103890304001c5d000c580141e40b528055aa899103400782c01003041c180036680e8a8600420491554980000603003e0f9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 69111000 1250 69109750 69109759
    0x1e12030e010b030105070f110106050406030f0516061d040902120303040c0b0a050714010b040f02030a0b0f0603040605090a0b1003140105100902030711030c01060e0c03160e041811 79
    0x205914281402d84000760351b082c00107080c480d41c0c1040076105203601100c030200e0300e0011403a29903030320004003a640c1d542c005840031050a0146000c20800300800500e414000c040b84c0001c03442d00074042c003180c250803c41c1c14071180c8100c0406da5961282e20001a2030742c0108101101c54503000b240d0b9581d0402c8404603403951000b41c5c089042c2c0d2005050f200002020350b1450b2401036959990800000e0345032140c8030940d200c2504220650340c80c02504000300003800c0068807450700d40c0342002600c55440501d40035803882c9050007804d4542904881d801500003401117800c5e103480003900d03d8401c0c034407400380052226505000b20030520240001c1101c0c00f47d510030079468000c1640301d080750005d030b40035120f1104c2050104885143e0b038019542c421030300d040804030403060b2008141150312041007280d859558030002c1c040e09030000c04654000046584041c00e515100c1e414010400304039aa200c02e00c0b034140710140d4280c0e07580d040001d0b60280c22250301d2048083d407800444203003907122068481c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 69112250 1250 69111000 69111011
    0x109090501150e2406030f0712020906071e0c0801090507140f01080411040608101505031005060402070f030201050f0a0e0d050702030a0b010612060e01030309031e12030e01 76
    0x4015020203042c1c02d440300c8051030300381904c41007504001214500d600c003441102c0003c130245150b640030040d600c41d0111050140c000c0c9031a4000401107151440c000229502c148502d0455840310803e840b0000e501002d41c1e246402c680c1007800b81d10103000300041008a40e03400c0420800419042819000d1140c01214039003034403540201e000540344255141c000ea0b504840598640c4501c420b142c1040c0510040d0000d802c524020400755140d54015036620791081d400c0e001d482109114012145205c1000003000718104000a501c8500398070700f609940da143e0001c10300701d036104ea044650b03031584100c0070030101000c3d26021303000c1c18040702c81c0301c940b18008e00082c0c007228550082142c4003612102403c01491102c106a806400070501680c043c480c092150000924000095001c0d015a0b1550030303841c85000042002d540d2650400340000c3c45507001000000e8105a0340300c16a41d10912843c1201010151444103c400c4e6001524592148030500711268250b845921000c030300600074010f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 69113500 1250 69112250 69112271
    0xc0a051317100e0c090c090f030303070e090f070206040305280c150605030309012001050103111f08160c020306070e0a08010902060304110d0512120f150103020903070305060109090501 81
    0x2101c1c0391480040e41c00141341400910f04d450f1b07071b0f03000b0006240000c018074120002680424503603042180c8140c040b82c0c000c054403c10307142031420b0070307030214084805103641d2528440080d1500c1c2c2c068002070a01a0104981d9600740d5041c1e8605079400405000c88041c0001c450002c103404075041095038258485070034111449400e006810a03100e020300150300d400b80c0400110362032244000c500300741001e440540c0984140a00800e40290301400c5410007450001d01003026181c8441007400c1001d240303a60030201150081c0ca00303580300c4000c3c036034000c044045200654a180828100a600d40a0a001c000d0180d0b08004a14000401990b17201082602c44924500726803960070041c0d4800c01c14000200050350310509140c00c0007001c3d01c81d03c1c06a00725600c1a02c0c1403681d849907020030002140e11002c4040c020001c0c0e620841320341001466041c128610310701078a80a40d8141099000106101107813070400a00d001035510030f00300d83e40f543e503131f42101c801803000b20012603455081c80d05040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 69114750 1250 69113500 69113503
    0x7121e0203190e030c0906010302040302060414031e0705010f090b071203060603060303080408030703020f030f01140f0d020d0203010e030c01050108070f03020918070302060a0507120201050c0a051317100e 90
    0xc00904050021704040d500b90040260300000280500d04042c1c00b000003000503101c804c05400123000e40000841d0b0130710800101410721103048514031140709400880a5940000510796007260800c6c200190340e02d074000400c9039250096000078105000008255042000f1103010202c1843d15980c2000255100e59049040d1141848054000b51080010402042c10b2a00547c1c1020310f50800625160f000350010303d50340c104486800c00d269080004202d282e01c1041d481550b003504590550040f1190800544030311300c8032002030b000e8003160740e0f00030440d04d00f51b208806640a034021a0b403200e1010440ca8080c000c2402502a68000d10400048a42004540c4801d4031f50003008440c807507170754000142c2c0b024440b45680c100d074803884e00f001002d0380743c3c00000d100f0342d55143e5450765110f1103402d050012540072400388085a2401c8100005182c5000603190440404d1130900c1d80d40e40303288241031345101c0c40d0704000000050003002c1c60b860381000a40440304545020180400f410343c0b150315 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 69116000 1250 69114750 69114767
    0xa0f03060608070903031d0d030906030f1e091109130302071a030601050a09090c0e24040b1c0e030301050901060306080703020f030a05071403150c07121e020319 71
    0x1500883c1d01380d441800064011807506214521a40c066001c08009000150304503450041c00e8001ca10242c4060003441d5040c001e003490f01042400034008448012000501044403000c43c51500e9a46c070010b6040001e40d01c0680e01144006203200c4040c1080303040c1401001d40300301c044000d4410b01c4030010b05460700e40e501c0c10a2100c13809074142160b58480040d5034540c0102e0b10752041100030b950102f41e040c1503101d0040d84a0141c1d4a11103c00603540a20000f291600d104401a0303019569495030079412030202e8080c0d0b0604540766450350070b80762000800d90346802c0b038031860a0501c01200914040000514101c48044413440c40c1666140c3c01a0104e03281030003058001d070404941031016050000c003220032010081d04803102e079891625100d0030895a50840c41c40c0d0703e542d0881c447c1074a0f04000070340007880720562072166420300140111030b07403007410001080c1070003840301c0700d41d0203000d2000302c10b0b40041d0f142c8a0444021b95031000352240d1200000d14a4005030f6002d14503950b20a2540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 69117250 1250 69116000 69116011
    0xe07060206040f110d05071404061706011503090b04050a020103231b0d0f0c030609020a0c17040e01030524010302030a231002090411070b010e0703110a0f03060608 72
    0x1054148803050f1141310060714050a401c0d004501c14032401d000401c10405840106070660407940d140c00504d080000740c1d00c1030ba00c401e01001c4160100c110302e0344007003641411100428041204550310a005501400d061340020701031215000400042c00004110001e0682c403d907810000d1424141c02222004290b00100008416000014000202c802d500a0807413082c000c4680c1812440a00c2106451141181e05911500d070128081e2030360f0107004150290003052815030801c040d01c04001c1140b040940060074815400122008820300311701201c0103420740800d80c2d111981c43c0c0c20001d9481200354801c024851421210305e0441c500403c207181030f030b82d0060141c10340a0042d1190240ea4003080100c20584150804008550350100200305000426800158844030789030100400c8410182c1503100d600c03800c1002c58001125442d405064a0b030a038401000c1d51210501200204407107802c0e400452000940e9254070360b00100100388003403ca58052000e183c4541048604240a659 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 69118500 1250 69117250 69117263
    0x1d0d050313030507050109140c010f05030108100506060c07060c0c05060715020c1c020705030f1b010c11040609060e0601170c0703110607050301030b0901020708090d0201120e010e0706020604 84
    0xd01c400070307110f4001041007501a100214030300e00292103c0c8800000680d1803240c5510200b62900b4070358000c45e084411503060b0801d070381103614080d5806d8403120119241070501d590703200068117507503400c002d440d1602c0c0f034101122001c90700c509002c0c040b9841c000d015101c400028200251620b04001241c0074164410820041508405d40c0c1e40003940006214000b0f501540a01c1c1c103603092198446c0444040644c000e000301842c00050505108191504013125002480301c240070b080040c044840385602868070460800d410f040a8002c1c0c96180ac88075071003410a038000540050540000c4190303244070208500b1602c82c1001514080e0000d48070162002d402c030006880c40d01441c018158860007030410b00500103018410909041e4215140d6006c1100400144240441e480600d548002010000c518040c0c0075200c9a85501841403c107100e001c040950004591094000c2c81c80701401d201d050040d003ca83e4440c0d030203444480700b980c1152050000005107140b00090a600450304140c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 69119750 1250 69118500 69118531
    0x3050f1b0a0c02010c0204110306120a0b0f040f06060b03071218031211030c0c010b0a060c080a1b06140603010b0108160903140303010305010c0e0108070806010908011d0d0503 77
    0x41c000e5400700140c0c03106070f0600201580c01005038690340079101e6215954001540e0341e152070003c10410f0345c5215020b81c0766a01581184001401d01002d094000310482c001035a903995074a010b070f44071900c8550040107503040c8a0300144903149400514003030212034a070207218030b032010030000c03c5882020002d40d00c11241d840c400c5c0860b0042c0c0104904040b450f102180101c20355055081a170300c15120000b82c3ea10004400c40648020302c910100c001d82258001c1036a49800c000400180207040041c1070698001907210040e40100c1c52460164001880f01c1e040940b10b04010009040780c4000e541e4041e880400203503d407030b06100b00212040305845060503626007000d4462107900d070002001c207200603140c021003c1030000e1240445004280c0085a83e50304502c1c1560035a1411106c403800d02c03040010740ba01e9a0380205c005540007106140c140300c29a100b03001211101d005600031100c039464481d2503050559041949030014000e20105c4548104c041001c8580e03100868068602c2103541 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 69121000 1250 69119750 69119767
    0x60215150409140a0b0604150b040603050a0b0d120f05090a120c050603010e090705031c0503090a020a060c0c0b0f0a0c15020301090207110f10030903050708070303050f1b 75
    0x20b6000c4007401d409100480d110f09909000d0300d1400c0c04040003503484050700c0c02003001601d81800740c0100303400800f00e51083c42c1c1c40d0644c15046805117000384024161600009201000c0c10f0b44840400c820007402c08034400c1e200d04100307800d84130205800f000102c920034110320300744c000e4040303447c07038007024200041c86442c0800009045101c45001c0740c0d00c18801100141c80d682d40300255000e400c900002c2006401d1030b03500a450302d940c50b840140240c00054040440040d8848460282060cd04090360303a40c0e500b10580d410004c1c0d01d80c0080d8070103150000400d0842d400141e5481982c4110440780e4005e454046184c050f004100d500d140d4013400304565044144a5681d001046100380c02c0348441b50050041d5000f81d030030036009140c40075800b003842c000b80702100110921070503041d11005c5605000b42e000c03030403441501ca40c1c0b006240e22010f10408140c0329904840c24190003c200e03985a890314a80203000c1e00d03080e01d031440f115500d00c0105400305000300e07144400d602c01410b814a030100f00f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 69122250 1250 69121000 69121009
    0x1080d050901030f02030106020c1309030207030b1302040905060a0e150402040c050c121306080601080f0712020c0a020109050303040b03070e0a08012a0311040504020906071b06021515 81
    0x340340c03601e04054460741080340d0400c850000d140032381420b4000e003e42a4a01c401d01640417105054480b685003407124000100360003040403c1600e41040240c0c00070303584c84403030039401e0b00b0102c0000d410501c0d240b01541401400300b46503008000f051000d000b14402075194940d01d07050351440050740148100802c0040c940387e80000e6804c012030a04504155041c40102d003041c0e0b202034003ca05040000b44400103040380c03034958020f0000790500400303d04100d4002040008000c11004a1001c01c03004103590b01d009264404600d80100b409554031002c0d03408003912028580c400b240401c403c8000407e0501e000302c140c4090320071007044907065689050003103a0000c07450301000c4d009140340401280303480b002e024408407660324903200107000021146544002620040e03000030949001801c908034198002140c0445008076009a02c8900c07043c0050f80f5481000c2006200e806201111325000410043c60000c861040d003d45039201070784024184a00e0046502c20900d038801c000000c0d0a140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 69123500 1250 69122250 69122257
    0x6060408030a030b0405360c1c0213022503020102090a06091508090d0e1807030507020d0806060702092e03140a02010807030c1403090f0c03070605190c02040f0603051501080d05 78
    0xb080c1c201d40340303550608d001c203021404994103441151080c0c040c04041d41400c400540b010b030754404045142c40540c0943c0300c2d0030b590422290f07428400c0c001c070f0001031507c01d405603100404010150429035541d0340015001d15101d206011510b8091a40a86118050343c950f6104081610103005d0106074804200d4100034900c0216030300511090304444060504548644a00c980351000941400c2c1410068907041c42003d402040145441c10080359880710f0041d555007580c1aa942c1c41c072910380311750440d052500c000e0055485801554030120340d02d4030007410000c484c0a8010407450807482101d46465401c0c010010b40402c1054010451852080d0700034030714412540340c0740c0c8004440796840141c581c410344081d00700383c1c01000ca42c500c1d0f030014401000c015000310010195680f03005e9025000d8042e0464088072181c4111810b0003490040340c0070968154028820040d210040540d0001029a4081a2000d1140044024040740c01980c080d060b0340c014002404100c04000c801c459950 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 69124750 1250 69123500 69123601
    0x2120612010e0601090e10090809120102160804030c0f030c0e06030114070201061401020303190b0111030a020601061b0c03080a03140f01080c060301150806060408030a030b0405 78
    0x42d600c0310100340c1c0401c140b004030f02034402d008010508194440d00c29260104000f46481764503e4081c040d00015948421070704036003410755820500e0b14000c12494020f000759441007070403c032486861810480340788014001e407485051802e04690321841c01c1c0500c45002e02000300384070140301c81842000c02d03a50905620a10007800400d903400301c2c460303080c0b07880380946410000d43e444d02401e1250400300c69000040c1e00082c801076086140c80c003404048208600700c01a105075440f14100b8007a440307401c901002403020340032607603121919200295030340030921a51000908600100510940414a51000d603810444000c1860b0854440281a9200310540f5052580e030ba422a1400042c03018210b1103143c11070260a61585020350883c1013407a650a001d00c280070420051040a0744d00444205401091402e01a03566840c07001c1503040c40b503500280c00c02c2c400400d034150605d5041d0000507080c81c1c240c81c10f0205842c0c0b01004140065980002c02c2d0b00c1c0b0725610030204052400c03d440404a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 69126000 1250 69124750 69124753
    0x304140402210609010506070b190b0306160912050a0b07020c04180501050f060a0306090c0b0403051b030c06040915030c0e010305011a010c020108090f0f0a0c050402120612 76
    0x620b1200c03040c28801c00c01d6041120070075008104403291402c40d040a00401058484a14101403a5074074030070030400404012071010821b03004410180b00d079104500c4810090101d80d1141440d030301c0e0000c00d214901e50300000508526002c20510b04500c101cac4042da50040c020481c0200a5543c2e01c80d21100400080441c828101a0030040d6214091b0502d014030b0040d003107844002c01d06190b42940c40041813980c0344803802040c002d003030f107400c07001c2c408581d0002c00000300c0d01070602d090310301650079030300918840f480402d021080c0031010030038074441e07408002c80d0b0155107035540c1403507110515010030340e070301c09020b22081000c16001d030070460142946144050415480340d9aa010303500fa2a0009030f12045c0030300040c42000400d10030407140600c5010400350800c0d6100000780964400a8000e041100c140c0201e08440c00801a40200403044c2050311509921110f00715950162b045003500c1d40002000d0000c0c82c0d040c603200303c4001803260300381005a552000140011100c80244503801c6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 69127250 1250 69126000 69126007
    0xc02010c1106030709030605090c0a0b030a020f03040308060916050301060509010216080a1205070c0b070503130303030c170126150f04060614030a02040e2104060206010e0106020304140402 83
    0x46aa5040046100c2e001301c1e200c0d941810704506102d0b007146c5004018844aa012100d081400d9607040c070b50340c2c11101e035980519941d0fa02c82000030040e00508186c0c02c041ca40220034001010340001c1c00504c02d1402340c42003070f001e81e83d1038001407903440800000404120208018801e81d48500000c041032007040c012182d401c854400b844d00100c03025401401180c2006d1003c3c1c013004101904050200201d15040d41058000d8541c0c040100883c0705811a49600050110401070240265888180104002440c03e6901c1c107001d8080c001c0c603078544c00007480e20702561500c0f8054200c0c03103050b5104541210542100c0d4440200c0c00141c00e5504201031150303980e1401c036102005030b01c500c2120300545090003030a0a01c1d1440540d15a0b03000440c600089100c51801c507180080c5524007640c0403a0301254850280100d141400c44c501c40612904000c900d078100007995003002007003100d409900311a1160390703d25181da41068280110740040e0401c00041084543d0b10306d40c4403a181004200614 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 69128500 1250 69127250 69127283
    0x20d060503120310080307150b0a03060f0c030507020a030509090402030307081804051005060910030b062d090a14010203040e091006060e060d05100e010b07060b010903030c02010c 79
    0x94000110001510303070500000304080f80204e401c500000313019881c0254108446640e40d1068464034100c00c0c404070f5610b4100d0ba2013955000540c00003035410107000c00015003030403080b20281c900c440303e070710203c0c0c241004038a80c01d1000652006142d0140e5a060500e0303100b40c100f0100110281c0140e038184024020f81c408590080001c221180c40803000a08650214083c00b040d100700500b040740942107400f04009603203542045480c0200200c901c0a624101414150010040d0400151b0040c101244034141c40707503501040341204008595524210380640d41a103968426202c0c0c07540c200c0f220003030400030004e000702d120341e003400140143c2e03003800e0b29013003407092440702241c0b854060b6200030380e0401d403e4520701c03514001c4c01d424603103585483c0144000c03442a10440380b0842c505a5520002003800c02d0281c4004064050b8501711503155a450103c01c000ba004020140c1c0c0b1070b8903009081d2840e40c014200d0740201c13540354071401121082600150307000005420140c0f40d82c90001d07506003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 69129750 1250 69128500 69128503
    0x6060406090513060e07181a030a0203070c080c0c04060b0301030c0611030c010c03060e090a030806010c030318030c170307080a1109030703080c0106080c06160f0b07120b01080403080703020d060503 87
    0x620031103075903030f801d812885a0040c80c041c02d929980100c1692403804600c510b052442c0c022a684501c103032b000940d60b80c0381d08004545451000001030004100481c030958143c0740840c4002900d08100c40500003203864025840300f911003807000404190700884100720103030140c01006824003510055a080895110300d071825520030392009000259561400d00440c40d0490000e030b00b041d007410080808070358558019000c000d0244c103d41c1407113100e42e191000c01d4400d402c90b205e4049241d032901240406840d000d080b80c90b410404840d5280e00319013503101c9034625002c4c0c038803505050303a5810040d281c4101d00d0006184064411900071010000c0014a0700c0800c4040c0c000c512450704c2a0343c82c020150701c142111010f40192600741c010000300500c607a070790001c0d0340030594655454201d20006241413011310180801c01400d0b240c0361006c000181c0d4120a03206c124070081002488900c9070b040046400c040200e0300203011038071038008030b500c80344650f0180012034020400090040e45410000703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 69131000 1250 69129750 69129779
    0x4030b010306051801090201020a0303330806010501020a03081303120e07030201020f21030601021e010f110a02060403080603100e0307022803080c07090c02010b0103050606040609051306 82
    0xa44010ba00c0e0000c0c01180002d542c0002003000d0319130020070240020380c2c0000d460300c01c1e251010b003c05866200c5c294100c0415000241294010071986e034581c8041650070045058601c20080d26003e000300000c3d155002181044d00e556040d5903030022692808400d03a00c810032904207404000011a26502e103d59612a125103440707200000e040c42071841c4002850041c101e400554240c2046004401050703080d180b800c0c14220b044c1801c2d071030b5170303074100100e1404c04140f007581400000240c2c036040703040040d448514540e28010042c40f601c0d007441c2c1d00352004d104402003940103a0041000502080c440d144103608000000c0548415000121240044c0d82e04400309540c03982002418004610704084c00f00380e540d0008100d80b2804685401403c800030140c40013506074400040c00f4424540244129000340c0b5141500f04042030320050000d00a01001221601081c54440858220711784541940e00b12101343c1d560900403800c2c4010f0090000806184554064841c400492a410780d503221 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 69132250 1250 69131000 69131003
    0x702100c050111190305090307020a030c030b160801060f2304061d030c0108040303060e0f040302012307110c0913050d1403070e030a0f200402090d03031104030b0103 73
    0x1600000449400e01e103084501090310b820014008001d16401150408030350100a46103003400110740c3e03114072203541980702e040c2000b544550314807404000c01080c0e061403c152030048407611000d40c3c1d10f40c0715280380601c07981c8880c00309030994010450140304088400c03040c20986820025092080c4800391003800c0401100084800403400303214840c0e2040d644c1d1010002c43e20040810101d01011070348480300d440f417160402550ba00014103040c0207800500040200e00758000c0b1601d09403560300500349098804900650a043c0200051094030030020403118a0b00d000c551035444c0c00c0780070385900c3c00e0300204c0800d90103440244000d6035140000717584210701c0c510081860100310315010381401e414403001c005011400907039240c801d5042058a0780440c9a040800b9400c0c01000020302e00250380400a00c21030344102c20b11b08200d0002c4003142036113040c1e9a0401e0b58041e000821040e0b000b04200c00350850042094000070034480d0b0049906002407803105440c141d12920b520306500c500740c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 69133500 1250 69132250 69132257
    0xc0306020901021902060304060c090b0a030207030809010b01090506030618010b03092112041707060b030105340e0a0902070302061005090402210a0605060a0b0a0203041703070210 79
    0x340c0d501c540d40c042c480c8003500006805803c2e08002a54001030050101500240800350380700480c110311402104810098030b00c00030b20700c0d00c2c0c82c00920000c02a501904c000c400043c0601c0c0820301440b0140a000c20705a4146c480710b003003074201810710003542c00c014505a804114000303540c09046808001d24080c2c44d03d40e004642c1e0780b519400300ea1410784240244444425140720010b28400038506843d881100906000001d8686040042e440c41c407030001a100381e0306c0052401b0402581d0351001c1c04001050b0001e1003da5200c205007035035014060080ca1001140d88640100f6524003500401480c41604041c18803924106c01720b844060213422942c03035142d00203100300506404200036680a00141c0c0c0b01980c1e50b01300804910111f0020300001d024142c6241c1036070540d2007880c640d0071180842811110051000c0c140075010f040e0980e50313140131f1016448089803e510070400c48400c0d01c203a400951509292448041200c4100950180c0c01d01080c400c15005a8508034880a1012983d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 69134750 1250 69133500 69133507
    0x506010e12060f010b03240102010b04021c1b0504030f1509030906080f01060914040912120605040b18040c050303040906090b0306090c0103111606050f0a020903060109090503070c030602 82
    0x5201d6860b0206800c4691002028410000016034247c0310314100403044010808070411100103170f01400c0240101341d4084d0011905418000d50a10280685503100000341710038010402441e9191200708207890002e00100802d00120300032401d500d0609128a040120400c501c40000045485801080300000d8400d4070070007141d61301c14215a04256800e07a149015407520340040d100c1c42a5124041c0c003407801011000702991250700900d051500407020200703520040600a0140c0c1700102406000d5181071804a900c0c10035100da5040b03810090690f0038031060140c041195100b000300101c80d40e1070305842c0032030b2a45042c07001e440108042c0390017080041c00c0680343d0041d50025103181e80a5400f00302040b0301c0c035400240307036070b031040081c00c002902403810301501480e0320641507051000742140d1007480802c03005a00c224480d161465625000d600c4001d0600260711541000d1035040c2e2141c40103000d0507546900801c00f2911541c100d034580500303580d400b0000150b581c0300f03442165020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 69136000 1250 69134750 69134761
    0x20301020d06061409090f090a1b09060906032a0f08030a09050d050d1101020906160b0108061311010c020414010302030601050d0807060b040b0a030c05040f02030c0304060506010e1206 81
    0x2c407a00d120813608108040c103010b114404a4070915004001000d01c9001501044801c3c106001c4650240c3e084038455120184c80f4081021441043c86a40c411500c0d18200054181c0ca603c00c0006403a44160409028981d1080c4600905000d6804515901102d0000155101640c1c030110080402d00051502d4044100c406068042240d210780d0203000e0980d03521002a4011802210800450401c03906544074414031500a00812944941004c000100d035880002c0c40c0b00000c1c4458400c002a104580e00ca103562174903604203440030030706003010121400c0010203003640d0030789209045c03414041020310707900021305407a50209110040280c01b0018015414280700190241500b43c1b9007149031501580d4001c10351240b0900904401d43d607401815643d60785411190a800e0700400c0010095100d0a0040b4000401d110300e5100e5460050405175658680c000e1b00c4c410740c0040500d504541c3d440d02c4820207841c0041174241008000303000e840d4a60b60300c8401c0280355100350003e02d002d2600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 69137250 1250 69136000 69136007
    0xc0302010e0d0201081b090d150e0304060503160201020f0d02130602070621150305030c1005011d04020a0504020408070f090b28030609110f010e06090d030c020301020d0606 76
    0x2000c54041c02c1d01c0d251072400340c0d810032a41504442061000c0c0c0036846400c85441c054050700300b026900040e41490714040c0040c00e1400c10409c43e0f0b828013000b1a5901100e4107582c0d1295215600105d001440042e680344003541c0c0090300100380b0f0001502d008612441c42001e0303070101080d90030035940812940c01428801071038034040c058600092880c0d5051060181510b02030304034104551440b061030341860784994010313503500b03009440c144038800d84a1502d140c50390401e00e0385800354841d42e40c91084001090141c6d5040325580310141c12144020135220703030105d9008006982013518120000b030076031541e1006000070f04898000d024058103108002061038090751000e04514101b44440030b4a580780b070304401c190505825101a80e902c600000b5846442c564805004c0d0361420411b882840141c0074007003402c603000c030b07440c7e00d40c9161f603c019200d04400d070b6540360304000d0500c45080c041c2044061346900900904140030041d500391f00190030390b03111f108015801030b2107a01c00c1248a41 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 69138500 1250 69137250 69137267
    0xb190f0305010501091205071203020c03150f0c030a140412030b09041e0507080d020d0306050315010311010c051207030207050603240f04090507080c030102120109020c0f06040c030201 81
    0x26103800d2040d0752600f00003c02c0400b03240034011406101c00804410032a0400003100105080c82c45810380c07854508003e0f44890715002d44501030f02503011a09400d41040204900c51400b500084502c0d8450741020241c90704001c00105101d580e408005107070700c5004002c603100301d2182102d80c004101e4030f00020241c2d0204030300d143c050040c11041c0000112900141c0705038a400a0700400b04000c1c500300145002c030a50710201440c02407048091030190f000c40d0107421081552000d0143c5036490b070a0540d44c001c4915100f092130440c100500000342c00100a510880c03051401450410254071000d00f00883d41c01c074608080e4001816008058062003c0310040800300c1e407031815031901101c01c440400c20701291942d01d404400340c1c0e0f0007940d138903c110b4040c2d101c00340c810001c0c2a442d280280d9a41c0003401070f4820740c402ca00ca031040070701d8140212561030305c2400c0f881500c3c0e403038407207080041e4104058801c101e01035030400020780081004040d1003a405039130315400d610700d0740c00050f10701c60 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 69139750 1250 69138500 69138527
    0xd05180306040b04021315090b010314070503040c050901051324120501050906010b0f030a02040306110d06080303090309040b0f0405160e0a060927050703020706140622060b19 77
    0x2400d100000040e80c01c2d0900c0c4404803070340c50b0f08c0414030015410040340100514940c811145e820603041c8416180c0c0325000c0d621035846103241c142855190000c00a000c8401d1141941c0320340a5103400314103002a411018510780245007000700c01085030703052600400590014010400218425024018240a11500010080c000c1c00140d41000000c5001d03204808180f15881c0002010456246466049030019504514108514010f0b03208550959000d40500014941040800711340c110012080380d000e0780d0741c04019403424200d48188805400c04001003644034001d6060304005445a0080500c6200c80900350f070a078100c0b40c840a00072103e4519124007501c40001c0600150750400b00400903a210071080300d0b03e80100d807010602040c15840c040f070701281804140211241c043d0040e1000d6403190000b44141178031302e4040c0b1801a002c48170560312248000c03c903202c519414403e40040310386000042007294035070300074031180d03400590b00d102c6d89042d611030b18244540c03180413544040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 69141000 1250 69139750 69139789
    0xf140a0903020316051011040602010e0d052215030203070207060c020607030813150605030d0309050d05091f020a12051c0f0b030a0b0a110406020d05180306040b0402 73
    0x200c0e058400968a0056400c0c242500c1c8020f80400140a010000c1c1c01e02c00c2e00c005000c1c082d4032902e07224003c20b038010f4415103001d0b6090400c4080038030030100c0e1403519480c182e683c45042c810001e240341d07100b0101682d41218240403942c00314840044800d009500c000c5600d0240e1742e8144030100a292409690044041101c90100705006940c0c2a040f5024180c01d441c00da0059200d40b4515040a04c0409005040001c600c4030b001c1c2c16556500a20300300c410450075602e810030600703421307016a4400b80c40240103402c648600e4180d00c0c015000340a9a2070080c014550300f25040e40994020110501d0038009070340320411003c10005455060014250b0900d001c40c1002c00322803110b481807003a440c0c2905001d458547c6c0300c2c050480c0e640030140d03040c40101120b101050a00f04510100429190503609a0410380d0f0001509035580440c0c0071101154010854007121120490b0550407260b0103114010554001c10005d0b0703800c100490060b40642d2410074581833a00c104a0040c13103407401030050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 69142250 1250 69141000 69141011
    0x6010e04051005061c150c02070501020717031b060108060112050c04050702120a090503070609060f14090a062c0d02121005010f030311010209090a09150f140a 70
    0x91000b0990040603501c200010501d52240e10000c0c036498006290003803002c903102c0102043c01100c240b000441d803411030f4200002200b0b448102c0e1501118001c40780964080c203001c021034601202c104201164280541e0f040034140c2c9194403007020000c0740c01070503610000c014004200148500c1d4010300d007004050700725004540c0d60300e8480c4a100f02442c891640c0d035000030340701e030300a100807801c100c5480b0a0070740d21011040060492606401545d0083c450b0030f4001c90070a014042c502c01f03664036621895002010390004a4141c1c0c40100c54030000907051021040700e443d1001440060310803500c890b810f0721380e04e2080240700b40d08c2030440c480242007034003882002d4498400c44a40305406440740103042604140452802d4030340c40005003040e10703107000068100c0d44a0200c40c01ea91081d91030b41c0d030231040008007900780c1c02400c0d5001d038007903074000c0800e002c14895409140d0580c421142c1000c89846048500212440c01400f10030050302e404000d80940c05002090b40d1001c11720100304031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 69143500 1250 69142250 69142253
    0x50717010e04020f3307030305060a030b041e0501020412050d0c111509030d2003030106120b01030e1f0e0a0507120c090c230307120b010c05030d0501050306010e04 72
    0x240354800c012480c0103003070325003542244428a100c5c0b13040e0410f000784900d6940e500c04d0f540c1a00c42d48080e0055000034a0300010403020314107030b140340c41200d800c0000304946d0785840d141c1d04114603a1b500100b403c0c071804805040000d0003030010f000241001c5414200c0c181840c1010350404444402500401880c0c0e00c40030000b0345120512030688c80300b5034660070002140322000e1302034404c80005d250305118440e40210721640c81a04a2001c281e03055044240c5094006017030b9807400b080c0288008244407010b888401540ba43c88506505414034011500a410745030490900001e083c4c0071400301000c0700b59282094981c01242010700140c4000c14031035609868164507150580503440f489003030707603015009004d500c40c950409800e10306800c00c02e1850400d8058901401009805800048080120341100c10076007038a00c2228161244e0328103001e4404007900030144080c01c18103001510021001090042014110001d071100f0001a2941007008040c9060f0059101c0001d5000c01c008000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 69144750 1250 69143500 69143509
    0x501051017060102030702180a06081212100905040507150f0503011e030b090309090a0c0c02010e041b0c0c090e0a08070c03080309060402040b0a0b0901050f0d050717010e0402 77
    0x201100c1d4850600855500c0e4400100e040d0300c269000698481c2484510301d1600b44071801c414010021102c0420805a0310446203407100003100720001e50600501941d0401c6000c0c0503015441031049610500043d00c8a050000b1244c007030b1005c0d0b505901000d0184007980d040c0901c00c159081c03c0c18420100c6501c40002441444140502c9002482c1c03404da000a07100a854010040c2d03a000f88900e00504c1d00d0610710703940e50080001c00707104002e0f51000c55441d51440c4103284105100b40d460b0150110b141d00113452919007400c03542e070080d039030745a40c0c1004501482100310b1007a041d55082c29101e06414540380b050240d0b000614410300c4d140307450103210b0b1300048190800e64030000058031082030741409503030314a590340060300a10001040245034000400d800784118400c660411100030004240502c07400580030390b403a550b808004450141d03000e180038005000d64400820315102d080c3c001c4405490094440e10082110b030051014026100301c6400d0250000c40642e02e0750b85400d40018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 69146000 1250 69144750 69144767
    0x50f03071701020f0a08160504030c090b030a020a0906060210020c1903020a0b0106030b0103180213021c1802100305070504031104020904111b03090f060306011808070905010510 78
    0x1da40c1c1a610240196281001e4040d5510200004001901d40d0030201c0e01400c0d491040744e210340d0350005456003413942405030003510180c80c5c21610465469041001e00001031540d2200d0130750520485004500580d2040113400c00f8090f1401c000c18443d2422101a1400140340d885250716030062202c000d0702003000401c040410f201d0508410602843e040582c2408840305010341500492400491042e406800480c2d6030a02aa8104100c905404c09114880c001e000d00035031010440022118148250b00500002810f1181c15140d0150b5030041030704031128a0301092074407400c3c501c00c40951900003a00d240d502184d003424404c0703107041e20000b01030748a82e0100410a031140d0403000100d0301c0b80e41c10703242e0300100540100304061584a5250240c2c100c00ea00311a842c810154000d5500390110613030341000c40c040c0481208d8454001000002c1c1c00040c09a410046050b40480d010440c5d007506c45c1c0100401006051014248400942075580580206004003a1079002c902810f5001840 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 69147250 1250 69146000 69146009
    0x11206081c05030c0304110a080303040615150915090503010905060a0506010f020a080708071a18030403050606060711090f06010f110a0b19091110090b041a070812070207050f0307 79
    0xe24452001e088009110712303c103900710100610000c0200300c00c008050b40484141c0c00700d1100d0010855956803441481d09596042c0400145c01701810410a40d08800001055034039040c19801c064171500071a00319015010141d5850380040c09005078080b040c03080300d800a800780380c03082c01141050f00c0695540f4100030001e1108000045900a002c0b12200b901e00e49a80412a03840d03510402c0e50305105420181c9a0141c03035500280102a081d000104803000c407544100035001c03d5079100200501070704003c8061b43c0700c45815080700c40590380c00c561a4800c1d540751005688178108034000510000c8402c10705014132109080e034000702c2e40d00003070301d0003000d40c041003844080d502c0c0480d0045004964643c0c810050800342c00c1e0301000030662070041007090542c0d00740c2c0b00502c03010301155480b0b1300b8400c9140c661030801042c0491500c821480e0341c1e4101c04c0f000945050880c0d07840c5c0300503902c428a09075071400c0007002d100a051781400127400610080f288601e0100c40c040019440e210244907 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 69148500 1250 69147250 69147263
    0x1c08060a0e0903090406080d0806040218091305190c0e0403050d0518011109190f051309020a06080402040e0a0506270f0d08091c0806011206081c05030c0304 69
    0x80e1140c2d8108101c03140803002400601001f0780e01c404450b940d0b02c508042c40041050b0344001096800c1601c00d41e884610302980f52040d1903446000c0c002041e5001c3d02045260704004802c02c0411010011407110320312030300700a4220f170764904050800007150b411802c2c0201640c020302c0082030740070081d90010815608006003545440381c40b00030120b403005c122020795003000484c280112465000d415259400d803021000010000b2004c2c0c1c12214502610381d51646000781031149080108510f003142215060005074501c0e260001504040075500100001d048101044114200340c06034012007171416000f044840510342c0c9084c0c580d4801428020f80f06c20b0030681c042400068a401c0114009080540742009610490030f40ca500020102d50046800340005c50b80070103000900d20b444141100302c42205980401c2c0483d00007101600d03090400151101c5803e10008a2180d08010145800144583d14102c034101c0401d2420200345410302c90140100035243c0100803c6980c41940540e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 69149750 1250 69148500 69148529
    0x90812090414010902180a03020a0314120c0304091a030a17040905011701061d0a09060605060a020a03020613080405040207050102040803070f0519051b0a0503010e1c08060a 76
    0x2000714008010040c41007052a04840001604011680c024403190044490840540400c4000d00a00c0c040b41d200094120001c03400c00c0000c542e0840d520503504d00340e0001d49108820040d1450807039000074400641170380001400b04061940e62081e80c00441d207e000054442841a0001c4d89454105001501d044c0500300e5402d03078030525004850181c021030104009035610f844000b07148680000090806601c0c01c00d0104485400039080c10703000c1003000040d86c0341e64600e650b20300070745900001201c0d0140c03208000701c0d0355039484015010300b0303610b070307004202201084c1002860850050800009201d803103030038070041a407410072070b0306540d819a000b69551501345007882c020700c5240d010b41058000480c02d0010403140c1001c1d00000e0b401501203880110f6000301741500d07180100e0004140d81d024043c0710729403003040c0c0d0080f01c2c200ca00400d80d40c0c0c0701c0d83c2d60700403e0035a0b031003503552002d50304040c5207462900b80303260303035044c2a0040e1b1500c07000c0b0b46400b50101d4034111140c0140b20445e160f00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 69151000 1250 69149750 69149767
    0x30504030f080a1d100b09190903030b33030709050607020d0602032401050307081303110319020709020a090b0d020f1605061303021015090608030306010f090812 71
    0x58200c4c1c2824140101c00a071808908100715449000f1000c228200d03e04080010b04203140148449000d62a03101c1c0241c4c54400a20380c01005060100d030460606032a104002e231190358060350219240200614850101c4490032000804010101701c4020942d0a00500c040154842c91000c00e846007516032503a61040360001851070f022059004000c40c0c000030070041200d100c120106403d039000b0b203144106001e160015130b0030303010440c0c1d803800207001c4000240d441c4401c44d4048540350f01a040c141f0180d01205000c03825940940c2001c40c030082e00311103413490b4950401201c0003d0805010842c01e202018000815a4803184a00e000300d0f100441c802c480356132180e044407a100c182c01540b42d66150242c0b0300068405507c02d0948507401001e00155000c03080d050348481c0c20342c1c15800707800c28843c03442c000300052852508407860400c000c03402240b8400d0794407808002c0e0030003200035510ba10340311000601b0404034400310030030046a030340104910280061020703031002100b86082d4850854 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 69152250 1250 69151000 69151021
    0x108010f121406090d14030108100b04090f06050601110a080307050a09150f090501020a0b04142503060b010903080d020f0d0f090309090624050f07061b030504030f08 73
    0x10984500b4a0b001d0715003801100c020009089108a03284c2e100c0010811282200c4910350009100c0c44000c2d400c01070b0b0f8120000a55400250258030051002580e403029441d10407482070b224500702e908507070300c10a000156800044c4018118402c10080c0b5400c1c0041d03480400d1800007074015000d1100120300449014001d00c07010b4080c0c0500000b99110b010804401080c0c0b0400000b140e011440800c8040303061751020038009a5141c000301101482d8a0f960b584036048801c400310050580140700241d61103410780552564100078030003d4040160031810014100c5100203500750511000c0101000056050010345000041c043c1c030043e118049103d1040d5148907005a007001c107440c0100c5460640c09691100c880140655202030120b501c03044000111041800345130001848200009003039030242d15150356452140c81c000e4100728401c3d18410080c1c00060003201eaa545444060719030f46c0701220400c102803450301e818050342c1002d440107058007245502031002c120f820000101405031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 69153500 1250 69152250 69152273
    0x10e19050f15060103050c03010501020c1509150c12070201021902180915011403030409150506070c0602011109011e020c030609010f0506180f040c0902070c0303020c0108010f12 78
    0x700760030b5400761041d090304118800412141c03d4080317841d1401103a45228080241c9040e140e0603001005405128004c04c408050b2a000b020310322501000540b0841d26002030300c011070070b940c2115585035404c0381400c50038607443c0d170112a00203000b4405034025030ba00090070751004140fa94220020b4640b030010822a0f1038005242c140100e100c810320041207400201d003072801500d035100b902184d0b02c40414100b03c00c0d80c0d4208170361580c002c0c0010320081010364040022101040a09120103507600086200c64022180a45402040e02d008010868081c007071300d01722030014070619182441000005c5c0099885980a6214040c464415005107000300403841c1716803401402c0360120310300238880c0c901802e070043c190300c9050300700030100310340c4c0c189007502e80c0440b4011005425103a4800b050800321860080c02a82c022000020018400c1914801000900d000d480701c48000e60030350801a250000344490141005445c0c001007056401304038510013510401d0000688180309410700305ca4148 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 69154750 1250 69153500 69153523
    0x50f0f0703050304030e0a0b0406050d1806090507090506060706020a030b090a150b0304020904030e0d0606032009040b013b011410020606010c03051615050603010e1905 74
    0x800041980600da085000345201c0d41c400c0d500c600c0341c0c9186406010480242e07109100030300e2400e2000380140c0d4007590241c5a82c0d0101035000600140c0612058101101c8a00c2035981b41d80e04c8018609000c01404660302800700c0040c10701503410b09402203400c41c80b0300c160140089034003191400000e44244c20918102c5d05c01024034030a814201c1c0300c50014109480a14440008283e00081035450f110070740380f141e9001014143e05035074540b0181e82401e99400165401501680340701d00103600340c42010080c60040440e507a140e041c40c0d1650a20400a040103445012540100400501044181410f44007805911803150100c41c6e030030090030107406c80500185c10071440e140380010b056240d080c12142504034144415018200b8090b0401c0c4030050240141c0111002075402c1d4026400c000096120749025403400d204c54200880640c0c41407004c07598180300c1c8800d4102410f560095540100049000f00951441018001e40d50503100f04030742e0001c0803040e80d1909020051000c4900c80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 69156000 1250 69154750 69154777
    0x907060e04090204020a09050f010309031b050c060403050f28060f02130b03190c0c0605040302070f0803030604050a020c0705150c0604050a0b2508060d0c090b042901050f 75
    0x841b80d440010700500e9143c0511030081e403110340c00c450558480d0040e10001600340d00c658107030502024080c0c030340c9c83c030404041d10140700303905491382ea6494030f000038401140584050601c50786800496400e00303003005c2009120181004440c4101c0001e4408600f405600038000110b600200c4107640190042c000308030000c002c0e0801c0005d11040110007948030b200c802e84030305400880b200508049480006c80d07803001035034000485d80007800d1984090b4010703010380121036280f0b98500300072054640580041e0780a1304007106000d2581000c1c014503800840100080d420000d03600e000c55962041c3d4451544a5021986203001e00385000c000c4808402081003030312124030705801c00590f183c2920320704841510a00300041d03400708000e0000b207001c01200030300d043d050300158412a0000c070058689a44405646200f200190890640c1c4009000107400803410400140c1000100c07040b0200040521845102c027040901c6404400320030440b007402c05c1d9880d000d281203404c0007800381c21a011680c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 69157250 1250 69156000 69156007
    0x80313050d0c15060501090b0d0e070b040302041b050702060d0908030a09030f020c011409010908030412170c07180212070305070e0102010203010308030a050c04090501090923063d08060f0907060e0409020402 91
    0x330614076800403c1a40d000f950180200015010800714600c1840500d01c0013840034003600340145007081c014a10564a80070220f4151115211961030340d0042d01d1750000595108c0003001055004001d89002e01c1041c0080e000710807590f00083e0400040d000b005202030b4000036442907688c02108240c4c0540654001c50703444035110500110454039480040d82d09031100c400e40a41c5040c0d402c100c40500c407041c40a04211440d01e81c00c41e28040c48001c0c2101c0064080c010008500400b440c01c03845005659008105401c0c081c0014192a007081035107411640100018000315100504a0f9040034002c18002070350340d5074400051040c051030700100c0f215400c00700009542c5109400c1400c425002e840000f1002044202040c58001550b4031035226030450f200184500e59076060b0785440140e283c6003090a05408549124010024600118616a280020f00c42e00d40c0821499a210b04445a4000203080411b18a60355504c503210f000308001c0b07015408103160f182c94100524a47c1c0c040d106548 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 69158500 1250 69157250 69157259
    0x8070e03163804030b0a090b09070f1d040b06190b0309010501060e091f05040c03020319050403171b030a020a0f050a0507080313050d0c15060501090b0d0e07 69
    0x50010611200c0c100c00d98500903070150301e1421021141d82c0ea010b09480385400d2550b6600708407000001c0118007025525080c84000c0b5120610813482a182403015000d002d00303118543c42c5038122600302a16440c801c1e10a03001039030305003d4041d001a0001c140d000599603d50018000c3e00910700d0042c40290809400a030b800d8410000e10f01840a04c002800301e43e0721000b0490301d12488400f51903102c2c1c4500041104800d82e00c844424100b02c150381079659075126004507040d070b00c0a244c6400040c0c2d000040050340c3c1c101044c410b0300303024540c40a110300d00300354400809468404d05d1040100088a0114140d601c85452807242c0030181d06403682c9903e85079103200000e40101000b40082011034a1071200c462152089070003d410544400303040507001d4643c8400e0741c0006010b0242606c3e81c0c07004102140d000c100c40b02c4540d5080e0b50b10032405000b45002e14030340d080940c2c104000e50034803100740405c0c0c4c1c0004c10341c42503030307118120705884d0110407103980b001e00003802c200344903400350700d0b00400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 69159750 1250 69158500 69158519
    0xa03110c01020a0f06020901020a170a091202030a20040507030c2d050a0513080105010f0801060f0302090601030f0c09080f070e0a0c1205010923040308070e0316 71
    0x82150620409448102441000580e240c691180000f0900e80c000d00381000015440c0d805003052a0061044804103c9680d980c2441032000035900b02c900280840c814042590010074480070304142204214070345215400309030b88162214008160032899080d61540f80820040740f010150010b00c03c0c48141070044015000746401c503650f40004900d00c103401010a900016901c000680d00315a2104200e40f480803240b94000303d2000702000070400c05802d440c0b003415000b0300581108c0b400000c05504d0546004d03814191740c0c1c0000030590401004200c0c180c1c418400400b02c5c0c2e016194066030b80c2d0f460340100c00030900312110b80c0c00d60b4074104409002030350200b14a4181c850000c115117403071201c80106646c4000c1403086580488014000070b0246002d07410821804009040036143c505450500c0307001d543e000d03000950200da581c0d5401100a02c0e5464460030605500001c0c03c4c02d00b0581c40040c5141030043c031400134000303a541c0060315614100840784030044500c42d01c04400340c5524046 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 69161000 1250 69159750 69159767
    0xf060d0504210201020c1e03090303030f0105040608071505030a06050d0f020108091b1306030812070e010e1c020a1203020c0a0503060c1605031209010209010f0305011a031302030a03 80
    0x18202c81000074076441056005100710341045903244000c186030300001803980c0b5001200350001050303000521003100309440800185000d1200c407400300846604220a0208452003940080f42070383c4400c104114008250690034031a144d14500349507241c3c2c9440d103a10203001c00341d02c8241c000c903500480c50140051000040c14052007607841c5502c80e22241d0906956000d18600d0001038000e41400ea0101e1401034482045401c1d012008200541d40303441c2d0003103d4001c0c030401140100b4210800c401c4036406180c01c0c43c60902420300850f00c1c3c0c2100003191845c1c6502c8134080400c4444c0142c441075685007103400e03009103500c08070620303440c0847c90000c2d106e00e81030240b180950301c0c10001042d546008078141e07120300e1a840003117051210001020009550140090710540400c0085540310007048800620440b01d5030b00250b510703490400010700341030078040000201441c01006000c0314111030820403d0300ca00d8001c1c40c0d142e407121102071807840381000d070080d0f040c40307041e0001d810590082c0c00c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 69162250 1250 69161000 69161033
    0x6020703021005090709051b2106040614060306010309080a170a0e0a020603070507020405040803190605060d0e0312070801080613020d0f1b09020309190f020f060d0504 74
    0x80c0d40222140c820701c0d8090f01d60944200b0f002c2d40061005224441c2554826036000120640a20300f90340a41c1c902d407510340c04000325998100b11400d0302502d1100540031141c00140550381044680c0c54210803035080000004043c1c4101c038000b000c1060343e07200760031400920380c000850b2030b030b544841000505204d03e800c59140d2810b01c1d0754002904414039118001100384802c02400b0700584c070794200b0800ea48000d01c0c2600340306c0d06201d40c1002d40c69910695120381c0c4552581d44c0e40382403c1658032813540b01c1c160249900c034181442400389464440c1940c12640e50100d0201d6611b82d9204d00a0660080c007261112440e130700d204003d001c1d50f00c028024120380b01c4c041a1031301901d4000b94404014990800a50095400410100020419800010140d0042c9131140450b4600c61078484061581d038040844250044113001d000d0300140811035400f0040c41025181400651700c50002500d0010041d216a110000a107440d07100d0100700d070a404c2089808002c1c610f028648400300383d205a00b07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 69163500 1250 69162250 69162253
    0xb030705030705030607030203100f0602060402090f091f060b030c071208040f1712040302011b090305120d02130303020708060c0304080319060b07050102030421050403060e07050d0602070302 84
    0x8000585040c00300380c5078240e420103800f400c8141e03244c010a0b00030f580003902d01030a403060104000381220b96510000c024200c240d01030441400c3c980100950800c0c080e00755940440c3e0441800741f1000002054944120000d201d0b0150160010083d00201010350040b190214000204061100341703800030104103118074001035040c04044021a5000011500100003840741448040455051803001a201441385940d0346031462041900329040070540c0c1c2140541c2d111000080406000c42403040174800c1d5203005000245192580d65a075402c007181c04501041c00030340102400e4903a0110740034032030f90000106070982e5034036000350703100c116204045840c014100850200d00325441140d00490b00602c1160031038032142084d650400c52400c01e0180c07181d0b031b00c03c00215801503002a002103030107040016101d1901e070500e5200c020740030380c082105010440300d9100c45600002a5410f0301c1c4c00480004003442c52121041c58a00b4070b030880799100f03202c10060410041c1c1034000b072003103c1c030a50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 69164750 1250 69163500 69163513
    0x50c041a030a030c11181006020f1216061811040203060a06050c07170601030b1605030402010e03010e1f1b2114010b0304030f0f0f1b0f0803010509010b0c15060102160602010b03 78
    0x123400c988550f040c214424075038112041d00402c0f40c01050241010075101c0c6030403030000141d5600c000459030140f1030780c0d4403511004415814800d0034034404800e03480c103880652442ca0204001081c1c2c0c145401004148040415413010300030f01000f950002d0308402402032040e5076064001c554420007440200c56402c59200020291000782d1075003411880c02d52079041c1141c4560380190b41c0c0c00350781c0e44426003541d6240001065800100258012040b01d0388561910340a03940c40d010540754491001e02000d4086089900c2056009462129505455001c448103401101c0d840010385000303200d0414212108001150004080d0004c0d40143d110340c0301ca450645400105072010000d49903208041010764010012060180602c1d00c90889107094021800f01207540c0c4500d020078043e801e41e803003140440140014245074031054050046040c0d00d43c1020f1488940e10345c2d5207070041e120410916000701280050b4020441c0450490f054a4603801c1c1e0740d107402000b8020120b0981040c440d100382c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 69166000 1250 69164750 69164759
    0x15050f070c29131505130b0a0f020102030609060409051006030b0a0513050a080f040807030c030308011a030112060e060405160b0901120b0f030a050c041a030a030c111810 75
    0x202c580e60f04902c6a6680c1c002e151549529010841400040902004006a802c0d13405c01070004c2010740781103081c4c640c4408980000805d41d1004032660029a841007050002951341d003080a0b46c050021100451070240514106050080110a03c506141050300100030000c4481e5a41d02c68418901c04101d141c0d11b4500803060040d540b000605140c201e51801008110b0200091003150200c48041317241690305d4141601e0480c00b6403098441c810001018800c042d4015441360061400941d00d40c040030490154440920040c1300d50132210800a01400800c502500400ba16403151402c2da40640b40c9810200e44980098046901140c2443c0b400b00e600943d00003aa0a03100d01030396001c2607100e0482001e001400480c00c101c3e40507041400782c1425680c20011461b0280c0f0910142c00302d80c41000902c0240c400d181a8a26070302071105090495450004003010f9540d01840d14081c04012800c103c404180410703c201e13000700e40c09814900e80950b409180d070050740b5841d9803120440e5103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 69167250 1250 69166000 69166079
    0x9090705180c07020906061b0a02190b0406030c1e030902040b04050c0904021602060f13061407030309060b090a09050f0609060402090403170a0b031615050f070c 71
    0x100d0b02140d500105001c54000741c02d01c910031a44c4424060091762410865254400e9184520001000785d0f41c096100700c0708500740088500d200040790300307140c0c15460910a41045070701950084504143e40d0380c003008403444c46804107200c2452000d200b8020070701c040800030050085100e05a0040342403921307030a260700706881424440c000c00f0840030b04010021003040044d41c0454451100240300e000380d0f201681e5540e0080c0100a150034581d035a4021401410300041c010783d00200510070f041001c0807868a09038100d40d400c50381494001890007043c906038004040b422040d076040342040c0d08005080d0250381c0000600c42c02136040310301c0a12100c802c41d940d4942101ca4104d1500a02e01080040c188807200310b400921070b0a225009444450099664203001c44410200c40c1d20b40c2c4042203c1d0030244111100231004a0342001424185040580701800c0303200c2041c01c008002800c0894800d865050340c007810341c080d02c003402c615030780d03110509015444c41080301100c640700c5002031103420 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 69168500 1250 69167250 69167299
    0xf080601051803160602060915040201020705040518060108211809090a050307030203030a1404030c0b07050c03040305101401030b0c09060c030a03060f0609060203030f07050909090705 81
    0x20140e40305440c1410690320041c801034682c00c520f03003502c1040c0d40240d07101010211030780038081540c010081032a203203042503e4050a80605100d440b0110309110260b41c1c0400c911054950650b40030a06880d450607008a82e020804104410b020301000419494404075a02c480d003061034006010115203060319900314071603511030b1040ca61444000d5005030130301c482c03040e41c800740c0c02e0107a504012a985a00e400d66002500031401a0800820020713400014851010340070325160380c0303001515207543d02810010541c0b20142401d001000090412071240f8201d460402001003607030b0300d440d900d24025aa54181103801080281021038804102c1080c40009040341d40090005c0415103a528001c5c0760f940c460b0b0b40d515000502040f81010300301003040146041a0a40e0f400101e151900392400e10115580d0080010801400002c000039a800403e581e0003d84415841555807a070200c00c8c0c4051007240c1c034032030b0480c01000070840412004544d2600705c400a41d0280c4481a400120032510714 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 69169750 1250 69168500 69168511
    0x1030509160302040c1e0801050301110c0607030b0307120501050411030a120507060212040b06090a0c05070215070f0c061d060f030402220207060f090309050603100306050a0b010f08 80
    0x340079010400140c6032980011400c611542858209009062520b40600c0c0c62418a000480d071203500401c00ca0800b4483c130760f2040a050269804c1017008410207840e04030203004c2104064032080742019a84c0c0501c1034070010805007035481240321a0749013460203030508542c1920082c1005811104504001c92f0510210364864540e2161209199081d106a00a01011380d20303160309102d0358181000300307161035019900030020b05000749003060400600c05d100810031110142400400ca4a0f6034000c015945860b07811100c000441c1021a80140c01c0c0c047e0000c090043e11190b1150130900c04038081c1c041c2a22515a6107103111101c100782c0c6c0c4050710913a02d049801450402040c40c00c0417021021b0340e08603200500103103140d010200f00359088042c01c030b5200041c2d40e000881c0c0081115501c58080c6d02e0b606000140b1080a103501c0c00f415280c0c462040b0381c02003500200041c45450802c1e00c850245500c600100b00030b0400000d0400141410b040650102e003002c0602800343e800750300080d2140b07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 69171000 1250 69169750 69169783
    0x1a090403090312050408030a0309110a241403040309060f08090303040b070507020315060406140303161403030f070801051207140303040906080a0201090b03010303020a0b18010c080601030509 84
    0x61840d9119941c43c54511448020000103000208403c04140010012918503a601241099403030a28841c0c900c140f2101620500150f4420403104490081126031620414500c022150b04610217441400402c0c5030400040c5002041100f0540c004514500f40c90081d80c408900010010054412170026940e00081703074400d100145c0003810800f8450f51050592400904058440d40400e1170700b20a100020f18448210f030402c81c40741000d01c0f0355001400641c076145645200000466101d1084c0d500220900c540c1c40c44401c10b2150301e520462f024545a07048a0b40c901c0e1544c80000e01c4502500d03140c00058800000140b2480d00380003401c24141404041c081032403901c29a04507245040c590300784c041c00148000030701903143d8440d000003403c0303001c09000009064800103228401a400c600501f5606100610209a0014001c4000303940072074445001e0321028ce20f0b5850070340501d09204158208901c2008860b40308203224007402080e2030070301043e100c0140b000e4461880f40010b4018 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 69172250 1250 69171000 69171017
    0x904090206040332030d02090d0b1017010228020109080d09030e090402010206060943020a050601060f0302090604180f2706090b010e1603060608010303120f0e011a090403 75
    0xb0301c40d1030f401230002c0c00c0020820200d1101640d44d690212070110756107404160007e5040107008040c2c400c2c1103003c03010030021403415400c20300c0403078000c200306000702c500101034110101e424003d502500c01d20340c1000100e034031250b9440c00c65016040a01c3c040300000c4014980400604048400c140980d0b4140c006e490560746407802c1c07050320100104001547c03040c4030141c3c800c582c40720321680c000c4500340e4400c061802051a0b28405440120741044c00c6500c410036102c0803603004a0101d0554025180440345840c42840072030281c0102080146e110380002000100c03c070042c0c0d480036010304001c60500001c0349100a64044030fa0846001402c080f610110551000c280d80c0e031452024800c0d0310014514996480e81d89940100360402003140440c041403100c12a450803e427105010545002d105140c1802d5000f003082c0e4040c4002001e01580740d800500340b4483d500544040000c001040007600310030080e00d400f800290f00c82190745d03100d5003054101400d165900e203110700e8054641460 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 69173500 1250 69172250 69172267
    0x60608040201120b1f030911030307030507080f0d02040f0501020105130809211902011701030c0902090d020d050601060905030a0c0b03060d06090803070f0216030602090409020604033203 82
    0x25104d541c0400380d0101003c5140e4804104440864407840100e50780005c1e07600d81840c014408111441c4203520a80c000d21603600000e130700504440d18030342c2c003289094544103d810003114902814500304080c90020801141e4580072401000489000344e00030700041c2c8403003290390031401c603201c07026050580401c0405454103000030750000791108000c45200d444009a52641084100c0803050900030813005280c055603401004660f807521821008032055140d65114144039000d4031410aa035500070441c00419a6041014010250003502d00c00d88102e1900e072540d1244000d000320004100544c401048a080020344d000c5140d90140c801124031b030801041d12056000107000c0c07540041c0c3c640b01d03800002c1c2d450003030110007442610b48649905221802130300346040c0702d00c42d508552055440b0f104071090502500101c0340c014500690345d0031070354013140c0a0210140301a400c0500003030004100051542c030800091801c13610f00d00d03948524a00104444d1504106000301d900c18015101c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 69174750 1250 69173500 69173537
    0x1090b060103021806090118080a05071a0703030b010504080f0d03111309020306120a05150601050c1f110a08040c080102070203030304080309030409060608150307060c03030515030102031603060608040201 90
    0x101c264030506008e80200d4848100540b9000950445021604982003002c2006030402c80c04028054000701e24000c51183d804101850140c5e10018081544a07840d07070645034090000c030303070240200c2d0b816110b078440646902c1b03a0f501c1d003c004040c0000c3c900791700803480410080644005643d403481c01070810b4030f0311412601039040508420343c000d00b14000d000d04000b0410000c44030354800c0015111071a804c58040ca0f80500080c20076040c1304040203107081d00301d00030401c4032100100d5030410403130120010f003c00040c070400b503040308a204c00103241c55420390000ea140b40718900c00c8c04440103803500c5400d458240d000d2411300039055801400031a0002d41d54030055540b001c120000c690401f580c0d80003000030740c1c86903409500451903003010300000a03504000550281e4081d0001d003c030900d1301d41c0c02402e0100c1c02c4009000c160703030784012942441c244455101c0c4160001c000707640724108082e00440c11f45180d445080401d2402400080650203040319501c07894058541010f0150800b01d81e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 69176000 1250 69174750 69174757
    0x1003030e060d0207030c060b0d0803040b0a090804090b03070b040b03060907030e060c1c06061b030512092b0203030c0f1210090b03010b10030b18010801090b060103021806 75
    0x80740d000106001250300030718148090002140a03550780c01700b0710301a042c00c408651800d00d4080c040c1c40b460340300001040c040f03401c4903005907000968044e2a48c4000c42d0400900300000000d00c3c5440000300020080e032960400e50507030400b103040e5500c1540d83e480c800130754851481880d14800c410320021b1030502d0800141d5920907050304000c14405c0e0103080b142d0420500700c91980c003a46c0e0114140301c20514900c0d415012482020040140b00d0038440064040d81030781d00101c0d040c4030089061001c1611400540700e1100300002c0c1c484070b9092001280d500c8007404180c00120306018081c68109400f100344601040c0010740156203542c94004422004c1e40c01411081900b03403040200b10542d44000e940f092081813100044402d0074103214100c020344840c4545a442603051481c0c01d0000d50707c00f690003841ca5458140011003c40000c08508001c0f50784071950f07920740b80100001342d03520064201c820030600ca0403290303566603183e50041d0200d006649149800015400c05100b4606280c1c1c001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 69177250 1250 69176000 69176027
    0x90f0515010e0303120403020304060e030a0f02040f09020d0b1807120f020103230103020f06070b010905040c030b07020c030c0901060509010305190218152b0f090303150e100303 78
    0x41da4a850749541761100500002e40307086005034030000d070800002d58444611700d8040f05c118040d148040f00d40d21115075516070464081d01c1280c2d00e0180301d01220b5941e04c50110198041d000101d5840e0504054805c244121149000740c08496000204000c010681c04290b80c80e40303c0345c003051680c07515100700c2d804045900320f05140d5110201d080c0381c403c020808021007208400e00300d043d8114814814074107403545026020f00000e106c44000551411026415034a01d854005440d64032402e1010541c8050351002e89005024400e0140740c0340c1c04900c0e0001903109800b00c17400e00580b0414031010081c2440340c080020024801080c2d150701c02e0f0415a0090032000301d1030400d00000c170b4158100c0c0d000c14400c0c540c00c4d030005c502501d14180310356101d40920050000c00d041c140001d680380c0c061000e6518191201c8980508103001d052281d00150401d011030b1001c00c0300f20014074000d00149800380c240407010170324070b40000320314000c401d1051086a0110040c842e4600d0360b6025240312003041c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 69178500 1250 69177250 69177253
    0xb0705100506042912030a0e01120603021207060e0d020603060120010507020f070902090f1201020c100b040b0907140d11030403200303060109030f020f04060306020301090f0515010e03 81
    0x2000f07808820318009840141305250320a0804202000030084c3c0300b0310907403008411750400e1028094443d0071910490030380ea028240382d2900020411060300a003d00d8000035401a01101503c245440015801090350f03180e807140b880720407800d010031100c1144410002d500210800c00101c0a52160304e4840e480d1080d814507400c03201140007003909586007110b103800180e000303501c00740305450208080742c020a02c0c510114602040070300403640e00b00b21554028092074004203c0c95515400b5411a81941a50010350302541207000001c000703002c4101c03a10b4811400c0c5058100989481c003802d90044a954032030103100c2070100c45600884e007090b403c4121060303680da810403242540700000c520a0f4425540e81c44030040c13403a009003d40c03901030300844040e030040c8100070081c1d800490b0070080e650080762000b00d41c182d03880000c1500b41d40400d059081410301000100304402d5402860598050f0788007070052000001010084070002c9503850031500c04c45071305008039400384415091040c0040c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 69179750 1250 69178500 69178511
    0x91a181512091f060f06140409050108010b270711210306030105130309052e02010e010605060a0903021903020303070b010338090709090506010801060b070510050604 73
    0xc407000405008031a2001207803c07084504241c2075400750b4012200800e26000c200044c2400025000341e2042c0c003500060082c0031030886251419081902c0c0184005c11040c06691b8590076014040c05c0c50003034090050410040152007500310020540045210050a07541c968400da0200c7e00205541004c0300d540c02400c110b404405490415582e4050744452040c0c1d603400c0c91010b050031510300030140340d0140c001c1100e54001951024100e0120780c012a20903640404103c200300c00081428031b902008002884210610341d0190031545440040e48001c12a80380c0d01d4081c400f20303104024010000035203080c814070040c54420800140d910b00d40e0003c400703603500c036070101c1d00e180d020003025a4200000001001040507011801c0035000150710540c451114880141041c4411440c404014240000014404101c20090342009001e182402c0c8034244441c2819510743c103080c05004003070b500345080861003280c0c1104031801c1c0c80d4080002d2109085104141d00140405481d07680e000b40c540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 69181000 1250 69179750 69179767
    0xf0203091908010c030203010e0a0b0a0e060f1206060909030a09090f0216081209030921120a05130504020a140f121806090606031b1302040303091a1815 67
    0x248a030810b904d913941c900603540c0d410010044d031514001000c00c0003035070400e00030f1555a1613059003d000c441d8995a04c0500c1d4882d2000a41d1255a010402e42c12002240408401170400500315005420983e41c40c14035885000005441f44500c0366207a004c9a0001000c1003a000b050348501c8000081400050401b28115491295100007000a0f641c3c001c0100700d0001000160704115000b8251400540c030b40508000820100a040c071061100922514448003400d0414090302104486e11000141d484072403610141c440d400c040040c0c030f5214101403002c605070400d442151000c00d400e448040b41c04504000d0266182d00c480c0c03544e20341202c14010141009014682c4074000c441d05401c0c5066090a816001d15104000f803d410050307000b481805015140881d5400340061400d5101592124030300c0455100ca031001200034002c3d10019002080c590f00915400c15501d0100c8681b110f83e481041040e090b01a504401000310800501a410703450180b0341004012000030001c4e0400890 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 69182250 1250 69181000 69181003
    0xf0d05072102060103150c080f06030a0f120f0804050a02040e030c030d0c030507030506010c060510080303040b07080603120406031503230717120d0219020a0c060f0203091908 77
    0x7110316900240c0c0c03010b0014001c10601c00030408915103a08000c2000108125000340fa0540260081c0d18104045000c9517440d10144186440b0075000b0001c000404503c1c41e00f00d02c1c4a4542001c400041c4401807807941e440c0c0320f0126a80219040b500410300c8540c1ba80800c0010151490201c4044c802045078840c00e08086c800743c0360f407015007640001c1c040000716000e410f60304020042001c041c030308010844140e03000b40c5052642604200e001500b40d8a201d41c0b205000760717035004004584804410801040320300c48580d481040640d840302011385404007816902c814000c103110070078405000c14820349110b40d00c4000306095401080c40801e649031920325040040d403490350020101455032104400d0f0401068004000c40c11607602010319030b410589d190002c401c11411481c1c800603444180b59119010b54030041c0c070080207081004003c200103580c6d2000442c007120103121079400010080d00506680b144034100d90051880c1081840400040e10003988061440d00032512000c14191070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 69183500 1250 69182250 69182303
    0x1018020a0e01090c11030717160c180903050a0806010201180303091b05030304140a0b03090d020607030203040b04140703060e010e0712021c030302120403030903110f0d0507 76
    0x140340d07501070920b50400a001d0240d40d02031405105102d21600d035101c0080300003088510b9203401c1640502d003680c064581960701e1140c2028403c1001450742140c09201032001018200d0300394400459281c2d442c0c0e25079005840c401c0074050003080d8148050078010b4015417109601a0381440001003244030b1084031039080d00a9281600040d5030713a031645d000c01c0f88940c1c1011001c51541901c8480d03a24100019660f88103d01944940181c003080b60501c0361600300044016216884640303440b403030489221692000306044030360041c800c10001c281074074081c1c0708403800340e50040e1080e4060703507840d124081d0661056410001e2031107800000800318402d03115640ca614103400012400c5a01e00c5415858601c0e650010319018846840010043e0340d5040b20200c1c1d040d080c41c4100c052402c032704040c0c00a0003003c041c08080100c1c80104002c060f819407010381224841d803540f0345002c1c001d80f1410ba9a060900304010140c1c032004404401d20b01460181a01a20419140c2400458810b0303088034030340e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 69184750 1250 69183500 69183509
    0xa11010b09040b0f062209031107090209130203010b0405040b0105090415150e0306040b1306150e0c0316030e0c0d051501080d020304050402030c0c06090a03110109051018020a 77
    0x48a1000c1c0521380035405030035134001c481103c603480e00168207800108840030369010710b030340c0b2a0744141110815010309081c0c0a510400c074140c13601285c0c0c90300c41c80042d600a2421740d20134140c1c0303050503031100c0700c0b803091300c0c1030316440015182000d0511040c04014503000040a050100c2440141a15503480c0580489109042c5505282c246440b9103080349004016000040c07004825040c43c0341d0300e001500d685e0037504155910350b030b43c580204640032074082d40006043c00d4140142c8001d02c0c0a18810382e02103a007e4905041e5543d146d4030000202d01042e01c60005840e0164640000c1034880c0d000081000c11030000d0399980801d8100244203018141d00032905900000c03171808100d1080120303030740100450030140c403050001100081d101e115902845200b16408404504401580c60a41e0312400310a012580d8506000c461240c4d2010707100c2c4120300003041d104018450300018000d5004030fa61020040c00f00c42c203407034850409080003030740141d481082c50308003c015070b650721141c0c0b000f0f1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 69186000 1250 69184750 69184763
    0xe010807260318190305060606070606030f050d090e07020a021005130f0f05010216060311120108030d05162c0402030403050a032405061c0c0509190501050a11010b0904 74
    0x10394900c00c0c40580008640e5000b480c500d00304d4100b0201e1030100e1895888201110030f0346c0d0364101031401500401150708040c0892401606010400c180055030500402c81ca171201003110340c0c5e03401e0504e1200e804440000c01a0414a20300c0300500313100128400c40d42c0d15040c120308007c1da842c04c14040c0140c07940140d14114640f00100318203100485441d01820342032000d8514841d2402c0c4601d20540c15110b01010955101c895407080c0510400342e540c41000310f1403110071540d44031a01d80d504c0c2c0104c20507000c0c4030700d000c000c140b000140c03489904450500d40c40f10943c070880481d40141c0000f410701004081c07100000b010f5a151348510055104520075210030b600c0e6400c0550060848215000b8284c0700564064100c1d21044c01e100b40d401180c0048810300d07a02d01c0150400d0014100c6105810031590038045054505904440a041c1c6140c0c1a55296200c0d030306840c54407609420362060754081403040001048292048071004082c41c8244008a07017201240f000ca039145100300c80a0702c20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 69187250 1250 69186000 69186037
    0x4051509010b0117040c0512100906051f030203070b0d09050703050d080a11030408090301020d050405061f230102071208030a140603070e070e04050903030a05010e0108072603 77
    0x5584c006101c610104440d503103255a03840c21360b0341c2a005051502401d886645161815506070740100407041e40c007d0a0002444080c01c00d00c1c0c00800340c00d0582c0d0007007003c219074290002201a0710325141c22250002d0052214620702148039601e0f03400560240328583c1c54010510100e41e00b044900001d6205500034400d500441c00f005141c4036014021412140c203001403159407401080030b403a002a0440c009503920344d8400c0000340240300300b906202c0c0150400f81040288103011030b50503c03d071b4103171216000040d0700751a1030304802802d01a0400c402e018610780c42044003240103d0302410303811f0046543c0a40c1b5800300e03501440041404076110200041080b00c0300c8080e0044040340900710f4a99100c9050080c00207403183d00501030030088482c240c00290035288603030040e000c81e100c050402c01c03950800c0020300e80c999204030f9640c00168100800042c50150181c050740c12a9115806032002506050031003210784403260000000100c5020b00e41082803060000380798210031070404010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 69188500 1250 69187250 69187271
    0x1110a020a03140607021903180302190e060d0305030f0c09060d06080106050609010203120406020d020403030504050f24070f12050c0c0609060a0309020303070512070302070f1a030405150901 84
    0xd0130000611080440d00078084030300c07a00944c104449405c95244c24120081106404001d699050340e500c0658001c0320714501d200c1c03a4503a100c2d02701c2035450790030081c0300560f18a0306000d4411400350b0300500040d401c20015041c01000d25101e0780001c1d40c129850b1404441a0020307102d90811000c02d0301281e581c46040105810921920009000030354040e400c0080030340011b51a4098900d003660000c013140000380421015074100c07200050350210840d21291a03040042031904903001d071900a0101c4800740c0c140c4e24040340711a0803502203813030361000d0070391b89180c7c0f800d80d821144003111907400d03660005000440081003181d0b052000d40e10760b44c44100c40c03082d151501c0c2d25419528090401008030400940318030044800c010464100440c2424051001c40d207144210311000c0d03c14020511090b410000450040c03800c140680c0c21100307c540c0b100302c004000c07035013449600008900020b1440040031401c01456115014505450b081c141d0b2031a24001c0c1941200c40c42c607680d5484003103a5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 69189750 1250 69188500 69188503
    0xb0a09020d120e030601060804060c120c0504290f0703110303040b2d060d020a09020705160b0901020604030c06020d050108030d06090509030a0315331d01110a020a0314 74
    0xc844078100d008105d41d5244c400081c0034942e014001030035454a84000c924200d019000f03500302d00d21581c10170020b54103d0700006107180c11a00a0410884a40582d1b0100d0002c600d5408869524800301a1500401491911581d80081c100701c0500c075240071318581c41e0070203001441c815800b91090342c00b90303d01101405030b10750f80106c1c89000b140c1286500703402910406091540171800b6038460409000f07500001c0c104600c3c030361040803120b000007010020000f01203040e600c81801d89024040090301c80680c1394032406420b5401d8010b901142c00100031070b100f0458001c0580c0664001440c1a1840d42c6a00036214260005001e0380e00002e40c0e204e402c0c5c080c0c45a01c00402c41c4035400c008a04040b14216228428000a441010703110b4075042c001040388000325000305400924261940780c0000320300d40040030880f90ba0781c4c2c0c0142e0f13884500420f0103400081c81340601c1007241c10600e003800c001921040c0c900d110400c1c8604c50700b400c0e04c0c01a181c141320000658000c2c500c4030f00d81050101c10a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 69191000 1250 69189750 69189767
    0x80c030d060b0c0a0b100e1519030512160b040302010504110303210c12070e0a06030b010804020d050c0301020703020f190807030804060f05010611010e190b0a09020d12 74
    0xca0005030100071041062001142600085a05c0441d10060b926228003c81c01980740d074200d000ca00c40800240007908201c00910034109105548841c945010382508910b0004184006002600040030491440709101c00a20000c0c4220404400541c6242c6400800e250121421401b5039940c405000070321a00d01d21a02c8406012002145000e8109044180360440d40a03641c49941c0c0900c046107452040d001035402001c0d402c5035070403d514082d40d0052070012804581401081a010003007111071090080c01c011000c183c4a0482c0e81d260796090040850f1018000d441c070b03026200e149146a503003030000301800ca0080d401040441200c183c00c6003004650708200c840321481207990382c00644400f003912510b54150814010941c1c0310b09180001c1c09008601c00c0f415458440080350868101c4100480d400c02c3c9002040890015110940c0d5400c1511942d414080300c82c0e060b0001485454240d54000941c840104040307403a41d0108485001e8032801300d0304001e064942e1580c1e50380c0701c40034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 69192250 1250 69191000 69191009
    0x90f03210e0c060c01020714070e01051005160201020c03030d0c031b08010e0703061a04080f010b06040504020705010b04060e1e04021003091110030c02070527090703080c030d06 78
    0x4000c00140d00c1e280c2541da14120075450300507003001c240c4041a000a505071000c003034020b120210b40078070789401e0686074403060203208a070480b0707000040f0301410704681780c1800403040d440782c0c0c0c68070b4440744107501001d0644070101d0441c860072240a00944041c00901201d005516002c1424203e007400a000c0c1c3c0c9110340303c81c2120a002c0480740c0b02c1baa20100050444030a04403545c150303190440d080700940746070b0700007540140070360540300303d200c0c071002c010422101d080c002d4401780c0c00740c64001d80c02e840e11903000d203134011424402400305240c654000c284691182c0c0000504803200004203054640d03d0b445010703551015410440e00500c1c540344c4152454104680382454902540003034007070502032008a04055490821400300180c2040107004928010800c590050100000030042d0040c8180781d40180500000003c03242881403507844042d070f4088400702c0c41084210386a03115100200b4405951007181c0001000c5150354005042544110000d10760310203840e503050094501ca90f01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 69193500 1250 69192250 69192317
    0x6080717030301030f03090b070f02040e03030f19023606070b010b1303051c031803050706090501060b072001050702091b0912030309010506010503040b19090f03 71
    0x340d2851000c80031044038150790748002031301c1801201d802c0444050355640c100354006103001440314144029101d03102c1c0c00d80d100f2142406110101c02c0c5550720303400181ca6050040341460003250724404c0c3d01400c001c6d8003041a80042c00d00384000707400c401c410400000c0c42ca404a550040c266440c6404810a229820a80c2c03101d00c0d240040d074900d00010414803485000e00800700d01e903000c00344c000c40d0250056420034204c1700a88403c820300324a184201d040c1354041782c03500c0854102030b040800c0c01c0640b55051b842e05801c02c2400d488250240800d800221110355990b500480c0d080b210201a09550b801034403625198041c450a00120309900c0c085203051010a01a907801030751341002c5554407021840690180580003548400d040c01460702c4913500c060140f44038044190004090352240001000030301142e22003000540799032000782c1d005040480c0001c0061410a48442e40c01d010102034080001c016120340c454881405e82d0350001c40002c0d07682100750302441d00342c0012030750f111131601 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 69194750 1250 69193500 69193529
    0x3030603050c040504030815060d020c1b0a06090b03040231230c07020a090518010b060405010225080a03080f060301050106020304050f011b0b06150306100e030a050d03060807 77
    0x403000742451f080107040d4513088000201500d21500c888040c0c552500c080309095454044034040a9200c46c1c125070750817480840450410407a10781401442c0444205859882d10182040381c90a40d540c030090081c0c1e00710034490b000c0c1c003080c00c06c0c010441011903d40f0704443c8a010601c214400c0d9068090a14022036404044012504020600c1a000050031141030354070350b20742c80494441d050b264400503004d803800007000310445910804503010030000000f08103c155007020400c1e035000398010980140c0c030812220030444008009450050382050441700240d40d40c404140c0303030043c0b44004070005002e103030a0100c8812010021504200114024400303981810f6000f5524040c505c1500e2085201e0901c002c15039000d417450728082030301404411001802420700740a91030054820320700a1401c40c2050155200020550b4003c5100806062507840d0b007601c1181d0700c4184600701640341c01150440400150f01700800820328515883c040f0312180381c445503a05150040e80040d06c104600c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 69196000 1250 69194750 69194753
    0x2060907030b06010c0311010c050301050f0603040b0112050703140c21150c090613030507050d0b0406020d1b0e0a1707150201060b04080606031b0f0907030f060303030603050c040504 80
    0x2c48205900000c2882e00c501a4038050804440d0518112103036092546086071a80c902c9900030011030594809440165491a41c1d105022140c0720455000c0d004200b0540144052070107000c101541c0c3d4000c000700c0d08280d490f5141d240340d50f005001219559444860b0b030300c0b8181041c02c43e10304480f104424551070400c00d0a0b045803611013846c54507407903c0711325000901d10690502540c190f824007424568448001d01510104d060a6000070b0394148110400042d16282841801d48080da1140d8807541680702c0f030b65120080d401c244403804105489031620000140c0d20511110098116900c244440c1207110030f101d00120381c1e82146500c95501180c1c0c60605000041e0001240c08045107462a00c4d83ea0204900414107604560a0041e00150028442c0c41c000b80c1240500e07130442c1514103030042400d04403160b030421902c05412000100b860715051500080403a4411180c0c2408199144905400f40c00c03117030f058000300c0200b940c41100740144002048001c0320540d05503000c10003030419 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 69197250 1250 69196000 69196013
    0x40b0403030b03010e12040906080102030c0a0c020d12080402040e0606061210050904080301090605030106140d0606032906030613021203090d06020405010e04060308040918020a080d0206090703 85
    0x18009000d25440d4803010040d61000d60051034a402c099083d20101d813540c000c2c50450342c4c014400c1e4408281800e6011030313641418402c480c05482c420b52001d242408104040e21585041441a84d200f10004400c101040c0c07000d1440005503021b603215001d600c1d0030700c1004211801c0303c600c1c03e0305a04c1041008103179194081103d808180304541a001655210358000f07031003031650801303604080c0000a120030800204041e5050360b0819009101190f140e10a0600703c506500c28184698060b9240130500d05044446110482c010701022070500d072a40c652480c4120305510301141842c840401c04e0340d0b50005030580360045822000340c00c550138504039810016155000180c8201c400c0140f9945020003003046400701c0b10045c08038090090b16080050094116220349400318020300d582216501e0503118281c2501c4d403044895044c28240440c0d00020020340c80d40005031803a080d07802d070142c1d503012500401017200000420551240c01402814100302800828503907000510600c0050103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 69198500 1250 69197250 69197273
    0x16091b0f051e040602030703090e06060d0534030f0504110f28150e0102100b030c0a0e06010e01170a1e140f011502061501021501090501051804 63
    0x40a28049480c2e8403400c042600c0d03500c00030110142d4207000100081d5498001c8064010107009448001d021561125080c0703c0002c100c440d075034008010400c1c00340401007507202c90380105440003201900c840000390703803045049030711654009028251501c503150340c0c580580c0c2d181c442003210900c001d04155681442250350321341c0d154414a68003000241075100d5160046003034401c0c04c15a42040d1001121107808480d034000c1c80b43d0314403400c8010210ba07026440d200c080c03e0045e4014900207280243e40e20040410b8a00c1550600503d500c0c100342d40d407020031000240454102034100c3e8288940050f00c401c5c1c0200115040c4001c1080d000c880440c00540b642c0e000001d01408100280034003150081560400c2d02e85c040e461811003840c110f00c0c0c251410500ca8075441424501c5a601c4070458400c03440c3c07400840c001a88030f40000f0b184100c01d41c44190308400107004540c540c15551851180600d02608001185643c40380100402d03d45000401100d0700da001140c100b40c24261600702e41c001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 69199750 1250 69198500 69198527
    0x20709020a03020f04060c0c0e010b03040204090c05030f0105010905060904080a08090307170a0905010203033c190609020a052703070f0303030509030301140904080c16091b 76
    0x15800300d103095000b40203404031807903003c3c0f0964640d80c490b02c03200d003d010010b80c2d10098914079003001e004102100d1140d8220305860b81c200c040c500f15036942c0e081001074140d11400702c3c7c6408021000046544040005040ca11001030020800c0c1d130401a518044440040c15a8450711001c01480045401c01d000c4450541c181c0c07800c80c0c095a50894428030303500c00c80400a100341c42202509107100071640c05001d031074072540e8611034125600c000490341c074041918400c1d1400340362104d01612000d21242180000010000c55100306505401281a12400c4444285044005918100d4020207100b4a000b8000c0703100c0840c2440b4078440010440d01440c270009800400c0000001d66003030310f10341a41c0b40d4000c014100c0e11000c0e1101316000f1503001910080300801d003020f02203a014400030042c0c83c1a83c100070b80f29080c006203c010042e02c480054070035a24101d040140d2084540d050044062111403040d61b04446840e20031b43c1000c94002d00001103848421101030404642d00c03081b03401c90031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 69201000 1250 69199750 69199769
    0x206130b1f08030307110114060112020d060308030c0306030613030206010e070309050a03030c180b070204052e03030e030f121b010204031505010e0705070204050a090605040c0e070f0207 82
    0x360501d078403482001c4054008605611000c0100514564044000303881e043c41c030b0000b03100b40c4103500700d407400ca20406e4800364086446039100c11501c11080d80078040744030f103122000c5800c5a4036160743c0890740c8191045c5011001c00010840039080402503240c20208940300031100e000c29490007034a032081806507002c00301c107407000b081149102e5082650080d8000c03040d03c5400061345406001000070805000128030184003000d4070710f0000c1c0f260300441c0c20050005d0f1910318280d00b04002450300400907050b00e40100b03030801c59103116007a040c081404940c0700480007800c508010789010048141c45100b40d0220000d60031440011030002c0b02104000401916580301502000a9840f040c0304598030350b04c0400c0001c184030040c16a00f04440c944030003007105980f508003410429004507000c034007040b820083c440060815900c040d5002803000c034005281e0703d0700e9070703810140e540584040e40c0304810400140701c06001038032419088a840d05010f406400070010186d202ea06511421055 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 69202250 1250 69201000 69201031
    0x40c05041a07210306060806010f140a1b0807020102151e04050c03030d021210060206010b0a05041a070201020d020c0d0f0203030706020a0903060e0a02090c2a010c0206130b 76
    0x410003400b000040d0356545590f02c602c0202a401c008000384010312940001a8640000c50703c254001c0e450210641e040341c1e1802420101c040714ac0381c1c598058007020b0100441c02c44596011b10f40d81d2042908035125040c0c540c2e54405e1170000a25003440b14054441070b2400c042808000321086034445401e02c0100b03c2c241d10f55607541081420040200145074041c000000d4403103802c1e0b501d038000d09201d00e120b4040240c580369451540010050741c0a60400759000c000144504501d590240c00036103038524000d4035280d110410042110007881d82e4182801011038000c046607018002d05c03c21a000740b0040c0b0340d40d5007620004a155460980c0505140c400340c0d010015900e0510442c1d21603034000303074103658880c400b240003481c3d034440d44410740303036a46081d4814650200200b4100b001c00d0300181481d03440e0b1520848102564000c0340412070703050309140c90f01000c010714a41d50808011080000424a0f81a000641046c038010402c800f0140c08501300350001c2c1106060030342105c401d0260054 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 69203500 1250 69202250 69202253
    0x212160e0301020f07020a0e16110a02060415030c0311160201020c09040f0c06081605030603010b04060305071e1511071d01031a07020c04021804020f040302040c05041a07 75
    0x110090340000054055000042024810b20904010a4070f28400c1e079036858010b0396803809488000c401d59403411140745044441031503902c0741c00c00c100340340f13000b1003030781c000315450760008201c6e90059010150304c00c980354050060607014818002072603014207080c00348992540440ca0140310f0b02200904500c2c103206c038002075900c208182d1031404000f030420314150515041108281d0115501114560080386001c90b4103441a803046020741c1000345110000f0422040c1504d05070001840160107650341d07040c5052030394640c003424000703500800103091468184540d81c80e000e507107502c11170109910a102000000c0d1004800d86013002189031024001c04400b5000e03003801c0c480d5008205078000c101e000400c0071203000c0eaa904a9105000c0350802048508001111000441c0ca04016800c04014032403182071a030000e10039811b0703030300481e0300c9030401d00d00140890f000302c4400d401a0300c01280c04e10450405100c0c0c22112074403420021b05280c0b400046036589101d03030040303c0620402040b07910 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 69204750 1250 69203500 69203507
    0x10209100f050409061d0601141602010c062301060905060414180406050f0a0506090402090921090f0102030c0304140d060c020105041b0f0e040c050603010b040603050a021216 77
    0xf000b900e400759081c45415a15610118a000d645c00100d82c0b0780698000f02e51190b000b1740069550740c6480400604008400144200c1c07049032950a0b41403041e55600400010b840d40b1401d05071761101e900192a0032184000d0205c0200160000014404140000d120940d1110103981c101c071480c5001c5290540e510010903060b1000160030761f400c008420500003004440c0e00304a1056060302140241640d810b60844242c031030580780190880d034054042005030402554859003c04180c080b039050306042030600081005404440084010214045401c1e14001070043d40e401c00900c011400c1c0680f90031516102e100394401c0d407203250360b1100076074040c0c0c8071503030825000c6401940c10410301d034440300082c0c0031340400c0b07504658048a29005d01a0700100403014029074040c0390031041c900c0c1c1061006002e040c0050416112183c10980004a503910500114040c03d082130f01e03903484034540325020303003a55006080356071418014005004400c0100070b08540c00380c0d5070090165102c05030302094 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 69206000 1250 69204750 69204757
    0xb09030f0403030804050105101a03060f120706080f04110607061401031104140403200703020a060507030210060e1b0c06070518010c0213090c12030c0b09010209100f05 74
    0x140080e00040307030000515810000c01c5211383c1c050700007400782c0c1d6a042d4507800c04004900840340380f075030b15143c1d064841c54140c01656020101410040d207502100340024220606481c610703080e50b001850038031555a002c017845410072403640c0307407074024109903981003240f0045552960040502003070000921000e900720028040c01d1402c440b0295869082c600c03440711402007a01d009504209400070584110100903204a8069641c01e680c01a0b101400007907001c3e11085580600c5580804000b599401c400300c40209030f1740d12407503a141d5062401900301403c2500c1c449429117040300c1042a50703515000e056124501710f1070840b07596010b92500801c0c0c0100e00b440c01042c45404204080260050010484610540800311491302d0001c01101d541ea43e000e0001d400c100824208825940d5030b802008100c2e1140e6804185151101641d01208001c0745050740002c0d01541e0707100c10b22220347c0c00c0903040b414180003545480d2099000c0341c0d0182454814408108003509034051192181003034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 69207250 1250 69206000 69206017
    0x3030909070519050a030e1c080a021c0b040b06040312050904020d0c02100e010902010e0906030703020d030f031409031204031101020d0603110a0e0103080313080304050a0501110f070b0903 83
    0x1c0100803d070402c0040071030b040422030034046850910468400400012000f04140d0b45040d0401451410b00b403c80d02000d002d08050b000e15024030890740c04070328544845500c00151800003401c0081070f410401900c0b00000c10358001e00f0100300510100d01007070b2802c42c586886003405665000d040000c40c0c024440c52604030381d210716000c6000310880d4003141003104155040014048420071480e80c43c201c0b8802c9a009010600030b49406c002400d1020aa40d4094001815244610744d03c0e00854025034561100b14000780314208069049034052041c2d0a4100c0841d400d441c0b81c1c40c003040c0c0c1070707aa03204076030400e0920700310f0100182c00c0621070200d441250680740000d545030748013aa0080302030400c0d40000c1305c110142500c1d0300890700b80341d00070703d044070a428030030b1000e0f902c8c580302c65500d0307800646409524460320b8086c4021658400c01140914403c20081c41c03040d00c00e003451421542c8075400c0c0c2480c0041003220741c9507025020240c0c1c4059410003440070142d102c00c1c50039403642c841c2c440c0c3d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 69208500 1250 69207250 69207277
    0xe030a03021828050406060f031d06010e0106080112080301030209130c0f03051002032a07060c0504170a1101200a0302030c070603050103051902010c14060105040614030309090705 79
    0x42c400c010300540712016111000c01c071864403c4544440c00c010a881490040100041407540c500fa100b0348281c000d05221200246544545111b2010f0141006400d0f00b00c944214002c43c0100086076101035040e0040940340076a0b5602031107940e552040d44010311001e44583d40c80800305850824040a0810480d845920401940e40c0c9019103e83c40000303100540300d6015268800d21020840d000304c91003503032044150340842c80200a8607c1800d803d014029040c1024800800010894802c1800c0e03a0716680f2410340301c0745410030455039604101880011600445181000200c0c802200940a0400d08160007c0801005c40d02a10700c5040100c03513062243c40040424590048014031449402c6800d55039080c0e10b4410540c143d030020b120003003150b40400c1d6042282e41804500101c04e901c1407600b0302d040c3e0b0840d01c40031a0f00117503a0811000790407a1004001c0c61505100c3d0b100108003810090b100c00c1700e0f803000a80c41303025040607503028608940010344254414001c03102c5100c006003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 69209750 1250 69208500 69208519
    0x60f0a0801050a0c02030309061b0d0f06090f0e0d0e03030906041202040e0f0a1511030403030c020f150c0d0605060d06090606050c030d0c02030d0f050411040e030a030218 75
    0x84a5001e014250f0b0b1000c1043d1820074801c0b1500d01c0482101e2007000120300802060300c5004115510f80f515118550740c5940c107020040c0d800400340a10b40251824420204401e424007403100212860301d04c4c4a0051032a00450a92010b07001c00d892054820784d00b04103100c8110300c1d010905600c5800a0141e0004000a0101e2841420302c10712600300d000359010880400d4109525039500009101200c140c1e0200c1501030004c1c56111030100020403403480881c4071900589503071443d030006d40b41100820780307030522651a1981003040c05a076a144c0c8008016640310703015400c6027101c0c06030400744000710004098000000315005440141f902414843d607030103038201008020b00280c011003081900788140050b04078890010303105090127200c06145400304603002c0000410b02141c1d20000e6000c14019403040b44050303c150b109004556101088a19140c83c003041740790509030800e80701d01e00d006141050180300005030f4a051003d410300580c4c90a104500d00c64000c040c0301990b900200340d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 69211000 1250 69209750 69209759
    0x71e020406050312070c0b0403020310020a020102070b13030f03020301050609010c06090519061104050609120a05100f11040819050c09180607031116081902070e100e01090203060f0a 80
    0xd00050001a00481e000405961a4001f5072a0b078807442c4070281d899884440e1030000303845c0c964014405100180001403400c1c80999680004000445070b040b00b802e6024030300780515800c0a40102e019002c6e1504615560400b03002601901030b0014a9042046414000c02000006c1c2e10140f030b5a500401210456000c84410380780c0c0c40354501d0111045030501d8400404403050005840c15070344018001801c00130314000b0300c49075106603c0d01c00d03050300c80c5502c01c5001c01d009100e002c9502c00740b140e010440c0e0303000550507400d0790b9000080009445007000100800d040210b549000c028140a00340d00d0081e0a041103458201582d050517808502d00d018010900804521541d802c503040381500c1050b80c6001040e801c0b201140154001500104402c0e1030402c00e801c2170510f0503103d08000343c01c1104180e004007450b08000301c200c015270302020090210110040084d94881c95245a0300665410090854046d034010700c2a400d445402102042460f500d1440360503503a140500005032440e81c0303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 69212250 1250 69211000 69211033
    0x3070c090209031203101701090605090c01020c010c1104050916060c0210020109030905060307030204030f05102403030302030c07080a0305060406060e1c030c0c03060e070b071e0204060503 83
    0x90750b01c4900c04e110b0102c0355091841ca04095901ca80350f0a121828076603c1c0040c2c00100b2151100341c91215540c440044c07000521074854503008000080081c8401b141840002e450305080000003410f01400802960000c0d0490780a03045601d41034501180680700c20307030014580400190703a541c180a04c8203010946a60000c034000c0054021110022240d945003030076805c9426203800039000800b1440c083c0414249000216000b1b0700c02c0c41e00501e40b541e2500c544170485039518040300c05401c1103496116a121a0003510001609000698000c510803190940c24804a03c00142415000320010700c6080d4140143c1e078100d90083d1405540d210030300301c01002031104a4542e0700c903610701200460041e2282c47d040e00202400303494070300c0c00c21a00d04c4c0e0100c000305624086081100012102b8000740606404600552107100003103040d1984117125801d246040d0002c52101e1b60501098012950107481d40b90640c0321510000002ca6680c00818054403994000036094414820007440d860071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 69213500 1250 69212250 69212257
    0x3021201060c0203060a06050d170f04030b1005040203060d03030c03060b03040b0f0106030b0105120a02040b0f070308070519111204080c010305010b040317130302030109030e0102010f09170c03070c0902 89
    0x8204d041d0342c940e513075030070080301141c22900410360420381d0f440c80c0c500044c5400702c12a49015044400324240600016617050941c0540c1085071040d10b100c040c00040c44803444000e001c2c102c1110158190700d813401c04100da220f088100501019281c1e07584080442c0603a2050004e481c507005450740da8603041c10481e44503101a074070030500342c0070800001030a034424400e0100c6000c05a60741841c19100404500c400d5a01500d854040d9a0800000a41ca00032000500004c4550744e091511116141400307440040e004000205110341000503880010401c9650910780c03140d030a00400c02481d0040b81031800c5a11000034604810004002c06c0740c0c0800a0250801e907001d0342c06010300e0781c8034414149280500d100052100c01004d0380c9840541c0c6880251800b030840c0c4043c89419540d039000242920000001135002ca42c07003008540d00f0303507420301810030446a104011301c00c002e4550340f110411580400d03031050b00380000c00c0b5100e00c1e2000b0300c116072419400030140c1c442c198490031014000d51 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 69214750 1250 69213500 69213503
    0x515100b03150117010302031906020c0a030903140c0906120a0212030d23070f0c0f0b0a0f090c060324080610060212040504050711010e061005030a2103021201060c 72
    0x480100000302800c020384d980310306a82c1d02601619000e00ca1a01c82c025074281c0350340807a5004d80038040300100e00c000700079160800e400b0b0380d00c09407101c0c61402c02c1011348a200c00380301c0c030035000240004030075162040001c0d007010013525103c01e46800c2c0e03042c15042240a040081d80000d5503080100c0d03152001000e08440140ea51080090010350380000c43c85602c28000074080e21440000180c40c1030007152404c0c140701080c2022403c1c01000e0385c07071802c9815546400c446041299042c8440041d81e07200d08510643c040d0005c11115010b500ca0441c00500c41c4240b40415031900441c641d640022003440071241100d065507640252130b000e0769a12174604a540340e44824a031000020190b20004000c0034070890005201c0c17506042c0300510000c0d1134001e141006000c400c00f82140a45400d2161222403040755010f4100e42c149240c41050b40d4001d03a20440c0f2079800300d50320b4000301c0d03102c3c0b141c1a50310028048984031000550b03003d40c040e004109810740d69120a07800041d04a40008101d044c0c0c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 69216000 1250 69214750 69214757
    0x20f0618102105090c0904290c120411060d0209030606030a0b01150c30020c03030f09040902040c020f0c0105040e060907090f260a0515100b031501 65
    0x90740c0309042180e0200341c80740c2200040300e66001c00c606100103075000c0c981003821001a54180b950040108045502c1a0707401c882d01a840d400c0c191043d4031a050703540f1070003a2100301150302d05140d200d00105001c6e0404401d150031016000c43c0c01c11440c0d1010b003101c840b010f00115118009a04200e0081d000100424081e0045400003942841d0202d81401c10039032044264041e030b400e08000300007003031111000b501031140c000402004922444028020034100aa0025030b4814018030090244c8000c4484010b5501c100d91126090344e020003501c03504483e00c042140c4480e1071400240151100e09400303901f081c07030509806501d6502241500c110401413045a06010340d40004451302d1195200320111203407180040707103081c81d003480c0c0d86421100d14a041c00b4003944404090b883e40407260701080c859600c0b01042c4401c01d0340f40203880030a40000e030242c01050910348915445035101074690b1a114500340016801c10a03414188010b03180c40b0324116101e140001c2064a03460187c25040e010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 69217250 1250 69216000 69216019
    0xe0c070c0801090b19021c02091e15090a0518060901060804050307150b03010f0e12040b0a050c07150305040605220605071205090706170114010c020f0618 68
    0x4801c14003a42c4a069071090100501c1d5031424004190700c002c0106102c038031502040a003408070441d45000c0c031b50f40c60003800180d440c1c90850401c45001c517007620b071950398800c945c035a80e06030741d644c402020a4200d00c004141d80b41c21901c0060404142ca4003e40d6000101401c0074031404c49400300184a40c40030348810703000d0390b00c400b0150742000049400606507441000000b000651b080481900d8410780030020850220002c0000c3c2599040c1c1c000e14606a40d403170fa07a000d0440b04012690b03503854851012450300c2d040c66210103462040804190511400084003c0042e40c00c02500c0c00401500005c8030154080101c0100980401e9070705480040c2802c0110342141c100a080d40a044000001440f484426941e088040c290092449040c4194020007940325000c42c001c081c07042251074081c01c0c102e4180b420241441c1d85100e040e0076400820001030010b03003210914951400c0c42424480d030320500da807000448941d1150f40c025080000801c0c0d004141c1090403410858000031078a03040b9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 69218500 1250 69217250 69217259
    0x80c0f060408160303061706060a06050a08040b040c030807030203091009060e13020d060f0302030d03090314090312040905070e030102130501050f040902042301020703030f080702070e0c070c 84
    0x559100544000d0081002001a042191030f940c0110920b00c1c032906000c21610384c0d42c480c09001103d600b07d543c81d02e42008041100600d080d041c07040140550b030800b20700b01040c2403c001d002500041005160305c0e80d03180490107001065006070300550740408596642c44081c079009450ba00040e40300c6000b078601030100300c00c00d030103060340c0e100751002940c0700070442400c0801c1104802060040b2401250708200e03d645003862401010050000c3c184007140c07552540c81454a00030000c00c0d802c003050300d803035080800a94010100040134410b40100e03911031180740c0029003801c4003450080100d040010300003540300710346d030480752003402c507a25840c18074903441060500b81e124111050003541d5803d08140400e40c054405002e02450302d0724010b0078907403190300905c201e0b40103810000c687e03205100501c400c0d8401c01446d0071100c4c0700b840500344103861945c0c0a4400c9808240c4070051241890008401c9803080144070010001c0041202c601d041401402740c003940a081d090f101045441c00100303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 69219750 1250 69218500 69218503
    0xe03072003030306060d020d090c06090602060f09030906210a0c08090f101a060406080103151b050307020139020c03070302010f020a0623130f02011803020607080c0f 73
    0x84c8149000380c851450a040303004800000d44c0f0091182d00c046030b803848040d0200c4c124440305400b501d445d80721900854102070b400b1f480c5c0726004181e08110b101800030062010004000c0d103002070400c3d210359403294640c200c100c1e500011030b50786404079500b03c0c04002d0790031800c2c0c00040088180382c40d1080795443c1c81c5400c64032455241c19108460707001e80e59211220980d6880b60240300c00440c0d514842c813015000090760303981f0a52000c000240c0d4000103205000c0354400c00c20700c600b8030003003c200c00400002060650b20b40d4400850520402000040f8036900030f410040b1800580004211182d501080400e44105500801ca540c84c4580300c0060031940000381c0c190288000400503c0740310310310b41c0115240d01c14444d400702107015000c441800030324240124040c2c48100d01c5410780e40011115840c0001000500c021000c0c1c031003d9584011903651981c01070225020319144034115044045002c03440c1032a40004e41003840091000240491000901222000c04c0c054618050354a00d80c3e0703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 69221000 1250 69219750 69219757
    0xb09030304050616090803030903040e07020312040b18010203100806060102150c0f040f0608041203050c03040308101214070f05100305091504060e061609030b09010e0307200303 78
    0x824561041000c01c070344034004450300c100041146004040c0545640d20306c0d0450300280c43c107035140e90021506120300324449501e0341c2e00c00b100348000c40c1402107040c182070030200060009003800e000c0c003022802038680c030310483c0c40403a4400001d66030303401c0074606800d45802d24407070701c0340f24040d00e004915250710100700040010a40d018060250f05e40320313001078042d030000310318174100c507400c00001404903c1c88007000d0041c0200d803134495052415051061042c07081600e004100b42c42c101c100110000210140c0b500a9094a05003c03540d452990307580300c0798240c2d0806031040c08510088410064035000c5901f00702032048c150f0341815526030150491450314000c03142c2c42600341c84103980c6070f44282d01659002e14110100c03180c01511011b18991100103079419100da9483e8840c06440050401c0348941100c1810300604130f0380e004240061058409001c001c0120181c80b0214050b03903401d40144200c00440380950760381d00041d16180c25400864000d0960003c1c0005125640d40f03008401d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 69222250 1250 69221000 69221003
    0x90d03050c12180f0409020d0c061206150c0302070e011518030203030717090d030f0201150509010603020a0504091a031204060c0b0402031609020307030b060309030702060a050409020f04030b09030304 88
    0x80c0d042504400081000c2400b111316210b400c42c2d5a0701001000d44e41d0b000c140f016240c0030720780e001c403410b09188000381140c00300d80c651040e441c1401801c001200e06039202c411112a80c0c03078480b052817030a02e8224100159548055401103000c000802c01c009160b001c0c02904910b619220a8000399410070b031a6a2034034440690700d0307001800100d001c5040500e0000d0648005101d0703a00d80f01100c1d00140310305510040035000580100100c0c040d0540911032100306c00c01040101c007105207004001007209105008a200305500851050100781c050020b030b0b80030380075104081c058140c0d03000e2140c0b60f4040e2071550350320074440c0000d80f110246e1107404075025200079586070803030820301d0745072552182ca020740100d0b054464540910006008241c49101800d001d140160360f0342010705009058481610381c03503218a070100180034800c5000000c4422140e410344d440da07200d0b816400c050314240032716409055124000103485484c410080014800c1d640300384003240f441e403076491103540d8a0104450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 69223500 1250 69222250 69222277
    0x10c0c0c0501050f1e040504140f04170423011701060e01350f060406120611040b0304050a170405180603030c0a0501021801080702100203060303090d03050c12 70
    0x102800075500c900024460141c4031030000e890900804526030007544070740745143c1c3c400c80226041c04a882e0a006030441c000000c0c620000f41d0800440408800801070402442c030040300003501c100c880079109440041100300c09200c00702c85412400c03419003001d000310a00144551182003a202089400141038030680d41c2c0710000480c0200c010340708403000f4407502c2201080310030b2440d00c00943c0b0b0b4150500841010403942e603402d00b81c1c1642810300d40a0310840c840e40c107100042c05032903d1074070a64134140e0001d10114007910160410340721481290000d00280c100041004180716000a2003204617100724003d103503d00902c1d20b02602402030307001d075980c8440054000b0150200c0080220b40201008054a1074000c2c2c488155140960340031084840740d4012031002c05051100c4041d43c800c460030300341134500380b500250007511550003818074051030b5808804910300c0c0c0c400304151091200f0142c00e0b143c405280341405891508001307907825161044041030b0340c012400c103040c0d036202c002540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 69224750 1250 69223500 69223523
    0xa120b07030e03040e0c1e0418111b0303040b0703020316050a02010b030106091e0203060d0f0f0b01030606170a2301090209040c0f0801050613050408090a03050609010c0c 75
    0x400480203810b50380d070080b19620007400081064080381e10700d0f90003100c100944507900c160307991f00b0f51840340d0710304800c840c000b000380802c0052040d01e81c160b01280c04143e074009030001288041c50030902401c101030700c004614a503501c00343d20002008500540c092100994071384d4484404030182c1c44122100070b144003200c5030360b0100c28001d10103002040414000480c5240112002c01d007154001c0c0c0c8589107643d207a00709070f201816246c55034989405585001d52841c507180000c1a00d101050800a2800c20911134070380c18004410303d12a10280e1103e406c01c3d1030b5035070341082400f0b0440740c002c0b04800c501d035440c614500f00d000900e0710f034900d0f40b0807a40d0742d0a44e074840b40c0c5a28005401c800708555500c454001006030754160740e05104a20810481c4c0da900d0629520800340301c025008400c950385090184580c66980c2660203064040c42c2c50080b88a96803440c0c035028070b0246039140780d040903101c42d0110030041e01094151050403958000c12801815050407524040c01d010b000d465820841c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 69226000 1250 69224750 69224761
    0x102100c0912030507050f030d0b04060803030c0f0c07060e010908010903020607050c010f020d0e010b010504030b0f040816050c0f0f130e0304080a050303160c081215060705010b0a120b 81
    0x10744420103a0b5000703042c4103040400e00d44a0300d04003607164603001c0320360704009112500002180300e0780c43e810300142c0d8100191424001625a2444042c100521240c4041104a21043e03010700b210078040b8440151101c4d60380d900b4001d0541c44d0045690b40c089030650002040580c0148039003030b40070750160b004008540747c4480513100c80e406010320014954a6000d0207465400c280018010230f451250300254511100c1481400c40300030b06000d604011007044204003040411081e690408151504031030181c40350b10703240240348035075400300090802030104201031000206120003400c03802d44d91801d40c0801401000005003100b000075500c485030860602244665a01c00b000550b9114200c1e85420f8844030070034508840c10804980c1030340000100503081c0c0b00012211201c00340703810211860b01041d80c030310019001e69080080b1314070b03c03400010303100c20045400401da800003400701c5644030f9071030600601a1648045140c05140e01210000c0c00b00084481400d141d5040200d10141c1d071501b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 69227250 1250 69226000 69226019
    0x74110030b030106050a08070f080609060117150a050405070503061308161b03060b01020610060305070c02040f0e06090c01052502041506030e010b03071503060e040602090102100c09 80
    0x1c0e15420780566864401003142c0e190643c0d0708001c1c040c034400800c45180740403003280003030304e00d600000841c1d04004103210701f5000c0080c5550640d01e05010b06c0c10803129007602149005604044031700030f11340b040107000e040041030748124050b0380500262038010761a50700745035544c001039564800e541048001d050100e40a5400384c00d0490b10106940854590381c3c03192641e903a21203400c00c2e9100400c010030010031400307105050711404280040e01c103a01c1d11000e140d80140c0c0310f203d20420302d41c032100011031140c420821b9800f00c42d03004104103c10004020f014004160044400c00548510f1006c200c0c980c0e0006580904014165200c52424103500100c08550325194840721081120041c80c2005a4890040b00c40610b030013903600c0381d07076842c1520080949466803206100350345002141c0c407441d14042010000d881340d0a40940007511170690440c0100031a511010802e1440002d00003048065002044958001d900711001c3c070301c001740d11004071595045400085a80040100301c130310305 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 69228500 1250 69227250 69227261
    0x2030d0c060b04060905100f0e180312100f12020d02040b1201110703090b1c110919031b0b031b190822050705040203060307411003 58
    0x10584002c2624008840032500742c46140d040030a0440c0c5640401c00b1740c2c10880140c0004104040d151505140780402580e81a940038200320f01c18103559100c40c81054042044810445002100b1140c6190030328250056626a0190001c010713164840001c41d60701c0820a5009190002c1462440039859401c020040c81c09000f42604581d03242040c403100310080c800c03401c0b880014022240c5d00c221501e401092050070f6002401c10100034000d8101c280c1039688200b141201d0305c540003075800c890600030603141c007036492070903030291210900e00b00741c000c03c000c1041183c0c820011940942000c00c03030300c01042001d0199040d4281c084c00080c10000500352802990300c56984994a04856007204171980050501024081038000c01031018010400c2400344030120303101080d0810700340320f41d111625040d00b445a188210b4000c004105141e400380b2148004001c0042850980a5a0004881b00d801c000589443c0c280140c140d00c034250950303042000550340f00408904441059803c00d400421 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 69229750 1250 69228500 69228503
    0x40602061504060b040303051804061508070905061b0c09040f1b05060d02090109090c0e0f0f0301060e0a051f0504091401020a200a0201080708070c2001020d020a02030d0c 75
    0x81e101c803400240808070000400140d4000c8c0d0714250f0301c0b24401501120310030301c0c210480c0114907016041090f94884034424440c0340a41c9042406604c1c0e100084422104a80049a005800103200c0502031481d00d00720385075000240075900b444400008110041d00212405820f13203540908602c0003600d41c3c020f8030480e4401010340d450140d1aa0b0108074117030084005907600541c00140c4510710740c1c2001d403100042190780805d010080800744010035000090054500035241c00e554001d1560b9041900703022044040d00800c031069079110038030110034040e91405c403440d18000204040001e01e42015824102c88014905c1e070781e190006010044c42c0c0a0410381e031501402400d114009428001052680d455507588114000071070580c13040c00d02d0040b400071590303110060000050743c019188a038052250308010b005965606d83c1619540300c80080100001d1602c04450b8030341c1d801203e4510300e58001c1e0f00f1519040c1811030f05a23074808015801a50652120303600340035040c461803884e200f95 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 69231000 1250 69229750 69229759
    0xd0203040b0a1209032a020105040512030409020d0c141201030b28051e060f010311130602010c0f03021e0903070306090b040204151d040c15020a02010f050406020615 73
    0x8000c0c40c11143c0840f104100c00720300051045079000810b80540d452540780c4050111101e0490a032030380042e1581c4228840e1314002e5a41e086030103a800001d100380c5004101d401e0041d50f803038000e0f410082c000c091800000d80411607001030101c20031019015101c00803940007000d40709900f50788905022400050890104076201a14010f00c180c5501e190b41080b0505500842c2605040c1c440800d6000d0302100340ba6030304070b130704208541581d03500f0403021b00c6507080c00c0009510410300c00c1a540c074030a161004908804902c8000b419540c154005034401b0610350f0359038a48503500f68200e0580c440d0001844009200f814803640b040b00b00c0009040740c0740010700f161030495803607039404155000c654050394810003c0f02004250f09040c0502400f0b00000e25070300548a04181514a41c3e00a0440c0480c039889030b080000c0c2000f2407800410b0160908442c0442ea121a540c4001c0d030f103500c440c0c000ca000035140006401031a005406480c00d41d48030b40c0180c40e66a54150458880015440807103900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 69232250 1250 69231000 69231017
    0x340b0a050a202208030705061005030c031e0316050a02010e01080601120b190e010e01080c0603010e041109040602090f09150105031b0c0f01150e0a0f060302120a03020606030d0203040b0a 82
    0x81c51300410050031030702e1180018002034601510790721110400ca5205501a030000c030750b2131103565800718050301440515151071041e10481c8041e14614058900c2d00860604500e50b240b090160004030000454400d0ba01c011521400400460f2000382c1030300e41501060040300c40d030304030301c009400c400d0f0344010103031a0004181c2c07041e440804104850348051036044100c0014808030b00b5501945000d0814940140210b072954002301d002c6100522800a203105c05401041c01c008092038214801c4000804944403800e0508000000354030940d243d9110740c404158a40090a15600092240001211544140044000640f2207600c01098000c20051080760030552040702c4d00a090a01c2483c0000d00d1032009400030303103003101c803000449005184517003000c001d0305400800301c60740f08200f070b80081351100040e40407002510040e040254800c0c0c103100d00200d08080058000c48031360081d030884000f074540301d0901d07442d2840c6104070300058004000a03c0315009900c002e11076010340e40b81400b00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 69233500 1250 69232250 69232259
    0xc1a090a060c0309050609070b0f1c060e0f0f0c090d0203010f061e170c1e0405010602010c1206030203030906031008071404060b340b0a050a2022 64
    0x1125410b60041010a544541c4541401010130041e40d200f00080024038601e030a00040602030300801201c0d201c85000091503a590480d041c00d010100000c0c0c02e0280010f640302c00314050008022610020a00f40d18800121490000f410700b038000c0c003020740d88a10300318a40d02400f501d0480744400307030380542d01d82d04441d1030745d4000d108a01c020180141c4540b50390302807250041003030019074171030001000e0a0503840307402c4074080f40454400d00200c2e2980400005215015400c6d03600a5003039074407500d08000083c00ea90190030481501c0e4940d950303003c2c2d182c100f51041c81110618040690194000d001181070350070108000d5400c9501000881500395480c2243c92030a00c0640110321804c0c1c49141c15800350410340612000780a0402005081800120500c01550f00c5010081610b210703500c0b40b040050440440084015003110b20152285030400254000c2c1c54241c42e0010918070304131424401e002c801c9000c4240700307190a41513181042101000c4590402c0f0700f112950032940e40360005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 69234750 1250 69233500 69233513
    0x61505190501030e0a03050a033b07170c0f0f0d080a021203060d030c03030e0f010203011a09100503220f05010c0206070203160503040f0605190c1a090a 67
    0x25014054901010100e400c00d8001030a8404140e01041d03241d01240510001a802406603540d100b8031b0329001501413400c00c03000c0f00004450000100601c0052460b5519010a9204454a440c10401c6480556461030403070000310070203500c07855a4102401c08600f034076100480d0700c0140c40052070380301144104400601d00c010072040803505c442d800103481d00595014000180d0604125100c0360851600c0008a203d02041d00401010044020b6001d01010300940c010421110743c14111243c400f4840465070007540280288842c400a4079100210340440b2011903001101c050300c130001200b20030f4002d581c04c0d0006850440490990718a8640e8040030b52100c1401c18000d0520144010580c2402821210500b1400007190040b40821280c190000100c1d010b041140d4000d032400304c4c0300e090007407c3d0302407a04066409041038000140443e804405019400c80b41c800c000c440c8418004203450700d0b890300790014001c540e031030b82e0050320101c2d40780b0f141d6201502d4070581e81000d42c181d079420b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 69236000 1250 69234750 69234769
    0xd06180804060507120e060a0c0f050304080a0c050a03030e0d030512241503060d050f0d09080f011b030c030b042a080103081801020703050307050a060c0503070903061505 75
    0x140000f0b41c000c1030400a0001e44441c07044c88109605000d040f05000784d02081d030340d124600380705040c0100c0c50054030410a0802801c0851038110094070f44890301c587d0750b652a08440681951311019001021403607141c03040d078403000c6070341c5600c42c4440c0b02000814402d10b00b89500040d1f0601c03506108a003884589a080c0340d120308000c1c1c001401c91120150394402d8503500e079600d1b5001c0c2da00e020603060105243c0c4101c07a0841d02c00ca81410071460f05160280c030707013070200300704056500680c1242c1e4001c40c1c10100b54015181300b2400c0c2c54260f01c150410034225061a60010106086805000031450190780251120005882d0214048001070046001d640c07013004078944018540b03a14400c491902840540c5810003458104090751468450792900d0046071400700e0750905283c1600300c16802040303040c00441d4044d0550340c551140c1c0c140280c803004000c0c8186e13640d504145120440038418001c49211300e0305610b589040605540f20302d801042480c1000d44c22107000032000c1400e50324207844 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 69237250 1250 69236000 69236009
    0x10203070b010e0703050901020c0a02011404050d060b010813030804080a050c1606020f0a050a06020306030f060a020910030c020d0305040303060f091b02010b1c020d060e03030708090601050d06180804 88
    0x40c03041d83e08004c100141140c1000f80f01c1611640b041c40030b00010407012404034034254091a0503918081c2e951540e508a100319070100d94400d01c090440410401c0c01c1c0c01c0005100000d03242d070740380c03982d0307495102180c0051568000c0016540c00d0010740065611400303040144400d00e801c80c02d10f1450802e80f45406a154021a4111442c050410101d0f604009040c02c04107110040c2024078950340d1415924071424000902840d00800050000d4404209584901d5071310801c840d118105416610001d41c055643d007405240720002c6d04581d40d000b030060f8200b00010380d008081004803507004800420010348100e00b0151201c000044020212508001074060128000f6207050500d210100030b500301903440382035905141e9040c03510380c3d9090307071007491100540c0280440c40d09480004c4143c9401c60000f0060703850004032140402c4004050740c460101c80d112507440c0d45072825010f640301000d114141d404003010107a140017035090b4000c03404400c075403108040361100315503a5001540080d000b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 69238500 1250 69237250 69237269
    0x4080a0305030a4206020d030b04090c030308010f14090c070c050415050112050705070206070302070b03041110090305120d090c090c080114150c0c150a02010b0103050907090b010203070b01 83
    0x62103104201480c68140190342c1210313440c1d0351032070084065100d0005102c4c80042c155a95501645901e89402503401592304c20ba45401d0304d51a854043e0a000003805481503449881e4408a83c10900b04810040443c004000c1507603540c4810403000160300264007180c0e4134002003000116500c0d40d001c0c204c418140c01c015860b0300e600b4a000105901c800e506641d45c801d0820082c090313516040011200d807960141e51041d91001c0c1814164907100c07a90317008181d40c000000c100010301040408001c46a001142d2201f0004c040d50f004898042c503c2c0005810b40d00241c00300d1080c00000b074005c2107160140c00000c41c03406815103a52894100b04e038000244644c8982c2200019075100701414090421200c41c1c5450842481c0401c05d44100307140341c150222800900c100c0e003014200000c0c074071800000c280f10f00d21564140140c4413500407103207030b202540c00c2c280041100c1d800781c06403500c101072650041405a1400b56100b011b403003184402410360000f0000480464103682d5034a0103007201c01c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 69239750 1250 69238500 69238571
    0x50907030e010c0e100302030609061c1203020a2c04050a0e0613050601150212130905090d08090316022e020102251211030918091204080a0305030a 65
    0x10f1228120a402039001054410809c2000d150368141e034054209800751007000341020150425100254243c4000d0301c00d4142101505046526030000c001e0884980e584074804120700b8009051000d1030010f204c1c5230484140015501d003030541c062503002c12003c0c0080354118440e02c0590400c101502c00c021145091805401885000c00900e40100308801c4141d0510400f0b07400251109201c5503850030483c400150409460f03040c01003500a800c00030410441403d28160b1503558003448011700c1c021807112030002e015000c2c0401520f02c8146400007825280314152b0810480b14800d010502c04e0b809003184100d084600070440002509841e00010394998428410720500585040d424410f0084c0c2c1100c140060b601e034010323030104a814200108901c00100045041d030007600f151035080001c9071148181140008511400f0b01205401d603000e0480107030801d85144070718001c1c0005941b0102c00b840000f441030340103551010140d180000e61020303203040014035240d9030840081544858 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 69241000 1250 69239750 69239777
    0x504030b060904030210021c06121703090a080904020d06030c080c0d08090108070215130b011202010e0904030c1707050d0e0f010c0507080313150207050102030301050907030e010c 79
    0x10348503400c403404865854240ca0680c2e8001d6071452030321095034101d03030045085801c2c2ca07880c0c1e204100003001810140482c41d1180044480702e00c4140d002c2e40c04081d43ca455003d103002c1d03441228020303580c41c3d0140c00c4801c181e4403138000c203621001000350007a50130864a0039401d0b80d446020b025610451896001500d04034a45240000152049204041c4e00300e94800282d580390889403512030a003000c580907039036013005070300300414841030300b541203801c0c4108095000744002085142d441108108001e98039800c3c2980c104880309030007408210f42a03072a4541c1e203001001c10f9485032003468008407948040e81c6c0c00d144640d07081038544146401041a10030000d0502a02120300710320b18007240c0c4625918001044c0c1c034030784040e55050120000c03c0a0070300c181444030102401c010f0085968078540344000c001c041000348104107245184c1d00d03010202c0342c0f01003000700464805030700035800d503401c1c44108240407601400040905940d10400c0c0030124083c019912120065180e001e418442c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 69242250 1250 69241000 69241013
    0x50d050403150b03030307030b0f09070f0f08100b070813030c060905030d09050f01050405060708090906060a27080d03060602060105191a0c0609061504020708030a090213020a050403 80
    0x1c001c0c0c0c0700307000f400c11051801c213840000960307600004038500490350441006c007088520062143c1c9a801c588940c081000d40c40d0025103801d0b40c1d00d03980ea00c219170510f05050071101c981080d0b0300d0303081c0d0003060141000700501e040060084075000f100b40300c0c54003c980454040180c1107502c120f400c288900c0c402c000a03038000c40c1321002010306070081c0844000100008003018810f0107901d106d103030f42130746142840e44200d042e0740142002401e150b0343d5031f01d02d04220360290406100c480c82043c1c0386e00000c0e198201030003550700d5075020351912540001d084d48100071909a0901a2000411b5044002078201c01002900140003440d180041c0c0035003800c10080c00c008050700000e0052010342c080d80415046502410b040b555801c42441c0130f0350038840c2e110814490f170302c0d0b01413a078400c01c01030000104002c50300500490080840007000b40c0c409007404180d0090a030080d003800000c1c070010314599465003102c003515200504501c0e641c0140e501c24800c03a003102210304002140401d0034020450b1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 69243500 1250 69242250 69242273
    0x102060c0909060d030e040f0207050705030c010c0627080c10061a0705032a07060201050601051206010216080d1115070c03090306020a17060108090d0f0903050d050403 74
    0x220110241c0c9800d040e60302142500001412040c01481c142c000d1005062249681440001c40100144070f61001d08031450007940040c83c0c2640c0600814000091034900015028031020061311602404c0c00a926040010400c401022600d9203040b0350060481000c1c0e00011640c42c4600c00721500c42c4110101c01d03140150840034604100c0c54072005100010021450100c01a030902109544400c2850301d01d00714000c0c400340040000c070403401c1c05142c01c25240c00000303002000044400055540300124242c0700240d07070075404281d04000c20764100075036456903a8860010f0040381c90700004100010701e01921035000d0801e540200c0c2c0303610340c400d9101e40b4030031280c006400240804203a400d1000f10f4900017414990a002ca00f40201c2d0425000303010384c0000f150440e20442d1140c1112502512600d83c0102d255118514000003524030b41c080c1c000c8901640c842401030004245450040d03c00508061004080c001001000000178000300000c0c00203039a40d03aa040e440f1407462400400500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 69244606 1106 69243500 69243511
    0x50f07110a141201020f04150e03060906090c0d02090106030203092103010f2103110a0804090e070e0c090d03050f130e060402040e0a02071b03030e010206 68
    0x80e0a40c07026515002a190000c0f200340081c1028200d119242d01d4020080c010b000c2445038201440d0310300794503065820000006500000080d00e0003034111080790b1a81e00000400c0320b80e1509010104440d80240c44484104500c2d50025480b008140100001c0560201c00151001810003000d4690a4011201c400081c0740c55460a220f034000d002e01000d520455a000481d010a1450144c400680480c0882c04c4c1416a0f021141c2c0e4040000d03221551240240340740100d0070701c00080001b04080480000c2c40c03010200c02506014070b5a01c254a0b110a00d41005400101401203a485040c120380d480c060305804d00c0e0640355401040c2210401030800b040c02032072008003920213400e46d068807070404074070340d1000d0801007603202d1030044001c0c0e100317001c01244c40440325401a0502174418440410549003802c611083c002141d4400e40020342c440c1e1071050207503010f004498000 = true := by decide +kernel

theorem cover : BRFrame.Cov 69064750 69244606 := by
  have h0 := BRFrame.cov_init 69064750
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69064750 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 69064750 ≤ n) (h2 : n < 69244606) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
