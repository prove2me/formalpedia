-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5406
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:46:11.981913+00:00
-- url     : https://prove2.me/submissions/8aa406bb-9ca7-4b91-83b2-6884b7ae432f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 972122302 ≤ n < 972302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 972123552 1250 972122302 972122309
    0x110912070e1b03011802160b0a0c0e06091003090209070f020c12030a11011d0c12030c060411030109170a02070b031302040e0313030308090606010f0c06020c1f020c011104 75
    0x107420030001003003202c075181c0301244a10b17180c1800500d828544440c2412412104004482613042c8004000c00d03c8002e20031000300007014240742c007001e200403001038140d201d0000410700c5110b503c640140e4181c4a9031090955907400b80010b11031741440356024080074803014001005209140700c0c4400b60400070380400014006d4070041d410042c0f200700036186009140803591442d943d400348484001c0508146440001c001009000440c00784170500200c0a8446261400e0364003c01c15103001142c0051990362054120345041030030940600001d001d00b01d15000a80080e55103a1182c40301c011040081c40c2a00054007100e50043c1e03a50010741030b5000469a0100d40210121104054181a040782c01c041c91120142c1c1c0c5031200c024045072010306581c0055001a843c3c0003000040340d410000c05801500900b015905010302482c01040c845020b0b000801c00e580109648148250400c5225442102178203824080112598003400030b42000c00190f025600f000031803021034040e4001ca4068 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 972124802 1250 972123552 972123601
    0x19051905060a050a1130010f0602120c0304050d080c01140a290d0609060609020910050711010e0d02090c0c1608030d0507050d0903120506010302030609040204110912070e 75
    0x2003a00301c881c06c05003108030000c61000e40c000c407001426254001e45800d0301a045003540c500002d0b007088002460003117192220194005c0400103c01941c800105550840b80200d6100c02528500d160881081c0101000104c9a41c208400e644140b40c1c1c40d00500e01c14283c603001009814421484031943c2c0d0340c0300c070200c5544066640d01341c400e41005060044414001c500c0443e0805640d074500c1c0c1240c0c00b6074840c5034a40c0c0d011407800d0740c51410100701803420600c2d01e1b0650501e403ca4850200304440304000c00c2c14030032180b4448c941c0d0b4403644011182e50340c008003001c175545061080401c065001c0140301002d8000c0101c0c810440c140780b107039032041e46c003000700a604001d4400d122000801014000605000f0706104000001c0340318040c0100b0944250382e448500b880e0a0081d100382d450140030300381818010f0040090540328812002ea01a404030f0700030405a110759410387c05446007108468000102c0b0b0710f0a614480006002c6088030300c00851140540d42c0d6510501d0010740c00c0607107041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 972126052 1250 972124802 972124807
    0x90f050f0109020a0509090906010302011701031208040f06021606051303051c02160503070302060a0c0e10050d0204031b14010f030f112b0501060219051905060a050a11 74
    0xb2000ca58003900d101e81160038858502400840001c500105c202c0350044c0395406140148110750380440000d185a000004092603541142e80d250303200001980302d44100310109001606100340080f15848542d00100110350390b4000d4045010380c800186025201a800c241c04100248124001c901070340b60180e80d200c6c103008800e000800019000a0a092419001d0100c09106075104c070701c404889119100031a900c020a18001e41010b8000300700900d141d14044c40218101e0704000f800c50b100c94121021084c240c02c01e50240c4690041c0c070305240a00740b0100d004820080c00761031003c980e4203142803402e0010360f10b00b11019060503518403d40080d0001040301e2046000703030082c1203400da42c0c0001107081c030034087d000c21154003c030481150500781200300048c0207a0610107640d01d800121401d0080c0d40c1080710295660100c492554812449001b0f61b8007032201c188104161000f81d801155952340c002d08225555003015142c1120540c944004030f07071078141074070900b801401c00c00313040c50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 972127302 1250 972126052 972126059
    0xc090a05030f2a0613410424080f0d0203040e09030c011b110f120705070b030c040501020d2a050c031203100506030105131508010903030204090f050f01 67
    0x243e020100700d034810240211802e146691844c004e04640c1d203004141e048403518060002c544a840e02105802c41c8000301da640040444402e00800d4603052090010340800c0d040000c03030010075041c2d00480f03202d00c40c620715024003010040c1080487c0d2040c412205c031151403558254586509840010151b4004c1000f041500441c480301c940c0041a0f005803401e00034004412070940b0004810025035209030491014425000b2509519041600005206081c0200d000b1030760b03042c00101c007410b40751012407070a0800108000040c0503021030610903450b070400c03101c4032490345c1040c0201405400380000d00140300c3d00ca004941c65001041c1070380254000c95124040500160407010342e080e0003542c02c6484540ca04110085c2d2901d44411003070b9903450101c0b041403000d259a0030007845224104010046903503201d040301108500b007240002c00300c0781d51142c49003268142d07006401d65403c11402c04140b5400d0390241040783d52004e020300074000c020320302d84121402150090702d980009801131 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 972128552 1250 972127302 972127333
    0x20d02160e060102120f030f01140d02090a091704051f0503060d0c030206160204060803040602330f0f0f0c0d0c12020c1b01020309010c030e010e0402030c090a05030f 73
    0x840c1c02c08018016a032420000101d034215540c400d406400700070a001050108503007012254500410502d00000380c103454403400600207440d1014041d100d01c196902052501405030b01218040341d1000c43d41c0900c04200c0025002504188100c1c1d205e40c240da40c0c0d299150b002144827001f23000b501da0344c0f5803940d1307200c50412014076001002951009000303207010005845450091420289044c001d000b1018948100300a454103504240c52070b0b001800100480d540002d00131135514003000b24901c0c50207610040726103a12070700d400c004030484a80c0501060364200c5507054056903641800e81c24942d03a075400021400426214040b09820070081038882440c80d602920300b0a8403482e1183c3c1054055004100f45e802980300d040301c03500305000c41c5601c00d88104903c0c0340304c4000e002440c200307040000080e10840032810090309102d41d840c1210102e80c402c410a006040004104544a080061070302c00c0d285c00c64034055004203040c0401113108d00c2d000400020041c2002e0040128100b00f4070703407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 972129802 1250 972128552 972128579
    0x31b111c0b04150609110d0e010608030a0c0f0b0f0906060f0108010308030426340209130f0311061f060e03120a020a1502070809060703022407020d0216 67
    0x450310200e80d502c0022612640b00c6c0590201900c81c4503805803951138220707405088810100c03009103544e2500c50200407135000070090769140101c1d42040c40c90400c850410010b2000202030050090300d0741e07070400c500c02112608060241801030b003180e125070b03500003d1041516080c125035001c00c04c1d010042001031301c10b200569209216180c1c16004e507a2516025082002d00d025080d0b0114000c680d050303460030345240c4a540d0b00d8006030440c80b0b0318030001e41c1d200f2401c010000a40143d80c600d000400349010001b417a42c507558070a03004e405198103420014400512080c0d003a18a00450b130110b400b075107075100648010031001c14000620f51030010141d80461038901034507054081da182440041030408050185100684c01603d01c0011901c0c00c101c0241c200315140c10744038414001e40c4c01040c5244c2c10760f40100010384185503100700c1420140d28100fa0b030122182e451180b10101b0101e078168050f194050340458003128103240c80d1200903030b11044031080f00c2c18010020700040103009000489d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 972131052 1250 972129802 972129833
    0x170903070b043002010c05040b040302060a02122106010f02060a0e0f03030a150b0a020a0b19051e0603010e0c0f1f0905011e020c0409031b111c0b04 65
    0x30002c0c3c3c0c42c0c5a060011180c80c01d26003140811502da01c1c03100440ea9028042c00e00c4c46140c41c41e04038030b030604002c03031180b0b00c2c09140070107400341602060f003210b81ca000b0848030030080c0e0207016081d225120f520008001c81c05483c40041441004404604254014002d41c0244007294019003456581c3c1011080180a1140902003a01c80c20940001c0a0b800f0300c000d5001e00c2c1103660100701c2070420842d054000c6480d5108219003030003000100112580480c1404d08198440c28064040d1034850014040041000c0c400820a2134482801220144d511300d031484880030104410141e0f440d08101800c0300c2c0c1032545080c1d280c2181825140619211504205806004001892913800700f02d0324801203d06142640200350020340900840d030b000003050400b0700200e80c1100c0c4242c1e4406009490700714141c54607000e1910341c660081018080d0420f040c4a241c5c6a0320361214101078140114040503100099004100d01102c05c80d50b40c00550351340b00300c3d42c0c001103220103030b403103da640c4042084441e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 972132302 1250 972131052 972131063
    0x609030308150415060206451513020a090203070c060b04020c0f0f011812110708030a2303060609090408220312030c0801060e0f04150303170903070b04 67
    0x1c4104c28810000c2c20890040c260f541d000385084d1910348281c03a1070320200030f2210011001d840d00c05200c002000f218100081c945e80541074610341e8008958980840e002407007900c00f400b0b1040001c42c3c100400000e000900807111181c420707a0700c0e8030003000c030310040d18644001540c21744074070082810340d04020750141020300014a031140303100d0100e0610b0014049c0e24100d405c5076440e6040b031602401980515041d030741c450050002c1d81da4a225070342034813010700024012215800400e0400c107112990040c158141960f0ba5490159001050030b003c04d001a000058010341c8400810180000e83c0d02c10440540b04914002c01d2008010480310000c0003194034407010000c8040240c0c1e04600c0d5540944510043c40070103003140b820a420302a41da100c0d50406103004526004560710104d86411545a401d285281a103054003088e1552198001c181d0441d04001520201010304c02c3c500049034020b41d124861444800d40e0100300140695800d0b082d80d10520460000c00d44005549400030b1168 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 972133552 1250 972132302 972132311
    0x40c1e030e0f01050711061b0901110a050a0318080a0f0b22061b02010902030d03051e041b0602030a050d0c0c050d0f110c09130303201306090303081504 67
    0x1c282c0c20709595084035100c0024215500d24481c0980400c0029000080001e00ca44210000e81070310b031442c0154030195040101c411555448c8850a00401115a03001019150701c0c0f502130402500c0c0518001e00480c44942425000074003c0e008114204074603400185244202022349445403003200c0a481d901d8200040d400c5004c90344c0f00705000d2404240303c0c100102d600845104004035082c0003038060030070340e410001100b00503078020443d0301c51140c1900740040c007511a01e00a528451110a1420800d107980051005006002c0140c1c0c0d5120f18212074020081e4441500b01e890b40170300300548002c5038051002c3e00b0454419003019441c400300e80741c807098500090b1120362611a404050b1030200c2c004040301d01ca01540856154000104080208174500c805008107004140042c46001e00c03204000f440010984603801c072001d044600581c184400001840040d03ea0b40302e0100344268922070341000507918060014002201d0301074231403007000d42c5c070840c219018400f29180103601c245d89 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 972134802 1250 972133552 972133573
    0x20307050409051606120513030c021203041d04060b0f060304080315060d02130506030112171207090f05090709141906050d06090e070614040e1302040c1e030e 70
    0x3682e18005100c29514801c4010441b008507003158000317404000d0009040c940d840202e07801007030000e811036042d00c40038aa070150f0003040b402c502480c0c00500b041411103071004503030f0843c03031034a9000307600528040110b11320704410002c0001104080d507810017400d1000034042807840025580c00707074030f43e807001003080340c0000041e03800c1d4040d2481e01440d0b640840c841110b01544108580a4030060b2990361455042a6200d41020303000c8400074016101c213050759030310203201021f46040c0005c3c03000c40d01b09424104e90180010401d8090400302c0008290f000480d45001003040b400b82d21540ca0f01c40720182403811420701008010348041c0c0110042c006d804070745011300104e0001742000d54a85407078101c2e1005d405c05940f0f996120302c2515081c400c2c410349c1c2c0c5c0d0780071640904485507404c02021604a82c44140140e0066900c40e010500607002048044081507180543d0180300b140e04118052441c0d0042d074540303690080d00300c01c503607010714114202030190340607605d40c560610854110446 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 972136052 1250 972134802 972134833
    0xf0804050a0c0b030405061b0f0a0e090f010501080a23040311150901060b0705070905040c0909060507030b1008061306090e07090c050304050a02090604331202030705040905 76
    0x95001402050f8008108418031205102c07650f0884c410890103151a092007400300c555000d5503d0808400e0800a0003440c1075001d008120082e04024082a207a841c0000c0c103266410700c24070850707000c01c039124001486e038607032441100741004170f10300c0d4005414069404040800070081c403c4040c40100007e503107400d58108100d801c41c030081031130f00c25180352030268642510300c6940600000c0c1401d01c05d9900151010800c0020340b00603440000b00c683d9181440040075115a000400da249003204440c01c1c00b10a1704114843d8007591003d01c200c02015003030000c0000346e00d07070000014600602252882c6030902c04003507200c00140c1c0202d000ca40321040882140d0310146401c000703501c0707450300300440c05140c016000c4c00765040c1840750070351800703032180e940302d242c0d895000384620200ba0014180b41e40319400200c10004900801c40b41d0001c07802c21040201c0101e6103400b103280c10030000078007064a244c2450043d98058064011540303003c0501002d89594001240c9600481d42c80c0c541080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 972137302 1250 972136052 972136073
    0x40f050906040203240a0f150801150e0105091503120a020106050a0e010810050903042318150607060902040e0d0807090b07030e0d12051c0504030f0804050a 69
    0x302200050000790030305104162400c189004100d050503062059900d10751201d10103d903100700c0042e80810b11100c42c01501009140b480f4041c00d03280030b0014045842c80301507100d800f080c0200094008802c1e125900080303c04ca00f4071680d6400568a40014080d00150394660f445e0407020f421950002c0c190000440540c00441c11200180c0d50707000100894035160341cae040002c00712510461400d5050016142d150342805003840041c948403c041400785008004a400030190f01420320b8120241d540800c7c3e681304010f2905101c2c00244031041c1102043d441282c4c0100382c20000c003072401d01710b2011b0140b140c0000c0001da82141da11000c1d0005600c0b240154040c01480901400203260000006083c0ba98061b281104000c0c02840c1030002803084403c0341d24554050038860002403941c000125404200c0d2801080c41b07038241d40407145c0c3c98102001e0010510440e84060a48200c103402030304a55045401400145040034a07a01060145900981050080081d030700d5010851301e6480040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 972138552 1250 972137302 972137311
    0x10f142214190605060702010206180c091602061830070602070b0702010e0d080414010e10060819030e0607080301230d2117250203030c0414040f05 65
    0x10082c121801c82d1400c01c9100e1a800f41204171002403c05070a0f40001b03540b17580041050019541c2d8144800d031546040001c0d425041380200304000f03500d8820356035000700200a0800700580b09090204500c6555410300065071207041c001001001074002000c181098100e130329049801400d0400d51a004120004180242c0107040c0540d44082c640703414a0400001050380341103926181c80919401004548241c008401b49041c144c5600d4608000c08441e0278407404014035881d101c0e98001c0d05c100480c0312984504600d40400841d0790b61000107032034003480382c0e09100401c26480c4107800a80030394510b040148000c0c10080c1401000c0d543d0400550013a04051149400402c95444401034034a84c80319900d0103403035010000c0c80369030b40d000c00b1244000d0070000d086a1200c10a104500ca00000042c0e00700c1102203180703508200c0259032001904062054500004103c0700c0005400002240d000c2c801c0e00c0c07425450b1514124600003007048440d03003150320545512124035110300a0051078013030b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 972139802 1250 972138552 972138571
    0xb1606020a11010207060605280302040b0f0616120c150513080304050106091b08061e030a080918010608130c0e010b0306040e1b061608040b03010f142214 68
    0x12401c040c10440d0080020016011074644200703604d0f13050327450340100002c480d41900c0100390003110f40b00285c00742c1403480e612038000c0f80115404100c11100c13404010002e000350f14000c103001d605074045030001121400900a00200c20000c41c4840a90344043e500a5148203c510f0003406652542142d0384161410b13561603454010900c6040010f1181c1c0450f01d202000e80f000e800002c00000e028418010a168468110019070884003200c035540340004800090941d1380d02c000c41c0c6007281e0305070010724445001d40c0c0d9000000c08440d407030000c5a4143c0d806034840c1141507541403c0780c800070329800000c071840420355034000341080b1052102400381000c41c50f480c0c1c40e8035180d0240000c4515407049035030280d000b049655458500008090301c3c023102a2007155541080c0a40300980d8211030b18002e05e6030400250024482c50604061030684039001c1e1906ca10607602d4007003020030304ca40f100886d0310514904240038400021400aa03a41e02c03843d4010810700218000112001c0003114409403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 972141052 1250 972139802 972139811
    0x110309040c051201050301094b06110406021504030513170c0307050a05150c0d0203090108010815060d031815020d14030408070503040e040f020a0b1606020a1101020706 74
    0x82e030341c800f085a41d0240100340d008205904040d114007444000039040d01e84141180c00a03000c0ea80480310310241e50302d4424480340060102031258403071403084581c084d22010700d40041495459003810440f0202d45a80d40248403041388101d4542c6007002c050030440c03d00c10100407640000001c40308420052044001c807040c0b45100b4082141046000c03100c6610075040000e06120a58548114209079641524041a50100200c80c5486032081c0d002e026000c1c4a841c005112007075001009000020003a61b415507180d0703031440055600ca1141c04204020728200b000a5120700b0300c902200c0540d400703850400840d54440d5803102100486d600700b0f26181800c500c11140c1690100301010302940c9500e40b2054038843c0031040c418030301014000401c03400d000a280030078081c0070816100030708607035101c18129050070b01d4807403d41c4001c40d501300d010b205400c00004603156600d081e242d06100300045940442003582d200e4000354402030100d000d1113082c138941200c1441c24800b92861603c100030024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 972142302 1250 972141052 972141067
    0x312091c0e0a12120315050a030b010603060b0a051903020d050f090610050102030d0c051c05090c040603150b030f0a0303021b030405130504080405130504020f03030a05040501110309040c05 83
    0x280c070034942250f04100c0f41e02e40e20380006008500c12118000c0d0368540081c07009584004041c8503121030348901d50241d02c103100402404000010075040303d1540d14100800b0303603a1312350b401e158041c14460741e0105000b800302c928405600000ca61881d5138610b001850b00307100d0b24035882203070000e031103000070380ca03403842000100b80e010000283c105d8240340903000440d00d0040005d60380e100d102009502a9210840b00813000c0c090300079074190116200300d14582d4022501d00380c00403c0100d03081d4030708d846003c480c0d007481e0505129590589402881715001c1101000c01c42c2c0c0030b032411640762900b612645c0113140c40d0343c405200c42101e00e40f0139039016130380c3e584040288044112040c417401d45070300100030420942d07070f0f40002e14421080c200c03000306e2039668034104100302e400b40b54080c940000c0034a816041614a0750700c0f00f4412131080390412004a1190705040d52405031446080c046901080188211342c014604c1000c40540881100c1c685260f1174040740039104007401100204078046003d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 972143552 1250 972142302 972142309
    0x1a030a140906162f1c0f0e010e01200708030d14010e06060304031116060e03010e0610180605180f1e0c161b060e0906030312091c0e 58
    0x38801d118618094070002d0780c403510742039120541ea84900708400d1407000313a040104144000e5000d0000c1d8502c066640030140f801615850603090400000740c0d540401940700d6000342110304d10410180e45804124980c000d80b030142c2c102e1041785800300e100d444400034000ca010002032009499928022400d2282c20b00900140c9206030010b80c3c10682e02d80030480c00b40c4070703e03040d00d0b401134042c9003981c110a205845141810300124200100b039651032400300c1c01d0360700300c901c00c0f101c624250001c108500c03e02c800e25803a4081969032841080c411142040686031441111001002c43c2c500010349a42e1400092001c0c02c0c0008003492444070710b020000400e100303204d21070380301c1251010640c588441100780480c1200003040044100b40100d506800c2000e00301c41822260350080c01e0000940c0e1101e110301903501c0512440000a540c0400454603080841456005110290042d418201c3c03491503041c04090003001029507104190703014098000041220b0740c040b801f0744440c0b03c0d080410781403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 972144802 1250 972143552 972143581
    0x31909090b03010203040b0720060103031e180501050d0e010212090d080702060c1e0a09031103010c3603060e010f181103100c030b03060a061a030a140906 68
    0x10b03110b41d00c140200004640000c1c0181d900c01030601d4844644040d07200213010302003140c44c840906200e054004010540c2000c1c81c8140342c50079044910407456070301d00480724200c904016811582024004000c0f81d401a400341080504174800450181c03203920303800b801c80c0c024400c02409a50300e8414131807001414801400d40780300c0bd00d0402c1a92511642c065966030010b04141100d1303600252a80014411504c07a02800d50310500b010383e2030b0300030b100041c000001400143c2c4c00041c060052040e6290500c1114810314031910f5400e024500782e0403030558880d0f17100d0041102285615a0152469091f5041000c0d5100f180d000076245000004076086691101b1010100ca1801c4640000e814810b28100c22460b071111a1181b810395100129003400100100f03076a5450030001c000c010180c25800424203a501602266481c0e500c0c48660420354041c1c2c07103101c4e0346e0014000e11003501741d545030041d030348908540f030081825808a420712040c0541210000402d411007801d002000481d08103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 972146052 1250 972144802 972144821
    0x30f150630020a030504020a0b0a021911060c0f1b0f040e07050411120106030603030914040b030f0a110303070b01030b0a02040b2b0b100e0409060609090c09050712090503190909 78
    0x18840d0804e6500140030707584036a019009a0f1402604140b50f00700400dc070070464200078040d0005844101060300281d499002d07050b00701d400c3c0551024140b9030380150030030b08101900207003c101545280d030b0901005069001c0550043e016414000c43d032a20380c1d009001940c086511aa55a070010345540202e60006800070020142065400c01c042030f4400c843d1401d4901080d2140f00f14500c0c14000780081c0007040e11075416021b88142c01580c040081201daa0441c050b42d40e044541915108040c3c0341d00c90b841004002064601c018004540310b4202c440e4480d403000001071270301d030312080281402c1d00401e05104143d0461115210100120304180c2d031581c000c04020712440e1002c00c00210f0810140c210341c01080303000e1800019550319074220702149e43e0800c40802150b5140d0701e08030b010b410049403d5070300e80c0b20150006640b901c03a100d054842d414950f52100c2082c40ca0100002600c0394040a540303620090004241c5a940400b220f5081d40d141c0d00c0b42c40f0554a03000100083c0d400d0441c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 972147302 1250 972146052 972146069
    0x1902030f07151209060f020408010f09170a090b0301032102010c0207090b01020709060810180f020121140609010f0803030c0702120d030f150630020a030504020a 71
    0x10420803080031080c600006401803d0003007404503c0b441100c014200000081e003d41c0c1401a0001d14621540c01031055500c40402488212041c904c1001070f26240c03900107103119122504180e80784120009411a00c1c1a0b20b06112001e950750800141a04203070004e907000c0c9202d43ca040364040d581c0d9004c030301640e8980000c0c01009204403020751950464480d2a407107948680a0580caa0310034010000602010401003050540f148034803959241c06e4500e02c09803a20b0217070f484020a401c182000400b542c0a410801c00890a60044490300c09410103542120189a00075040703403a107000703000030314416a0600d43c85107000d07020401c0d890f1040e403180c1c41055070700300140b0500c840070040742c2d4042176031401c066540200c0d00c04a0b6512040e009030390650b018245030000300c01d44c150050511001c4c140000c3c08299281c4a02644410b001d2103010045664218002d1450202a4000311a1100e541c9500d81c3d4403500c170040c02c180d030300038850000013039583c01c20401140740007014000584941e8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 972148552 1250 972147302 972147313
    0x60e13060506120c090a0f0306050702151302060d14040309051207060513050a12050106050a050a15022a1906210204080a0f1a040b0705130302031902030f 68
    0x140c04141c4074407482507400c02000003040090200e00321303c01220b0003c10702404081c135456640180c0d01c0c500100e8042158a9400d24010802e054800903801c00403c89142d1552180c1d120609010800000404104d0b08920700344181561380c0b90310710524424000001c0e42000c507140500d4000c1910080c1d4000f94401c00c600c0f154118030110009000b03040c0c4d03070036082a90b43c8048032804480c180c1d80941c0702c55408000b459000c80d109240482000300684240d00074000c950320303a030800506103a94040c042e009508144100031503070541d10258003155480c0166116100d440c881a490a1080200d030440f079007041e00c400f2540e0801d190b0b0310380c40e48a80c91a4210302d5040003801805081862501340342035084190900c0300b1002a8100d03002000a0300071076030f5100c02d610b8081c0800489103401c0d41c04156081124908074078030135074188079950011f0f0700203090341c030b02d1015100341d0004030b19020300f48000c3c0b1002c00140c0b410000c90840c00100302a0070311841461041524001c00001042001d4100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 972149802 1250 972148552 972148559
    0x10e1906030308061c050f0a03020f0f0c3d0e01051c0e1204090b0901090c0e1c05160905160c120324051002030c121303020604060e1306 60
    0xc1d00044205c43c82007500300032680d1a1140d00450034080c0640c0a41c0d2004070340040e0008820a00d980b00e5001c0da005040280320054840d2107419a4000c031390441660300c0024580004074402c2c030301c070126403800b4540c410340001000c4e4880e403001e81140401c6c3c2031411146a00300700360211034402481c150340340a58160380010880058040b200c106511003200c183c00010030f1201024104914402c1600c0756903480000c03000d0501014150f00550345070f000414042d4042c010040144402c0d201c02c20701070b00c60018000440000f0309040c410502c0481cbc00c00004405014031703440d03500102043d00f0064109003c0900701d41e400b40c4200035460000302d490081c1900116484031458115420f1500c040912100340c000e0800d82c52184843c480200311a82c0c822009c02840055034000c4d50b0100d288032900c0d030142e80e2840707801c01021260384400144030358072501c10010005000307451000c80c2019520b07030201d050364019811010100380d00002c46034007070400014049000280d4101804920724 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 972151052 1250 972149802 972149807
    0x309030c0b130b0a051e0405090609390703020616030608150604020d240f1805090f010920040c08070e031501080c011403060102070519030803010e19060303 69
    0x168460300000c5000421285040c501420913106d544860f510342002138065030403134500c03660245c000c02d441907015002250340e07814041c1589221f01004000c402440300380034410141c0b019400c25a00908540b0071004021aa9000190030890b02c2a0020603c03414510b0480400500381d030703c0802018604501040340480003d90042c12001c025100700881d2030700c2021902a10035954034002503410300d40340b00080101040c684010b0380c040c0005503009a00d07048082c0c41070107a80300b0451000c41584a0304642c821a51003030b03820400600071074090b4103009030164250381c07204205960304c1603045805030303000080400c00c040c01801160200314401d103262001e00124000b030503c8080181c800210022501c040040d50310204d83d24182c888035613507074449140e45544c1d048010340001c490400c00c10044103036000f44c85c0981b07030507009805c0c014103000a214034031004a600c2e0b06628800074000003c903200000450283c074002d03001041614102e01000742003a100546039071100d251520820100e907 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 972152302 1250 972151052 972151087
    0x12050414040e030f07260a080703151505040e0709170a0305040902090607020d0605330f0102030f0a0504060f0216050105162301141605070c0b070309030c0b 69
    0xa00041e00e0341d15000c1c1c81c11b1113110f04201e68801000f46000010190091118070050a00000b155807582c5959031803090850990700007081540007226020010300000f100607500b20068616494083d0609584050b09520703440140c400f04003041c007540c011f00c480882c05c20200312001c8a2401440180441c0e82d00404503c150711600340843c1d40410022101e80d5035000300c40700780b80c004100d44001007080c01c1000040405441e6603035141c000450b081811904d08480c410340144291004480000c400244070850203413801550440c0003c0203c40082e03100c02011f0140380407030ba51000e4540c0d01303250004d0800602c066840095602542d00310405140c01c40c1a4411384800b840c00545503205950521541c1d18032060040002148801c02d0004200382481034804143d00c40c001d000844500d03507000e038207402c00d0b82c001a4510090303c003501c0e054000c034014103485208503c1d002203250380350740030703500364000d404114002908488100180403102142c00701804001e6195880c2114107140c071121031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 972153552 1250 972152302 972152317
    0x20d0c0915050307090909060b01030b0f060313080f040806100e151e063106020613050a1a0723090114250506090114070c020d12050414040e03 63
    0x440040041c0084d8440d0303810364010302e0258824041f400f1549481009400c12036034850000746000d138002601d142080d00e40d029010003034810751442e141d01421141203480110306650300278040010381d000348112001000101a540060144d500386400c03410402985580f180c818100d0b4a4103000c0400d070341d50501083c0c03010458003144c0303106860340302841004d1901056036120601040e20020b00c10300016859000d030a42c0c604034403018006401504000d120b014140041c0c0c0960001810498806806250356000354212408103009644442401010b01c95800e400c104a0051046640c2c00541c803290180c1c20300803100301e07038a22020118481c0120581c042c10001e2081e03401c801c3e140d500c1c08840800d03000000c0451650310300c004014040c0c0d010f40003102d840c0314140018200100610820f8014568840c51180b292110314040b1440001604141da001e0300c041100c4002502c402400a40302c410707500e81070303155481e02c0300100003180790700788035800380b07003040780001c4103403070101c01c403000e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 972154802 1250 972153552 972153557
    0xc0801141501020708070807060905030f070501050304030c0b0106110607021c141902071a040f03230a06290603130c17030909010902130b0c0a060906020d0c0915 71
    0x5200c1c1e074004074a00b510590004c485030080b00b00200d4014000700b0b2103000d03a540da403144911156140b09240d0f5031070390301f154094aa04000300a02c03480d0304c01c40083d50041c2c0a441d00300b00030b0039a40c40311243c481c42a8001d80114025954110300c040050002a501040030b0018100b04210031420348440305a050488080040f0060604107611207802038603081e209260315400300e09072094000c0d594409900922a140030280e4400c1806000c074811541541c1c0418540207101d0b11b0355481c468951840288540311100c5420b80c4d4001d0343c4100099440d01c0d005444c0800d5030713200805a0714202078200c2003840741005010110740e180d01da440403030707801049211143c0c0d404020350610608002c8a6007180901e0a80d0741441001c60070b00201070264201e0480e14800300742d07a80c2e441101284138a007000000680341c01403c00402e42c01c0400f81c019002e41000340c0d5a0100c0e40e41c0d40341d04840903140121a05540424a410848440e00c11200c01140d9410f1407141c080c1403511045645005028903002c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 972156052 1250 972154802 972154831
    0x904050c0f04090609231b090c0702090405010606030e01020a1403220f050111031603090c050a090501031502211b071203150f050603130b010f030c080114 68
    0x70300352101e500c101038040d0480f0381040013404900d030644424000722280c1d2850000e0820018001401003401c1c00d0b182460b4400440002d00031b818416440001401c01c0c02c048424820603000d600c41140292190f4130800000642c50309242c07002d01145d91074110002d45138810712110f1901a005512409031000050807035890b9074544550035400440c91401c40d03062005050b5610801c03000000c0140c074903101d44000d0010810314807800000c2c2c00111480b0382820390b1503c10740c1e1400d001ea4000b0000e68000c1a2541203983c6a40c00710719007101c1c0703074010b1842990718001001132100406844500468200301580351100311001100090020314111010308000c0700852021a440b82c03040c18403002078030358942c690781141884030040c074000b42510003003810a2403502c44401c1b01c010b00340c01e80b0984c0003034003c05801c1c034081c8000382d0002003454803c00c4411651034049950700310a0f6000309046c01154860504504c0d00e0444201190300251045c0e04020724000340d0741580405640c480008000441c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 972157302 1250 972156052 972156079
    0xf0706090501090b0906071b0810151202030a0c06020c0102011401141302280f08012d05090c0a0906141e0904050a02090109081908090a1509030b060904050c 69
    0x11490f10400f00001c0c000b181c1210b80008492480144030304442c4580700340c604a0b081b40720701800362405050b008005000326882442400300331145d4030413145c0040c0490361040d1050340c8403542d10240760401e10250380104581041c1e907909000d100f0b64880c00b01200039195152541c034070060120083c2040c49100301002103034000c0b4855060380c0c0e070003022003518020310300020070003d003410306084c0950029024410114003e4000c5400318100c0d00800f00c1c1d02c900000c4120040d16040036001c40010090905100059503901c101c1ea480c011540140350320f90380c41e003068001e0010065980072109021b0b000c200c0704400614041540c00a4041c00d448600740c100201c042c05c140e200c0c4a4001d9846890401803241300c04455000e1301d13090b8001e80b1840b101a407100047c690300c81c90b602d4a41d101138041c0c000b040003d805100907164080d005011028038070f80b120440d40d2011896451800080c2d0788c0d15081041c000341c0b508803500041c09035110b04850609490307094507a4045104c0901590b2443d1142 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 972158552 1250 972157302 972157309
    0x8100c1101020409020a0908010c080a051f151806091a0c01050f040b0a090809130605060a12050114010e1207120506040b1b2b060303020f0706090501090b09 69
    0x22100300300354001c6640c2c1340c544000030000e4004813840070004082c080086803510701417003034040010103525038030b0560752401140c802400b80113180300c040c804241107000c030380310010403c0e501034042141e80704045600190000c2801803c1d00c07030340516030800681041803036080b180c4001a106181d614a00c0300f000711000c440d6030300c50892074034065864901001803c16030a600240034038441c0c0c8680c00e450b29491000000d848210720081e080240800c610b8400345841c00c0c4090603d04214800328025641e0f60000d840fa0b086441c01d640803440800d46032845010911803036003d0082d184459080f6110b050008104480180c003050040240c8180107070309200400522009194550845030082c1d0b2a00d800b41e21610192012104403c000c1c000c01d2a02d6421600040e81c0e0164229460030f0a0b000f0403131001851442412005140c05d144181c1400c07000c41c0500340c0a14004e400900f64105504980d40c0340000e41c1e800780302000301407201885244e921000c100115010220001d440b00c0800c2c000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 972159802 1250 972158552 972158567
    0xe07020105060d172104120801180f06080109030206070908070f05060703021203010915050406051f0c0227162f07120b10080a0204024f08100c 63
    0x100850140440800c8882031140ea440717502c600d00c40c111240d010b490154081d81c00c0b9800b1700501c04801e8560030000c0e51444140d0052a6015401c0e001245003507413903100710700710340880758242e0060300448100b045060300035600d6002040c5030340041102a14025400e04a100340f40140e078450140010031038103040c420410221500f040002441e50b82d40c1d07980c440303402805075107200c40303200840030300005481c0f078541b103114201c5102402d11028221a903010000d03510800441c0c60601295048400260b1210f0581141d4a0070700c2d11842c86038040362100d080f0f1104000c1c20b5001c2d10002d180b20040540c0d00c40003900c0704e442c030031065101520701c28a0301211501c035034006140c14401c407940040c50040f5204c16200640c00b801e8080e169440300e02e009501009540194000c0d603224804a00050410398010300540c481c4480c0b400410070031101200314561205450002c02d2200900410384241c0240e60034404908044000c40f02440c268403070b521146000700c80b1446540d81c079518003800340a05136 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 972161052 1250 972159802 972159817
    0x40905030c250b0331060c0315080a0f02010f030e06090d0933050715060501020705010c2d020d050d08010902040308030420030111040e07020105060d17 67
    0x35200c8000d03500900710284030701c21189082d0b60400000000b80b016800382104c1c01910120b030f03200500d40c3d004c5080c45111500f0264001d813603842c1640c50001c00c0d00340c8501654180146c2c0e010807190211000114020016081404680c02c44143c04001a0303031040b0401c0e526034282001919000001420382c018245c541c000b40c25401041c2c10426048000708130b60141540b980c6903900180c0d01d400d8045907400300003c41c24507103031100080e105e030400300c25503486810403c0e25041d0310741021650b4402c031030b0619548040c141521108203108a40c2c050080002404080ca0201098801900c41c10300b415480c0c030070b0f159483c288600c00212400c154602845003500540500c80c21006031400680da0400b80e1201c90000300180000320309a002e5001700c0f4116500320500c00d007940c80ea626110410801d6010161085171422060705660310280160301100c060b05611a4440307203050410b85010100426003021a45031001f041496a5a0030345120344c0c5400000c1034a80d01500a145071441c481c40e40c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 972162302 1250 972161052 972161077
    0x130b0f0307080c040e0d0c140c270606161106090612040314041a09122e0603081e091309110103090c060f090f0605040314060405070504090503 63
    0x11001c2407102e0006224440c555003a90204040d141c1000d0568a03400d0314135202000420510007a00030030182520056084600c1d02541c80070044080080e45003c90098801d1311000c0f1185119400071807100055440002924954500306e00b0f104182e042800190006050845504101045840311020380d219100003400007956034004110921040302e003140c040b0001481c0110841410301400c0c107960842d0303001072100c92011010460b000740c0380c00c202c0c1041c2e013180c08200f900b0340d284001c01444940c0710003800803140141c484410603441486242d5010401400c0140c20000659440c00700e56444111341d01a40c1c88811200d121141c905c41c41600c0365102043c05c1a0100402440d0300c021903040c4103060340c03004401300400550544510440160048903110000c0012602038000c003000c840d80e528260031002e072a0b100c414031044968101d040000d4001c01c05004100880c64034003024000d03407000300500e10f0103a07501d40d80c40c4000d0003814000d0f6140c805c564100310302041a0740003902e080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 972163552 1250 972162302 972162313
    0x2031b0a060609061e180207020111060c0318031314010c06140a060603050915070c051c0807090b030c0d06053102131a1309090201031a130b0f03 64
    0x150083e6018203114011903004580207612102c5900c0d07100e444208446020003800e1030010305440100003508103d800360306110300d00c4040b81c00d410b020302c980e9110749001481c040e12070400c41d10b424141036403000941400d602c03c01c0200c8991140140b0b410854a002410004160345000100d03800945a0340c010921410a02500801d1b603034035004600c5a00c120000300400355541c90f04400340c44050f9120600c5801105003a420502c02c00752103503102089041c54034041c0804d6455a1034080c02500384102ca43d50010b890841c0c03036105003901d407c841146007051559040108407030391807202411020041500060080c400d078660740081004050040c481d00320041701e0001241100b81700301c11400c01d07a107590070b0700349e02c2c0011b071007500c0b07102c0707003524200341e1250030300e15400d42c0b1300c10b280c41c0d6820500040c4055008601d540c0c071400040d0890040104883c01c0510000d016113036003038404080b01591800e0024552121980013401350180c100110301c80101038082110700704a04100e40c2c250068 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 972164802 1250 972163552 972163559
    0x20c070306062102090f15031f0c08042019080334200406081e06010b160c08030328050c040605132c0f010602031b0a0606 54
    0x41d42c40001126102d000d040103100001605400340084503030000d500c4a0100d02003010b582241041541c00030380b460f20341c0c07030003008000083d18064104115400060404144440d100c105009149041c80079017009a454209950b0b410307010042e940c13035a443c0c80c0303031650890707044e58403110700c000104d00b00041d1003002074442600c0303500c2e40c0c0a446136040100f12003024080d10112420006001c0900915021801809a440010342e1102220b8450071001c0c209134001d4550719441900c0003040c40a004000c040425010b44240008414100c2070503002800100440600882240c0041021440760f09103c3c800b842c0c005485840c80d04544190310000c0104060b40002248000d0a079040014903408000601c40c042c0035034004961400c0e540ca0284000c0001c1c50041c0040d200d003402e800c00d0a06482d494804058001038141c1c00400301c154559508001d0244a0500381e0b0004803440342c0c40d042c1c1d0b0520002959a00c20040f2042c055940081241c0081c0320a2001d00d50140d4028001c0c8040c594 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 972166052 1250 972164802 972164813
    0x309050a030b0901141b07031205090601240914130f050912130b09011b0506040303180f122105011e030507060c0215030916170703060e01020c0703 65
    0x1295100700c690b00c0c00401c5501e00c0d400e00f540d20301c11003140000c95018071042021b4440d50b04040b00032001e1000b80c90300003880c07010784e005261180b45600b005001640c034000314100c48200380c03005100c4160303440c0003d040c800d43c060221800e8130b9280c080709044000002c00304011088210701403403928507100014188208079040300f40074141c940216003201080700e500b80481d124040c2412003001604100f040b0040300746001c2d101800050504034400e1007000c0103406001044c1c3d004480303a80180e0204010150148507041140f40f20100290b120b012903a05e80040c0300504801030701f000104844114a548500c03c82089803100501e517850307040c040c00c10070019000030700030f03202018404207540c200508403015040460750410002c010036880c0200640c1c02c244042c03001ea800c040f06240c19012902c403070000318018200e400007083c403c0c081c01a90103c0030303000d0304842c2c41c500b984500b08420440004100c01505d401110000c0d507541154250f40c0248150311428049001d4114000184003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 972167302 1250 972166052 972166073
    0x10090c02160b1204060e010b0d0602030a06061d1201020d020c06100503060f1302040b10051305041a150c0d170a1103070309140615030106210f0309050a03 68
    0x210301003800e00c60380b103011502441c01402015501c241c07441c000200444c0e000d0300b0220983c003c03003000003410441400444c0602c414540300352580394000040c003042c82d01d14410940201081e1400d095140c0301c4005940360310800f8462144a40401a602005040298121200030000035000c55840c03800a42c0b86446407030803189890610040d210004180c200850400c3c458101d95840f05c2840c2d46500000000038204182a07811580d9071801703808684411b000442c03890129100e2039202d850060000d0701502a64002c07e000c0ca0829407585d03460421002070411441c0100c40040500c1401c0300600c155004290300a080d6100e8110340030040d6070448c0c58160170040c0724000344030303070340e900b050035000e0b901c401c0d4184030018420400070300d406100794098186540304903000c0c4031074251342c07072414503240e02954080790440003983c420b06070340707000d10800f00184001031045901015100c46900d982d481e1800107010500304100101c1010b2080c01a0b0001c0c2c00020000c40784241c40b41400e4507900c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 972168552 1250 972167302 972167323
    0x90c09090a062306100c0c0f1401020706120f020906070c030b070306060801170f011515030603050d261e1e011a040902041205010c050403031710090c02 67
    0xa02e07140343c2e12510100c40b103800140081e9501001103946440c8140400700311841c06842c1040881e00341140021b101c2c8403204001d03c00c90110315950b50501c2030509000c00ca01800034190350090a04002084e0046030300a4101c00c0711a00188072440030072648084c2c072408040c194000b100107409000c0081c6612070100341c901a6840002c10381ea81e4100303600712841d501418011a88041c01001052841d104292b0592010020780d03286400045030a42920b003240024481031400b0704d07042c081c20b442c6e17807170080300443c2601e4144546407031034485503241c1c003a58544404000740140782401001802c01801980d030210503d0701c10a01d010450480355604400040c0c810008040c08100880080020f0039401d1040d010201d00d02d2346002c0034441c0310503000d5114240f107607043c00f0004010820780b0103030004121495158210b100e15142c0320342151030b03008407207051000511083c0701090303021120007401050072101c01900e4664540943d070702c8062340d1204071103034105241041450b50200364140403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 972169802 1250 972168552 972168563
    0x180a030606030614040b0c0d0f0f0915020703090504050907050913060b060a0e010e03010b0a06080117150a020f040510050913050c0a0c020d1a0106080601080408090108090c09090a 79
    0x103100000e801c011404c1c006a03000340280340c100d0b01040a82d4a15030050545c02481040003c00810303003e040415140c034005100035159445007650705008500c003800e000c1d0f28001000314a841110340d405400c080d85802117502540c2e65000060390b0827400c10024001d400024951809490503090038443c428415030b04590440c1090f0701e4000c1e80c240f09055a00e890b815840b0307060f80d1080c0000460b60819a8100f0b40c4d4107648440501000f078075140b00d55400b4100681c0d0703103186903040c100d01c0320306020a88220001d503800030b079078610420710304d40580e500000100d2001da6281300c038410303031103860040303400c1560302c100c41c908603c2035250040e005043d00102500c80d039202d000b55100c103104590048600500d065820854680454410740c003080003144010a1074240d14056111031b0051030b00741c0111603800600c0d00040c420260001c0c013103075128600b46010001444c090303484103040d00070444041d05000025000c10301495040c000d200701e9001c003400f02c15152403c550301030b6488421041c26500e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 972171052 1250 972169802 972169811
    0x1507080d1503020901060305041505010b070308090a02010e100212040b0414040501051c14070e090601080c010207060c11040c0917030f1902030408030a0203041523180a0306060306 79
    0xd407894050025800c40342c0003001421142c3c680813040e400f41c40c0090084a0210f90a075400541382410b1191501074410707130502688900c0e139440e01074400a0301402c404059030200362035000503a84403258015011083c1c1d901d00303c0400034942a072921054104032090f0040c08200030030030303034041400780c42210541a00300f0803181360382050004459017030160f0b5401441d03e80f8102c10b50300c0900b04807100b5070300c42e4120059049010f0207003030804007940c008000348103e010034004494000c0140314050018400a0081c0c0700010340041d580b01c141d48948802d01140a840c2c03410b018a2007003d03400714401030410b010b142c00448004103a44840c1c003601c0013000c0703007141115403040000140e070229008540402e1814084640c0b541284015902c2c0008510003000003280070b03c42817000d0040751015030000c5072603900340f80c0802005035251400600300007039840010030001800409101d512013034004039507118074140188180100400b403190308041003100010070403d03a40d00500440b07014950422 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 972172302 1250 972171052 972171071
    0x4020906040e100509102c190210031b081006030b030714030a021c0b0705030903090904021c080c01051f03081606050112030906050a0219021507080d 66
    0x485218150220303060b80414080e2200c0032844c0d124a40080c504030444842c11004654481507070b13403e581c5241e02007605858529040c0c070305a403044c82d00c1000d40c0039100741c003120312003100c0c0002040f5010744542e2682040b54030032402030b40502c020203020000e6111245202d840a40403410903aa00008100b45050010b001c030701c2881005200d2038010040e00d40c06181040817000300c04011030722603241c01004807401c01a616000081810389200800b4884403015081141030705c24000e1600060240400c10404c000030040115210f42a0440d4403030502c0c0c8542c00891034650f11691720704003006c041c1044c0b4003403149050140081015500007804255201140c01d072550200482820482c52070349004d00000b5032400140c800b40510100900380381c08161101001e4a40a034029103901c40780d05040070500d5070000d44800508254103125242c481ca01c44000d54a4104e5000d80da0f0401c01000680115503070b00da00c40e2001440ca091903a11890281060705180d801600305130b019a02c0d010520 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 972173552 1250 972172302 972172309
    0xd020d0e0102071716080d0f050f0301030b1305030307030e16030f0f110a1409092a0105090d050c1816200d0f0906080c0301060e2704020906 62
    0x39101a84180d02a2024525007291a040241000e0342c0809030b0040130b080c00018480c40500000501e030540c018449901040c00140480b25001289070401108001d2008045020002c07030741100da214101c0e645a1b40c5401088280e501110002419400000103101001d50305400590a181e041c00070380300b0104401c42c0d40349404246100045c40c20740b0100c510804a40c880e100908202c0c01003108114216240001a07488d00003900300c00038030381241400900e21704211240c694800071801c0205115656114010704201440100301c9800c1c1c3c010002c0c0b6003d03489401035a180c03c1006d0200450200a49419030f1110521110b4a0117500c2e20340c1c0c0e403d9048030041440e070043c4c1c1c0c030062445442804a5041b190700082610200d000071b05d0490341e14501c881040414221001503840c0303a644100103030020982c50b565442281040300b003030709110340200c41c0c0c8200c1b811114a030030200450800c40300420640c85940d03400010380581005e8a15240310031000140c4a144203c44013091640c811041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 972174802 1250 972173552 972173567
    0x13030309050d080a0605090f0402101101060602060711010209030618210306040506101d2707110a150207031809151208070b15031002120903040e0406050703060f080d020d 75
    0xd034625441c8c000c0214001d818444244415040c039480c027006500c046601c914251070b0709500080050f0300c0072080181d034951081180c032052006c00c000f545041e00c420300103503803204058164102e8031f6a007015000a241d0421049124070541140340840c9080501448925001290303442d024034109000107a4500c3c00409050410000d0345810340c803400c1c5401c0c40000818034000b41c039000b8084a04480104612215031408040c01d200803420038508194020300d45184400a4142a44440510b1002078401460b00402c003003092001030315503060303050441e405940c1c2c541000f9210b100c40000705981140d07401c00a129500030b0400040b25a0b80d12000003680c03200c41014180c00e20900010000800c400843c81c0c004551181805420303000d100000c0c140588000c1e40308030180e000070300a40030100858099448022400a075052500d03144000250b070304000d1000380301958902c00580a180664849000740c50584012000303142c490034000e80e0f03080900d2600000d44120548411254450080d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 972176052 1250 972174802 972174811
    0x30109140f0f040503070f0b04021008090c040e0106120c1a040f05101e050703201e1204090b04150510030c03090501140609011203050313030309050d080a060509 71
    0x4540707075140c0e516078a800d0b0754072014100300c0300c90104019100128003105107540788140a140e14803400c0c18180304100d245c0d0080c00f06002844012420003070780f0074000c0f900e0082c0f294169004241d0046411f1040e00501d0180c0280b01c54210040011044c04514075080d0182c0f101980e0030f1003568514402d0407031501885c494909070322031504c024012418104040200c0703000310300300302031031081e034078a034514459607113a041000070400308115051652105201c40070721039244610743d007012403008040d01c170071140720640b6401c4211041410700d80300c10403109035081c6080c004517807100c0e100d418560240c010f88031494825818140514501c05c00c3c001000c044800041c641002c3c980307031003000c0c2c01504ca2208054145543d6804200101c2c1003030182815120290b01403904520f009010800108010382041c1e8841c80c0c02244540000d030030808a0b03410100003864850342000320f240880140000c15402421402000c05403d90713a0b0700100d9082c00342d01041d500303200c0d168944051100c1d0410485 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 972177302 1250 972176052 972176071
    0x20309090105060f120127060b2508130e0106050a0f030507171303090806101a04150e0109060203270103090b07090503010b0a03030e0f0a091103010914 67
    0x10010412443c01c8802000282d041004140c00d04100941c03802c03c00000340e001a802c8036201d02d01c07564090b408807003600e00c40c440e0703c0c08100c0682440c0e45003a060241d11102c0202d40d005903034049850040c0e80c4141076641d807003170080b583c030f01e01d12240a511101510852034000038003400840e1403405401920700c0005160340d9040340740c507408811005008068a103106000d00e0b040300a050103009503100748109000078081c036108000745401400034503950b00100720b1340c115600b4045000f000a58040032a07054190382c0c036290040050a0a82e072060798000301145c104402481d541d582c2200032040070407001d8850f80681c41d507808003070381c80703200f0070b100624801c4104007502402d10900d0322004100806241c0003454500302d070f440000310001034070705401240310440c08103d2031400340111992468151a070624251031a50013030b20307028803d2680ca108288071038088829807544001680204415107050050040031206000c240c1c0c03003030142103041030600c81c1c00c2001d640c600851a000d100c080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 972178552 1250 972177302 972177319
    0x14160605190e0306041b080d031a0603040b16200d020705152d07150c031406060d0f021801090f03120c030215010905070e0f030304050d0804030f050d0f020309 70
    0x603070310802c6c0f007405ca949446c04414200740c081000c071000c0003e03600d0f41105482c0000c1100340303451411103105018040612a06c01007041100044191040a412103400c0314101c4040202010a0f50002c40095101500c0022820010380111000400400300f070000d4003600c0102c1e44803002d00405202c4c641000c40380081c00c0282c070002c1c50058403140311682e100d101d110f01c2488004030419440e8080103003581d220900704460040c4007114480c2021000d0305017410007110b2140100c44003118001080184079880114050804440d160409503106508927411980c0b18510b4213040b001c0c109510145001860500001c5400304c1140300700d1041d00e810039051124440211401c8600a00c0c141e030480850041d0f4040740101088000b0311400313844c4c0380601048610b00b98000410410080e00c0143c82901c0e0850810805c0c0c501104883c10f4460544942c5a03210060809041d507200d2036100820844915064000f408000705103820b103580259501c0410b0904441e0486e81d0707000340e10007142d015000c0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 972179802 1250 972178552 972178561
    0x20f040b1f0e030307031707020d0c060209030a06060e09150f150a09020d02031503150403030b01170a0603021f09050d1505100317130314160605190e0306 68
    0x2008505100d01805182182c2d0903000480400d0442c2c1055104401250114507100154503411048640c0700c036061006220880e42d80e0b5004000768200c4c2009804107500240310b110a85092241d03d040540142c0144003650340c80d02c2441c0e140e24119001d008600a00030001504190300604900801d11454402e9480c0c440000044010204001e602d52004650500040f6407866001401071803600103030050712407805144a144002181030300d1351198101c116040414200401e8081d04160180340004042e0454001070b100d90300e000d01d44900140e500300812915044070b402003429280700303846680017460000e480d91002c21f10141c0503030104600010501c020b040c105100300900380150442026400b40c00c00c3c2a040f00d506940c0c02c0b404000d110f030f00341b040c000200001244822000c0741c0d1441c04002040080100303015000c000d003221216031268a480f171040081c600c41c41440ca0502107420344d030703400280584d0700030107003030191800311700f0f40c070620381d0113034140031010301010b806031060707130799 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 972181052 1250 972179802 972179839
    0x60a02070f0b09030c060705040f0608010320031e0322081e1603060504030e01080c16050708060c370e0316080c0109170d230a0804020f040b 62
    0xb4000c1460074244400d00a001d221502044207a00a031415110b03981c1e076908000307000c0e04890103030b002841404810001000040c0c0154050405800c4035a100f5404518410010b07080c43c801e10400703100c405203034102410a0340b01200420072040c1a6052141c2000f00300d168503403130b800510413a0541d4208280c0211560700c0102d03981040c8803840191281a050110754206140c41500140d41d0a580d41c0200400c040d00400d000007031010034201100649000f14040195201e40e4181c0c40d400460543e0302010480100400c0300900000c0042d0303000d51400035901082500200303c90f61224000d210920100301d11010507205e900d07075000c0c0c690b8860310b90410640d0211444800181c05115180000d40d01d13000c01d048240281c10010701a2010b0405207000610300003064004a100c081403080b8074012050006001600c82042e0600c4041203054030b6036524891011070a0711000c1c000054072100c4664041388041c4603910031154440c00c5060f0105010842d00b100b0b03204c030740002c82e58541005005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 972182302 1250 972181052 972181073
    0x6090105100804030203070209010e091005060901120318060203031603090812060d0609050c181e07110714010f02010e0c041d0f0a1a100317090306070f02060a02070f 73
    0x1340240122440d101c0280c1c04034032821401d1b4450030300c84103c1e60510601140501c05514003441c007005c14402c80c00c0202c0018201007062081c0d40144032034080e09010540621b203807605090700200c0e0781c118155a008043d48035801202c0b2145000c0075040c0c0e80e48058028072942c1f00445e048a2101c0c04e048000700c4050300c90f02d0150201e81c5c82032100d04100700280709402000c01c81031060780504160782542050005031056440c0c1484422005000c0040c841440300018080c07002440ba510403a4540030429103a0800101d0280c20340d0080c6000810355048048c0660070900c82a81c41c00d13828040e0120403422102d081001807003d4100344175003992890140c014480c03080594034481c082c140717110320351841e10054038914203a030f801059009050000c1261188404800403a4800040c03400c4c1e09015142c09090000403e1800c90006060707003c0a814192002c008024046134024141510081c103180c1e0502d491000502c070b20000034460078000e009480f41185d020410f07502c3d0b0b4001c2e079135400441e0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 972183552 1250 972182302 972182311
    0x12060103050d0f11010c110c060414150c0f0a05100204080d08040309170a0611040b1b030720130c020a02061e12100819060b030a08040914060901051008 67
    0x8130074502e044810040038441c42008100c991a284066901c004032942803904030203515100b024140010401e84a8815420600c00c2c01107a1000c2c489018500011550155101c54119841103c2d609010501c0020380e59811500501c1242c040321210054070301641f04074020702800d034210908820b02d060180d00329a800a20a00f030000450f51281006a0f080c25900841d0410754803d00092050082e107100f9a80b000c81908992480c040c10101c000c1404d210b18611f000a0b1040c00060a2250b0802e20a171610305900503c2104105580121002c0d01804032103043e03c14500e035290215951842e1040910800c040d801920050100760200f114a8000d240718a0000d414000c0000301e003407525004161000e5071480c0d2030b0050070701e412116080d03010703038101450962125132080c285005807484030300e46c0b6610010100c3c02c40101c1c00482d04081625034002e080080100340829551840e03080820320040c80a101e0380d160f80c5200400c080800207101d02d9400c5003070f40c800700900e94415049907901 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 972184802 1250 972183552 972183557
    0x213031202150c1201050307050d020114160c0e0f0907180603120f180e0f04050102070f060b010f1404030f050f10090b15010930060b12060103050d0f 66
    0x30840c0800002c20105021075200e10403100000e0f011610500261680d8013600b82a401400740608010100c1d1808005000290501c80d5980c0220780402e41c4d0170071a0941d1070110004410110300d4a807002001700c2501490b003259400b00d0001d6904c032030541c0e05601c25009c900007000602d24109600070503040340010501c00e16100c04011000c2103855601e80700001240e5a0041c03103196100000b00085002d0034802950040f50364104400856084507030703000880c0540c00d0351291103c2c60154028460100020a90902d000c429818021150b0200c105004282c90b440d002160780f15084400400400c45035001d15020301c028008903850f51401610303140300381c0440d4440382c030200340c803890009400410820741d52501028070410900c01c0e42c8640001c42c0c1410420200c21440010788030800c1c60207110741e503545a148040c405589900e00b100711740c11880c440a040f107a50300340301c40035224208250380201d0540f01d200240c0140007450134100ea801401a0426004150003120000c8123217903503908 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 972186052 1250 972184802 972184813
    0x121b09240411130f03050606090708010e0c0408011506140901140702030a050f030a14090306150103180f050c0a180f09170a020607031e020702041d03071103010213031202 75
    0x600440807040032004d4070510048403480381c0303507180980c500003004007103138004c00c00c500070f022100e50004400742c195031000b0b801c1c200b03139030300c45000c04d05e94007880e40300324959801e001c00c0000440e503411180c419940140e40e001e01e402454224050340744200080c213400181e0342c0f00c1c0101c01c4204030019010051005064030340f88031140c0c03174240c94004c1d42d072520f070b41130782002804056454010030185910001c1d00c400764202080400003075210b0100a01a482c6809600200449030f80300c0d80c01075135204e22040c1340d000300ca00e150502046180011000303e50901c00c40070102040d1404080c0c6504560034001e000c411b12078082e0001019240b0521042c1d0820303128004280016402c07600c07117958003d00003440e504c540d4020750003440d018000d81040181854071a50000b810b5108a0100c0380400018001d0307500c3e20644082001852003078144c5450791109880080e0944000c4018004031f801804014100c240c000101402c0381b180510307440d04400341c01c3c0108001000c0d103030050036121581c0180d81 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 972187302 1250 972186052 972186067
    0x13020706061502062e060c05120a0908190f03052808040b0708010612020c030c0d0f11060105090411040b040f05070f0c02090411121b09240411 63
    0xd100d451003082c800240e044081080307654250b03528003c0c03401d0307214035180404074443c0040f440d03114954007891041024004c058028000c0170800f84058090b1006110364880d0b0160004180b4030f1a4042d0a01038056130440b80201c00031852420f4809821490702b90700b0480e295000e680319801070030840d030140d540c0e940d44100d0f0034481009402054403a03c99202519080c9070a071383c6010010710341d00a00500130014030a041e07000366516191044420010380e542d450007a00c0303241d0b010700c1484442c64481c070114000c2c85075201c0710604103140d0603150800c015040791901f0780c030343d0300034012071342c000c000140020f0200306000308410b4145000fa10020b202c0071204003143c16201d0441c0014540b030b4603142231220040d80000c0c102c0d14401d8a00c0d141211841c2e0b5400a052110007803c09044d240801c01210040d58540c4410605804100708650311640c4290500c2107103825410401c2c822507500002640744060400409140d0317404c0848540090421402c1000600c03200034181107049061103109c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 972188552 1250 972187302 972187319
    0x8300a03021e0c031c0513120c0506010b04060f0807082d1003020901050418020d02040e0d0c0b0a0605030d12020405062107050906250c090e12091302070606 69
    0x307000c032201e4280134540da69641c41303c0c0707449041400641d400c01490f0901704a448003840300c0408005038420b076503582c1c10080320700480300340401c00c101a29500805000159070441400140111081a144c1d80c4000b41c00038425a14000101c900c6004101000b002400709035011408414030300030581c84c4190b82d0030108100f20004000ca4405c00150744402051040d0302d41401250300500040303d040c42128150042c1d01d110030b0094070001e00801d00c0242c44801c541d65078200204c40c02413070003103030140c2040c1000282000d040700c100345c8540c40302401007102065603000701e0017078400103030080c181059001c1c4115010f040c03e070803000000ba820300c03001c1041e0795118003d103500407080c03840300e103000d1000c01410183c6c10098841420b02104204161035612501c0c1601c98481050099a488510390301400012115501c0002c00c0b400512002040c3e007376850f440b1040014280b0116138107042c008070700322002d1041c00030042c0e002c100600b0300c04502c0d01940040528600c0340c1030201d506a50344002e07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 972189802 1250 972188552 972188557
    0x2070812100807080a02090a0f020309031c06030c0b0d0b100f031a0919180303020c1c052505010c030c1206180507051308300a03021e 59
    0x888440400c044240072000341c092250001500c04440038028051034021255a80c00030004024000c000c00e00004200315000c0d8000d24242e84640029581ca2520005a030740702d602c00240c44010406518000121400e9441600c003542c0d80b120b00c628010707007001c1d11000702c3e4020b40301420705141c44050000054668200064603801c0780e03240c8082d40a0410006000c2e6104c0d040640550402d120019240d81c0c0c0b00c007800c5400c0340c5038034034954020408580350805401d01c00509050412010502010598075038002d140c02c030100000c1d04c954602d540e104402e000008000c80001072000e0100300140ca04400024041400321520080c409440fa5103060a50f2190030001022035551048108080c4c0c000321018411203110750104003039800d046a180c00c200742c50307404004c060780d500002480ba0380a107040303c998503100781800118503982d0303408581c0d94502c0ca444e95004690600502d203041d03805441420240340b070035002410518682e000f00d009400460b01c101c0c0303400f40c40700c0d402d0704000b043c0300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 972191052 1250 972189802 972189817
    0x203010b0d081306140a1809090f11010c02011e0c0c0305011512031b03050702061803010b0315042909070603111207030f11040f0509130201020a0b0a020708 69
    0x741912814011295500d2003c40d41c896414001300940c00001100070034101c400840d1641003030782d03902c151402c90304e8a2026681002110311b24080190050007145500c42503060701c644d4401b0b000031145401120340c800d01c0c00000b40894000203422400d41e121034444c8080030800c0c98015100e000c65155000458156801501c850355525131040d0710000e4410b81c80050702c51150040071100c4240e8004149003c404240001c10034894098410944a0030803103080a400800c415220f5003440c40d815102e03400c40c5140c511941c40c042ca084141c0c100070403484010100801d0180f180d81c0c90352030301001c2d00e400d8400d84410394a1000d4a003540319080c00c03641d020b40b034040004e094076410301502400316112107203403094910301486440c0c5801e0301c500c11141d001d105881d001c54166202c250242c080c20002500d10b10148000c034000c114100d28a400c0c00444c0c400f22105480354482c90740e500c096506041c00640181c221030b840001084814002c0f41d0451155440141390643e9605c81400a4102e440c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 972192302 1250 972191052 972191063
    0x307410c03120c010c0309080f0a03060b071101090614042303030c030c0705030a0c03030e010212190e190608041a01030f0b060a0b031f0e0906011a0f0706090203010b0d 74
    0x20f02100801800d00c45c14207a01501d0400708800a1142c8400703589005402c09540040c20000d5500700c1c05200e0781286006166400c032003511200603281260070301d14505207640c0000c82041c40056000c0c82130b0728821440f10007407202441c180c18080c10b494440c041030b4801400c85031340c0d40c41c5c040f107880800060001c0200c05011355143d13074800c40054200a1326500030b5203c0e0348280c24100200302240040c400b10395050418003464500703100140c2c100021450b030117241640104450100707810029000b07207020055603c101401c0c2c0301c4001c100ca07041c0260306407080300c100402e0520906002d60500c0390083d0141d22007803402c000b4a55980c240007004d81045652541c00c03d140010841c0c6010040d4100b0030443e4034161160508012000c9400001c22a6040d002c1515003030345494014180c40c000382048403074030011803900c14030041c1e85600a1290110a0106141440c60075132448282c0d1032885080d01114507003503c584501015204c5844203990655131580c0d40e50302540c1711a203408110b032041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 972193552 1250 972192302 972192307
    0x2032b03152117040f0f08150603011506081005010801031e1e0f0b070e010c03031107060501090213060203073201050a0f0b030703031707050c0f0307410c0312 70
    0x18002d490300f030a507101b2160910061001d0100785004201c2280c260700740c25443c1599070f11440041d01524043c1c1c0c0c0306100c216000d5002c100240e010b4002441210030460b00c081c09aa550011075014409110103401c003410000d4440082c14602e207000a024003400d4140032211807105248681304000314100d50020260440303400f0400f0f0100c403140d0040d26810320503258184540041d018410040000b0201543e40040c5800808410183d400d03880d04134608200541c0c42d00c1515000f98400910902c11190205c4005562440002115800c3e0f03030042c2040341001c1500d040c10301141e05001c04240840d0b81c2011610206000d118452090754490070101e82c4401e1008503d00700c0714904000c9021340c02a4505102107a0414008102040d80315507584060b45c804000321f0b0316000e0940d00d030b00c00380100c0290000c000c00000152202a000e22035003841a00e16901e42c03000f8014844520000060191000c008a07003241d0102d400c4c061068152003158583c500004c1c1041e466150303001c1e601002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 972194802 1250 972193552 972193559
    0x3020c0615150f091909090c140d030903080c011b1d0109050a061b0b01030b101d06060d0605120706090801050f0c03040f02032b0315211704 62
    0x250900250105500740d002d1804074401d0038482144100c01410303001d45c0d10f000c60503014141c0c2008010003820320a0007041603805038a0b1a00c01050b81e4030510300450500300302d4110030300c2c1101040d100542d041d11080c0d216442c50ba60800c298108440c0c020703003556106003a03054072060f01c0d5014440c00751591201c810694030303040c00d0307070000440340c080781004481c042c1406151100343c04202900c0c09403c126001d0380ea008011044070000c00001003030420418000020001d058081500400d03400c200e183d880c80c1c0b9019408481002c0121280c40e03c04a078010451030b00f00f600040920480c6400080b8820b6152030210340708100010801005038044c1d42c003040035941c40400040a0310180000744403904140010200c0d0076000341c1640d000d083c00101190800a02049602d1300d207502800f51440b01d10040540342742c0d242901a04100d80088001840201b407080c4605100c0c540e203d812642c00b0b03401d01601030041503074070000c6584010b2441c00300011a01c0c264018a0b45000c10402907611404c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 972196052 1250 972194802 972194809
    0xa09020d150c020d050427140108190f02010f0509121c0c05030d150e0106050a0813020a030b0a090614090c0603090d0804021302071a060121090303020c0615 69
    0x21009940700454000440c0c8100007517022003110102c0f09100c1803e019000089410b260201090034040061071400b044a04000480913000b0f0485000c40c042d00c988100043d100580c070802c0c00c400512a42c8200c500600560045180d50f1030b201103458000c0c11720480c2c8000c070b9040681c03d05060404e603c01c400007003c1f01520282101c58041600d0035200c510080c1d5681c03a542c1c0696804c0309001900c410055103011111100200107207020000203006580d140d078054002e43c042d50306003001a0081d00058012052605080a0710380d028200050481c41d60311640101c860140500a8030ba8441c05510041079030b83c0581c05141200c0d2380b401950307080a801d8180780900c103003001406010144104030032400045008050401c042c10084c007903a4440c400940240088068400864804200401403010081403440310407a00e032981d00e0300c1d444000064410821740803000428000d004034203002c040290b00103110961180c207026003011500d40b40745040c080e00319118007242c105005054107a11b03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 972197302 1250 972196052 972196061
    0xc0304080d0c1d0a03080f0c1609060501020610030809280303110708010905031c1103090307060f181704120b0f0c04050d020f0d021011012702090a09020d15 69
    0x604913242a07000d0f2642e40e0b0340c2140c0c0035082d10680c0450000c1240415141e0602c298114006982003c0b1040b0b504c85600c071004003043e001d0b040c0144a10000200c811b06100d00c8003060340d80043c4941d0409428000b001482c440c001c0034900d1000f00b0b0743c1744001c3c03004880545c4010b10302c641ca4207018800310402c0c1907c5e240c86580b0140140c0c1c10807602001180000c4116071101c45021019210307110100145005008220550030404a0000030021110004005000e440b4422031b404c0c040c5101c0101900162503454034000d140c2c40d0a1621000003862003c00c3d91030003140455a035040036680c4d060301940102c8154255110080380041080c2000d656102c103520036038041d42642043d051402046c03e4481c03000d030090048204509502c3d0300e5480c3c0e1040d801c4c03158000c10401c0c0c0e1004103100140000f02040d4070443c40e600703141c50455221008549001ca005009000408510381034003080303545c8502821140645035a01c0d4030f1005600e49039042c0701045c0c00b6424101303290b01080d00c1d090803036 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 972198552 1250 972197302 972197357
    0x905040e031e090a1502030c1605030f0f03030a02090f04020301060503190203100b2215141c021b010203131a100512070504020c1005010812030c0304080d0c 69
    0x1590100300c0340c078030343d903401c05031809172000090482d4000f14090780a0345144251052046a0304c0b0b0080c0d000c404150102c000380c283d4500350180c0301850f041c1c3c01a2560fa103a0304281c90401e4106200103540e400e441d81c05080c0700440204a00710006900c03001c5800c81c2c1c000c0e008080040e1001081045510b0200c0c1503a414a02409045241d403400080840c00208180148030750702d000060b107081140c000d5488442a072001c0701c1008029680c0d500d104124100c41c18103500032404102c42d0098500d040710039a8244103940d64940c00c07411b21150703548020b51018076054007480048200014004017480a50301c1342060301a800304444040c1040031000d000000c1030400410304600b0441140c00001500084880558007144040340d24840d140c1002c3c44ca03044250014804201c00f0035900740020300072080d000c1070504002c0c07644c03a4186a600c03a01e903110a02002101000030803600c000f10070045038805c1c00b8854090412220391440c80c00e540b08000228000b400702c00c400441d00f0184d040d10300e041d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 972199802 1250 972198552 972198607
    0x21e010203041a04051c05070501020d0e0c0109031104020f07050303010e01031a07050703030f02162f0a030305090a051003020d1401120201110a0b07020304031704240905040e03 78
    0x918013aa10a40e46e070b00740f1303d01072076013280641901c10341a008030190b0703d085900500942d241c652000d0444000d02010244001a11401d2103940042d4040c082000603a500500c410351303204200d50622001c0e520003402100d140800704400e1010030740c280040c5010742482c400001e03465143d07041c54112101d030017611845c3d239a001814000c089400004840c05240e140c1804250304160a140307000034040d00302d6880e2092404c90004041200c2c48980855040c080d541803220040014104020702034900202074002010580a0001c0b9000d40c3c060410001e00404c0c0c0000303d40c5441c0807452a142e440b4902c008250081a0140b5001450007040341c41110052070a416615258054080641104019042c0030055048040006041c040d0b1084141c00c54081c0b0310358100080000d580358003074441900e1852151b04034034007410008007200e080304d82a01e400407400b4a140540300d603801200700e070503003480384001000406866034003500030a0880c9070040c0d6294401e10428004004001d14030481 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 972201052 1250 972199802 972199853
    0x1615020114010531020705061f030b0c13091d0a020f01050c030403050307050a0b0907030c15051b1015050d0803040510140610020a03090b0307021e01020304 69
    0x441ea24010003042c1110003c070f41003204c10503000384411401c80d502c43c10003282100010080c00d810129001846154031801c2110a9692501c0c03540800f84e8030141c5405c6480002e00c000c1001c43c140070000c6400a000382c245a00c0c0040e88007402e1000c042030f900c40a25241c032812000c0d1040c1345007107030030401d0140343c1c00b80014401036400178100301c81c855403043c140140400e11410641e0304005903406143e1050880c2d5035a2168240f880d43d805540a084035800c0911000912a031408980c1e40c048030392010300070b540d1905100724a01880c0480e5007010400c44d0a200401d910b0b44143d880c140320340004c1025040240d01030481c801520286281d4204d060710b00041084a41c9510000b030400c030b81c00000c415146d403100e2030000d0410203004186500c250801d02d0601104940d1107600b405590100e480e100c3c0c504c8001c030282d864041d0101d002e408541a40004c2003181c280400459001400c1d20644041014a91005000880f500807480c0540c0d404410030081140312000c0c0f20f039100c02c00180b0724 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 972202302 1250 972201052 972201071
    0x30e0f0301020c1518010213050a0b160f0305160b1b0c0a060c0516060e0712050c010f03060810050a0507050403261308161505090d08090316150201 65
    0x80e41c0744c9020f1461801501c3c6a4001108019801240e1044482c940001c0d5075540e01082180c041003001c1c051103100d043d1380707007000ac1d001311100121103000520024081c00354051780c41e40701e001a07600c2415402d0010400011003034640c2e0102c041045441110002d01a04200030000003102c1c031910702106034541045a030101d07002c000f40605000e41d1151002c1900c18003d881241c00307001c1c030701c10341c3da5031440368804c3c2c0100300480d00066492000042251143c55484081202c400e0090304060f186400c51000350803e5445040d20400342c0440341004141c00d9682d00307000d440d26944a12201c0c0701613464080c001c5d0300441d4014503420070070300e103880d038145801c6440320b010401d8071040c2c01000c3c0b0281e001001280602109440c1e12040c2e0a50a041c10f6954010b156200c08800d51a5001c6951030031020038200751320210080c607419595209801c1c190500c043c0281c1c2118071909542220090150070481d9400304003501113080700000030708105141803414286444040079113815a410b040500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 972203552 1250 972202302 972202327
    0x18270c04210c0e07050a390f0506010b0c0f010c020334030e040f06140d17070503120108030906030412050705010e0102030106020d0306080d0c03110604030e0f030102 73
    0x80d000003000604060744007503180240e0786105030ba00402c8500c000808012000e40c004001e0042140941c885140b2030520325481c02d002401a4602c203203000250b290909000010f41218207454881c000b9042103a4a640b9614508a42644030125400c0c1c00600d12086950602c144001800340d08001e01c8409290310b8040e45902a011146840245505c031480702c044040040e070004482500d0301106411031400e00401400b20202c0541c000c0703085c11244681c20445200d02004c4804c040d03031030b0901059010800c50a09507016081e40c503500c00042558a41d980d0307800502d442c52040c8025950b4030b01c9283e00c8010340005922022b800d800a00000903030341c031000c007103035801a4809031440c03112598210680b00c6008a000c090003541c6001e1404000001c15401035058600c1134088448210403c04214140c81d00b41c040c80140d80c02504502c50b465000e603030815100c80c400e0502100002003002d0442c50801b007200d040c1c0010750302c001d2168640c180369010001680d4150025442c1c0900c00d15031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 972204802 1250 972203552 972203579
    0xc14090604090b2103090117070804020415030c14090f0412230a12050a09080706050921030403090905043306060201050609070e030d0518270c04 64
    0x16000442e032a180f19141c103a440382a6100d07030303075100c034990b1400203240700c0c02c00e0303a9800c07034815a808501035020805440c00f00540d490300c1f4404035a9028007a0783c0baa401e11019041210030042004500c80c1c001c000900328500c100040d002441c842034110300042d04000003544041d01c4014090003450034403000c50320740021000380520320300309003d5040c810354038111144064000b4120404011410b50210740d40109801ca04540b200e0b018410354aa18410800321211141c4c02808010304106410010b42c6540200d640181c2c07400c26141c0382c0480d0300e10043c20070001417514204540000070482016042110f100c094a00786408020600d0f00340d450282c0350017807061208d50300281c1000580c0010b01e41100d0300c0416421042031210700d6480c50040c0c0030704001d55181d48121800e03c00908458460031808c28102c9004004100b201143d10040d1410f0303022624a031841c8003190500304d0706840b8484540300460000d140307900106000c13460f440780c811000d402900841c0003044204688a0043c11 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 972206052 1250 972204802 972204809
    0x906030210300f0605010806060412171b0f01020a1209050703051603031b05070e07020705220b1e04020d0f05010305010617030a120e0f0703060c14090604 68
    0x34440c0403078001c4103000860031024200240080882d11a180e0812440e4104000090294409001d22900c41c00151a0a441107600340d0304100306000802280c00201e100b84980c074000d04041c80d03044240380c1d4060065012104004442142819400304001c081240c3d038002d082c42d000031030900c0503040c8010005d00d16072102e61405512183c1d0b00007405810b120210065034000c04640e83c180c0c0111710641304845500c410750100740800c00c00144281c40240c040c40d19a400005014203d04280f80746c070b07004034003400c3e00b011481a15000704442d1148912180c0c280c15080701c0c0f040d81044040c0120036940c1600d010303406401c0ca042c11a8a00401c10b5100b207034505d0442e009625014803030102001000c0c49450180043d04103000041440700651010f81598460440000c1940c1040b03100c666038031508446100283c040c0003d40303080250365000d0001351550a06a442620300c58400d1494240250802d4400e10b90310000c04074141d400902c00081d0380200e2129900f000080030010704580214817 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 972207302 1250 972206052 972206057
    0x30506100f2c040c08102003090a0506040b0a110a0e060a0c080301180b0102060c0d0c0e19080706090515070c050a0e0601140c1b0a090c050c070906030210 68
    0x11400a902510500441c2c500012000400540c40c140c20704500c402e41e0340c8107901490060640c0340c0082000c2d13020746461800c00c0300040c44179460706a1400d409510081c001e01290103070200d4200011400c1c008203016074001e0420038681d0500c5010700c0100c80c150b280d600c201c141e0410001e10150f030003ca40a5801e10200e8007a07443e0744081405070707107180380540300038140c1d03100100221b01c00c0c0c51010508011050342c031042101142003001607a96100584045d83c0c6000e00340b120a05d04180d6800481d0309c0d01051034100c0c2c0c41d0400e0300205000040c0c4540004416103403410034030041000300041030090440703150080c1c140e440d01e404100011110340750702c1c0381080001410b0007848403154148004084c05881c500f40c2d05da94040e0703030120b40002d1301d40e240001e20601d44030b00302c0d0700c0940c01d0b201e0110380390b0081c1400621411b540d149a00050751312076001441c4050010f440309051040040c1e00c04030743c4440d42e807a010042c9003400e0000d16004580d6442c500346007400542c4a9074641c1c46501d42d2030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 972208552 1250 972207302 972207329
    0x7030f050f1e040809030a03020318041811150d140726060a030c060f080703140c0315060c1506030109170a054501021b01030e06070504030506100f 65
    0x1030030045024401c2e20407050305440b1f102c0c00e810405600000a184400010300502a4203100e001000156803246c0383e0301c40ca400d000a4414041450070850100c5203400500801d9a820f00070584c40098002d4000c48000d29581c00c141e030208042403014580c07189a51403c1480303010440c52031403006000032a21030744800c0110004425171030f1164108095070308921510390103584c0711001012400810b080d03000144070350b000700703512174040e0049100803041e0320903061141d42c45a1044501d900010807000388039400c403545401070380307a400080c0f148404c400050070860700449500b003221600502064040d80c07403c1030301e40c0441c943d00d6556410f40000d24840c2c0d0380e0300540340112610300404d07032031103c915000060300c00312144801103240341000e8180440c4000101136490652498400d0100c1d000d60400051580044d8817440a09055441418001403803070309528010300c0c1601c111b4006010070703000203050040c0402088100e034026907120900602504090441e4102507040c030861000c0c6109 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 972209802 1250 972208552 972208561
    0xc11030a0f0e030303010b131a1c090b0a0f0b0f060313030c05010c1e0e0904060f020412050c0102060c0c0705151c06060306050a0b0417120307030f050f1e 68
    0xe601c5840d02c41c03000074110703a241d58441c4007008841e170048503203d0080c000c944002031080101c62102c03910086c4500b459040480c032585100304500c85e141501001c994800180000842080405004800c100d0380024614039036a00c800484080c5d80c0804d1140000400f1130f4025a110000c50703900c0344031840071808141081c5425141902250300041207035003030850708980c40d0352200c403c48029501d18088c6004206140d015203003550030404050f0007900160000780481d80b250003072141c0c00d40034030005150554a840c010844515078000319456000088101e03282c0d0b904000c19600520341072900e501c1c003411031010a50b2425144903090107101c040340c2334941a00d001c000c2c2c0d2559900000c0540f50700140c01d40c405e0081880b0b00501c80032a2520f0008a40c508090060b4800d5418030310a440c40d0a040040a160f50407000d206414140711f542040306074041d90201550281150307071004180c40319048405420780e07100402c030000361640b04042000c000c2c0d10388e020a2401115402041a40c1c6a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 972211052 1250 972209802 972209807
    0xf1b02040207020d0b15100e01020d20031803060f060d1121010e070803130e040602130303051c051006080709050312270f010f0e03010510090c11030a0f 67
    0x144c5400103040c03403142e10b00304800b41300c3c8140110311a010488102d411102c3d0070209441c0d0702c001c608250b0060b84071041c43c0c55041d00079640102d50741c00208074461500c85200c401481c40d800315400e00e000e10f00342c0e03000380c4241c2010010941c0001180003403018526140010420306802c1040c050721042500311403900c280c8a81d0f883d001c0526501d410a200c84903400e007400c0c040d050040f04011148244000010305034008426030f0000c209450031580203c0c5000d203070240b2200064001d450007942000700d900d255041d00b8403140118400d44500352641d01001c1c1005028402e1030356400c031942003504002480d8620f502c0360055408600b06405242c44201c2c0840780390340c1c1c503001301e0b13090302c90b081e4580004180d80c03002d0042c1c1d10b921120303400316a000341030410710686e43d20705aa0b0818110b02c80e0711041c0d0300a0001481d4901e2600c0c1809981c031510300001c0c00e442c001d60b0005006c018805050107110400e00594841814905124807a02042c2264694034843c84d0300980c1000241500d40c01e501c2d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 972212302 1250 972211052 972211069
    0x1f140405040f270b18150403090810090809060d0f0c0e120318091306060e15010e01080c030a0902060c0303101703070b19020307090302010f1b0204020702 68
    0x10041c000304604104845a84010100202e200703c480f0b18000c62088200c01d5211a1400a50f2041d60f07100141c1701c64282c94014202076011000501405451105600000c006244110b000342d8070f01d030b03025160451150401080c6c0245000c06030030080c45101081c0d03280102c40c070b01c40c000d80d06103030ba0303180b41c2d079507800100045104011410304100500b14003580c000121070180b0022140d4240d4a0b100040c103c1d5240718028040b41075042d11101110145815403001b039101482810140e0381903c03e5445104842c0e0581040f40e07a03156032001c1c403d81d12000b801c1041304030020b00303142d4501c0c000340002070900f00d80145441c1592600100003009002503802180da6564054a40c0d515a0300040e8603e0b102d80046596240c5d8140f910700000c0c0caa61009440c1c10700400c080080c40ca8107226480b02c5c2e0010300002d01c002c41c651043d8420640c08480340c401141720309103643d40c0d81101800c40c07000406c20503103010440304000b11148600e00c5048201000c52641d54122001a41c0b81c1c003901c00302e202003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 972213552 1250 972212302 972212309
    0x10903050f0601050405010b25050a0b0a05041511031602250e0c040b071407030b090307140f1f0e07061205010603050c12130503041e051f1404 63
    0x500034031034040301c5000c0000342103050707a40c11541441681e03203c44650210b030050507120042105040303041008084000940c03003609001c7d02c2990000426600d696910b4403080e100c2000d1140e58030304120501801d00110035507252185014002c0542c82c20028402c0e00018040c1000a05c0104804038254000c0205040c2100301414511380700391409010b4141d12894850f42200e0300d81c2c000010882c1c01c08030304807810344e040b00d45000e051a0341c0740c40c9c03151030040b080014803240c800c292011010440d40040940301c3c15035a0000c640e030701c04514105016000b03503034400c0000e81c03101d2035510b034100f00072070360302d04805030340000900107803190000700041d08003407040c10b9413130060a801041013a448803803e8040822114140301e640d0741c03010b040f421504200c07a20785c0e1001080c42450540c4c045100c01c642c110f076000e500c2c000c2807151030b100c031400e507403041c0d0004580405d107251700c00381c0032a07460741c8200900048411005080030900a40b10030318003016802c5c1003061009140e41c50700c0c403200640d0040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 972214802 1250 972213552 972213563
    0xf060515091f1e0806090d050301120f15050105040c0e0108010b070503040b130f0602060408070b1536010503070312050f040605040f05030d3e030d1b020615010903 72
    0x280d0700c80e1001070740e507525800f0380c4d036460040100095540d08001200184480c0740d644c0c50389140e2820385a840401e0303904c0411190035280d0700c08074012601450b2080c1541409c00000200382d4505420802100c480f01810418071144a14004040c1c0c1c1005150b41120910312496580e00d80c01d10340b5a04520a540141400d500b01107158500c1040080c0018140c4440404050065403511b8050382e07201300c104d9004111200030020040020124100250010301c90450b000c001c915190019484c1100811050702460399084020144000050041d10040184194200d25414140440d4132000d40f03010203000c880088160700070f200e11460441d4012141d1580d83c54445864401c024915170040c40742d44441c5000040c0410b8030301c0e000c0380301b100e1446651140884c26401c40300c80d0448002e0003420710305610014450150750415140b48601c1d4030794890146076101c8540c5104c40440f9400c07a0104142071000780788529240c0c000481075000215020040e90301008600103d4080c111600000d08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 972216052 1250 972214802 972214829
    0x105220306050603121801050a0306170a0204062102040b010521010810050705071104020c0d05040e012405032205010c0f0518041a0d0f060515091f 65
    0x244107055114a005074004c400741c500460300c1c064a000c850148041e035228503007650120144543c0504014039100e4803904021640070340e07070850420690780d440c0000810307400c84001d030310440c40e00340b06860190450b01000340201c40d150091208050200700000d002d590b8400b00d081d00c41c0c1c018019600e60445480c40a40409a02038826201c10b00c01c2c410b5070325030f2188203001d421203a144e0103807a100301d0403030f5116030802c0003075101c261002032140840f98001d5402c02060722403c005100b0301010202a4540c135079034034076150b071840305104e050b401001c0044040030b0340d001d0840b0f850200982d01015140c415280d0300d800c044001c03004210250803126251900c481010407006400040718031040ba01c50019000310070358140c400c0c1c0718240b49890807070045000d842080c80c0590089010100680e850003481300d0440104510032a69001a1900e6541418040c00c1141d640226688039072001045da0071105503001044c1041c4015040600707820409007c1207221603000c0c00c03507004244e001e8044c0e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 972217302 1250 972216052 972216059
    0x90f02071e0302190b04020105030712051003030e0402030108030306150d021b19030801120501110c1c0c0209011a1c1b0e0603011e0315060603050a09020d02010522 72
    0x10324a507120001c40150145042c0140c00c11030b0f800c10040c51076040b600c1051955956801154560320051504091100040308150412542d100d00c0d44505c42400760b0046060031410003609200c03100c00850302c182c4c01080184a8180c000c8141c0303400103401d54011650115411006410f401019030842c1158130101ea1110f110907210301d9038a440a10809503204a0910000843d03900003c0300080c000c18602c000400003204520000e4904030701800000655180c00300350781c10b4030b0b031103038213450425071001e20444019880d03481d030400c0452041c1446800c1c0700455010a410681c140702e55884601c540b0020f50300450031804480c001004990510001c0c00010051001080034a004184400c42e0100020540307002392002c450001d0010006800c40e1720b010300082c540014400030a420895800c00000000d603510a0b07001c000b8542d00000c83c200341004801070444000520314441182081094405600c0d0f41100c0034a194081c0f03003240c0ea40c0300f283e101034990030713280f40c902d040c5524017007002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 972218552 1250 972217302 972217343
    0x7080c060601030b041a090a0e0714030d0906020607030c09360c05090f1f080108060f1e0709050a1706131a040c0513021e0c07090f0207 60
    0x94410700003600c0c100036070003640051004070703120306c40b0078404c1c1400c03003071400c1c51403625098155100b41001c2c4040790000c10b50b420a0700740540781c2e010910f05121512004500c2c0740078010480b9071000e40c41d003003485030701e0010020347e500c078090400c41c181079940f00f441010300c2c801c0c032210010b07041d407103240d07240750700c1990384a0b4140d40807038010310f000014600c0c00c1080700d40030f00400003141050b5481c1c50074403c080c1c00f0801c04d000914000b541c41180380c0b011002c24990303c0c6c5280e24642998032440c28544c90424800c0c100030000703003d48018000f1b4000c224001c12400101c10f4108100046110503a0310050241d64424094001940c000e40e01240040c2d581159000c00487d0010342c41512010785170720020350b16200503803074000c09042c1c4e440445c154407900c1d902078552044c01380400904041d60b0700c0c0404d0030340100e0011512501c5c2c0010b000c14030010414030000703800703030220030407440d10061188440d00d450081c00b80c1190b0307035103500c5d849240013003540666844942000c01281c0320741d00ea01b0b85 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 972219802 1250 972218552 972218563
    0xf0f02280c0812040603020c030c060403080f130c030605040302160b070501140402010818031c050403031b050d0c02100e070e0f09100b1305040b06190f050402090607080c 75
    0xc40e07000148540201d149500032880c1d40c0c45180c0140554146420308005501a4010390503654503440107100d40d8070380810400101d4011070017601c484145050a000c0c202500b90300500034941408040315000004030700925001c05c507a0000e42c00110303a1110b02d03080b0b0500311441e40400343c9060b040e5010811074000c0c030007841118490b000030810880840e01748c4d040120100c501a0102da660000904005201ca11460700704084c6400c0e64548030998400c2c8114160752081895a26a15010071040507058400c00350841d00e45020081d1044050f80c0041c41440760184100705992a00f0740003038001d000b0401c540c006903504000b0b10541c1d0500601c20741c0c1d10268032584030903c41d0040807840f0344020b1640d41c1d000d15070f018060003160210101c1c41c0d001c0e00c10030704915008130030b0307203000c1c0c7c81c000b210b2141d20f0049101b0031031035200d811728008115580c14417034111180d840c0022030800620150b4420345003101d8054801503101d100c0b01c8009081030140d014042e003d0341001440d50500f9030041030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 972221052 1250 972219802 972219883
    0x90f120606031005090709020705070807030c0e011d0402131806020315090c0409090f14073b040309050603160305010f0b03040201030f02160503120603030a0f0f02 72
    0x1180d498550b000b25120039070304140e0705c83c00b040d0002c0c54107102d102440c0e0014000940107004031000d070380e41d9401301480c1100d01d40c000c0c2d41d08880c407201803002440170b4444c54010251000807000d11001c0110001c10b00e00d019100902c41c11500c1801c0c1243c1c3c200341c009450071914800c0580c0c2c81c041a08104020354003c80d9105480d065a0012245628110038018000c000c14215a410035040981c4c400051002c2e01069600c58140043c45001503c2d190001860660341c9015000c207501d402d425030300641070050000c20300f00c4240ea109084401162100707c1c018243e00d03c00b106904c4c1c0f030900751251422034011640100e000020090400082c810a2100c1c50340c0d6502004641c1e038410304416040c01c0c9020ba032404081c10008180598401d801007010500340c85001403420604034410080000c4849044420344c101213000c0d40d114034800f01c0c0e181e20a505030301070b500e424409800240010841c0e4850014421200340c145860340c42000000f90001f041d4546100784010807507028000d030018030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 972222302 1250 972221052 972221059
    0x220606050910080c04030f1505151e060724050702030408060f24130c03060504060e04171608070606150309031b02030a120e1e06030a02090f120606 65
    0x3185602e81481090340324071402100126608040c01e5030f032114140c089800054481624101e040101016103201d02809004588401021000041c0c14414000301201c4200701c29100b00100130660f0316604125200540c0c40b917950303c0907007040b6518240c00380398152000360b55031070902000100c9400200030406d0740c240f1801c9901d01e6070751203910313402041708803000e0000e13042100c0c00440c44244a00000c0101200400c011420242040e03200102d90781c040c0c035500000e8454608100f40d02305032140e46d0180a280f80e03042c142c2d103050b880704114103000700035004d102000000ca10402c0b488040203841d905a01032030040d9522911300305100035003011700412030800e5441d032010b02046d000c1d10a211f036440d03041e29143d1000002c141d01418842807284103a0709030003001c00303000024040350001090780780c06032640341d030340381100341401410940e1180500c01600005007000c141ea88103802e4a61081041c9000350b91400064082007241502c034660329004408020032a100308004154140304280c150b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 972223552 1250 972222302 972222319
    0x7080706090e09010e0a03200a0c06091403150405160b1c0506011205060a09091b290f07081201061e0e060a0302040b0d02040504060b04142206060509 66
    0x20380f145801c0310f030004c460200359480b4081c00c80000303018208900721514840341100140c00313195481070810780390314130485555400c03c02c18460117412a000c10060320544043d0110341e103040c1c0110360303216070315070403180340059100004080260030060043c0b40201c00d04811003040d920b403140b0b8515006108990340950050041d000c668440f4455070b84078a00c16503948141074140102e1800810001e403420b40c010110300004102c418460158000f0360384280400034909024803490181603e458000030003a503900702403d04050004281d80014580460841d0f6071100518110740d01d41c0300301300000b40407240c00715070700312215048180b440c120380243d280c003915085d2980410f2030304120400513002064074160880103a05085004d8107001d443c5090043c030f0240c60308020b01640d0090030402c190381d81c00080c1488182054000c0e04000d1004850050416040440c400c144031000c003000e501812282c22240d42401041200e21540401054100016502c4040062043c0d1000b000b072401070864 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 972224802 1250 972223552 972223561
    0x60f0306050d0b06150c0f030904060515030708091c0c05010f02041505030c0904060f03030e01031103060103200f07060501170c0d1a070e19080d1107080706090e 71
    0x2024510710250350000ca82c030102d0313560030304010900601c800c003201c022000740200545088100602e68040202800075902e400b054020002502c010381c0166004082044c00152819207020580380c22644908000c080ca603a045000b600e0a103030b68038045260303a40314900c905402e40001b04260150f00440007400359850903440c1d05d09a20072441105198498a0020b0f00810f10a401554010b140101440d1808506400140650b00f41c2d80140e00040350024003082055002039800d07024642c01e0a080c000f14402001e410038902008000c9410b058980c034918075400100d0001c29907541c41b0441c400d4580f86109130070009600034001c11034940b0701d02070001c41c10b9088090700541c040889802007202d6a070080a11040710340d191000c4a82c2031040e0034100c1e00ca0303040381c44103120b00300e00e070350740c02c0c034102c1100402ca1003020780c0030744c909000305803078040c00900700101b10070607101100e0400c0050080b008020720319110265000702c4041c010352501088148c0d01c0b040490846440d1104d46070319403034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 972226052 1250 972224802 972224809
    0x2101106061009050f132307110a0b060f1327050c0f010c050106120b060d0c140d0c290319091103010f0e06072a06060f060f030605 58
    0xe0700c00441c02040704507008200074170b080b21150f1003140014054004c002d0610120340c00b912460f0500c00410b812001148894034100309400760321020f240b40c9442c0554400c418992101070000c4003030900c1220000107039258071562103035001c03008007a100c1503aa105210300000203000610740c00400c10a80c0200300320903010102c0382108641c2000251071964005800c2058903428400d50b18184a000a00400403070b81c06c2c40f44000900d07480700c0710aa510309a28251001c440300030001803141c0c01c6035000e030700802d060301c500900b0b6517440000c1c8924800c1c1701c40051560321008100420f500303003007000494841d840c0300d4600307202615099000740c019a0014091403c0c041142c0e04030070000c440000220204458000e03010b040d00402c10301861806210110303095494204410b440c41d521605c1d42d643c00d42c4104016a0b2107a02403600b2030700c00039071168010340e400208084884040300c1144d00c4060007140da1080c0c0081034003050364802142c0e0f5901c081d002c020311350b5813400424580540000d40d0308 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 972227302 1250 972226052 972226069
    0x80603030c03040e0703330b0c030d1d160f0603020a021005040606091a0a09060f0b0304080d09031e09060e0d240f0e01110f03040f0210110606 63
    0x420407000386040c1410000e100c0103c80000b0282810940c89140046e42d428203198030b10441020244c01181000205c4900f4210b44969484480401d01c200041048080040251680764039030210210310001904034152600c640d100555001d801111a004980315400505008554001140700c0d420740d958a0158100d004440c260f40160304030030a01148001e45c0d51105034001c0c0301e55800520755807221001c000b2514030121180000752149000e2842e032034428815402002091004d00445003085522004000c980c412244208004000700c1e007004108070644034494101c0304208081449801e000382410312803041640007440592407035a14502c204805c13016200251940c4a140d2906010b00042c1d10b00c0c07a100b03031908166001e0030355012480c10000e0f60148030355140420782000322401c42c412a514540d034050540e15002081d461240100b0a451421a244402d03a0b102c1d0b8641c04c00b028940e003409030007540500000104450075400914415a8445070b0003100c55550300c9000303101418 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 972228552 1250 972227302 972227317
    0x11b02010c0f030c081902010b0a0308041806180b33070503121018050405060411030a080c060a0b030606030a080c030f0c010c081303050d0b0103021204030305010608060303 76
    0x2440c501407510224051030020031442e8441e15008004075403036181c5116a40100d406c0000b0356503541d04103c8036941c24064032409501c02c86040c00341a00c1d40e621036801784642c0c40b074094083c041c81c0c0c0c10b00e6501d002d6400381000713001a1240f00c40c040d00090f4030400074840240001e2241da0611550f1411800f08184402042a0600d21084508601c20741c03450703542100c501112188000c1001d40e503545101c00003607001d02c181c803259440660909001c80c02c802010980780301d045141404200108a00240c1c0d07941003a001061040d1030800c0c070010034149829900050081d81c000103400788150400a041ca104107401d5204101c1c4104900400d0703154841914140d5241d404501e01c100496000350042908075019030032240f0300801c0c00c101150b141c10401d4039034001d035520414908166040b58a00b80c2c056148440c240d681000f5940150841c040c0221a91007a82c0e911158506640203a04640c80910900482c0350381745800d15009003d046c00340102000140700c000030944509000042d40c0e102c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 972229802 1250 972228552 972228557
    0x50603190f2730050304170d0914010e0c3d140f09040b04060906030b0414011e0f02070c140f030d0c02190e0103080c060c040f0e04062009011b0201 65
    0x703c0c00742d042151940c1024005070b032088070002910b0498400c1000425041c0700d00380717000c1400404d42c00c090301c10440300f601803c0b0302c3c1d0524080340e00104010907a03118440c0d0490b91502e21480c00e06120340000e41110180508210080c0044080d04001004514dd69001e44c0d540150011a801408260242d0450030704564028004c2080a113003503007046890070001740001440742d581d2201e40e015644160f0090300e0100600c424081071200e145101402c4600b0b8034001d00c1400347c0c4024146200c0c0304100e610300e5055462410f00d0391000a034046801d0381c0d030000d080c440700d181c03111000542c6a07411500103100d070703007528490002403c0100b440c0c5143c001c1b03a103500e10b281e40c0e25000d101c14414150a41d0401540302c52011440c81c050000803406540280c2030f0075140c40c09405242d1504002508007204c0482c00d004c1042860401801c0c0025203920306941c1e6802c0e21146440c10240c60348012400003191000400c1e45040504000b400c0009800d80c0c82c0304214410114844515688140c082d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 972231052 1250 972229802 972229883
    0x91c052d0d14070f0215130302031501143309190806010909290f01090504050709021b010504080c0d0c020d060e120705030310050603190f27 62
    0xb03d2138010844001074000740c00300c4040c1000e6040c580b401d1f44954a42c01e80c10589410034001d60a00704402200003d44078004c0c0362550400c40ba00c030090b07044980c00d034843c02003104081c10509064414000c1340c03130920024440800b4011510260b500004401ca0181441800810120440e09140700846401c0800344c4040e9003001d130140042e11280c80d0507035006059481c5904e500102029004c6041150459098070741000c003266003a80f01c1c10f80c0800315403070521040c040400c10200d0301000b2240e45010050303036a251031030140070852001d50055455480c01d0b0070003081c0301081e001441988074503001d031820203200c41c0b0250f900e442011710103034014641e45109000a4400da1081503d003000707004540042001200007600f81d840020110b41b107401c040b00303000c0c40d00e4042c0e40c0200074120444800342181f808442000700034001d64081c0c3c080c10b41318142e420b4810340560120020b20070441f0342a02c14024411140c8004040c0c100494402c4c407020280e207643c42800341ca03c0c488101c9801c4080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 972232302 1250 972231052 972231067
    0x151206060a02070b030c030601091706190621030201050a0c08012d0603060510140d2004240c0f0f08160605071103091c052d0d14 57
    0x1459800c240c1da44000d40c03085080c08541150380f080a14850421480a59074901e0b080c0001000350f407080c0e000c405460007585200390544008917206034041400803c13148404003244401c0098103055100c0403040c003481c1200c400b80450380d0540320041c0e01903002071102c1c1e00c460030040d04031008451182c00040d840d000511000ca400300c02c00303620105444031400319411102040004204980c400720119660386010405820880346140c20400141481c001c860340c480034081c43c51240a0156000740e0b40c84084035604408880820341600c0000ca42c242c6503902c03420ba009000c2c0c40b030500340641d0b010328810200c0a41c800c40384c8003070982c0d100f1003038002c40b96503586898010303400c01801c56004505004811030b45164107500b4018a01400300414141420301d0041c0440c0070360502d00149400400c5000c0d0903464041440e40c840c001c200510b01c0650103030034171a04000c01c0880800440c5248050340e45401110503030668036401001c1512007400781c05809035108903000003100784080050000c2b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 972233552 1250 972232302 972232309
    0x230c1213050f0c03071a07050708030c01060b18060313060c0309050c37050910290405060913090804060f0203190806041b1e111c0c0b01060e151206 65
    0x1d054101e15810b041c1480c03d203903a2103080961a0300582b10540c404101280481e401340030f0fa00090613901c03a0580b5148030038101000b8000320038640ba00030000000803803101c0703001c50f500c480310681001c0100b0480702d007410020b002e0045498240c1c2c4600c540c490100c940d00c0c2070000d003500c8424a80c0c505100c6801c1c0c440189010b210358809a040e0009010001020703121500c03c2449144e80c00c0c2e00144440c106610341c603012003114801207103500e030004003a40400d18442241e003a02e4044500d02d48854513440060076030518800d4010805023456190001c000054000d8000c2d5032075602c0301030b1403013a0a14100d17034034040c0300110340060440882480300b5502589040c2c0c0c011902400c0131500c801107501001080b074502000c540000c240c2c44e07200580300c0381151061880343c080d18058080c881c40c0881f071035950014031800708800242d680f070514102c2c002c0841000030307580083e003906190b9541e4000350400c6824814603001d59508070451110300d004008a4001c19058070054005440d84001e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 972234802 1250 972233552 972233579
    0xb0301140112060803070309090e070302130b2706031f020a0905102d050d3204060b0409150b150d1509230c1213050f0c0307 55
    0x441c18010380d10700c419078418003402070348050407002000350b07510809850002c0c003107480350b4443c03046946403420882c004c180100e2141d045940449440c40c450380c0c2c5022800052016960199110030a0302c10542c90000440031103000310343c6202c040c84165210780a160b294500c02d41d611158084090f40c1d40403440341d550142c150450189052100e003500d4a0102c4d000c00c00c2c00700e08002040020030100b8100509840c0c004091502e00c0050741c0a03003290001514034025151103002c4107448440100b54407814240303008912106007c03041c284030070707900d030100342500a0758242d40180c01c4c1030030754040d4100386c0600d04042d54041003006c0c1700300f01c0c4e6104800502d03440d4441907010300444054920350350300c04041e10b240c0841100008845900d0300c07600140500c5c40d4000e44d0b00505212549000b48076031142c1c0300010440850b001525034840e0300814052003583c6028056142c0841070000c80c0c04583c20b880b03003070b6108500b224020410403450039030700e1840189290b815031107644180b11105000c5113 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 972236052 1250 972234802 972234839
    0x18150c1e05061812040303120f0e0c0d080903061f0e041109100801020c250302060316090b040608010305010c210e0a0c0611070e16050a110a050c1302040b0301 70
    0x25a2000b2034100307100c2d461503016034010f0300003400c0034844104003601845601200d0044009c10400271080203401600c411003500840e20a1044000340303400e00c000e01d000c81e2064140141520003600d4400c0c0c1c070a45920850340c01c407400400e800000b282d02000c48102a0140c2e4002c4242501103200c5801c101c040440102058803c2c0030304500001c0312038090015114911003103003e8a072036181d0060505190840c00c82096030120290303020000350321041e00710f0303820104081004880c200042c4003560810f6059201c0d00c545d200009002580c5580840b160341640d200388028403580440010490395111800b607180c0001c180c038052a4202c405d82c0e0320041c000081d144c1a0303001c814241c3c8824101c192581c0c00a00030406007101810300c601c0c00e2006e58054070113007000303803400c0c1416460044808203c44045090020000c0c2d10f91102e0701829580d402c8456441c219156104249016034803424817000315401541c4844402c003083c07000303009646c15118000a83c9045030f10300050440070306031008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 972237302 1250 972236052 972236101
    0x1b05010b04290307050d03050c0f101514100e150d060e09030c032703010f14090f060f0a060b03070c0201080a09050d18150c1e0506 58
    0x12441403803a1240d01500e00c00b0012144040a042002c0302d03854494030100880a20a40080304140700710b07a600f5807100c03070641c0c1600c0d1568a410b0508038583c42d25000701d503503100520907107102c80c2d0650320304e4204c5203c2507030100e84121155911491003002c11240000740398040c5c024510740078072071301c10391008803211402130044210b0100039240c1002031b070201070b024208070b85071001031096005120b07410760030000b8100103520707000e81155030036200d0117441c03034011011800d5003141d54000d10a030340213070000700300600801c080350907854404002e0807011080798100d003407000011a513910100340e42e074010030020090b1056a0301d8600080001400800280300036903038040100c0d10341d91a401451062050780c07034800b1150014000580402401000309004500741242c44001500100d843c0e195104a0708003100a070107004024041042142c100c545004400c881c2080781c26803012400c083c1600a012003603850012510040041c83d40d2400944298450700205000010440c490342ca14600703079 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 972238552 1250 972237302 972237311
    0x801061b0525140108040b0a021305150304140303070f110f030c03070302060a110a030207054b0d05220e0420011b03030906181407061b0501 62
    0x4481e0ba03140c62030400c03a03681200d903004280b226030210840e1020030320302420084028038040c5d8400300c0210303008111100482e0045860301d0b40240c20041440580801030400c42901a0310452507440e40007118142d4003d840c500380640142d0001c0102c901414980d030369080741e00c0c400042a281a50580c0281d891403180030289c000442d002e0024080d0b0408140c0a1541e035001410000e28082014000d21445458450700034000b4002400319018140c8505016854000303a00300325040c50304a001050201d03255501d241403800c404803000000040c03051340201c48603030b0742c1c0106c08400b502210110941c3c0c011740c00c2c2d599203070091020381039000205010021a2146030500740e0307607807000d42c46a1520300180e402c0c04104800320140d105404011030f400208000f000c030000b8421603540c4000200e4007509031910050520071f4000d010442d801450038400c9440d803120500e0200c2d110f040680d04000c120f500403000120100307040c0111651669811034010300281e65004110901c1c0c422075596596 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 972239802 1250 972238552 972238573
    0x60a0911060c120f12010603060506040501080703020904090b0613021305011404080102040303020d08011706150109030501050408030601020c0306010e19060801050f220b0a020705070e13060b010801061b05 90
    0x15000281399200680e5075480e240c0e44507900e081d0200070181c00c100c0c07c3c1410a0014426501c5000569080300d50920f803681d0b00d9258150280e00a20a1b4050503802600303010b4403c09010324071281c1e900a40303003a15100314134241c10b002d8104900400340c003039003100300d9942c2c01c1100f58454480840a151055015403030190341c0d480301800ca03403050384201e0150b00080880800d40350042100741c01042612124142e000c2c50f5614a6160100201400d060b1010307080002d1049e4447c0303004101856000000f00158101f07810680c203150012518503006116003c5151564100440e485040f1800d102d06d2a0882e218580510103e0340c212000340721140d034400000540a2007401201d010706450310380e070b07c480e00b841c0d2562410000c45c564080880c02041d10424005100c074110541c0c0101c070810016100d90755403410a0500940794414010394081405000c1c0c0070b408202c903a0104d40c8580020000720030100015100e4a000b480341d403020815000c41c1b0030410b102f5000d030703000e000d1182040c0c4107010302 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 972241052 1250 972239802 972239833
    0x20d271e051305010f060905100327060b2115040303090606061709030f1b16061805030a08040e101707090f110f0c01090b0109050603060a0911060c 65
    0x100c0350b10380d514443e03d40c001040803980324a111006882d1618194611030308182c046001c0c03e0003200200101555694250424800921140c843c0e00940c01507004544440c200500505031010711140b24082400c41c610440d9aa8031703000c88441c0241004d0111400c281d48912040c0400030016000d0503205c011138400100c4610480300038001a4803035100c0403e40301c2c203040c02410010710f90841c541c002c0145104044481c0e00340d6550100c4c00c03243ca00a5200390000a00344bd20046005401c4406101b01265554005080e060340c02070910300250420358900815607907051a102c0074080075800c00040c0113680012001c1c0b0360100360100c240e8a081d542d4a498648800552000c84d150380220905100d2090540a801c408821100b41801411403010900c002d500c13522649052600e03000030400b07514a0f00b03410000004d500450300188075a5240ca810001e04012504284240110380015900002620800050b240c000c0c980d409018284410700c9004d602520130402030b4403c60300851860103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 972242302 1250 972241052 972241069
    0x70611120412030f0305071e050c01051e1e16030e07080d0e060702091f0b0d0204050a0e04120e0301090f0f030e010f050307030c030605030d020d271e05 67
    0x72180b00030b1140000c0c0d0a000b03040304d403084145020581400d0500010aa00029502c403080a00c144c0c50700a40a4490aa40d01e11541c043c40209500300000c006503940e0a02107801000d810203584052030750762070001c28420070042c0f1800c0301c0145020204905000d20b640c4d81c44030b40310358140000c2580407405820300e4148a07074044c2c0703041d44c010070b0140b01040d80b0400d810803180e82620114200940c0b54005403202400401c01089000514210100340c400d0401c260000d111500038107954040444480c00a9032090041e140640b5600b28001410509240710b11300c21500111b40d00005903030010225100300300d08000d1a415900c42d152071000c0394130705000382d015500c14850101140c40b185409465036400c011003c0c140811520100e520b90780203c1125031091040c40d0014580d114003006a00070611034000a8140c412000800c1c45290000f8000c0c46c1a025621030b115864141418032882200d1005801d00740040d040c410440401e03402e0703002800240c240b1590a410780c0701c01c0801d00c650b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 972243552 1250 972242302 972242309
    0x8030f0d1d0703061a030a060c020a08070b04050613050d0311091903210c030e1804030806130501120f152313031b0309051002011a030606030706111204 67
    0x5802090b4204100b004030b2150b424017080c0b40102124072110300c03000940322088000c000c3c11240d2982d0104140c10f109001d403811180d030041015032602c142d4100364003c404112011280d0b44103040109000319000302c10301c200703981d1040041004080f44102203000e01441090404500e900307000b04200c0da604d1844e03603600304c0002d4586054003455030a0440a0001c011a00c0300c9085009030b90700d5105d41d00060f02441c0c1c0d6018201551030411810209a0301917140c1c5203401815184002d010030107034051121130040c01c085810f000b10114501c510400c8074000e201301420b405d1002c07114800a00c10f0360b07055030040d0090381906202d603400c160705415500005040c1602541062044450560304403160350419281c4805110340c50003603030080e0451403074803900a50003420000b02010944143da421010300005020dd0302016000d03c4064003030031a1003180c6401c405c088201201a00b230015249100703c03001402080420f142c040290b43c80c51520b400500799019010a00070008812001003009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 972244802 1250 972243552 972243611
    0x52b0f08041502010506040b010c2010090302190f051002120d020703020d0203071e060b0a090515042c070b0c1011070b0402090709180e060c0408030f0d 67
    0x80c02c03034005000307086030700040080384a01e182010500a590740008031141c0d05900150b20340700010f00c219154408a00e0320003c0d6071210003520001d01c0e01d03134000407110440c1d10aa5120480c111350044007000c40c29240039140d08140901c0c003c209520709400d84c4400c100343d0703005a42c024110842c5a1b80c5036032041d540701301d10640000e050010140d0401071503042250f140301450406102c1d5171031440e505881c0170340d000d102001d4500740017031050590000040300c01c002c0a0b00700480d83c0d039041001800088400760f0340c0c0200704400c03182c0d41c00c01e4041e00c0100b41c0d0320010501da4060303010000810380100654602d003031081c604085a001c00b410021310071400014000d0110900c5001020709079454110000c1980205025180003da84101c6454001d41d0440300840507907104d050440382074825600400b411f904407031031039413096200e0b8800c0700c1caa1110000e41e4455030700c11804001500c5580308400301d95200300300313a508044902014081001723101c08003103020881d56040e0007020800d145510380c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 972246052 1250 972244802 972244829
    0x30203070b070b06040207080f0c070e06030102090f0d0c0519150f02030304030f050c01060f17010902030d08060a030b0a05071106010b120c1e070507052b0f0804 71
    0x154542008410300402601d91003900d44030300b65a41610882000d031031240115004039500d02000031407800d9501070544250082c2d01c4206881e04141d45501302e10900c4480c0841502107806402e0600032104000c601034465047c86500c0420702c0200b0402000075188900c0541c000300d03250740c6003400748802000c80380c1a08202400e086249000038803180e9450144603500c501e0441650b00801925402501400c1c288901c50001c0003e07140c520455984000e203518206e00440e00ca66024054400d41702840140b0400e2038401070300070301700c68038418044d505601c14800380c001c1a22a118190b4410409800c0e019403699030b640314400d40000365040c21003180c0300c9080020140c0e2042d90310215a00fa080180501c1d450b050404549203d980c2041c54810405000180c0344401d0380215104034141c1c0b4581094003000c0c09103910307650400141150303140a003110001c0c0d54035002c0071021103a500c00709110542c0d102c00d10041112001440c0032203000f101d0300705400209101d070740580020b10013020090f4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 972247302 1250 972246052 972246059
    0xc030b0f0f150108010b07020a091d10020f030c13081e100b0120031303050a050d05040308040b160212160f1d190c033204081602130501 60
    0x440040010601e40e00058044072079603543e81e20000075811180741c03040a07540c0711400c5c000701e07400d2080c40d0403400c00706081030f1107484080004060b5140720102c1c1d100f641c090119031841a0300760702c9075541d2400510804c1c4045024100391304020011300600d40c02207203007113584141250030125010401104807101c4507204c2041081400628270451840380104401c840e0140041c0018001e0828941130f0301d10401074080c140010030440340358444207086020007650364039080356101d405c2c80084849018a12154031107600481c25201a25841607200e428a800c0c00600c5859070000d5017043e102c010140030f02005a1100c5004110711007a200c0584844040e281403040d40d61991350040303110039448102081202d50350602211403000e841e5004143c0c0e280c0300c0c040b01c140f0310030300c8401c2c1e00540390010030030700282c00d503004e140310350305140319942d03a00560301410643c0c1d400c03403220900b414020030002d00094102d0004181d00c220314084090100700580100c1d204920003000701c1c0e0125910700062 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 972248552 1250 972247302 972247321
    0x50c060103081c02131802070c150f1805011209121215050102031206041508031306050307170a1d01060e01090b0607140705040f0f0c0f09030308040c030b0f 69
    0x34a11081003e0190302e0101c035440c070543c04456a1003588400c24441101102c4985640c044400c1d050b00020003485e111b448143c80c10040701d040b8a03010100301005e0400803402e0042d1743c1c14120306464541d51000a241c1b00040d22030b241c0130748035040c80503522a807040010340e4000d01c090140000b5941d1421112080786010b0403107002044044401444100400082c1c0c2d0020403601c1c20603815840c0005621054049400740c803158580c2e020b58500640041403880000004e0040041c1764006441110340d910400ea40d28401500c440e000280c868540d8075100500b0315072075030448034507100050116100d9244011200407c81d2450391130751a00380c200000c0103030f05800ca0140c03440c4c21003007140c5015400010b001e0b00c148000140241c0100d1440b03410000305005820003060302500034008011102038280041c24000b640da4006858001220b040720300c90009545510761603100c010b51141103840c20784035404020000c81d03910343c8484000c00081c02070081c140c01541075201d010706a00b440d4910 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 972249802 1250 972248552 972248587
    0x1081303121803031113030206090a0b1c060911030c0c0c060c0f120f09130609090b06090702072603040f06032c03030411030c0316080f06010f090b01050c06010308 72
    0x5250b01c4c0009100c91a040c038101959542100c0c8e0403600e043c0e4401c07420021402800c000c0c1c0c401e27403c003400414202d502407030584061014020041003000195110100002150030410340d07030030300380024400180b00c0a8148001c00d20700c5540021100520301d0740002500030390041540500d941c000c030b4000070350780030308020702e605855458400a06019114032410510300808800501c00c41e0b26148400d175000c090f92018000d0081010280883c402500b016103e000c1b00740c43d02d42c040c80007103001803080340c4040b81007410798210381c80c160080008210f10200ca0048412050040c2c0130030040000c00b10707030300000c107801000c260300e0203d10300205159050341c681c5c0c00e41c5843ca10043c01d4490a181000210407258031983c842030003000b15030b40307001085ca846102c2c021f45816200b0b0607220407031141e001d0184c208a40c041c0c4119010b100c04c80f02a640c0f6094207220b40c00b02104200c405002061554000020f03003e410302d0042e0902103440d210f5484c0401c2a40180c9200c0350003e030008026100640 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 972251052 1250 972249802 972249821
    0x319110c0706090b0a0509010c05010c0306140103450f050705011b0206031314072d23090420060a02030a08072312090c0108130312180303 61
    0x500e0f40c080d07458180c00e240c0621591500d9000c2050009003031203581e0164184000d01c0760000005c0222005010340079004010900484824001002e0320500640c4240180803a40e01600d4221015184000a512420039000c0b004109600c403d1000d6041003814490400150302074034400d890f100e04d0382446401c0c14070a801c098104044012240d040c140c12a1012240e103a041e9000b680e00e0b5109584003c840d92810300003400721618080c4210303900c90025044054420701c030b2508134654001405442001810000070400e100c110400700045c03100c502c0025081c82221809095907131400c4001040c0d580202e908850384002c200c0c1d000c44202c403a030b800100300101070703d03e81d15062007280040c0d502d0148401c039004008003540055805407007540c2001501e070b0980000b0100110349816803240f40c00c01c04003a100c1100f030a00003518691700080000400506840d0340342e044d02d030b041c690510107403400c1c01603082c4645829070301c000d03e401e0b01c00c18180d443c3d20800082c0ca00028a001030940f1840304 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 972252302 1250 972251052 972251057
    0x1115160302011d1501061110020d09020306010f300b041a07020d05070b090a02030106270b0607080a0302090a26060f0a0902013501080a03050d020319110c0706 70
    0x103103009140d640d1202840c5c15180c1030b0805a42c18201544ca06180619415002c00554004221200140c00304e4001c00441c3e4401c60554000e680c890312a0200c490191040a107070004020400b5101c030003486240c000c0c42803200384644502d07c0f684901c400040144c030116000c0c801900c001040d5000544825045180d6102a1100c0111440010030b58040d00c2c1000d80710b0803201d0041000e46600304044800c05038060000d00840350707140084024103407042069919011604200881150544641040a80c0061206040c0401c40e101c03a000f54200783ea840d014103030300f081084856a18444100003d1000ba052850070203400030094498500c0a40080c000340d000344d0a100f003101490750055403010100300000b6110269000403985000d00c800c040d5800c51a0303030442d40106480302e0701c1d801260b9040040900d1641d07902c603000d95640c4409005400100144000484200350303400540d000000218100c040801559404040b20701d03d12a6050342e00d0005082c002004090000318002c08850 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 972253552 1250 972252302 972252313
    0xc0e070504120b0619080610050301230403050d110a0f260924010e060303070b0f0a0e0f0703060e07031e030c05060108160b071115160302011d 63
    0x828008032040340d100010500d510003400200c2036112800380c00f5200b85d61402d8102c0556980807403d1701c41c0720039940c4000c0104444000706903402c0500072a00281ca499180c40001c44200d4046120507001400440802c8030070020103003030f8022400750300e003514800c00b4460f540b0040c090004d061103030102020414007a880000d25000c08502e0300740310f807e2121b03010520711a503d0075690fa050180056003d0b1520030745c904500b03030501901c48680c0c103036005008a4030150710742a041690300d000c0e0500c01092203002e0300001c1d0b1840b50903421a60890175800010950071846c4171801d080030020840745490764454142001400800d000b51820101c01d08083d100040c03d544408131325000c420000301068807201a03200c10107100b1104c20401721b8010043d04c041d03585604132503455007480800c90522000080001c0354040d1003008807803c0c01d5001402c05000001c01041c00072007c0607403c5104036213414040a0042c441c1c100800c01c4080c4a83d000203511340c90003030b04022035000180d051000d42e200703 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 972254802 1250 972253552 972253559
    0x1801020712081603021e0601030515090a20131e02030108150c0919030b0a061d07020a0611040e090105060d150b0406120204050a0b03060a021804090c0e070504 70
    0x38034084610300c00c0300c0c04032202250f8a504003a4600981002c1640d0700e500e1075000203400e40030104000303045c0d034801d505a845644240040c4c6494038402e0320040c2c0150020951080021030049c00903c42c0341408080d549442d81950014801c40d81d8404030a8826480302c80f01c903c81c0c0303006902444d000100074002c60455041800c0d050366120fa50041b01a1ba40041000c9015403e150707050b2b07450b46c20300130901c041080e051207110018811a120440380141042d02099010f13026000d41c0c0d059070020640220701880c001101c0100c034001801c0e400a50080103070381400709150b401414000d070469415195204d00c3c0c0301000f40040d40040c00803c159250500b405800c0d919601804400b5411030000e100700c808031079074035000b0b040070b24000703074403d14241c1c0000300c012030780b000c0c1e01c4214000c6038200000d40d1540500350a03030f2000c07401194140c11400000b81039869550207807104540b443c602d03102c040c0405000c241122400b9600303603020044a03030100015181150300d190311111070b01c1c0c00360400d441c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 972256052 1250 972254802 972254813
    0xc07050c0a121e0809041e0219020d05031e0415050903041a04151808030408010c0f08060f24031f1e05043c0b0a080606091b1801020712 60
    0x1703021000351003551100000c0d6001c01d4a10030700071001c818090215070300d25108244a1028503880c40d0200940501c1c0807c020f00e07409802900d1140340c58140c550a4507240700804481040c00500031182403640b483d0802c0e28028a200d883d20071800740d0001c503903aa0800d0625041d40018684140b66042c0422052010341c1520b40c0c909541036990402e00000c405100030303421091299040150184004540001d00800540141d164941d5589890300e50440c1c0200032240503104032055a0050024801841e4a0401c501c040c3d103c10000207440c0c541d00c026190041c0d43c0d6005039050401650000c46100585180034000c00081c41005000c2c2100040d07880c4443e4500c0b054441e15109070303940c4158030302c042c003044221204407c244c174242c0e405003246200108040070036500c6448151070580c04500b07905107429030700305460b80303040240343d02d0361134204200b00148010249105541c4080a0074030121260b800392035003850081184a5000000c40020f01d02107081d80016000302014030003201080d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 972257302 1250 972256052 972256057
    0xb03041e140c1906051e0405130f0606030228140d1a04020307141602090c0a0e030c0f1e040603080a0f02030a140d0603080d0207140c090c07050c0a121e08 68
    0xc1c1718103414600c008032520007003034080c0d0341c080c6030000d12400349c100701c02180b5480783d02048145502000401c2d20350f18100d0803401380406818007001c04508007030340318110510302d044040103171510902072004403520500c1a000b12a8110074142c03102ca141014580ca400d440d5211002598114298580550300419104004074040404080000c10b0522103400d00c041583d03194000c0c10140389424070501b0411954000c4800900280c0c0b840c856845900c1c02003154045aa40101800401c80c544000c010400059040181d5038500c1c5000000e11501d60f801808002d5009015a0b0746642e0000c0024013501503a030085011904104001d110003a003000b161365001c2180070425440b020000802801400c0030b0b04081c125040106030800b00c5e21241d00204800d501c20100c014000c1c05000c080d960301c1002d12a550352094282e000640d17001c101c1000ba1040301c0c064400c440e071240862021560700ca005410a15410175814030a5041c0310300b403400804140003141080000c0c4c40103480b00b00c03050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 972258552 1250 972257302 972257317
    0x3031302120f0a14190309050f0112060e04020909010905071203170108031c0e030301061110061202010801060e0f06030c0f160317010b03041e140c190605 68
    0x2000d14a9090020000c00c11580100034181400c40f003021015040080d50591014242c50341403083c00c096540700201c0f13150054416a040e1a03060060342004100000b2106514259040001d503c2d080da070310205074001e980050402c2848100c0608080c014050101e00051a010840e07040020b400002840000c000e01190000c4c00d81e420080e0442c035044525610135004070301417214020001c10300705c0300800145202143d0401082c405103041200c402500d01d8210703400794a4100307100403c03c00c1d0265844000911640c0c040d10a02a0742e80d040d01c0c110b807610340181e0b03a50321041c45c18408650300810050701503c030130704000042281501c000750a0500407009240181404000706030051030040a03a0001e1000c0001d5684903031441c038500f211040e107590181c00180000b0303040402e1405604e0854140c03003c3da0ad603280323903503120340700c11f1035500c2d0034401c49130380321030f02c0d140f40e4041407030940320b501e540445c907000e00491036002040060300c100e149841114050314480c10004c050b040700803903841 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 972259802 1250 972258552 972258559
    0xf1205060403050f0c03030a050f010f06120e070312030507120b0d060f0b28060e09130c050a060315060e1806030c100f0f0305060d020d171603090803031302 69
    0x44d400b0129804a40d40503060301c1e00150320011050020015540c0c003c00d115400c11010004543c0e41e50030010f000d19014030a200c0810295910490300540f107801050a039409a070484503040d07070325076613280c01d030081d4410000003954840030f00c08017550004002c0218010010144062290040000c0103820300c201d0007450996924440b0800707840d990001c071311600300108000c0403a925006044c03403d00c4e10221040d02030098040108440e409510b0030090303200041d1000109580300c500040004640c00b0301501e11203c2d410300080c41d56a64001c40c0301400569602240a144c2c1d61500c030a01c41c16500312000703004a5450340b071030ba80c440b004608444150034098004940707540d00442d0034038682513110354102941900c51110396030481d80c820780007460341d51905100103441790b0440403a030040d649a50b00c603c811511001520344410200c2003207004088804c210103501e07543c00c035103602041c10781d807001d90000000000d040e003000b02107000748a03c07005180f440c0b07000308544082c1c242c075001c001e20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 972261052 1250 972259802 972259807
    0x171501120203060f04050106020a2102060105091906090615020a02063c091c0c0312031506020706020111041d1902271f03020306041808040f120506040305 68
    0x890341c2d580013900366032a0b001e0b000b000a5610741034000e4441a04602c01d6860420020400381020f0f020104804d44a140b0340c00b818407a400e003010402c3c1301d08003a103510000c44204034480b040580d01c1c427a00f001001c030040001400c80c9894014000700e81000204015904518200d0000d0303120b5908071411a504a841c0812076a0b0030520010060484080d142c5003a600c0c0e0410b4030f03403034804c0e00103000908003113030410f500c04c15440c003a1001343d094078001880040b455108000181000d403040c842103c66040101d15041d410307488454011042e4011001a40404004c0246640a200e0b0103c121b540c001c0e024500f41c149508a0340001d1b43c4000b420141440100040c101d005030f400400b00140d600f2400d43d03640d070002003000320325088202810040b0000d429800c003540740c99180c1c2c204a010802c2d01031a00c3c41d00786400d074001e410050085800c5511418015030900b00660300301c8510384141840c54480d420a0794024803403215802c8101076107548282d842c042000003544651040c2c0c14589150b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 972262302 1250 972261052 972261061
    0x80712081015020705011103120f0103061416050906070f030c0c1508041202031603080a0f1a0f011b051e0303040804030803040c09050c0c0c03010b0a05091f06171501120203 76
    0x38554840d910f0740c1d810494049d020f10401155003941941200c2c083c000c00c1c403500d03c000b0381c0c0c1164034506941b20310106107900d808005541c0110054100100000e004e5410107003140c4401c43c1d0345010300000c50000325480000010010f49184103000b800380e050101c0c09012040b04003600440c00908040c0a00c4980548036560318820402ca4080a9001504050303468403450040e0180c6030641d901c240340c03400c040e09008122103030301c81c200b60300b00040c0c01407076981d2140d8240000754002c82c413803904100401c0460240078415141070f0000d02d1090008081d07600d2101855803038001d070b1030890308081d0000c00902000c9540c030019541606e4100000c966130f911a0b107840c024156040e400341000a051a08000039082c9542c0a00303290fa404038141d034200c40040d400c1600720380d0480d522a0303028251807401d0103a400d041408035440f91900701003c0e030040000b04050800200c0b54000d0000070721745001d01d10700d8548074040c00d400c0300c902084a00308007030400020341818052164028103d90120014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 972263552 1250 972262302 972262337
    0x1d0a0305030606040801060e01180203070504051903020402220e0103020109170f0615010e09061c03141306180f0303081f030308010f060c050c0402030408071208101502070501 77
    0x218005c1c10000004c200c0750b40d40351140e5802840c2482aa0705085040e80305100606403402101d00c80d192030741d01e080c03400b41404204003210400148024206420720703800700040c2c48500c020010b45290880d12000b80601c80f00a0b504044280c001c2e11015800c0307001080142d0700302d0200b50580e403180c0800320f018200d09181c10700c0c101b580c051059051144000b0300c004424120310030304c0c04500530780e9081e0f80040c0b40e500784446070405481c1184c10041803060446036141074014030513503e12900d442501d1640d010714102c940d40000c0513405041000603420480d803500b080e40d003000404a19000840d96192480041c205500c0f4071024007802002c8001508551251003041222500c40686c001969100e040041400d40e00b406104200c03072241c040441c00d42d01802402080307a0f807000c002c5c040040840306000180d04041c4c0200d80000c0305004120028080f0503c0704015003075650390807007600e41503103014482d10780d580c1715060f00c040c00a484410705034041540320940c0c0c02030070900700c0824050701c03d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 972264802 1250 972263552 972263557
    0x4090b0105041d060c070b070206090a110111010510140d05060703020d0b03030a030f200702100c020a12050c1012090318090e070504060e070f0302090603040b09011d0a0305030606 79
    0x840c2c05402c0c100403a001170722001d480d00c1c5001d001c0c0c0b007401c1e0750342a10a03681c1d01c1d029901202c8550099110400003400c4110280710b00c94103142c0146401c80b4650443d080d01e1003510484e0f00c0c141c2100c410300440c0401ca9041811b2030045411021100954603800e4413070740c0c040c0114081580006242441c11055000324224000240450341e4980f00510011300520819200800590400141c0c1c1100e05e045c0e0420103101880d01019490410326600704070014940c0528a010300924545820150750b480120100805128400d17540001180c03504070b00f0906060305140c419030300702141d07000380e6900900c60241586504d60016005c1c10300c1c141074491040402c007880f80b2201e550004514a80d40350001030301da070311141c11243d845849004201c1900d00e98090000c2041048000460091044007204e840c1c103111b040c01803900300d498020405543c412102900e8160b5590240907410000344500c103000c5005c00c0d520036404000160250b10760495040103820420044003203500c5648103000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 972266052 1250 972264802 972264851
    0xc15090c09132a03060b01080105030d1b1103060c0a0201051608040605060f03120403020a1203050a180b16032309010309020f10170c0406090e041b080102090f04090b010504 76
    0xa94243d4669034540003000e031003420398040c00502c4640001031107080014a40e451004651070b1803c0c8550b24400070110004c0791a000d50b4901ea2500035120151810301c1058050f81d40510f2040d90f4002c241c40190946001034001c08814003401d011039416680452400e400582c0640042041c1d00c8850009050065000132540d15004070134601600101000c0200204c03403003581c0c1c20810994540d40c030b5122000c7c1c8040500410b000300b102d500072621580b024184144c0b510302c1040c40030740b00c1405001540140c01d0f0701001d030200b207e06105054001001416041396004503105402800441030180d02500c1c0b4940c1c141500c07082c0c021f04540c0c2e640000c1e41204809400346940205189004201d9403048030415501a050804110868a048202c07070680307034603442c1e40304994503201008500c0707500104203a804d030f44041c505a00301c07000e4150300e000800b8010009a00e4003940c2c81040103511801c860b16108604d0055100009a4182000c0e41114411500000c50009940d1904000f001840 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 972267302 1250 972266052 972266123
    0x1207080606040f1b050d140402060708030405070e0108030a030e0303100b0d24140d0302071a070807050606040c0c0203060a18050703051b010e180c0c15090c0913 71
    0x9003512001944000940b445200d01c0c1014480d26003651286201d4280582340030750040420401c02c0e0110f1041801181c020b440340342290300c65540d0303207803801002c02c007170300300d5001c1e6000003072a20103e80d0300d40952107040c500500554a182014480e601c10350019104011040d08003080035503000c01d180e440110710042c41850500d0000314244002c1e0410104d0041c0d0820040c240442060350400380d9481d8440c59068008049690403c4420300ca803885050f501d050000040003403800190481c0701524130b0340c1c86940203001604040c0c042205650503000200204034803500501d002d6540020b040360418234443c0e00107041c000e070109034900039a004a002c1c24501c6581c1c00001044000280d8000424500041d850005140c01c01180c40303000b444401c0e0340c0b01407000f070b2040e04640c80740441908858220700c920314118201c035145003054001e50440d4a0400c101040165280051201c0c00040a044070b2031080c0d803801c0d6a2031048162040d0700605a003103c600c481002ca1480c10f03041c1015800203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 972268552 1250 972267302 972267341
    0x80a0b0607050c1c2a030f06020c151014030a050d0801031a0c0d0b041b021f05010b031f0504060b0315030601080309060a031b020c1207080606040f 65
    0x500b050756946034100d400c1030050f121003c5250501c411100c07140b108070340c054010140e09034520b080644185c4075040d00013580001810010026407402d192000b40d0748180ea0150300c4c3c070b034103048003410414940307400c00204045204001038100081c0c1020207032518140026200c50700140401d1034110447c40040c000d00c06c01031003480c03454103d80e4240c12288210182810000ca0003103442c508032095664088014091102c02c11035102a001005456030140c400039180d004081001d100480100e00fa00250b0040c21620070410040903000e004520707000024030840d49401201c15946c48010280800018490381c0f01840d603494840100c01060010024020a616243d00c2d0140360700990f40c60135400c101080304003181c103010a0480c12144040055800d01c00c0d01010302c225a40640d18403800c040d51100641031010000d004561a4047c5500604000503075000707000e00d074002011400007a501c43d0f80b042003a944005070f04e42e406a0103440110b80c0045403504c440c05480306911707049400a51 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 972269802 1250 972268552 972268567
    0xf0102120a1718120a0203071212050c04060906020a051914010f05060a1d0c0307031514010201290d0c0b0d0b010207090e210909160e0109060c03080a0b06 68
    0x43d04201c07007958a1800b91585400d5951043c0020701c2511100d0001d600140116000303d0b01c054818440011113042c200106201725455400b02c0d942251910b013803d0300402c041c02001d40c49110705019003141e00080c0350103155511000e1342d9071b203092811148180d0142910041060310114021b04681c0c0030300910001d002c2d51041409000111007150180c1e030b1218000400e001c0440d6071420b40d00a94010440c161641d40c100304140e0307c01000c1400b415161000b0304d416501c0b80380000c00916441c8110301e44412850002030940e201c610843c045103d8103038507104081120b14038100c448100300c8250000403498544108145d01540c0701002c110008508e142902070a070f0044203d4510907800c2d246009e48690b802c01c11500300100c0300000340d2122040710011080019403001103841e005607542400c008900141500b4012205001612500094520100c0c2c010141c0c154109090074040c80640c2003e00040180d0070303842002e030402464801007620307820b05a0042c1d008440151070b46554018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 972271052 1250 972269802 972269821
    0x10e1e0a15050309122802190f050706080415020a020a0c0e060a08010606051c0906061503180f0f020f09070903020108010905010e1b0c0115080c0f0102120a17 70
    0x104030b134420514096100f80d50303080b00c42502140e5150400300030170b00340e90f21040705a034101074011424000398072030900d00b042148110150300c01c800c2c3c800c00600c41c1c2c00c18240b5140341000000d500c60400d11910070140b0000030359203c40090290003866005803140c0380c12b00120f280005506e40600810001d400102c1c404030340c0701c0b82a200354400d0780e5680e000c550750503c3c02d00b22211780c0301d850300080c014482d00b00c94240300c0040364542001c1182c04a072000307450300c030320040742d00319030120050030645001c10344400d0f05401201500040000d01103144a019154801c4100050500a040c41c0003c659902190794403a41192154405443c0501c5840d003000c016203103408901040c0c0c08211100300000e55170090b80121416a80b0310b10840159403600300259419031410052201064018444200e20b84024420742c443c441c0308403c2018018540141141000000c002c194020180f04d644585143d03000a9602c441c00296900b01d580c17141c030550103c4100c284130b0150210000b61009100f032904e0f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 972272302 1250 972271052 972271057
    0x1d1f1515050c2e0525030e070f06030c0801080c0f06031e010b0c100513110a2315090d0201050c0109150507021c02060705130504020304060c0e010e1e0a1505 69
    0x24001c4070401054a80d0312030520402002c10040e0300541641c5c3c084248144250480914008040110ba0605482e5440145000116040350303001075070741c050010f8030079400200389005045110140080880341c001044280f2446080c1602032403001000c103a02c66116041c982440e08006294180355841e94030415155114070030b010140d118101c9910301c00d0010f4450980160210f0003102042500c554400c1754021320961000d030300c0040c2c4480065903510005400720b1202c001544035942c070300b0040410904090040341031130300240a000c0d0001c0c940f14940d44200c01502420002d890b590702d580d20038050301c05210020284041d403000592070301a0340e0041e500805981c0c007038075450440c2c0141c044501201910480050340040c0201d200c2c0c50081008120200b0366640d200748003501da0000c2010783c5d01c19901101c88680d9080d217103402c0b641c061080e150741c41007403030300c181d8940c412400100e0303050b0010680c010881d2209002d50065495021203c001c1004209800b0301003030404d00503180b038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 972273552 1250 972272302 972272383
    0xa060903080a060b030f07031122060309050309010804111c0b06040510090203150d080a02070e0601140c0309030105010314060c0901121d1f1515050c 66
    0x50000070228228100301c1c01284259000d00324854210f075202d2070181c0c0340c400050501c5c4140360b914000c98008604900041c10031050314400c440c0142c09a005404010341240e21000816160144400010b80003208a59000038240f90000080d01c490406807100c00c4a9209568001e082c29641031b865000700c00102c4e0707003501132281681a940c1c0c040a2100343c890841d00c070440180403003002c0c0b20342c55056001c0e40e00404803a00115a400d0b01c0c03030119191409009069540c90004203210382002d904121200291024040901c1c450a010700043d00e40345103070382054234100340420750b00ac001c0c0041082d00c041080050080c800c650796070501d040011400d417034025081c041c1c000003648800c0b20a00700c880c0080103a540c000041c10071850b0b031004004150300a141541d804800840061041003000e00038081900345201c0c014107007511004a641d500000e00c07844201d100c0c100300754202d604030100c0d031401d981426036980c0900400c4600308922421140c4050f45411002100130003002e00c010a1b8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 972274802 1250 972273552 972273557
    0xb03060115080103020d0611070b06030f0c03060121080f031b040302090403030b19090b0a0504050402060f0c1006120b090118060b01050904050a0c030507050f0403230a060903 77
    0x50398860048140c80c01c03049810301c0c04504864010001400c00e843d2440100e800f680c0005202d40c0344065600741e59106540540e890000c000c02e2100c6803030240b0981c130322410400002e0003050303a5800400c0d02c03800144140d480b031001404045003482c203030340f402c10301807588124255950303010304c2e00b4010140c00999000d62100f6210759562016010f250032941540d4000300032030b203103076503da6044015002c1610020f03000040c00080d0700700c03441c0c0c1d8040c0c1da001d031180300e1004c9241c0031660180110100302e036010500c82c80c14101030001585031001150240c1d803d017000144c0d941c030008001454940d84c030400c40c03101e03403815000040300740d91004c0e1081d411303210304009070160b11054040c0d4280c4114103401c5640c00c0c50781d0712510000703040e6441500c0b05101818840c4c100901040001d00b110412200b40b804180c803480c4007140b60fa41849065400619402d0541c00d100c1c030205e82251600071404000e0510105c030755244013600f4130003148080340655100b11002c04a84c0d107041d038081c100d412000c0b0702 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 972276052 1250 972274802 972274813
    0x1c021e0d09060e012304080313030507060e01090212070605030f041e031101050106142209021305130e0613030e060a0c23030909060409080403080408120310150e030f010b03 76
    0x4810300c545c83c10900a9801c40030190650f100c46e071390716017503d240c04400c8044c08003c10000d0001003c6004803040524050000166a481e900505c521912450b4000d14a50009002402170b95040000c2d0307a00f00b140c41e02ca444d2130342d440e40ba100100c6102e003a250a45a091500c00c4410036601c41180f8141801490083c86266664a4191001215660411103000d024003150306018085400c050a86108000f00146036640d50341c03020482e84042074407503820320840800d100908102c00405460f140b60a0204130b0000310020264036410003070310604d80c203401d100840c1c0925104a80c4200440c400601507980c400038618007818403441a1011100e01c2840002101d0b00d00f400325000c050130405801551910389543c08100c07664800400341fa03440360756412000085600d00003d00701451044298582e07803814a0b0000d49892200100d644410004008001c0b110001440040880e807401d17031018901070070ac4070103640a42d41c00104a802d031091008000707025a054100d24201f05080d4107455 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 972277302 1250 972276052 972276101
    0x60c080f0c10180c05010509030a06290f15070f0804090504030e011430100519060c02040b12060709061b1a090a171c021e0d09060e01 59
    0x83d40d2205140054640c20b010300342000035501a43c010000100010140c495070315581e0749102c12546a81c010645150082c0003061001c0c942188a88464000f124101a00f07000a40012403001c040c02e10400030040c04280e0004200640584202c0268405000c40c0c4441c3c0310180680100002c86d0160006030180e02081074550051440d44229001003151607e0a003400010400ca900c01c40d0352400c40005509000c00d8415410810300e0084801d9581c402c040392a101c10403082001040701141c40442c020403c01007160003100071014164103840220350721440c1000515803070000c0c10f12446500a6000f0400034503440341d201800d071602d40c0c07995140740c811844515401242d10740b00a219030200d12180c0c600004450700c0540c0032600034115442100c260740d407604400c2000c000710015100100c3c110b8850b014a150510003403040c54400c505040d000030303100440b40284800791a450800040041320341c142074000341040c0750800024020141d401c20924020803940c82841d140c0c000510711784 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 972278552 1250 972277302 972277331
    0xa03050319090945140d1701051302040e040b061c05062e060507061109010e040e070f0806061203120114010c0b0a050a05010807050109060c080f0c10 66
    0x11000c4e0a10111881041c50351500948500103800c003003281640b514600041d2101001e071326840070b1031045588002140c041c0070141d00d0301001401c584103000c94800d10154a40c51180d00904450080352640603405210101c81c2c000d10640d003000c114100e03d82d0820081c0210707003030054001c21007a02d0240c1c110300d008207220b91a401e8400300030140d412020109000101505080100e4011181c8140070104820307443c14051000303500140100304017003501c2c0107105440c450b01403540c501004042c070342403000000908190300300c1640c0340300b5541d540081150074001c12403a03002c0d08540c4000901c09444101d1284e0384c8a08503800c600c10035030354400b14503000001c002e032049900c000403c44996402e20702c2c1c203143c2c400f8483c8a28100080582440b01190344242c001d40034848001d00080d245c20307c50302a4080d510147c120181a80c0034120810187e6132004841c000c41c0d44a2400c801841d20707514024400344104001446410030110f400b034210740d004251110310540801c4100824480344110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 972279802 1250 972278552 972278561
    0x80d0e0901060e0d020a05100c060b0904150c090f090f050c13170109151a030d02030a11121201081b03060606160209070306081002070b150a030503190909 68
    0x2120b000610042180c180781c1440ba002c040301520040c20103507910b40720004070b05200d402140050000c1c000654460074400c2620640c0741e001020765040c030b017928154407000d80c445881c031f0048000ca070307070f0380b41d4041c0d2280f14206031405090807080101c107051b074131016400900b0009140c41d090358078010124950b40d80b40021581007001800790b0780c03045031400c1261314000c1809000c0c00455500e941490000490a850004c0c240242110018480c41d07004043e41ca55201581c1040c000d80c4034094100c00140c000003507c05040092500080d00c900b10040c03a800c100c03140082426942010503040c4440070050b031114161036450313007190091b0095900da240e5016258440300d4150300640f01151250070028010031044002401c0b89030f0b0068180e0124001d000102e8420740000e5489900740301c00c1c1f4003404110742940d040b010550900700c2a4035084e112401c080c201030500045045c200c0b5042c0c0b00d00d40403400031600710781070f281c41d182e030b4880800c0c1c04842c2040d40c40c001a4410008236860100b4440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 972281052 1250 972279802 972279809
    0xa05131506230313030c08120708100801020702090a0b040b0d05030c0d05130608151305060f04020903070e07110604031707110c090a0f1e050609010e13081201080d0e0901 75
    0x4d01100c1868151810f48100340041c0056841344002c1040f41c0c03200c0f110b0302c0c81c5402910141c0e00c0c00d0244c03404841000c801c4a40b5002040c0e03d0f4010480b81000d80d840180c0b41e6040744603481c00164402e2031000060007041c009141c65081242e030300c0c0c4102844404406001030100341c0c000d40f049603501900c03c46491143d040d5440b086841c1c8603007404443d01c41c3c00c200e54001c45010300b0307992032901c060020762101f0302a070002011580380c0c010080f080c1042e41540c0c01400b0151030035810008403000082c1c990310307140104845940044001008213205141c9075010403140425281c517402e050500034808244805031800c0031001501103034030720348a00005280c0241b540090030303030b032a040000c1100032031001c0e111420a075240c1d0004a24540c2c030341b1500000c41403c01c0003110808a5004e490282c43c03004059512030b410281c01044680b141c017000c164040c100c3c0a00c2010400b140c43c0c5a03000b80030308902c1100f03403014040040748050000030600b05400c0329441d880b41e48046c0b4000c001e00541c0901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 972282302 1250 972281052 972281071
    0x5060406050d080f0d050103150c0212040e190e0f01050c09060f1c0e0708100509070e180d1115160507020609030f0606011d0a051315062303 62
    0x6103603038081038003c4042c10a1500d070801c0c2c10b1074020040c00c0e0b01e0a40e20b0a80003900d40308610207455604401e184506803031190180007808924012254190743c83c02244541c11300014a0000501c109000c0412000110b24034442000241e0510811070f07900d81c00501c40c10070071740c03030000401c21420105094441c070b004001c1510b0701c1c108000301a524160480341d0340030100c00c04603103c452100598043d05e4182c10303000c8002c00140e40380031005407501c410410540301d9645000e013441312840020440324161104000c03000019100e00c4080d0303140c000c6d0403800708030500905d0040c02d0001c0d48183e0707002d07183c2e0035141200c110441c00801c0801031002034403001c03441070203c802c009003e8042c1c8003811040c3e000030201d42c1080400e0b8003290400034440c0c502031941c0c100204010140d030300074030300010941140d841c0c1c0340e400051402280300d645040c02070510070108002c110445030715075000100200000c00280300c000d03a64900c042d1107000f203110b0140748481c0303c85481c1c4108800d87d066904c1250000b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 972283552 1250 972282302 972282319
    0x507060c1110210f11031608091018030f020f0a02040c0e0a0803030a0e07060c06092405041e030e0609030708070605071b05090a0f0e0a150506040605 66
    0x8104084001454076407800d010103c9111a9002d10900b0701c8001c0f0401c02ca80071a41c5880900035804441c010320195501280c140280010080c03010400a00701c1480e08000b01c498640300c03645c41c41e00c104001403422150400000805030900c442c400240d1a1103031300e454900300741c0844142e80f500c2507803071070124075032000c0d001ea005071506800001c0344521908017499072651240109180c40300a401c007000c280d100009002d2002c0c0c00c0d00c1500d041844280c050007880c3d091560080c50040c0032a00079106130707120384408003440310200e4000241103071106506200b0b04003822400182408444c180e600c2c00b03c10008849100410141c450f00c26032555074800844013510400420b0b4001a41c0343e90141308004003c18008400c0290501a00180d240d40b070321201c1900c1e21328084018440d007500300c1155004c041042e612030001e00c40d0880344007800170900b07118000000e0003d0144501250f55440b8a0a40c00c050200c81581441d41d118014000c0c0001d580700402c5c00155015482210303000040c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 972284802 1250 972283552 972283583
    0x10804020f2e0c0c0b0a0512190903030c030b0f0609011101090f050a1b0e0c0a02011e14060d030c170405040908040e0906100501180803030f040507060c 67
    0x80340e030b4168200b030241d8000c1803141d00002201c0e4a40d110b0490085029003035034605000302c495072030300140300b51000180b900c2c0d4814402011406040040e0001100000110781002ea0890390349011001d086810001e09626007002000343c0a48504200803904c1d012100915003442d20384010003c0c1d010388024540706410b0011606801c4001c155030f6a5580c078100c02002501c0341510a54085c069001065100504e09101005d8104107003d40407145222504011126000042c680d1042170390001d66201c82c0151800d0b40580540c003800420403544002010190400b0750100c5c0c102c3c40b10700b10300c140e2665441b05102404020420250219100c03130407103000188001000440b906c4031550315030401d6501d802040c01d9418680701184d000d20301003001d10450602d000c6165004096800414003800c08014490b40b40840340225810003030071101c80203ca21070542200d004001c940300f101c0d030720f15065940142d2001d0a4a0440d268020b0040020301d4511440042d074000340c1000b1101900c501 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 972286052 1250 972284802 972284809
    0x3030e04060620030f0c0705130c020703020d03020f010905010606020d0c0c0b0702012003071406040c030b06120f030301051c0c181b0c0b010504110d0905010b090103060614010804020f 81
    0x10f030300192031a9444104a145c4141910401501800321b5010041240301d040000708242450b000c03094001407442c105083c0e02c40c60340018443c046a40541c0e0314101d11490b0f040490500241311180390b03230383d03090a8101c02002015444181298015801d4480006c80000d04440b00c503080400504500800901405251400b00041000a20505103c520458224200c0454113425a40780e50f06400120746a0244610071032000c00501560015155a02d01556200c071007804601015001d800c03c600041d00b56103800990a501407540c00484000a420007031559881d40240034240c040c00d50500c01020038500c0074000c0a42c6548481e007c9215400c0c0300d000a002007261500045840d100e070142080e00a14101050924400d903036980d1102c122401c00b842d03034041c183e11150242d480c081e4203455030b80052090300d2000300030b4440400c40e032159007449400341080c0541c40703900180c0c82c800002002140d912107011540451004042c0c4200308005550000040340e019402c4100422510040e16 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 972287302 1250 972286052 972286097
    0x203070f0b06061c0905010b0a1206091407030501390e01030920011808150414060f040b090606060f1c0f0b03070902071703101d0103030e040606 64
    0x180c0030f820305040c0315422030003400d41c0d15800c50042285560f81c9900041c0038007801440f0040e2001e0f11342c1c00c9014580f0341d900c42d00074000301d40600050f941d4002c1c4420850003010f4045840c6a28003110289030710b81c14803900a20104420040140d88400d00c60b010780301200981404d0513007503000e03604102440c80103031442d0b019070381c0e61410169245040300025900b50021030001050840d40e55540501c80b00140c1803002c082c05405c3c2139000d5035402c00143d8000a01030071682c06545c1d801031540c49929085480c14582c0320955a1030041e8000c200403100003000c03292013240140284801504d80c41074554441100b500d0483d001802080702c5d04541481d00b00074118007500166802d60445402621402c90303483c00ca040800c542c0320954080649001c0003010094414900c00310310309040d075a03c1c1d40a01d46a0002076503009070100004003e000007070017a10040c50010301020002200d80450068403a090200b02c002c200705403160391071410a441854250303115500c901100c00c1480e56603442c80c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 972288552 1250 972287302 972287311
    0x80606090c0703081f0b0a0305061212071a010603020c2a01080612120408070e2e090501060f030c030c02070314070b0d0605030c0613260d0c120203070f0b 68
    0xf460184c5d40761030f0440100ea000b00a0800144440c1c130b5841450000f8181c400c040c0c5410321480c0a03a410307c86021000c5031100d4400300488949903140c200d80341c451090754030a0084810700d1184400090740c035415400600d0212540001c1e98039000d0351981680068140c2007600b03a25190466140d07004e940288200758109800030041448168840342c00e524001c00c81503039103280381c40460704001c821020010000a07040743d00c20010300d450403155082034200e419000611140101c01c25000e00c90420400c0c102510303000e14140010340c0c40d50009004aa04140c00000103032802c032031400d5441c801d2061142e608080d81c081c00c0d0b05403460b120f82400c050010348441e0a80035110001880507243c0c8000c00403440541000309801b4039010405081514441c1014041d29040002e485482001c0d00311105403000310f10010342802a6100c2c41006103030104e041c28080c416600f5648040b5001195000058480d145402c0c80c0c40c800b000c100c1c2c40340101c0d440140034808003943c44001411003061076501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 972289802 1250 972288552 972288571
    0xf0a0e151201050405010e071a030c0a050903030a0201140109090210031e060e010f080f060106050c0115181b050d091106030709031202010507052205040e07080606090c070308 77
    0x51181d04828242182d1041d2411900d580d5a003400c104503017411321140005101d0a20301c1c501c009000d1840a0240c44020685071510741d00080400d80c00307004800b9142c540a01808880d12041100f101030300801e410021118610000c80001580d039610f4020101c80300d43c0648a100b030030701d0602d0300794043c10031100c80c1c0500300806844c0c1040c42c0424410007000380b045a41114580d40360080d0018841283c6d0044401034010030202135105800150076411144a4a13184d507454a54039800c500501034000002e0380f181940c032002070b40905600200703013504d540f280200900c054082d0300056842d21040300401140003804401251511544203000d0540130306604070000081ca80003840f2a402144c944022a545c403800b070051040c80180c000c5006a0790008000d1400d201101602600540301c0403401c24401381c205003034070010010408003d043c003900034050011840e44d020740300c4006004002082c81042c0000d1080c0ca440d540c1c080c02419403404079032038142c140d281201e00c420001d020485 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 972291052 1250 972289802 972289819
    0x403060b040b041e0b0306060a0302221806150e0604090503130608100f0b0304081b0a030201060911040e0c0a0908150402010e0f2b020a0305010207020f0a0e15 70
    0x2190300c83d4094000c0d042a100c0c480f205803131101d03000808403400400458069030101041200c551104014002545c0d012076448011801e00751340321103407209000b2174000c120b00384400e032021003900062440b100c603c41d52090089466502182d262040e03280f090040000c035230b2011440c02d083c039601c200191406078080d03900e0000400601c010a940303d50101c1c00040c0c6600c2001000084900024042c044140b0069003503481c001d20401d843c080504080d110841c0044e0307407800c80642a600d00c4610f20340c1d0702034510441142c20041c1c001c0840784102e08616080520b160188401c43d0119030a5400081c10405144c907081e00c461070542111100c0300c00e110700d00001068040d42000125141e100d40300c00c07010700d40340c00d2000501c425071011149000320000c0307884420076a6110103000c007102c803811240000aa00000c22240d0281426003c1d411403400a004424000b0640007018968001d541c0f503d1a00c108800740031404c1c1d554070074070400c94041310218900c8003da05040504d17501c01003803081c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 972292302 1250 972291052 972291071
    0x81807030b040503040504050603120a14390c01021002090a21050c0a0b1605190c0e2d0c040906080d0201050a022d12041a1b0403060b04 60
    0xa040550542d429602d552000c10100614a024050181c7c010011f6000d0703d40c10300544107218813030080e4030081c41446a182d440c044144101019180154071010501440ca84061442103840e6aa00e552003050312441c003014510042c009144110301c8010b82c01006000000700d64140290032003050740764820516000011310030f22030f0100c0189058500035008064806180c601d142070140c0d826140691940e00003002050000001d49000d00c1038841801c0035901c4c5841c20905094440d0303a103008102004c403840080c0b0070b50400c1a13083e00c002c0e2805d0040d82d00d541e20720b50140c0c00340108020305000c41c100d429009000120b01240c10080000d000c41c14181c46402810544606800101c4103038046070008860300e5090250940000a0110452a02010010702d5042a44980c803900e040100a2a40840764180b98115081c5034044000c01d851401c1500c1d2000030200c0c00850200700c8902400400d800d140d6030a403611a182c0c00840d15441c207440c50307550402901c0030583e01c030f50266603042810b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 972293552 1250 972292302 972292313
    0x6040212070906030c020c0f01081e1e01090b090105060c01060807030602220608160c0204051e010f0f06120f0603060b01030c030908040306091502070308060f06070308180703 77
    0x807809200d4507114050a241000320050480d8805031000741154084044c84201e07884a00402000d00c00a1a1061456594000319a44c2000010321307444440c0010f400c01405404447d00041603945018050010366a00c0c10800c0a407100710580d40da012a01c0f40041029180c070340003d00d1040d03504000810b540d59200700ca03900304400e951007550303510740003c0d005c072041c034100e881500d6000c001c0030803203291070030024014074a0800810712448049241101402c03039002c5c49804500c4c0e41c3c020414005890303c03005401c61100e074104141c8030f00301040300125102c032115003c40c0642c2c820881201c080c130720f428801c88852354003d00d2603800c00d03905ea030341c181d40d518030f40a40d10286014103008542039003440001000c690810021000301440c09501c0800590354030104c4040f29000b1401054490ba181408000000036900c21440c103031001030000300b00754001e4a15407185034201c40080070141f405050000030b02c51002c004001640e14000501c2c042c2001044090070910b03034080301c40c681c3d2a40e459 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 972294802 1250 972293552 972293587
    0x806130c080f070603050703021e0a12060b0d11180d1118010f050609030a08030402041509091709010c0b0c040b040b090a05031609090809150304060c050a1403060402 73
    0x42c1212600f00000600c449030301401840c0d04604585001c5162401859203035100305080009100301075030004001d1942d52190320010603541d000c5600308600ca80d5909150002d5024040201c10141800381c90700c030070b40d000c00540d0101021790141ea070120180d002040640005450308554540340f041c411103043d183c0200e17000040c0240500e5401d45e504000f0841078146065012900c20b0404215007502d130f84001c1001030010782c0c00b00708580c903902c83c0d1000401030714a00c24885001052400c00144810080e00200045401002d0b02e081148508400c46c030503114040308180800c000681d00400544c2c0c400301107500000c1080c503503003410f8076269508525402503010007509403001c1000c4e05545445c01e01c0d07000404045000301108a111600e0283d00d108501c289030000ba55511900144030301c410848cd0000f0000b080d407840004803070002c00e401d8000340d500391581031034100040c0c0401c0c0190200d80c14003500703840e8840c20a5005160000390307400100940d0708180c007807290172610b00e0f1150b030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 972296052 1250 972294802 972294823
    0xf043602090f0f21120c070608010b07170c070806130b090703020a03030f090305030a11060f0603030301150327030206090a1e0812012c010806130c08 66
    0x150703681040c8801c0100306444549114400c4005090124441e510001300c0151581070403500352095a00c011000c2c01c0c11766110307a50a1212000588425144021400310242c60180c0c85107200c50b40c80301c14204481c065508003c10703000b60187c4441d080c16240c0e0240c4200c000400c21030301050b494210360303810100c0555003844242d41d444600c904009090300b0041e03210841c400208030080c65070b000102074102900c805814404003416000d403862140e11020069904035040303981e42d5003061401055942e41c42010009030042e01c0c0450207000304200701d0741c015540180214216400e01c07490340c45200710458950185179950009030458606c102d910440382c41c01c6c1004104c00e401e0341c00c029003445001840b5541540250500c90001662407a01d1045401509400207002c0980c0c0b0f0030100300c0c40340f007151500c1c481601e0700005441140d11002d00c01c2e17694032134410003004d1401c4141408402c085c06444550303005100080c07900102c00700803c07225030040881c40222070b80c5014060030010800d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 972297302 1250 972296052 972296159
    0x9150f050a2a1115190c0219030305060a09051e160c060902151b1c091809081206150304110d0303060b0f03100503030f04 54
    0x104400c0040c14441e09112119003407291011105445a000b640351030440c001c0c0501c802c1545101c101c400800c00c1400d040301503000c1c000d241c108003140080416102c140140328508005a00101d1840030402c407104044800b00f8509400e800d5034207130060031008044d517400c040742403400038403e0a03c0c05003070b00030203c000c1160b4403200740350035801c1720b188018034450080740301405540499038042c409600240c3c206800007135900c59817000a2051140c0c07051a02c001d071002c00c2e5017183c4000307480c070005050399401c116400c62400107003a40520742400b14250105051550800c2074504130b620503500341c14642400103135180c25584035a41908400b0840071490300200c1000150304003000c1c0c2803001e00d80d1201090852609981d01c0350004100014107028500f100282d40425009400003c041c0c1506016180c9031342458681c1d8015800c202d40300c101108640e800000e48c0d05012044070255451800424500782c1459140380d104140192043c4200c402484406817000720703a403680800c1f40485 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 972298552 1250 972297302 972297311
    0x31e161e050906011205061f030515010f020a110307080102070803040618231e0a0506130506060120060403080402010824040908040515030711030f04050409150f 71
    0x90040d40040001604200c2c090001c12041c005140e80009081800d55800040899141e03111008594031590200325601d140345001c414203d0180c06411580c800e000003e008050a01340000444510006038122000f41e0000444100070801001c40380440e410050b04176440150354070801403c90b4880c82042d2840c031008005c2c0800c001c03681c000c40000010042d5000d041034a0307600c81140b44250041088004041b80e2aa458451018002c0121901c07100c0414440f008090759815218504c0c000c0446050241d1030000e400107400240c9045200e030031000820241c3d49502c01910071707a018420502507003002d128100c41c3da000801480f84210b1196582d421031382001e2002411400010780603c1c0c01c201011501507041c0300c0b405210025007411200811104801d0800c4059032003150007040d01300030109098098a01000021405189160758081d40e141d040d00000c0e803603000d02d440c0c0384451401000100702074a4a90058030400e40204a140c03482d0710b441c802c0300d0854041316030800c4501d483c3c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 972299802 1250 972298552 972298589
    0x10e060d090209091c09080c100c020d0c14011e2304181d0a0b19020409020a0f0207030c050118090f0c030e0d02060a200705010203040606090b031e16 66
    0x19807030514030442c179070402c003141e141020905a1100580e01010f80280300d44086500003a01c100e2002c03a02c0e58000d080359504034403a09098030382200c3e5006061629a245000302c1d45540f2689180340b22580110070181d1540089030101e0b0342007100c8062141c00858091440d40b140c0c40580180b0003082d20400d01d200011074582d800d015180b01c41c0100541d403010325100004080b01040050f035050b40035040925a0384c440805820310103040c0d0800104a1000c40c0c04580640704e0f90080c0000c45194543c0030300c810a00d80200e94843d06400001c00013444c040c01008954007a031400c8030118001496807070101d44521801c8200ea1002d849070041c2d07511900c01d603000d103400d44640c0c001c00f8a142c015064802c0d000d00301030f5694030060130136103401da039900198035100f40344040c12003610b2080a420760380d103140e8108036020350410b48095076001c4c83c1410000b40a02903114801c040040a0050420a0003d4080354551503040840490307074000c1c5494505560403800514000e04038003103269907251030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 972301052 1250 972299802 972299833
    0x9100c02150a0f0e21030702030c0604050303040b030c070f0303140601050f040513140f2508061915111002040f030f0302010b090c0301080f0705010e060d09020909 72
    0x784284120984442007000302c000c2ca61044048102e02c3c0715061044140000c1e40100e00c0082d1791520a03103802c00003110581a80b18044024075a80d80202c080700c900f08283e10410480340300e50700c186130313140d032040104105c2286640d000e1a0b000f060f500c44642841b945894400704448801e60031030001e60b03203003056103441038a42102d540090342840c1250801e00e12080405062040b400b03a50b10441c0c110200312032038030103500305400710414400b140320381d1304181c0f2803140e007030342c0070b035440d004c1c1540307190750150941e00041040d44210125aa455400d40341c16041c031505440f42158240d03854001c3d000454440c04189030403003444030b00d40d500d05010004040300c84c24800034540030003045004020800550801000007400d403900004c00260b82000c51406030300401458158030341040c00c420400c4512441300740910b040795200d9040e10106041001041d4880009019081c0450032083c035080c00303401d104d405080d454203184000035100d90260001407130410102c403c41c41603400140b420b8010344 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 972302158 1106 972301052 972301069
    0x20f0105092a031615140a050f070f2415032a0b0a0e011b08090402040f030809010306060921150207050a1407030201080a0207050309100c02 62
    0x88130088041d550446501c900d4501040f070810070301d00785006074819490034280780e40c6140303441c554680070307070791504000603071048000141320b00300c0050250a1070b07054050240100f41e288002110600c100080103000040d111410300b0400d01b0039841c00004082034a901c01c4107100702003182c0003007140329403240084000344603604000041564011004010020840d565074400d002c0f610010f5a1902c040030b089502c504583d4149808184054083c0880030300042015203401d580342c0201715809550380040e242d14200003032500d955070701481a940200900d041518103645411410241c13104ca6103500e00004601c800001e0070051031810307600909040c3c182c21512802d0707900b00940d8843d213152080b2500d907400200340105003400212801103035030580d0380c0542540d585602c1c202941251804075840d21040c48022465a9894140e4211041d29510301d40030031003d00400c000030 = true := by decide +kernel

theorem cover : BRFrame.Cov 972122302 972302158 := by
  have h0 := BRFrame.cov_init 972122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 972122302 ≤ n) (h2 : n < 972302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
