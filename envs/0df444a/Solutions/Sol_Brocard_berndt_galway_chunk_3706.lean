-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3706
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:26:44.965827+00:00
-- url     : https://prove2.me/submissions/5ca8e54d-e29f-409a-909c-1dd1925a9609

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 666366906 ≤ n < 666546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 666368156 1250 666366906 666366913
    0x80a05060906040914030d050f0c0403020108190915020d0b06040b0a0e010207030f0503071208060f09060f030123061008041203020f0309011406010f0219080f0406050a0f050c 77
    0x442d50300340002464942400e94454010b40c01e50325008030100b00400e880ca642d5840000c02c0c0c9480c076800389504030060980103d40c8010031007000541e90100c6e2786070300200003903034161a500c88c010148004080f4840d0003400041004105400000c8030340c007030010380704048014041c801c5020104509841140540a54100e00b4010303811164070440f18101507007810700480740055240d845648180510400841d4507034000200b803010400009600c18610034141031025090904400281d004d03041660124051081c640006001c0c4d81c5424600f016500060000c11030010880303010050080640529144110f1803000b288140c00d010b01e240034000c001d070f52010302030380700e41c0d80301c824984080015504040d02031100d0040030000784002c1d80a042e05400008210900b40440c21100900401150500c04203100f4803079060b03004074504041c180300201d440b40101c5a80f4080a81d4020585001d000c001e010130080350051f00280100b13000352041d100c1c0a4480744003503080300d040c814117501d0141c030341 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 666369406 1250 666368156 666368161
    0x270618040b0702030c0f070501020d030506010e0904110409110414060a170a08040e160302090d08090d060203070f17151009170106060e030607020c0108071b080a080a050609 76
    0x300e441c07207210340120702d520540e46809a0030340c0503850811a01103ca0441d0000d0030100706940c0c0400c80c510b43c000c4907081c14420b52030444000307880d0b00f4101c1c99407800380704600c1c0007604120840031000e10780300009204003c500d0160900c00c40e6003107a8150140a07900e00b5001c040d44040061b840c82c45044010305c1078610500706a000d1800c40c40700c950100c418810f040050b4001181c0202a0000c0e0000743e540349502e262020a060429581d0801c040c14581704004070740c915220705401002450304800303c5035032040725a0105034078101c09100a8103161000c0309002d0b8480c1c0c400011002000c1a654084015240000009030341c0c4064585078a104210b0b044082c042c1046521425800b0b0710b82000d28010b1740e9007948003400580042407141c0799640e003009020098207c541042690002d45c0200200d2400c80c0c0042e40c1c40101c1c9643d107040c48642c2e0002041c0a00c9002444c410f4240b8080020103580380d4681a45a904040610300126005000003800d2201c94428030348078801c024141e00858 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 666370656 1250 666369406 666369413
    0x3010e0f1e01060b040308071e030905010c150905010501030c0806061f0e0409062702060708030606040f0e0109140702060c1308060f2d2427061804 65
    0x3441944002030082d529590001080300c8650040c000841c0a6981255076540e5484c007030300d00300380101050301211244240036005c81d60008944050f100d00b800d00c400c17540400d0801012a0500c0040da03e40c007410440300908000c41900084d04032481100001c001e2380c1c440180645460303080700e00071740003000586040300c00c00700010900351000880c2094100442e09001183c01e49125090550394180c0324000a00590700409442c1001d000404002074107924550014aa070f121708140075080e003801101007101075a80d44211401810028542040c441ea1201102c1c1e0241091258000a92910214030412000340c1030092181905a014014690320349a1400c05d5802503404042c8200080002198904d001c01510340903a101c0074240c895132030701c117244841450808441c54105110045c0e50070150030440344540c4c1040b514030300515004106982005280c0810420540c80010a10010088003042500d900c107203a030b1441700820340c1d50780d00c140050200100590f9076a48542000140031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 666371906 1250 666370656 666370693
    0x3080415021b1912030206070212040b120603030c1005040c090902061c0209040c2f0316020d12080402040b04050603030d11040e16090f0b04120c0806100503010e0f 72
    0x1903200008502003504c0310b01810a80c01140c80890250348803c0900c20515010040c42030544000c01c2c83c94034040c145066000240554082e1241407510780020441d150341c00e00c10f888030300a00c1c4040711a440307210108907002d04030658094400b42c440c41004180003095000f00e4404a030007400707091800141c01190350040929411003c0741c150f080c00340203440d586501844031100c04c940d4504105954001c5201e207508140b03a84a054006405402d411160300407041d9002c1c07140103007188000c1c400a0011070034030302810302d00612035015030500798492600002c005000e280241c0302040341c1c5410600f400b04803081681e8040d4180d10601103992010465080060a01841d68100d8100341d41c4800c4d00e410344000340c8581407074402000e840c1f0b03003066001d00024005d08044000d9180c4600c1c00f82000349038405d5006042210b50046001400c3c404040d002070024901e4004488a91901412900d83c0c0002c0b801070718420750030980030112013100000c905060040c4140985840500c4841c0082c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 666373156 1250 666371906 666371929
    0x71a071d0114160f14030c010509010b0a060807090801020d0e0c0307030c0909020a0b030c04031b0e07200f0d0201180b060607020d050318100c0302070306110408030403080415021b 79
    0x1500d015000500700000d001c0305c168001699a03400854403180c61040003825101c0040050503260b241141c64119030395035910110448649003060f820a454246e002c4812807002d07005542658000135108404115950054025140040c1500c184000d950101602d400e0280710180c085001002e041c130a102c40c6520020078540300910a08076540d454900c030b842504215004039100c80082410014006200c086840c075280440480741d5403400d100c034010301045c01600c1102000b81d482840440302c0105a441d07520401d0002c119080c4640da01956a07841c050005614015400d1000e200a000402030348207121a6002d103440c40a507846000348101c81e000407001742d03800600c42c0e214002040090000b88070042c00a4050802112800103008061060442c880c0030048070341119000710758046060415280d00010124004010003030300b50301401550803940307040c00b000600004000170712000b8011984071000d2601203025400007607031144013a180c000d007020003455000c1e1862810102298 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 666374406 1250 666373156 666373163
    0x30f030f082a0f070c090e0d050708040b1b03070c03050c060a0909022803150f0e06010c03050c01061206061a16051903030e010b2202071a071d011416 66
    0x3404d1888548400700700d044542d0080341481d5485d801c0a400200512040780c0154075410658a03000306039031641414816440703016984c410108201c403080300002d50541c1414501002ca94a4803a1814600c120802d0351000b2621449050304068003800c0040070395003030000a884403c010b520b000001704c060f603c000e0384ca01e6003140e00100034080240c1116285204111035600181d4110035048000c41409990401e1b441540c940d071003040001012001554019000c1c640820f100d02c007450191303030a006035420740d4202e5081c4007020a1340188441c030b241e40c02d8081c8a00303002e800c0da0b4102c4001400440c0c104843d0040042040400c014048400d60000e10301c01e9007100c85c1c04c6180b04150455658203013040380002d45035007141901c0c02090250010140e4121030041100c424040e006e0f00e401288264030f01003d80100c1c0c80018000c040603880300002c0000311142e21803030718100c01421520082404072288088102c01c0025500c9492031000d1448241c243c00d00e403124148640d0789120707003400100c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 666375656 1250 666374406 666374437
    0x703152102030303040c171203060103021b06150414010e2e0b0a03150807061404030203100c2a033605010e0d0f06090507030f030f082a 60
    0x18030041e1810001148900d0040c061200c18a041c94034424401c1031541703030317401c00d603200000c6601d000302e641c0c00302c80e00300d0802d0038010f0f90f402c03140458050758010750076001146e005010802044600e1180c103d41d041c10300b200e08120001c109011940ba100c000c0c084c05c2a400021000144103510b001c807031a0000b4680c9070121360610b4000480007840c041501700c10306070400800da202c802a0140543e10400030076803603100d0410308190b00a80e503490346118038401c0120b041c1a10b59043d81c81340481e4040c54025080c0c031204000d019050b0041c2c101c0303560240c001001c80028500c1210008034440240c8515081c0412003021501c046800341c08100c01d4100440f41100c894007a00101c05c502c0d840403040318003a201c01c900d00f4001606aa1410785018014100d2402001c005440e00c10100c4c03050790700680c00281849607007003040c0f44c1205900014410076092080742e0a15400c600450461038080ea9400303e9560384241c8600b450002085405002e00040d07c2e040c03005070f40d50094022940c010b00c09 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 666376906 1250 666375656 666375719
    0x1305010e0d0c14180403021b0604090f15080d08010b090402190206060a06032a0309120503010915030b16031107080309010e12190c06140906070315 65
    0x4200c05021940e1041c80b40d0f6284440d03c6245003001c8250442c81d580221207501145810b8801a44620105c0c10b8a070100b000c105107080e06039510000d51300500780c02c81d41045085034200c0504003c000010300c2e03413444840e8140001c0c8240c4002045c6480703802030350300d40c0300d0f42c0d1170184044480e8002511065200d502403014041031084a07900095051303450b030023080b2504101d818848400f00d40e4004008060030800c080b5942845455401162040c0c042d107080d880f9402c9808400070b20861100400b02054904503d40d440d030310002450582d11072034010020040b083d80c0301486000e642c440100300c82c1c08140000c90a0300079031510181c2c0c4609007800306111501a0300c1240c2603105100403034000750040103208901c0403d00c22030101004034001011840500d03100248580501c5883c0d900c208111001c101c0428803a0440b0703182c50b03a100300c050103201f690718142400418101c601c0c10302c0e4410f00c000107101ca4441d0141c401410125403905140340d040894010381c19015a02113810311074520b00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 666378156 1250 666376906 666376913
    0x10b0d03051c0e0c1801051c050109080a08011a090901120609080a1815021c02070506030a09030305062e020114041103150708010e1503151b1305010e0d 67
    0x20f10030002024030050042c00c29034004101c0d200d1070b030b8001340300c01c58406401444123488103600c680180d01d45245001c9910421301c0d05502400400c03070014800740010030507640c0326130090200e42c1661110042c4d11145041e1400e562aa801003250407503101401800402c1000d000140e070700381c0180100c00c08101140035032541e41031a841040c0101c000b0310484e844458248036460003501038a62503100e2904c08651000081d0b40e21114121400b400b01c051034840d0b00c4500170403912000b010f003d82655141c3c031303151181200901101c44141e003c070b4109800219a8138200500d2450b00c80007180d00d00d04c0000c5d9a0541810b01c40415104065650700d00c0c80805c020003407051144510301c01da08800e54510320009260030010340b60324400000c00b0f803070180301c855904111750074195444c013074503100103a507280c1421081c08100c10027580c050050f07591080c0880942018184181c080082003185001c0c00420301485108003214002d00742c0d0050414401c03584900301019841800401000401e5510b4a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 666379406 1250 666378156 666378161
    0x603032f070b07060f05150a0503120301052e0804021503100902182206050306040809090417130905070f0212090a050603010f1508091506030718020417010b0d03051c 73
    0x72500c642c1007c4002c01e0552034540112190040d0206a003c1e00c200c00344180d80107903c4c0010300070342e88115015043d00800c0320044592070307040e2286c450b14100426140300c4c05400a00280c5069001c2c030700b89107054003804900380442e40600c6800800c03107566458141444020741080c90244409400443c8040e9503a0320b416100007202894019430140040131a51001111807552086000740c001500300b01c08a143c1d6419940100e0080e201c0090a40d44c502e860030680280f4000c140c800a000315181d203c80601e000c2480680703580d06820032060303e0f40c4100b60b03a0618085900001640584030320300001a00c00c000e09083e01018203c411500c2e1214009030303035034009030002d4070007070045041040850051900201448028240340c00182480440300e9100c90300346403034082101c03004020824540342005030000030b094440844100c05280a440c230f000c0d51042c841d256541c5c02c0e044080320200e1041c803a10130342d40002402e003801e0301400da4080d2065006070f0349074801c003d03811120301345980709030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 666380656 1250 666379406 666379411
    0x21804031110060f0f060c1106090907030207050c040b0607031d04090f06060b090603010b0a0210110703020c030729070f060f140408030a020705100603032f070b07060f05 75
    0x528020030810300344010604210b07116403000280d8071851100b0866250007e0100600d50341155a45036103090301404145284210000b190700708084001300800e4541c103a002e0951517204400380c4284501c1740b0b080100780c9400aa146030701040401ca9400000d001711111500c0d03180c8100b8081908181100040803194240343c282c0b500b0780540c0c902c070104811803113410050208420f0050a000052001c04d1190105001d8112100f5001540c0c01d082d5000308429404610900300511600100c0c00820f019600170020031805441082ca10119918001c500f0406445030b100101d2503031078244a020003050b460714810000e02074100101c2000c2030128a014511500403000031840c4040f034500c1000719002c0b03e40e03041b040c480140a00001644600c01c407a0420003410700036848800c107060150038001501c0c101000640340c40c100204258010480e901c82e01c00d213003480c40c0060000c800311090041440100000ba0708440c1091101802c0140030300021030082c040014044421503020301155004e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 666381906 1250 666380656 666380683
    0x1803050d080108060106080903030a0c030f050a060f080f030703181509060f0f09060807051317012409090c170105090706051804181707110a030218040311 68
    0x66800512241c10200807040c01084030b450407100d0348c5410000c0c2c580742c1c003020780b00341c0d42c068a45560203000c038401c0c1c03c0103941007100c5070100314a09103900307000300800f040e01c1100c482030401080014140e4000c20b0030a0311049071006545011400d60303044840c03d16002c10741000c0306c41680081103402111a500c14070020503205c65039907900700000600280300d410100000c000200c400d0540e86076000442c0012074980e810140da894480b10400d0b601c40c010688022095030000000180d81c080c034840e0003103010743c060000c0049000380c20900440c444281900340c6900182803082060401e45e0703100703480c82402120001016500c07a003181d040c55541d00c0c404070080c0c0d100e40600a04040c244480f070000d01150900900d00b182c070020811103589403441c0c0911680c0d039400d55500301d60341400349240560340500d0140e10f248450048403080d42144109444035402c2465010321410b104c02d400341906e40040008201d01408003118119480c02081101000300c105030490a00c6000c0002800b540c40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 666383156 1250 666381906 666381917
    0xf030103030314010e07210b300604080403080a051c0203240102120d020904060b040812070f11010e03061311060712050a030e030a1d1e011803050d 65
    0xf902002e0703a801c40410707000b485280c400101803100581d0070a2450391840c8070030800a1101901c0307810700009040f031061040e04402d002d003084051001599005030400d2281280940359165441065a51841210001c00c1d00390204024408603040303001030301d006003861030850302d0070203c2c1000d0b9414022110070861780039008800c0c02840d00300446c0d400c1c0c0e2513108411601e440310f00f13200001e581e403041181813040c0d1200002e0002c80044250100c0707440081c040c1061003a159a8582d0481d645d01c14410300b05103014403902c640e242d004c40740491708515049201e501e1840c3c155142d031402d0030040d0700028140310a85415414a0b00d0600a091052130044440003074900c00e424881c065600180809205410411900c00000c81112400c82c5c604034170b241141d00e4007030751a010340c0144150200c160440c440441d160405950003644414150722700c192445a4034940001d03c0041d2034403400d020007180d10100820303515403040f800c011580200c806010405035907510303000d0502000b90340c01c02c0003070f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 666384406 1250 666383156 666383171
    0x8120d0f0204061d240d1104031a0109020723030702041d1b280e0903181903021c060203040809010228030806040f0e0714010309080306090604020f0301030303 70
    0x40c058404480c83c03a13040e180211030b2038022415822407060511100011103001c03600e841510481d40c001e2141410540171584d8607900e1f801c100d46d541302003000076900091b0360000450740b50068003d444aa503408050020300d580815031855045024103400300c000e21050211401507602e5015008010684030300a039001d0148040990910341070700100c9090544803c0400e02340d40321382080f00c001d800021041280720722aa0000401010a42d021025010740c8505112181c9404002081d01c0a00b00a4411488800f0002d10019088511252041d40e000b45010805400c10744000c41c46102d907568480100d03065560740500701d800a407410345038000046801d811030350b010440030071440ea50100010a10311280c504580a0f441c015000781044111400300d50700380c90301e07045000700d00e80d00d8405102250404415aa07919010720030100c0e00006081d402185500031301c101c184154014800c21b00c0c513603a001c240204200302070013070360b0010350030860506180104000386002e18401c0e680411540c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 666385656 1250 666384406 666384437
    0x507120e030a05031303272c1b0d18060b010318140a0f110f01080702250e01060807030e0102040f03030309051c02031b0708120d0f020406 61
    0x250150103400c04960310030882c1c10a442e4012040d40d40c044000440750008001c01e2400f203944400c0302140c1c11000e100201400c4421202030040c1d0281d4503450a000c8041c0c0b0030b6200d213291604890406400d00b0100310118194144c0380b214466021000401d407403034050640c0103001103402c223080307010b1142d462020403000c00c41c050094002c02c03030b000d00e400d01c0410840c0c0d070000e490100051005104080c06030107410796020a2160180642c0c0141702c41c6400c43c1385d401c0ca49030103150f5651680c400c0c3c51042d08001558040c00900e03020320b034141d0041c030350030241d0012055184100001007040c0c18801d503000a000c0f0305204a00d000e00300580e120910f07810455006026074075008903502060340144801d000c00e00c0c58899100c103d030b4251038003003103041036814074508040300d0310810707140500300407804c950b21500000205144001c541000c40510b0f2240a01030311150780d80030351a42c030b411400b001c080c151f20420103400c02440c5c620000811440d0010f01074202c0c1d00c1988050007141110002d038040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 666386906 1250 666385656 666385661
    0x907050d1134080405010c0302010b061b101b0c03020a020a1706090106030b06090406021306030605030c0f03121c05090c120312040204110408190b090a0302030d09110301050712 78
    0xd203a15000300900c0b6140c1e40c0d41081c01d001303a0041c0c80c1041340d101000300a1500c00d4025600d82880501590b0307507442e00719415a40398000d040307445414401e0010010605500c2e21407507000380c80320780f003a10f110b010b01c9408407015499010203508610403801034002599440c200400240f1046d200e460303403004c51f201c0e8a82022402080c3d141941d2410408001181c08004911b6101400300d4001d8500c1e41e0394a4030030004d0040350b10841d0200300c2000041f172600e4140d030102050321000c800f02cae41104003801c10004860002505150550000008400340381d2002c1d0140c181e0800c0f00389600c1d800c210020724101112070031034401c404ca80c03200d0f03c014420f080126581c500c95122502035407030300c2d200040b10580914040c000901642c0d9402e406800c0030120002e550107040164140c6500318041c0e00000c880c1ca0034510141c40e81c403a03a84c0454081d51000a002c845d6940c140c0140d8145504814000e0040070070080950700c000c441421038619a03000c0c41118440e4000d5142e100384880441e15a408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 666388156 1250 666386906 666386977
    0xf11040605360712050612010e06040201030f0b2b290f07080711190302030301140a18150f1502010e0d050418093305060907050d11 58
    0x1e040881d4814000c3d20b03070b4000d610080000c10342801107400d46034040072444200714102058100c0d4030b094024101c0180101303185014a000b6a0140301c590100c41800c8200c40c5e14010b101c2c0d02aa013280f05c03140c00403240360004203130a015000381400c0c1001c4c0d16120266070190130656008000c03041c050031050035145045400070001c10385800c01e8940075038003422a61010f80f1000c10302c01c138801d0741d601d8050204030031040381000011140d010240b500e00a0340e02c0d0828001c1c501c40425000f9000d81c0d07410300081a600301d0f101071a840c0752024010742e5440080040a08030010941801c0000c11b04c820900707000401404c0c00c80b1664584081c6460090031074261501901260b041384803c2d0b60195480002d540907200500204142e8400c3c049500004002d070f860002c0c003000c200b10040d04004065481880d901808003983c60611629407850002c461089900983c0b10540303802180744d0034410170113012008425000002c62421242e02c01c0391580220242d003100030780a00740d5a2034161260502c88 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 666389406 1250 666388156 666388249
    0x20f040e0c09062208010e070e01050402070b160c170a02010c0201060302031e100c050405030706030203090a03030b030c1e040e0f0604060c0215010321020a0f11040605 74
    0x1818046940002040c81c81480c03403541c1034244400c0640150110b104c102e130014074a10000300018200841070340c1d00e400700b80c801c1031721760440103000182c03605007802250b8039142d00204682d01030b90303282081d01c902d15035650b102c02001910070fa20400204018401c41300c0d420f941041c0358662181020003402d450498100710116410400c0800058800141108414030301000c444420304070500e0b0103190062550013010202d0034140d800b407002d60400010016584241c058405098850005230b0a038881940c017050f06600252000000c00d20031352041d44200c1d40241911481808070002400d4460070180c54041c0311140d41d0bd10b0000c3c6024401d501240b41d030103002e865280d841450300c079220500100060066a2181000c000241c4203010500440d455501400085e5843e400c0c10300b400184e030b03181080c8001c40c03811410201400014600105580050104480207043c0d95014035070031081078007500b050b1105404030302a80c4050f207003555020480d880d69024041141d82d00e2042c0c1c00392441c034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 666390656 1250 666389406 666389431
    0x100209091e0a0c02030708030f0f060607050706050901030f2301150e060309190510050c0f0319060f06050c07150f0503100b04031b06020105070203120415020f040e 72
    0xc1c245000c0c00c078a8075404180d00c0000101c030780000109034114801d0a50041c031000c000410400807001c05152680a24400c0d13a0207130385540c680051010510844902a02e90f80c002c140821440e0710640c0107210580d018900404c651381140052020764110080e03403014400c00e8104125054640d2a0190041006145216000b02000b401814080701c1c0c044850040b80c0000010301e0304441089070301c008030082c810740350100c0300600308507132944004410000d1080c200b03000325454803100c2040c0d51540c1001024549540c803561000200f6007880114505d116841d1140041c100050301010001030500c0d84405036070309100d806460074100300d60031125280007402000c21029500082040c4118003a0901555035103c402ca00c5006000c947e11141024000107030100400103070340b4176203100c000e0026841c1c16090f1034201c16800da420072102c0078010b138014007500d915641341094081d003041c05025120200074840a902041e80c5c8803518000c81c030307000080e00304124038145510980c4044010002d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 666391906 1250 666390656 666390691
    0x8041401020d05251a070809060702162c0709080f030a0f2001090f1505090c010c11040c0c02090a0b060909090102190e120f03042610020909 62
    0x140c01603000c12a5403001c0c000300300b0900800420031112106030b5105940c2c041700b450704910091200170704a40c1d0520358043c10000c9005140005408e080d6848070102c8800c41380d050403103031026880c00c200d5004c000c0d103104014008080d141c80e9518080d1001e40e40e40c01400781020689440d240c9801350400a0b58000c21040f000103a00140704c0d0140100e40c6402d88103c040844c00c080c1c10070040e03120745402c0d4a0b02e8400f504222440080c00b810901c5540f8034004000c1d141e0101023103030402c4a2400d03094128100c003098543c410386555088500c54000d0700c4c0c0c00d002c0140402c04648194040e400480c91000c102c0041d46000c90400368884641001801100e514601007859030280c0307135180e03018185101c041070300907900790142c910912034130130000e10b84000800000c2c0040c14400c10580120796444841035002d2000c03402e01100d4001000031032805251144040b00000d5104042264448104980b80703c000140104003d035000e0500141e150342d03171401000142400604594540c0d05503582c0e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 666393156 1250 666391906 666391927
    0x70e01030512161a011424160501140f010b04230d060f09060b04180224040303050d060605160b0a0b1c1e0f060504030c08041401020d05 60
    0x480c05001c60b40d0068468070f6245222000c2c12203004104000e2210b01c0d144050705100070a00d8109040f156503228a881485145091000b096040e0784e20400502952450020602c025001880c8000014002e1060000e4070b4561900716016103900c40c035840740314401c4c4442c40d03182c1002240540184010340d441c152030302411240782502c0c8500741d449610020000d40c0e450b035914001c500c4050b0808024000403004032303600d4000784850b10040311128581803c1034001e0901d4404e1021840003401050349d100d0154080013007610003941100340e00d410840910030701020030710180c40114801e4417025110300521030b4900076200700b50040001c00800b07008242003c444004941c081a80003202000340d91244500b0340082c2548a0469400803d0381d0070802d04810708006003603855000303d00001035031007104004400c0a0405502038100d903442255440800e030594405500b00b403080c2072581e00c030340d000c1d036580c40181c109912441c0388820b05183c00380c4650301070180e032000d040c3c946000d600e000505034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 666394406 1250 666393156 666393163
    0x1530011d1b03030d06122f0f0d020315190506090402040e21130b030106080105060a0908060a1b09061d0109031a01030201090b0c03040e1e01031202070e010305 70
    0x110003007001d206410340981d6510306000f10b42c402440c0388000c0c00000d031142401c09500d0704c4110f081f40c032000c613a4501001c04010000000c100010060710800414100f01044052075281c01e000341d1040030b00d4440401a50100452a1207620359801d0750030718a48942c0c0c241910340c521080018681c140800c11101c0d0740c0d410000344c1d10a5044600040280c9a180040d1410382c0d05403503110311f040c0494420102c003481e00040d100d81c0c800c0504401e0002e451b007400e0303140c0d03003c20321480c2c010544000c0180700e1450804080c000780c08192030059000c0365600c1195140107002e8a42800c1140d40760940300d0b800d0b6409400c02d903500f11505004e002c482c605100205109503c00700701d00340401c00e0542c5002607102e102c02d100116040481c43d0050703006560b81070320a29081c8802c901141321100d001648603881c03002d45d0000746d511805582041c0c0f0b024540700c0002c2000385152074074a103030300c60008680b40d10510301e4003031400b8441d884100b100b0034038082e00e441d00e5034006481c030b81e82d1304004000180001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 666395656 1250 666394406 666394423
    0x19051306020a11070f0519120f05031606060e01051f0813081c05161205070302040b07050f060106020f06011a1306020d0e0a0b031530011d 61
    0x3100140c0d00e6a00e4401241d02e0600c1060704000f80c06088030003d10850300b44800d40c26654100c408403410404a50003142200e0f940c8a428000089100040d0118444550058181d8007501c0ada0b441d0241400d82001c148899410844d4103540d030b89024401c003002c0508007070141c103080e50507882003110440098000781c01c020580d0300b08618100090041c403071594400c1c00d030680c00842d1070785614481050310b03160080c480c240020b540ca0080010f4071603d0340200c500e40c00840341c698100d80d014400c03030800034150040000d010315408100019113605000b00801ca06405071004d4212075032119202810281c042c1d0165085512200d4001c0c90000f010500c03c0c1140da40f1642c0d400641180e91041d43c460080c007141000d406203082c400224250041840781d9402d1a6548048500c04114100a801c03403117402510f100700e40500000c0c400c05015140a240b50070010460520388000680d81c1a0000075407030450540c40b1400740001648000f4052400324840020b990003801d50b103079160356a6039848 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 666396906 1250 666395656 666395663
    0xe01030506011704050f0102120906090a03080a02072d02040f0203070917150c04080d0503160e040605030d050426120706090203070906080d022a0301060e040b190513 73
    0xf01d40132900304482041906440b03941036009646030342e0442c0004400500031201c40c1d0341c5016002c005600c0300720101d10f0380c004035819184e90300769848034040a002500244401c8034000f00008035078203c0302c1c0c801e840f4244103030300d000700030000022403040c00241d8052a06514007103005200f8007852a401c00c0c010700589a2189010601100506206240000145090030400820350510282d225214000d07c15a16043c0c01c5980d81c01482d88122540e1104503000354088921410034074025101d20307103090603003100a0001c02c0b10341c1c03034030002030603d410816103c0224100250410041030400c3c0f002e007000455640405d81c94090400c800d407500c131007508115031404002100820000683c0c060302600b50050200c448490300c03200528000c2045028042d880d1040f410000042440040c140105500c0f0581844460320034070007200c1d030071240c048842e5040d500c407040420444081903485110714000c0700300405504085428107020f240e95440c84081508040420440403e0001c07145400d560 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 666398156 1250 666396906 666396947
    0xc2104090b030106031208010302030d020c090403050a02150a061e1206021e030a021305101e1211030615180105091804050a050f0705090615040305030d05070e0103050601 75
    0x15050006801820f00e0f0304024031095440301c482041d981d000340058140c038825400c460b0cd20044240a9950300b81002c0c130690300074000030000d40002c0c8608081c2c030b1451050300450300802c02c00c18003503480c3c0000701c41c41c0c44084c0e5104810015540c07002d02c0e114031601441c0200444034105202407a2100e0f4405001d4191030b000038002001036000c2090903801c5003a04e000076200c5c02c000c030340000a035004210b80c94042c1b8031400d01007441e240114103040000300ca511803024040b26051144010f0782da03c0e152000b07200c1b004d035804c100c9500f42d011390703d0034040b4200c44640e80d00d0314208006078101c40700c0c284480660b003808081d2030004510441c0c50090b8003401c202e80c0304c0c0d20403000208086260150003468036040300900c01000000510107102030b100300241d5042052501d61655144518401c4544c00201500426a6810040800d0200000140989142c151070340c55840c5558001c400d0100510355410802c460150f00848c0c80400324800d10f0140b14074201400001c000d200200d40f40444480d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 666399406 1250 666398156 666398171
    0x203090c0603011d010e06090f0c09040903050d1808040b0c0c0a140307051c0305030606070b01120c0801230a1508010207020406050604120b07090503120c210409 71
    0x1104201038280000001c041e10390300e41e159440d81c2d080c19102c004141100d1013640001c01c250b8501c4010754400c80d0301410031000c51785c0d08921180d04800190000c17038180800c000742240c58030346010b1062240d010340c036002c2c0c3d5003000030940030032070b100c4a00301a05c0030201010040000c20b060111360444d01c4003c1800d4407013954000d43d0307080031b076011011503001c19140c41c001803047d4000b40300c401016049040e2400c00b40c7c0c904c02c1c040000c0100c01c0c2c500740c80c00c0e42e03000c0380000380c0a440515002880904110b003041034594a010304504d0a8100015829401c180001004041070701c1c1000380078030760001e115131200074078100b80d0003856450900410102100040042e0503d80c002c0c100c903540b11500c00102c42e0394440340380c000e600c0064140d014034245100815541401c600305e030112a9242c03246804501141c032148081540901140100804c91000081943d01040300b6124080b03c103039120b070b48001d10503501d490059084c00202c29002e624a690390f54241100958040f26143c400104441 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 666400656 1250 666399406 666399421
    0x901050108030f130e0f010611060103120c0812041b0902211315020d0e07050d02060a11011b030e0f15060a0905090d3906090206030a2405090103060203 67
    0xb100c50f0000b490090f4010300b0445446e2610303241034100e90303051700d9010032985820001c40c6c85010901010b0320044504a0725001076121701c0e41c0384011030065640c81d08140c000f03800075940c0d210545054410072a1a160700d058802002c00400041c00705800c1145030440c01e003a01602400c600452580c6c2d0a8004000303540c011981c184002d406500858180c00f140b24020100001e400218003555900d00c0d102c0000703c220750002d031a4041c0c840080c20007006000981c03c0100b40d501c960313100410841059100c0910305c5c002d0042c201c014a0b10000004040d00b24500141260803c150320409640040420907581c43d0104101c0030f00c1c07403841d45190a555400e0f0100b8440c0c0601d900c250020780c139103010014200f0380030403200303900d00c85541ca0007100298882180003c02d080072901d1a0f00d03580002e00076010001c049031240031845842c011030038803080d0f000950b05070422a2100c1c20346860701c0c165410b21040010702c400c00c030b010906c421803460401d0042402c5280500000341b03160b07800800304141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 666401906 1250 666400656 666400687
    0x2040506010915090806060307080a0b060301110708091e060307030b0102120d0501150906271a210705040332070f151d0a050303160b0901050108030f 66
    0x282c14203140f1006003c92840b0024450400ea21034106240500408200140740100d104422524084010320070922151511014950085d003050751666840c0d286612141d0141c0c0070f040d4081c00750130225102c2c11404144003603610342180c015070041c2c0aaa443e422a40c0d01002c3d03d8120b01c0d117240c000360ba16030020040c2d00d040801040341c00d8040c00854007146841c00390304040d041e202c8080e1058900e140546098450000031700031000804d81c28080b28a560250a000325000b680a50005000d00e5851003409007040c000d28185141d40c2d0005000d28164140f0300707900100301d640d051202501d190800f001483c0d80030391f01008048290600d0003170004c00c0c40b10611300e0004c50b060b482d043e29042038401d00b50354040d04c0c820001c0c1020f680c10300103180c203401041040c41ca030242d03e41c4d05200108402040405501d000800c0d1701c601004400310382d5881c104080c10302101c007500c040344c06815034100030414040003810707003543e681000d0044c045800080261001c01c100c5000c2940c440007440c212425 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 666403156 1250 666401906 666401909
    0x10090e01110f04060314070215100b13060305090c031207021513060f030c0e12011508101512032307110f09040c05060f0409020705070e070219020405060109 69
    0xc040c0020955000e403042e500001c00456110351010007032481c3c01403100080001c1200d1542c090303005096244048440c0508940e03101c1d40c1000c1c446203040d2101e900b42c455410900c281443c42e1002c81050003203e42510a098110308840d0007170007005000341c00650366000c4980200160340e00401e01908540324034070300c1158405444071040d26081c0314400302a550388a4890140000e00b0324101421090191140b403484903d01d645449022804905100f9544496445070100399620000828034068a030000400b802c0d000010f401502523500303048055135000140d44c0003901c0c12400030001c0a52445801c405194181000340640d40c842007020b80084620301c5c40c00c280e40c00014140208200003842d85031075941142c1445103234009a00307029000008550007807203803544880034001d6140a00280c580c40143d0040c0924140d240c085580a0f0b0b04030040440b141e41c0000b0040c00540a104032041e0720540b2403000340303646500d01482c42d899024070003001e406240d80d103000c20080e0748515040d03070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 666404406 1250 666403156 666403181
    0x1091d04150e1b0a05150f030403050c030c0705120106061707091a0406090909030806090603160b070212030a082d18060601050c0a030323090f010b010810090e01 71
    0x210f0309a0010b02003070182d1040240c2c14803500c1c403600081401d240c203c2d1800c20394105520b1080c100b40548400a14075807019000340d09000091010815681c42007000b401900150806003003140e03d00402d20401c243c0705c1c0c4184800d40d0604500f40700c10355118007080c030803101100080e01140c803a050255540041031700034001c3c0442d4055803243c0f040407080100304440359982c070f0100d11940e40c8030360f2007103500c0e90000400140d0560040380083c549050500c0d0412401001c0e0741c589102c40308400038010700741d030104101350310110705041940340441c5d10b140d10b0b00c68080918600200004001c1a40341c0080c5882c1c405c0d00c03049284c000804400c0c22680104684203016881401c02580c950042408a203400c05c40707105200008005504c18400d4480c0c441c01d80d00103182078801550301354080c1c02e01100030842a00420f0110150204243c02940a842c2030f00c05460941c94525040d400e450380e40407101c0c10311000006003c81158030441840407610300c0c850002e102e140e007030000c9014040660040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 666405656 1250 666404406 666404413
    0xc2203060905030c070801060b0d0b0f042d0612020904210c060f0903080c09041806050f0a09020a050121050403030608010f09230708100b01091d04150e 67
    0x95042020000041c9a40d5074044110345c0d140d540d801e00715083e20160b004440c44041d041c8035280120610f03801041c1e50100090841c4621141c0f08003080460304240750016038021a440690100700d824040c60300d042d154076505200c070700d04180ea0222568803407840240109030400028042c45040c00e58500c075505600c2c00c50501503502d80303008015071102c0c5800e807105803074056448010b40c00d80c410b981c4000e5064592046564030b040b01c4450940011205540007030721500550320a0084150b10441540302c1c000000b0b55007007482190018070340c02044a003095103040c1c0d8070310140e6034002c0060708807402442e042400b03580d030303000c0060580c2c0a0b03180ca503100d07400c19044c40b08042d016081281524140402040303d041c07800690710545d0802100034201c00060800c028100001c0c1003043d6400b4001d00031100a10758a170300582c540010b80110000641d0f0b100300920742e43d0307401050300340180f0540c00c2030343c00000c0c0c0742800d0402c1031010301300034001d5213250140d182c0102e6a4100c40100240007007a07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 666406906 1250 666405656 666405671
    0x41a0c0a05060f010501030212011e0f0f0e0f131205041215050702011a131418010b09040812070e030708010603060b01110d050307020c04050c0c150c220306 69
    0xc01d0b503402041c2d0b80305005070364940022506521034070035200c2079140260b560200344d1030a000d100404071a05074188403c0e10404c1d010401101008180d002441006502e00303d0601e0500502003244018104142c003c41550078050001071200060000e02c0e000003200003250036040f4165900c0c0b095902071564a0182103c04041c01070020000b941078103020024480c1d0f03510100704a0885004040307403411b0200c20001084141072890b60b8000c91000202c0015400c9244158000090402c803159902404102201d6508401c207005d44089600251400c8990b03041c250b0300d400050180c040703c030000c0801c403400105054421280c40901800c00350545200d5521421040d010348010b000c242e690b103041042410302035204204001d404401c41c0060118034009001c110351540c405012070045124190701914156503d03ca4a402400f42d40006035942d412103641c00e0901004442440c400d0401204100c200a0090201e900340d0400703010400b50010090303800c4002e584d8603000608450300c0c0824 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 666408156 1250 666406906 666406913
    0x50a0906050a1206180c050412080313050708030d060b09150d0605041b270636140108071d03030423010809030903100c02011d06011401090506041a0c0a 67
    0x1a4a0300369010381801d01908602c0c6c1415542446148903944c1c04000c04a10740e03000c150510090742c0c020b142c03078000c042d000e61a502c039030303290044907045041e454000148024004101c0e104100080031009421400c0c182098005030044680c0c11100070001000a641c118040c01607005c0c401612000b0010042c40940c203044181c40d04d44070780c203800440c140c2c0c1074a0054041c0240101c01b103110344080c09175110304000085626020944000e101c8aca030305024291b88150a0b03030300361805107100341e4440742c55150040da10040c40e2440c3c1c445041c4841c8070140145191721112000e0341500c09104400207800b0725010901c0c6100708d51107041c17089003a00c24204070440181071090604000da0340c102c5281c84011400e52640314070415241d06501c0905010002d061a0f00318607855026400002000b081300155900418070701c1001e0611034001c80c00501c0404007419404c0c1e1501828a0710400321800c02c4045841840750f40141c4a44038491104140c107204180308071340c40e980c7c045090340d0741c1020385e00c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 666409406 1250 666408156 666408179
    0x112050703020a03060509010315090f121e03141803040f031104110a020606090402311109132c070503060a0902030a030e03070f0602060a060501050a0906050a1206 72
    0x440b0f8600081c03c0000008041c0b600c03401c46410f981d00105122140403421010000400b04840103c4400d28010035007408a088686409058069a112201d502c01c5119003015070f403240152520a05241048006070f281e40282d015030301801103a140104107240100546c03850040b03034040d49130a00303650004010031050074100494a0b0050320140030391107025130001001d000b0140d5020040c0d00100000c0c03524503200040350307006400640040d000b25050402c06d81c5a04c0b81d900030000040418001c064010524460b0301c80c20280c1210b41406c060943c800203521500319080c2045454070f900348040049000200c2101c0204084543c4140341c81c030100307054840c2e429110b9584a8040d04d000511219203c0c000c44101540c010090b011803412030790182d03080300c1401c01d9a82c05114600000c9614240741101101030300194000f44524034040074840c1c1036881d0b07600800d0410a061250440e1a82c10010050541d1312a050076911460440011100c9000c41019042d04078148040003641c3c00044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 666410656 1250 666409406 666409417
    0x7030515012007090218090903031f03060c030504020307050a122418110603060a230310200703140307030e0d0521090c0103020903160303030c1701060e010806011205070302 76
    0x104401002c1078211b000b000000e1b03500300c0b050011078100700002a40c014682d800c0381100084014000c10840d100d0302da9108450109841c1400300f0b03900c1060005528007040100c00400044960490280c10000c034485040c120650007458200400603106000041421035902601c03450710400101e6003a12011411481c000301c01e81e100758215510010505040d002c0f01e01c203050151032400c0c000e25100506080d0080001d0121f8a0741c0542c02e5410540d40c14044500301401c0e03000c010400c09221003e03c805a25000d124141c10642001103400217900002450802812401e05c180c40f0781d0f65240c103a01a00c000c4124410b2400b9400325440c0c102d0300070020300307818080103440658400030309480f40441c01055840c0d59195002103070240b0707158403035001001d50202c044d050f0f807140c0140d40d004c85240d83d21904200c01180e1198685845103a001c50501341d001d4030a2103003038240d45030031000351445100c400a5410030240c800046c580740d00800da045943d240322201007000f85860f4030020020f4001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 666411906 1250 666410656 666410677
    0x26130327180e192009011a0d1109040e0703020d0308090a052505041a1905091005100f091208070206070b24150307090302090405030909070305150120070902 69
    0x300440c02e0048110035264041c042c034040d196040c81e90031f01403181c8801091101503113940c0c01c104290704480c1000c2c00784084e903400b500342980d1181c0f040400c02060358011042c1342000c0d07020700070420150799440540c00c00b0a8150501240988801080a044c10148040a01a0310940000d40c00c0d00e10b01000140c00c0c0e00030660048846521a8204820345840181c40b40b0240c001c0d0101c50740520b03001d00c002e58581600c400d0440c11598840204d0b40345a421a50f440030f00d02440020001410846401810170030103141c0085e03030a440c01c0000c1c0c0800d699004400d0762079070110b043c0041180c02001c0368011070f0000d0090741c682d0604d1400c60f0140d10102c80040d40c0442c6800d100311a840c010030813000c201001004110b00318140b015510b420f0300010b20104c1045003074900000540c03541200c46000324042d030081e50741c951102081c80850100a00706004151030030781009540c00c41c481e9210030000b42440d1180004048214074040c0c02d00344251580d5501540700005515140c650083c275030b0001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 666413156 1250 666411906 666411923
    0x1508070e090601060c03080f09010e07080c03010b04020a08010915051e011403011a09030a0215041406030f0103030509040b04050a0603020102190c050126130327180e19 74
    0x300c4080c1110040d0031050001d001c184c91f68080741600c02e02400040c0c0c020443c0c80000b03945a09001c03440d24104155011414a802008450b0302604080c000d00c02d01c041c055130198540381d04640000d00d10342052140020b62561400c688000e00c048140d044010308000b45070500c6041c031050440010705002d2205800316024104d03650740054007005803412100d5280c50b064900c8101411078043d13601014009600d4002c03e2200700c0141d8542c2c00d00ca00803110700362000c1d1984d040ca28680418581e504645115141c14410000c0c0003200300d0f40030341905e40c1441c05685520121001c100030740151804c184c0e019042c0f90800159982d540d01c80300031a8000da00329000b102c0d00d6240c0c0c1841c8407900b0005030001c65105002c0c03020b54000c1d40c0c006492120601088018000543e4402c0089070039611000030240088910040c10383c40403a980d09180c0400c010410781e01e03070300351a0708040883e1107030040045084c108511700e0003a079130010704010400016074070141e00550112150b04915001154242c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 666414406 1250 666413156 666413159
    0x40f240305010803090d05010905030a090e070306080304090f020d141504050405030d05040c0317182e0903020901260d090b03040c180903021015091508070e090601 72
    0x40c824000c0034100c412040255140484410600a42d03010081080d101e41d900d550480e40000d00030002000c0e288010781e9610032513030411914040515001e02100d0401d420018107001d405004000c403411110807040025965040440e00c001a01501d00605034030342c5041c60906407a25400351b400d208404140c24078054044150070070040b680c0a98000c1c0c400d074014402c010003080380f0360080d50418040d11081000a590783d6540341c01d0082c07580c5100d00e0a20101d10050040350000320100c0080080312408107141e0341303440501c070b822000d064060b82d40ca072038000303445801e0003106542d01550300a06950030300c0d80c40315000007140030000000850f4014080c0781192001000c80c1c02d880b91070051343d81c40003280c5810100c0700b80d904080c0081d101614030410004500703034580d0701c4180c0c05020140125404006003000303420300c114400c20302403103418000c12280304402c80101405030f869003080010300d19400541c41101040c1c40d0010803241c42040b002098400600030064803800e4185c0c110f840b240e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 666415656 1250 666414406 666414479
    0x60318010f2f0415090305030c0a120905060715060f0f05090a0e06012304020c06150102070b090d080f04030807060f0902062a070b070311010507200102040f 69
    0x10b0008044580e50346009100900a031544015604020507861800513040358894682e2411540a280e00b0000c46d4804000b0360100080382c00c3c2c82802840358105802c40d1441d04010480c180b1541c81d00031316401881c02440c101c64000e52100000c2c10542082c0c03898140c8441035000c0036140c50064900c01c1501d2000949512480d01420015900c9903000d400142d1800344e447c0012100c191822100300e1f5a084503400a44680c405060900018030041030241040076411003d44070380c6800702e0454211150500410b0110021182c290030243c030140012803003800e114026018000713110769501c100040010612070703000f010b1310800740500c10401107041c0c40c4d1100c0040303502c2c10340001d4000500780300d102d40c2c041c3d50a02c048080069a403080d42000340c24159039060501c0b5400c60050607034082052000d041d0321840c1c0709403480b82e0400070030003401d00d400040c0c02041e1025200300d5880c1d03240c80d80c401c0141c0c29010b0324002c3c40c4114032085481d0325039a1520101a50418680103070f003c0c43c1c00c400c0c40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 666416906 1250 666415656 666415721
    0x1906031a0f150a020705090c1908040203071203050903010e01020306122803050c0a0501051611121303060f0f1b092d030b040201020c100806060318010f 67
    0x20500400048240c01c9090340c0440c10f400040c05281940601c04002405450380540c041c400c5040d45801640c4d034100721011044035041a0000c001c000140c420040140c40c00a151030541c0d01031041200300602c2883d044a01d44070304958190107500f80640256940b8054010310302940d000c448580c03598101040155072900e2007405003400100c1490f0b842d618494101030807600c10b010340381440c5400e88001c0c51920f41105003070f0483d410380d5164104070810302c12121404a0420364601800b0340002c100a05541744904c084c0102000d00006880c00440c065602220045620000900496000c017032144024000c1d080004442c80c00c1c0340c9a0303040303050501d00020403980d180e201e0010960400090020329034403119210a90000e62102c1c1082c090000c1c0c1900065100d643c0c1102140f800c1d00c0024104602c0c034030750358060850007004541d181c0d04010f040368170000a640040e22550380f40342410f4040014503d200c2254038203412000e10000d541c0100e445c500501074041056001514a40d81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 666418156 1250 666416906 666416929
    0x2f070807030302181f03050c1309020a051c05010e0f010b0d0903020f0a060605040e07050d110102010b09070c02150f0d09140d080f010e06090408091906031a 69
    0x500601004038000282c081d82c0034241c626003c101000840902d40040703001c0031031182402000003050031590740b0141e03240c02900d5000501c61404c074106440401d0503842d4812a00070042c03500d0f00405e10110b02e41c0b1901c142c50130030703861120103548100082c10f00d000038a8203000b4003103d102c002000902405480a406040b1000081c05900d03051010394680001c008c108405c031304600520412a450400412000d0744882c06a140042d802d4034020401c01141d00300321041c00d141e00480f030100483e5030307a0305008440c41e400c41e901c3d0300c0340702c0c00b07900407401000c0740654540d2103c103601c24070940640c04003282c0c042910136294841480e0b0070315044c420318086c0301c00c100001783e8208460381c80b0002541241c00b51906c561411341e40450303420700035420101d401c608080012a03060800042c142c80450081c01060250307080302240c1085d4012404510700100301400803c000601c8e0401512190b012080320180d15100d4100640c6446005002d000300424a1420300d40141d100c01c100d2411200718403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 666419406 1250 666418156 666418163
    0x7060201110703032004090605010908010b0a05090406020706020a05040e071718010603051b010207140604051e1012064a070203190f090506030c0d2f07 67
    0x5040c0b0030b2556085001d04007269140d402c00c0103444002a400300080050005801d95010106005040000040802601d94084641607040003448245500c600e02004140c1d9015503a001050380d40d401d0a0010744201640140304a10001d061081213602401503c00d0311051782c031800054450300801c98080d2030064501010171002804210b01071591b80b854500485c1e90000414156030b03c1e1921750809501c0e988451112600e508a440c1e15a41072288002070306c06149c208000000c29408501035004a0045501550503a640c1400c1c05401c500c0d242d20014000380350030b0100358801d00003020503114107010303a101404e209000c5030325004d030718844a60000351041c84450114944110250501082c0806407406004010900610301008480c0c401c0034907400469403280c140c800503010180560360700c2c0070040c014458010322540030780303030380110b03002151410b48070b880341c4140c0c01c454451310034034048080c54240010741c210703841c090b0000c1158004404032800c50130780840d0003180c480d080004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 666420656 1250 666419406 666419441
    0x9060310050603190c140a1a0f0c030705070e0c211509160206010b18040f060b040905060a0501050c100507020c0a0303031d070f030303050c0d050f070207060201 71
    0x18260300aa120640c0190b000b000c0301e61a50911254200400c0e60880945104040400c00e000c400302240c030a0000c9001030710a00070461a045000c494001943d0401c241040001039511000f844c3c4819180140d0301078040e02c0d42c1c0c8c10305217000d0399104031511680d00400090b20014030441c807844141c03141e0400c039036860740d0a1a000d544026100780c004240e1300c2d1207001c50300c05810f02d849900c811403207a40014403032608015114800ba103401416402240212020000d008440da440d04582040c80d10070344010527803180d10210007001e40f1680d0040c8200d9000410300145101882d00f015000d203c003940e040c0001da40f91401120320b44541d5042c40c41c03c1c2e1020092080e116425400359070b001076a48140c86003190b030f00d400140306020307990003500007d80b220b8030b10401100070b00380981a0b0f02c440c00146210b92509003840c0410b6014400502495030700e40005820702807a104456064211510800040c038180144600d074072016500d0800510030301c8070100b800740c01440f030700701070001c0c02545 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 666421906 1250 666420656 666420673
    0x1206010c21030b0a0b041802070f0507030b090604110f040e01020c0703140c01080402011d1003050703140610110f0118120c1709030a0f03090603110928030c091505090603 75
    0x540708075016400c11421f05643c09c00c200000f043c040040401030510800c0501001e6185061803c211030000d001124541c00c10b505100000e143c18010080b40d1b4016103080c103102a001000400070540f586501e01594000141c19118001c0410a05c2c25240300303c2001c02c60409180480eaa02c000981040303000c22101000300307015600414014256010301d600007450010035a011400280d19000d03072034041b94607403003882440c07030301402400f9942400e204565018a000f000040d51544084401005c1c04a140d0500740170700380c28000e2001240160009001c10038a41442c01403040343c20406a420122628441852030302c24800c01c600789800c802c00c10b000050190300c40781507603c00701c00d40b40c0c50703c1886020f00000312501c40040405001c0d40321036080c07502d45040a0151000300d251544070030b40801010030155a02404c000048850390f2000c96040c2e815032200d440780005030406030440c100754030000382204e01504550b52900300072008034116543c1d030f000c1c00b4602c4c80994181d41e160700311b0ba54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 666423156 1250 666421906 666421919
    0x5150307080106180e031813021909120209040303150806090d090e09060c09040e1b030d09060212090f09010b030a15240905040603080c011103060102031206010c21030b0a0b04 77
    0x2c000d0f1f46500042080300982d100c03c03140800c0741e10030028180607030812005886443d40012010008000d0b01c051034070510031550015124980080004003855650340500003c0c1c42d0358a03590000e08458002c59445081030304030b4690b40c4298094810014000040204407030320b07921549400307003035110020200c07a120191090b8075900001c1c00160070a03501c2d0340c41009010300700f003070061860000c20350302d6a0030240700c181420300304461280828050306510411400341d00080302d4500c0c41c1143e03d02074075842e48800294018049054080d40706e529000045000054a0011802030030707040e00c1001451622407001020880a10030124001e903034076020701e81181c5200000289250350320304001022348900004084402c81e82040e1001c900214698401b88001d124903000798140303660300750a5240410000f5600e20601d051070f2000b0404201041d0242d0145041001c6c899021540b88c9000807001d648513407103030614642c40002420301c003002c0c5450405d10041015114000d122610340340c2001c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 666424406 1250 666423156 666423187
    0x100e01060e010308091909090203010609050c0703030545010603080a03020a030e03030a020a0206010f0e13030c0501140702010515090a0c0c170918010b07030305150307080106180e03 80
    0x410175030000c0658500f070f01c2099070340001c1c2e0003820100b0400074503412580145400c6502e03540014002d00d1402c000e0096020014056800e01e5034503140205090f51960404541210840c0f12008948032031001c82076900c00034003011400c0140d10034032585013000000b06d50b00360b406510018005031410400508120301c650002c0c03181c400c45050110702503600050f403620b141d0007120485103803503022600c0441c0a50511186005146820724480c03c0390620415410f00d10b009001401c080c1240300c0c5982c02c0501440c04c0011443c3c224008102404418a10303082048048504d98019442c000006900d05041e0441a2041d203002c0d0501d8070b2075451102000041440449010034000481e0990001403240034452485103406140507459900705424001c02825000020103000b03c100018069112800c099400c200c4c0c0520300031486490f1007603460880040d00350b066400d800b580c0c8000c1100181504808120381c4403c030b03400e20401a88040074100d8041c520701c448136170400c10a0300c40151035034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 666425656 1250 666424406 666424417
    0x601030c14040b03070e0108100615030905070905070e04050c03040506040219030c1d07020607020307023d0806010f020703020f060f030703060e0c1606150902040602100e01060e010308 81
    0x10300009010300310300340000c2c604103056012451034440440144888c90044c4414591a0b6071070b0380902049040c00038182c6001e501052140030190340300031240a01c0010081c4200034022400100b00c141040d210091442c580303130030010701032818080031600d00d40d000d004403407086030464050701e42c1d0f840b070707600f00200d1040c00c000004001d54600000b101007034500304500d008000d43c4100d19850000d150344d060108100502800c01e5402c1141000b03d0280c011040b180440c3d811102c03882c40300b841096400048084802c40306080c89101212a501007070940500205012912845010f94441d00111a60030b5240e80040040e00110410001410600034407500030708020080c90030300d84107240c1c6a540c0d4000b103d030000040c1d1590790820840d400211510740000740b0401040c5402a5601110303508400d240c00185503641d039038000700b209803030b816404e03015011400080d5581c0d55982402581c0304154507002003418030703100b0b02400c03201051160780d0469021140105d0385a10750b4070b50301c0d0b942e000b4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 666426906 1250 666425656 666425659
    0x40317040f060e1e01051501021f020c011104080c0108060f010e2403090d0816050a0e210c0312030412050c0a0501050a0e21161a040305070308090601030c14 69
    0x903114150511320581004419209500c1c0002549240c050110040146c0701d22403036040d900b04281d40d045a14840b10100d0700c3d82a1408050303580c0e00441109401400c0015500d60101008900403500c2000403541341d08650090b641c204a9858a40421112501480f41140451b104000e203044a081040e02400a0441d080204035071803030401469900b81d100300c41008682c1c00030145d0280c4280c109603019000385002041d05a003000712032000d0241e10560440400f0306c641000c1c0540c00b565400c5031118909429203604803100c005018180d07036245011006440790090024003200c03440200152803007103402240304007612950342070507120760340110b00c024003038024603201001092090103018020b803a5510002101c00b441d00c00030781000182200d5070020840c1e5503150342103c0e2140182d40300c16080c03102d6009210910b2600032425580030001e000c01040c190100424141c1103800303002494041d45a1201c0b542c1c80e500d00030f441c1d030806d02000780750140401040c894004040708100c802c440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 666428156 1250 666426906 666426913
    0x20105060a120201030908030106090510030c050315120a050f011805100b0625020405160c020f0307181b2a111306140d0b0610051c05040317040f060e 66
    0x130503247d0424551098020002049001104202d2414450442d1060700001c3c501007204162511005000307100241c0b9500f608540e0010b8040b040c1d8a04d0281401051208120784583d80c40f460b0868a90404400395211946042400705100660f000c8202c1300a42c0720028004542325040b5880040800703011041d00440c080c01412090901c1042c030700424618400700b84048140c40c410001640c10050071580300002d0b2400c1200029080b8080030009503044039564110040880400e29200c41c591051b180000d0844490301440c58962200c81e0214040505036400e0304008419207540106c46a00c45101c5005912021207400e0000340c3c81c0114828258002400c08020000b18020305d134200074640280e82d22010800d82e0030004c05400725031000e845044100c5c0c0c03191103150310b901c0001c0016004d02041c07a9034818840c030460031140c2808601e44015109041604c00794000c04084504501051030a4040c0105500c10301100344507030361100c12424100c0c1e140d0741d0034014240001d0058480c0c803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 666429406 1250 666428156 666428171
    0xf0411060307020a020406050109060c020d02041107030503041e2411040803090112050105031504080f041215110a050c07050907031505100912030512190c020105060a12020103 77
    0x140c60000440c0150b0055000700b01c26081401040100d50365548180d0601c4005103007009120b40008040e40300580403200f05200780054004103000c2c03c4142c28001032658006511020142c1041c083c500230f078000c1103011081200c8000102c0c4038140d0260140c141d0b40000301103150a40c50b140c5001500380c401d5404501c05070b048100540741d400a8003c10143c5d0070100d2040340325684100317130320204510001d050165502d02000b0a44a100f4003100f1030076000f0b82030004091103001005c95107402c1c81c19005079039844c4e540c101d5400b48146e0407021518a260800c900b121315440e4001c1c4401702d850302170400d10f0701c85c0a041c2a2400d034451a190100707402070f03540c009035a540d0344992501ca41040d88010880c0319886503d081d400000380c114910525100100c0700360702d588926001c051311200138442d801985182815100d1b0b006c1c04003042845c5000c1402c10a03000c507980001070600c600a0810f01c2940207210381a405c2e0b400448003650001c002000c10090610304000d01c0381a180107050004498 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 666430656 1250 666429406 666429409
    0x12070503030d0203010602010c02121e1b07030201120c05041202180403120b0303040b0703032007030e0909061b0a030e010518070b040e010504020702130507080702100b090f0411 78
    0x54102001602c40340c2d5011004100b01602801044050740052015021029110b01c403001c0e103000321011701000081c082d1020341050090000c4506c00d004594445992030600b010315036581c45540000c9002034041e41e000004500d0500440741780300c129032585400e0604100e996480103111070000d0b40e105d246416143d03c44580842480e010b40e020707a54651305551300302c90038401e581c2400900ca02130f500c01c0008000d00e843c0402174983e403680c980f07008540e540520300c613688407103c0700a651040320400121a010035410005001c0c2100090703954603000c1d61030300c03031940d2100c20031510321010081d0080d00c2a030074500031004017079282d103d003000500c0c1483c0440190031a8406ca44030b031404180e0540800828a042040b080108660180390740740a00b4143d1980104070306219650041e50041103401c11940c5000c1002c4210107410001c02051030b100c680100345d91300c2540e0800140c002d0003500c410901d901c2c01085000140900000001e480d4070003013107803910005000360359829085c123400304031303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 666431906 1250 666430656 666430663
    0x1208191802041505030f0a020901140a0503101506051207030b031c11070b03072a0819080610050a211103040c0806060907050c0f030310030b0604050f0612070503 71
    0x40510320b081c503d0294108801d25103000c9003014441020f80c002c24003500160b0f5150041410354805141c04151080110301040f1016000d40240d07034140604880c49214095a42c002c0390310015400d84140c1c081d40e1103d0a440724410840000820070600c1d00242030342e4001e8006805c4a01c0144c2101d4078209200f00d009454220740700d10f200003c5007040000c0343c00d4410010032014245a094203803a50074400c001414032403030564440c0b8031188560703826102d0b200151103145135039002a1459540c041150a00d035215200c60302e0361010032031500c0440c21500b442d0150054800864a81e90300c0c00c501d2100541e4041c414808080c49518600c0040302080611300504006641d864140c1d038580c241460312102000c030035000962650b010000700303d00d50340c03a000b407603400c201d450400694410307506000c241031043d814a1101148000018030074041c000f02d843d01c040ba0300620002c84e403a00c0e4901001b090701c00c15540320205400b2070020608928110045034a8002c40100b201d902c190f40b0710103e4103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 666433156 1250 666431906 666431921
    0x3070207170d02060a0c05070f05120403060b040c0f0e04090c3b1b07080706050928051b210a0213092f03030313120819180204 56
    0x70560014602aa0240c1e0100300c13045d0858a0a4400d116005903850001c040303000300440901000080c80d0600f082c00018401d286c40540d4140189075216261f040071005000c00d072030f1f540c0c01186807039400b6642c644036150000c0103000d00d41d508013844c60800c0070000600360002d4156004458654000391a00c022001212504661641c441c584005001504401911a017500c04481141e02c02c02c1030304001032525600000840c00da00703895a0290424075135500400d900280350034680003e00640c001e00040d4101d0100d41c0c160031030800000c85408001078101040020082c0d480881e9460713103615a00e0f0783d21000c00000e41074054480c01214950001c0348803940000281d0041c0f0464000e504000e40014800c1d02d03048018041c036041a0b8848151816010241420382035013509203040c40400056142458002811039859041144000780044010030040f00d0403d4220101c00081e07014080032449641d101e80700c00300d15181c1044082c00342010415076510280e10030858401661541716505 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 666434406 1250 666433156 666433199
    0x110f040e070801051c0f06110a020604051c020325023303070c02040b0402041505040e1e010303030f090b010e150406080a150b060a21020712030203070207 68
    0x541a0620401c0608040410b03004140a051001e05000c485000319501900d8641c0c0074500184e0718000d800c00c1c0000f400740e06079400030280005075100c42290b0000d42c0c035001328013070015200801d84d1221a09203081000203920090b8000740000000c200b540152031054a8055808a401780c071b01782d0004441c9082d80013400c20b000f84070005d01e0201b4020240c0c000c10440c0585002d071460400c0480070300409480310000744a251500d070038940b582c4840c1c060720020002e2011074400a61210409801500640600c00145222600081c103828941160041c04018aa60882c035a403c64804070080c00400320340807481900c2c0d84051000500c5411064000c245c03484030301680c1d09044d00204240f42d03d000b01c1d1880749040190503c090000401c40006030b81d4061000310144444c1c850710b81c0078100401341d8644c050008a01080e40d1600110080720034810000841c502c1c50200c1c1c0d0701d500724051150050509925001444419406a801980c01921500499041036a100240001d4943c41c0142c0d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 666435656 1250 666434406 666434429
    0x213170a0b0f1915140a05041a13021305060c1c03020903100e1e01140a0b011b03050d0207050102190509040b010302070f0602071502130311090405060406110f04 71
    0x1d0508450840901511100c003414000d8541c4c034011100080710a000b280c1c0c0b606510361203400141d1b662040d00c4c00070040500188981003223190500004010250b289000304001561400302000910888814055003001c480005007800144451900519040380c0140701e00854440c00c0c0c01103004101c0000c1c556a8096944d2000d0010701d410150b000010300040c904000444c0c200e8000804c5e1030f007100041c014401e8125000342c01803805864103106083d240e44e900424820010020f8200350081a000c2c1c0b94070103105941c03c540782c00c50340404000341c00500203002d50220204c068000f00341ccd00c1c0c0540009030818442895902648003100001d0010901c0024a1422414240140a01013509080031810279185849809490000007402080700394000340340e000b0085040f001c420800b2400c48110b403900382111711510700d8502ea000946132903001040040311032400a001c644515480700c007905a607111540d400700a00361803818900b10050074006440181700c0030001d44020003155180c9c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 666436906 1250 666435656 666435661
    0x6041707060207060b0a050907081b0913390e0f042d0b0a051908060103060509010b040902010f200a080304060f09050d0c06140c03060f040213170a0b0f 67
    0x8000080446900c2613002318203820400c00b40c1908174000c1a8003c0250a000b200e900d020380303c0005621a00040c80d92050f0244403500098080340d000d40100c442d100c00001c00017020303419140900501600506c6641b048081d000e8040c3e118560320444000c014254516000424001030191042ca40d0301c0b0708202c40c0a1076a0b110003144080d9090300703024081c4200100c0c1106404628410028000d203030051070030754210304060040140d00d800402c240b9061303902550312032504030043c1c90140c4060b02250b0038180c20080d40d00d81480340483c0c144e4140c48410600311268001c1c0d03490148001301c0100000c44007071004440f50f0a200503480d1034450944643d90f0b20b4185002030072143c2c0c400042108601d442070b8a80058070000f001125081a400d0400d03101d803051420348084c001140c0e0705405214903000b8080e09403412005103025540c200d40c0c01c0c004da844070080c402280960175040031000810081049082801e00c000c8010000320415a04001d040361079210740b03da0309894038150340080108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 666438156 1250 666436906 666436909
    0x90904030203030411090601020d20070e1509010501051b010b06040b12010f08070b0304080408070303050a022a040b030c1002060702071a0712020118030203130f0806041707060207060b 81
    0x200080c0710602110103001b1800c0180001b551401c00d070750003d0600c14035200344502d0070f2120072950000c0403081c08980200351500c031000c800500540e40d901c076070062102d00c0210b603e001d007540c50580301e0680d189414180024000c81103131058101081c0350395a25030000580740c403680000e202801496251b5035840040362140c00190788164802a8840a40c40301071201100c041003041c2100c08040720161280c44a0030912094401c5901c42007240c0b2411030000100740e0498040c160003051a02600c1c3c004424840c040781c440841c0c0b01c1214040002050102d1a01d0141d005500c040c0c4045c084400e186003807804106071100000101000d03034002d40c06c10401541c1000364070301409011030b031210b0310000d81c8400c080c20301075244024408025504101503d520035403001a41903650754000130035070503900f00a9202c1e4042c200407100401012400b14081c40a10610400c9800401c0141f041d562542c81d105100426004502c00e08041009120081003250020f8030340c040c0140d000040c40141d550 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 666439406 1250 666438156 666438173
    0x209042004050903031f1724060a06110f031201090b2b0f0b100810020c150601030b0604090c0906080405060619090c17090a1205070201050909040302030304 69
    0x18003880c45141002c007008800c1078044250707600f003408400c10b6803016014807116001080c081c0c01000d200e041c0c1c5011800c3c44500040d00038650080b8546546112128580780150700200315007054014401d640100003a501c00e541e050201d45000013501e40c21240141018150351200312070340c6240d1600300040c86404400d115184118008481c10410b80c1c120207850510428203140615044000b01c4a01e014800d0b809801d04030503600441c0d081e031516082d030030300d07908404c0d070b0162189511907020019070044052081340c0090040c24001e042181c000c07403e0890700240180743e20304040d100c00d40c0b0b0a1070388400b4042c0020b0705440501281c90485000000c0c62074070303030380c0c0803404000e81c180034440401c1d0003040f0359411080c291303880000304e00d410b0034039a441d8030980c1c03207403520300d1500c030150b00c80b60703840700141150300c601c0c40007001a81ca54001c65540c40d91304c4034014220607010700c0044042c50207003006003800740c03060621504100010300040c400110882c0c0540241e01300000708400c003c40b19 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 666440656 1250 666439406 666439463
    0x60a06020105070f05030606070c270c02030f1b0d12140601140a0c140d110307170a0905030a0f0615080c131803020c1002071a0f07020904 61
    0x1803008000314a8200401058070140c0a022001e0000020101e216038440104661071182c201c03d2081c1c03050740e030f1020b0840c011901d865110414460120701201e40410f07002e09080c01500b0f034000c500780002c134800d02c2565031111012004006018140da0040d06041c003240703581d002103807501d206500f6401c010000b0340b103035007030040301060260080007600d0b0780040d0071018440c0341c200d00d00c0d201c0e00701e64015184501e1202c030207850101445038401c4900c01c001041c1e0400c40865035260190690240495a640030b54900200400041024031030b0400703020340a00398005461514503856961000420706000014106489200c00c151a640030b0000724001c1803920307141403030103807420b900d000740558a85a80f200d019220300070011042c01c060f0510341141616030320700e10f115400e0507064680607542e08075808020707004400d545030b0034130858000b0900c2811035a0801c3c0180540002000910459112040124000394180848000741c0c0380c060f54184510f2107561400009100c1c14400c3c0d401e002d80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 666441906 1250 666440656 666440669
    0x2a1419081e0c0406050702030f062d1e0601021e06071416120c0618020f060c0a02041107120e01020c0d0812040c05100503161d130e010204060305060a 66
    0x1c00c140051544010300301c400700e0700540790060300e0711454400030307041c03486014031804d00c2d04c0340e0810312106402c618000e03058030f10700f421010100340070302d179082c0002c0c8411500d0103041e904000c0042074103018641d80582c04201403040d07411602540c02c01c2480211a004440c1e95503001c101040311050304030201e02550f2100c1e451440c1000101d40603041a2030301110001d00c05441c04191071303641070049084003140784d4840b4041c440d6a043c0711029190031540d08050b41300d030740f192591030558180201210aa441150090301d00c500b5079809020243c0701040004420810801c0f429002c540940a20080c00703126a0720320103e466081c000a142c841c10b8402c0900c80d0025810311000140604100c0c3c0ca0b402810b050702e062907540b42071240c0c449440b130344115000458802040031180c0e01c40c00540c40f0f44100403918440001491045075400c0c08040103540c1d4a107000701d1012540742c4490869902c070751540f008201c9035504807032603003a0303040340d07101e4008240c41e8070034800c05140400c00384010307000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 666443156 1250 666441906 666441961
    0x6010612060e011202100212040b071a010e0103121707020109143f1b01050f060f0904060b040e070f0b030921070503040e0a2a141908 59
    0x40c00421001809510002032080750900c86c4c0c840307142d00900042d900300b568010369684860781c5810711601e0f0352100c402160300300c0c0510300c40c02c0c6480440c14114142c3e400101001480e81c296a02c0c405081d100d102102d040c0566041110740100c0c002540d82c0c400c00f03181e4008107c0c2d20040c079003480980e070f5101600310340d40c00c0142000884038407499865149120705080010068a280180100040f40b0024180e04c2c02c00041c0d14840610410b02a10342407161b40081000c5d076108005a44003103425a1100c1d4020040651089146022144c0703d0b0094001c070800690146500c7c0050100c07440d545000340341d500311800030003800b0f2140440d94020013404220928503d04008441c0e107a1032003c1c00441c2d00e1031042c1d918510a6600e0064403c426070103402c41e6904c0c1d4658a910491081c103d9610002e9410480c1000e841505061414121401c50004046d11404100b00380d6600c41451469900c0f8482480a009075102005002e08402110f403680c4906041602c48010700c059007d01c000100342 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 666444406 1250 666443156 666443159
    0x2040b041a10090e0c031e060604031101180f0510030506060406030c09090e030306090a0c1403062b05010b060301060c0f03030e151009360506010612060e01 69
    0x4203030445100c00020212502d032088442c00505441c00083d64011030360b1841d0a00410000041c668010b50045032124060700e14400611100085d10a04035041a0402000e00c070400010b010a6004100d028050606105445800180c0d4902c5a403982c0304044507600004200800c0c1050507005050507036a1038180914541800403441e54411841404101a9509004856140f042929a0150420309024081051105011541c03600103030359007032152b0201030104003440c4a031702c2804049005174880301b50300d50076850805015000284161342084c00100307621201c01c2c140d1015044e00001407442c0b90454500e060103421580f114902d035001d000c0c100010303c0003a402c03610300761420303070f0024883e60312400c549021405461203001c0400248107840018074045d122044140c400c0880050501030503a642c040030003075500510408c4030b0801e003d4101c95040e09101d0f09811032880710f660702c840e40d003042da4415140c69001d0f030000300051345403640701c4400309031802508020303d0b210400f02c0d190f5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 666445656 1250 666444406 666444431
    0x6010c020a0e040c05030a0803040c0f18151502071401170a020a0210060626011406070512120a0b060301031703060a030b010b0a02210304080f040b0a030902040b04 72
    0xc4594024600c0c8110321100040070413101c251001e0260001505640c0140090325003883c403504261800c40b40ca00030300c0004030307030b05800c0512031044511002030840c548040c035010710002e204a580741c0f078542c801068080b4480034a41c01082001000364000c2c00083d180500c1c079030614802050040c10441c3c003103a04540034542c60046904010007030801a95105541010391600c5101d595440096041c20f0000510681288207041c20b1202c051040000e40c21440d89484908001d003c5d08941c5902e6010403243c2d81001c1c7c0203005000e2142045801d03a090404a0b4182900000d8095900040305001c100e00035002c0d0183d035109200650f5500d0441d411940e0741443c1d16949100d8079407202c00800020701503945c85c41e2a600a5400c00c0103c802940c440000444039404046d10700058401c6940e05032200c0e1040480c01c00241c8251b881c5030030b6803039aa45035031003a44000564548004140804559450050010000c403469074400068801e0144103000948008400c076612446c900b040030f0511 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 666446906 1250 666445656 666445669
    0xc05070b0a110328030902151207031e0903090302032b0311030412051c020408150f01050909120d0f1410030204020f0c010221060907050a030207060b030d0f0806010c02 74
    0x9018800c42480e04e030480000324018444d00d20040d51144a102d101203800f00c00c80300802c41001c00c1d8004842a6440741c10540544500910071105d00d403490030b00b043c0d201c0c00c1c3c1d446440d4541c0309244c050b0a00d51f482e000640b5203110340924507100a0340011301d01c0c8104034089425200c40c0702d81405d1041c0505c910341018240001030000d40428a210540d0036207510500442c0c0195030031180440e00f5415603040741c4001c2d0083c3c051022603200d88041921144115403115100e01c000c0c007114a41d503801d0030180a505000500400c500703200700c004c41c48820000c0d0003c0c0100100300d6000258400812030b852080c0e0301503c8070300400e00b801005000d4024680071040080d280c0540e000350343e031440944011503a00c43c80c03802c0100d5500c0468203c0d19001c41040c2c100d42002082d441d419692642c030200040108280d03a02c001241c0104440403046000e5005030240038020f21000600946400100c1e0424100d10000c00c0000c00310141c00d498030350010303c0b20b50446000c1c03070440806030b8140d010998 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 666448156 1250 666446906 666446947
    0x90905280503040b0325020c0a090b0d02041d0a0609021009030302060a27050c1905090f0402042a080711070611190f1205031905070c05070b0a1103 65
    0x207000d000040006d98400d400040100e803c1320710200c4c013500000e8628002c0d202e1198410940c400c0c20010400144003a04d402200c40503074000b400c0c8810a80320380c7c00c2200504000711014400302080c03880b14079801081c84809005402104042040941c41c410000c107514001e00c2e80090000d604428004a54009002e6501000641c400202200148580124144050030001407141c0c009686410400e000c074840411940644580d29030840803035941c0c102d6a058000c5039007083d0044002468468042c24040d08980040c0c0009200840d40c11281c2080c0e4ee041c2001c1d4187c1113525940314901c0d449a6401c1d407005c0c0d2480c02d601d202e03055014060b01d074642441200d00b005005d58071400308100a0008485981d035030090041c0802440c03504404840006074165851505030484001c640e01400449200e00031052211035403840b00c1d00014021320b000340c06034040260248003080090010440b82001c0c1c12808000307500d070361611030010303d0340320b40f030303495000701d8200740012240446410f08500c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 666449406 1250 666448156 666448169
    0x80403030c0905090702010c0852050702211b041d0706110a030e06030903070b010b090307050d08032806150806041802150409090528050304 62
    0x40c0501815600b182c0300101d9030030032640401d4510a01c807041ea015441a000301404e0344aa01e400d07510a2110302c0106030030007001c040b25003140c403000039640e02400c100c200e8926910f4211030b078048211f400806440004000310100b540081d004055250a503d401001052007281c02416170004a0792910b40703004410201010500320b2640301c031591590049850020740c0e180c0c0380217071200c00191a035070359031501c11440400e090700d044030b42e003850204451080c04d8068550340c40c4240c002e401d10004e903100404100d0140428841100011800701c04c190003082c038510741303070b456071f842030304142c00e1007465400343c0d115013116080314000411075810380e503100f00c82c070b000a907615410b5050118290603945824518900d400b201068031041119402482c0d4520743d100001650760b501030004407906030300900010020001d0842c0140f130003564094014921124142c203144c1d03142001d406455541404466a4004881c0354401c060b0b803030300e5040d1500040034001c01506040d210741c1d40700e1246000b41e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 666450656 1250 666449406 666449411
    0x4030e0906130f0b1201060f0e2a07240506040903020a02130b090f1006030216140102040803040e01170102040501050a2d0206040302120301050a0b0903191b090c08040303 75
    0x34610707290315a00048058401505d0b2a4103e000301d080c0900801080c003500107440b94004001c50911f00300054103200700d580b074445a00000841224450304103002e40e540591300310400903100000d041181840840e5019030b14110401d0b00441c03036005030390300180464081d600c0c02c203000c004254005580b030710341a0180c13200d410945812065031701800054a40039040840e0006100354403400101c0f26105d140c800b05242e055a1700c482c001c5040e0300c52000b45518841d49245544082026100300c3d0488a04280005240c5555800d0082c1160081d41c800f614862050004000e040140e001e100c843c9041d20008524042c20000044c100780034560161041180b458811025a401a292000a0701e1031009075030310006204c0c0000d590398000c0300d048005001d000008a4190072010549050f110020a20f074003090418102000c0c5421030000640d0501c42c4210040b101c0011450050103140119000fa880072151340c01c0d0b0561414a5201c1c18056282c86291207a10b03a01088407030b002517062502 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 666451906 1250 666450656 666450671
    0x1107080702060c06010308030106030f060510050c01090606170c030304031703090703060513051c050319151d0709050f0f0d0b090d0f110601030803070c080a020604030e090613 77
    0x460628001c03414440290b204e500d00110a100340c103005503048071183e40c1c00740700c2e071071741290310900307031602d80c41416041056400b0018600b8065006404003c400400009204100d07849640c01d840141e13000c5000100c6c50003080031410030600c4151031108040d0000d41c035140ca03560340c042d104a00e00c0380c1541440000700108010b004180b1400c0001c54008409105a0400030458030440c110003104880760f10030403642904268014110046410380341d10f40c40c2c110ba82d031030381001240141840400701c299844004981d04074107801d1201c0030f030815040480c1c0403603000c9020482010b01810790018468612010400b542d26850350030024081901d40101c00159400480c01d2000340e00c400900309071107402000307a12a000240909001100d41c0c4d002d00200b100042960004102c1c5006101074100740300600110320440000d641010b103916200e0800820390719010700303680046020400581220703051106040c0d200000c0796075107000b180c481c4100c1c1410f030001000760800c10342c4424031940305c265 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 666453156 1250 666451906 666451909
    0x601090e0a050321062403131b0806071d060a0c02060315041518150e0f090c060a1d0f060403060603061802100804080d1b030e011107080702 62
    0x1440301c00c5900034100c9888040009002c403040091141060b090038000d0300140542c6010328000c003c0014050141c810148840035108269000030181140a0180015000052100f00c4416941d1702040703403400805050249440c14928007034120801c01c081810400e940c5004e21701007042a1a0444146559401620f001d85140ea61807078040d40c8104048100218080240c1040d031810000b1581084554000ca05c9071110703043d03034050030b140e800c191940c100000c3c6030703588040100c502501c05e0812040d41c606c2100207002c0100c2c0d042c00700c15007501c24481c1c070900c08c11064440b2581242d801e82412000d001c01008101d04241c00d641c480031040740007115031502c0428240841010341110358694607030909101070066448221141403034501d900602401c0c20f90302000c034a600030440d01c1440c032806401c8603111009401a22585400c1060325900f04180c85040148484032140b40844415042d01804171040c0b80c2b66151a40d041c2036102c01019003500449081e154401d01c404c3e2503815500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 666454406 1250 666453156 666453163
    0x17040c0306020408161707030807060e0102041e0807152105090f1005010b072d1208060f0306072d02010905070b2811060709050a0609080601090e 64
    0x3440944020310005004c6207940000c40c89400301107400182d840c04944e10140c00e001b14101c0b400d001301e1a04800d00031700004903035000420105028583c0419148040880d80f0308990081e4003860400c0b4070507d49a0001118541030402000c2c0c54015048291404152421001814040b082003124196001c0528a40107508014280ca2238108000034500041910769070344e0040c40c00c0c4210300c22940710b07064000260161034140e480d001400c90414803290303560130485d409456402d1038041e003c9059400d02e9140080000c1150288a103c2d521031620b5078083c1c4985070240c41c03180581c80c44015540d407034600280c0c0c15045065460000c00380d420000c6080480c101041034805103800d4100710395001075054000c80040c030702881c142e42e902661020f84903441d114903000000c0000c4d80c0411921030300d0345c04c0c0c0341403650320003400c00d14a03141d1490b080a092050440394280803600022040c0700703500380703018124040c2030581007040c08141880c4070035944640521070070700040e444290004c1145401e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 666455656 1250 666454406 666454409
    0xa0507060e060702250506131e1502150612150a06080d1b0b06132c0c0a0312110615030c01052d0912010f0e010c17040c 53
    0xe0010802940090605501c64000340c0e024401403040c0c0e282c0d441481d58415000e9818100c00920380701d0986084144541908107004445009000c080c0000d0620640b4a0000e812141502c075001741d6402d1142000c0620140c0c011902154010750030580301032103901c003407900702d142103800340825442c40c030075146065010302785000000c61843c20300401c0207841d00800f0565030b01c581510041d0b01c103c9001c03256034000c840201c09800d80c001c24100410103003149a6000080274203001142400d1481d800c0aa442c08000c0340040369040020360201182c4d0b00c3c0050b03038008814040d081030072200700080c80750384a40c040079040100c13400c0410450b174018048606090002c1c400c0e24071034503002030304029580703d00741503602030b01401000410a6124000b00c4109000e090048c20380b410f150301124042c14102c00c10409012000c100414590b0350740c84d1980c551910610010a020303071108080c4059a605060856143e070506055031103081d0018041c501c55944110640d4403035456080000c0714000c507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 666456906 1250 666455656 666455663
    0xc0317091c03140f060a030605090309041109030c04020313110a0512060103050c090c030a0f0e192d0201050304060f02040f06020609070315090203010b09150a2304020a0507 76
    0x125030603041c03803034054004120840710300b41c0c3c85845660b00021038680503012604107038000c1c2510002d00000e0b150b5440107400c54a00002c503410070790040e02003800c44800d0031040f071515801140c0b101c071501c2e0030891744180c100281c45c15411030070408441d1036001c01211000b42221803101c1d180e12035484040b10300009040003084000c07442c1c221f0a0071611007400307001c01c2c2c0d514020422188614181100c4090003901e848010502c5d650383c18840ea8000c111490404070780325202c0900e0030012004100c040248041c1d0074510701d03004064a40400d00130304a5080308181265411418040001e444004280d40d40a0900301d50705d68132407030a40020201c0110104095202140c04940c035440500000140e07030b0990200d0780c080d00d0309025180d0312440b5110003082e40404d048c44000382103541d044205c0051000d0b001040280da880c00103030b17043e031085800180c034101002c01c558840c83c1581d44a4014000f211480040d076901c00c40e500800100039000328040e46e0000b8607440c4084c8107000701d441d80d542 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 666458156 1250 666456906 666456943
    0xb1803030c0d05030108150405121605100c17040206070615031703012310110a020406032616020d0c030222110405031c0212040e070f0c031709 63
    0xe0b03500040c1807600203000345507007889014403107520801c9100340c440c0119000710040008120602c09089142d22000d5861445090b402c0c0e07070000200104111f08010b452810041234007500c4110003402107603840a0010050040418400941c49a4003221a0b0310341001c0e01041d1205190301c0c19040042e02d5000070308024130502c0242c040c61529024505a07440305048a05008240303860084807126400c046070b000c1035041c1440101c5005965a500c0b43d0800e40659140c407004d80c00107011110a58000c0c0e07540307094043c48400b0b8041100e00e00e050303240c03416000c50a1450000c642404c1d0101420001d0080c04107220007000c0c0116985004001c650003031240c10702803811484070a04a4032a0008040181488015841051024280d030255040a4020003640d0040e5602e000b05000b244480300035030107201c0600d81e00016420061004d800c1c09128500581441400103008400040b443c50401c0201c0351442c001a501041c8010300181300507040b811511240d02c104e082c0b07940ca01c4103001a80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 666459406 1250 666458156 666458173
    0xf0a1811091512010c2c09330306010501051c1a310209030307080304080f0310060210060f180608100b0f0f011e050909070503060310060b1803030c 65
    0x2005411011081030070340d407401003840e840030884100c00e0159180d000306d100c91000302d048078284402901d40c0804c14208440050701c0c100c1c062100b8140c0c1002c0f00e4000c40341c0200c04c0c0d065040401165005040a103042c602d8808008001c0402114030000140d403a40c58081c405213031346d40e032074442192110042c1202c0201003030121f4103041100043c20540c2d100d1425214400702c5a0364820f031003c20801401551900c130890340c0b02c14a0341e0009004452540003404070000c03100d0ba8401851044c00c0d00484104001e003000000fa181002d01800065281e0610009002c2d0302c0d160001c00040303c40302c0e00080130f40c43c0c400c4501e9014212581140500b03124140c10050381c6c0041d5000107070882d1003502c2040c00e000c05002400040c0b0861150f00340802da01200d40c0440c1c1d4070305000e40d000002245001820142400002085441c040e01c11100040b008004c0c06070034034040c07081c5910010003440421080c0d24041c80401d05005040a95420103c1c0c50601d107032a84092040315071281d14042540c0112 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 666460656 1250 666459406 666459439
    0x1020d1b0c0e15010e010f0309080d0f1508120414060d1104060306090e0d0f0504080f07060f02010b03250e0109061a0c120319050f0a18110915 63
    0x540200c3c0c505180303105040b80c0c2225540100848141260107a4901907000c5400005402a04200e0011981e107181001001410001da01c11115050071144006c17074141c5601c0c007a015007590f2a001012107800c00d00601d100c410000086604a0340188003101e15180c04400141c1c40740030b600349000880c0e051400c0000c22055500007001a030741c183d141007205644403d000011150342c250207042a61040503091400b0f40644181019002d507840d0181c5070586a070350b5507003040c5905e041c03480194070ad4803084c0000b41d0062000d203c0c9091a1000300000201200041d660300c1504041520303110502198020008480700d181b00984050346650601d5652050880d00902c0f086c8907014202030b80c030384980c90400c3e40b00d0841e1701030300d90301005009419550002c50559030025100c41c0b0070305403544454803802e00d18065184a0120401c0701d104030f141c009142411fa0341c1a0145c100c0c81c1444462040c00681e0000e2032040340c01095038200001c3e50344016919200c1610f80ca04d50340100c40110a019a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 666461906 1250 666460656 666460679
    0xa0b090901050406051e0a0b060c030a02062706070c060e0a050606030c01020619181403181207120c3b1506070204110418060509040201020d1b0c 64
    0x1e2482144208480d07900da01e0344421810b103103820302006c24503030004114400e0064000d4124454020032086c5031003400300c4410314561050307040303401603000303d010007240c07a281103980c056091100444c0c00e242e0000c001c0c0283c913a80c00410000a10641c00754050a00c01c0e65070080d05c025040000310380c1418003074208503a8403141100d400d0301ca0700c10403007225030039403022072510f0103103070400e44d2804208403c44100020b801c004801040f505e5414070b03500003254600c005500d1051000014660f10624018204500404064801e00440782c0b10004000640c0c00182c110481c0d043c11050503c0450310310302101d040a0039801008801d8000c4002050b45c10039262001c18142480450201a0038458110001c0c0c40c08860810b44414030981c4094903080020040000d544001e000041070714240d020280103802940208a0f580c100e5051040a40011f00c240009000e0854996605141c15030000713640e2180401100100a0624003807030f4401511113001c007006500920808020b522410740700e50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 666463156 1250 666461906 666461911
    0x506030108210703020c0d08090a0b0a0e0406060f0311040f06020c09090604210210060602011b02060c0a1b080403060c08011223070b030a0e0706260a0b09090105 71
    0x60b00c202c41c010312001c00e03000c2c00071102d00c1c0d03615030043d0562444050401180016101c403e40e6002c50800140b64141d80e40700612000d00100000546c4800c0c1d007210040c0301080000f0018012440c003c400d01c80c1c981c2200c10500f201610307113004160b405484c1050076282c002e581c0954040d9202c0d0001103082e83d008904000302c4001943c62164950729401c1059490105485c0949003241c070005e94070f91100345540e0302003000c0c503a004440580304009000e40480da29684a400180d6450242d02180180000c005407903030510701c014041c608211030034442d940304465149040c0815500c019914445c0150300306c1c9280e030840092611f0340d507a030504001920440c00c0c0300c2e000420020001c200340c056022081d680c2d41e080b1112004202c0e410350584403007100c44026024501c255800040c007500064000c600c04c203124603000c124a030354a04003d14003000c6800010601120b5040c101d410311428400d16141c507105600c560f582c2d140c03002d080c03000788007000000e038001c2d040100300024224150010390 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 666464406 1250 666463156 666463183
    0x50103030315030c2312060414010908250f03020c0114040b03040b0a0f1d01050114010f03020d02040e390f070203190b04050f0c0a030b100506030108 66
    0x700b04a0210b5010700d0181c12404000c1046451060910000c25540400d500b06000f690070341540000180000b020303420a80c62803261a07000b0410030040204440c4904500c040c100001d0100200039600c050580c001d1940c800114001103200d01071260b000c20814920580102018042140506009499204500c801c501207807070380144c0800341c0c1030f9100b19011138035001d8440c0d007117171200d658a100408000d030410803501d4840303010300e42048180c4501c1b25680f140f04410500341409511407425540b05034008050089590340351700f460303604810a040d0046072031900583e612405041c0300001d01860308080441d0601c50100f02d030411158401c070505c22029031aa00044802000340300c00500024020102d082c801d00c1620940c1744424040c0c94013a1008003a180041d00300c01a00d1402410800d0540d80030070541e00303001c00e2050500040d40801c9031640907001c000c40703d50100307285020030303c00140408041c10000f1915411400001c02404002304065501d5a4034480250b84514604072503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 666465656 1250 666464406 666464411
    0x1f02030a0e0a0308041820040302040b0a0e0106081003080a0807120e0c01180b07080913140c0a050c0a0c1d01050a0909081908160806030a08031f090501030303 70
    0x10703981842d190800e0421030740d0110200703203403600388200c1d14907070341a400b030401101351202c06500c032210800c0b0401d030381a9611004c90f07484074078500401c000e07074144180b906e02131100b0074020300030003d5076103503281956102d003840c00325a02c41001050354202c81e5030002d403151402103484080f45074020001070041e1034540d603640c004150340308140100c801c1000401e010b03602883c0022041d50003180348045080301d9065061845990701013000040c0c3c0204003ca580c14800511603440e442d20102003520805001d504100101001d0441a0b00130009000c07100000008900c40c2e00e5988914111280005c40701e0070f13503045803400c1ca44910f03006000d00a0207c51900c00c1940d2080b0558401c00c3c904075a0000d205c441040d1030078080500601042d9001d85108504000c180801b1104040080c00025980c1d22500a841c20139082392400c2d560400b136400700007000c404d102c002c0c0e90001d0840c000a81042c1c01564139162142c031218040c0701c01c0c0c20305650303100907400000e81c9003c81d48403504030790284d1010b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 666466906 1250 666465656 666465677
    0x10c14010f1533030b030a1a0c1318022106011119140109020a2903010303021507110d0903050d050f0a03050a0204050d110f10020a030e1f02030a 64
    0x8032050101140d00c0080f4156002e1100742c0c5069603800030300c00e559002e00380010340c1003264000c00d06040100c98140d42603166801a68555045030402c2c1e07600c0340c20702078030341d041c40f10105068021300b02c24458034606c902c8031600e1b10100b1943ea811208024a440013480b16030681241c080204101240c010340030800001c4407244410303020030018801100701c4400429522190b071031500002d655a440e2101f9943c402c0c03104016180c0c012540081c3c03c00036091a030314030715071842075a07401e05c0e000c3c06000c412007440100700103a00044d01041010f03c9010030b2066544007402100d6011550154001c1c521400399004045908140054141c034003c0c4152851398200c10300540d594481c0c1540b17403010000030403a0981240c483c0e0700c40b98100c00a158050304d0950b49100140303036203d00700c9099485070707038200c4000c41d10325000c0200c00ca80c1c1030130703500703861a0030300c01c0c3c0003039240c41c0e143c640542403151046d50b40e0925a00d090348c0740c00c1c410500300920300b80030b2032510003540c07034002ca00e00c400454140000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 666468156 1250 666466906 666466919
    0x1d0405041a0f16050f040905010f09110f040303110a060f0c11010b090f04140604030314060307050603010504151701020c120c030a03020d2c0d030e03040302010c14010f15 75
    0x201900c15a108203d080e400d0416031821262039114280c1303400e02c540207210100d061003541c00740c2c6009000c240c501d035900d18200794410003201c290301b81c039000b0000d04104010080517680e05450480c1e4150600c04d119a80d1842440e05212409200034401c40c40c102061003041c08075480035412241503600c05a1000105840d1403c031440541615400030079480000d2100c2e81642c0801c3e80315104054040c01017556045c410318240742920201c001c244c5503030204260b45100072807154055402c030001c010540c600404a1081c0c807040c01401d020b50f03142c1c02c880c0c84400e80d00030400000c045c84108401c0c0324580600180c001c4d084064507180780d0152801e134205440144080e00c03419001c0d40051450081020340550081d402400703600601c6d1345582004200ec03d11010b584501c29085c03400e03249904400001030304100d039000d52801031510b071014030820301c040002600c040e05c1d42800d11145400080c1084901002421a004525801c007950150202040d400c0458140515000d44000d182c580d007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 666469406 1250 666468156 666468181
    0x9040e011a0604050306010b37080a14060103020a03110403200108040512160f0c1502030a020a0f06091707051b0117101701061406070b01061d0405041a 67
    0x404c07594964009030042c8003072280c1c807004002602d184000070f88541e030f05000150038600603a02c00f5141716006801c00c40040d8012400a9001040b00020004143d08141d0790803c560007808842c1010340c00b02cae120741e40340d0080d80030408404010720080e40719541e130b24140c0c820b41c5011910440440303428034010125400341024602996104c00a031050082203120105690080a000400d0344030210140000c501c0310886880304502560003000040c0c28a106107040d090341d10440000c55100f00041c50003207038041410120154841c5440ca080d4084d424110b000c5d206001029000c03200e440343ca40c48455480c0014503c503881242510300e03800d00e007182641440004244180400c400ba14001c440c40d189003140340d071018030b008031700c01c3c4982c940d05281076a14900116087c03e80d900c1c10103201000846942400d5014202c80ca036190000170307034541103c3e02c0c0600c224000c0c8001c450b01b2020301c444884500d601d50038050300800082c50241420020310308640d591581403070344000400e40c8a800a03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 666470656 1250 666469406 666469409
    0x15091f081509010c02061b091311190e0d020603041502031e0f010608040f210504090608060106050f03090c04090605070e01140a0507020d060c03060815070f0e030309040e011a0604 79
    0x401f103c10456003615800200f030781311041c100d501050015010707a007070805200b80c0d8840f499141000382c4500c0c4502e04c034154216210880800e02a240444c2c121654a080c8000e0400d94150350741902c3e5140e502d4111b00956295444001e102e0000c000c1241803916100a5804280340c5055040151204041602d59000a001e028001000031002401241c4d80c0c0240b10038162240081036069500304030700222124010100c000028400201042410003a0040c103001c3e022034009032156526040c0041d0442c071810716001049034001c0006510182c051001e0348040344007034000d11001000d440c2c090004c00c411103069000c948941c1e00e4400c103502c01c4150300d807000d01c807032411803070320804d0141540c603500712920032a400b0903d00b603142c0c0002e0a0340506016682992408900d1a041c490000d0034004c41c7c07240715032684504002c11020aa000c0305a104007006418130040320203084010074110312602800940250401e81c0400301c1d4041540070b0703220075070204910948440000c08100351403156 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 666471906 1250 666470656 666470671
    0x5060714040501080121020a0e0a0e03123105011b0516030302090301060b0d02030403091502060a0b06120403020726030403020f0f0306041a15091f081509010c0206 72
    0x4c100c01440700c484029241403102240241c038184200150340061101c42c16138000950780c405240500228075104d008020100c600c850103181041001c040031050404028100c1d010b443c0b2002040783d100b00d00caa101d1101d0b8160b00074407440c002e40f0781081070180c07800d5250303400308100404110504a1080c81030b6449064114158000340c0c00948049001e0341202c09042e516550340d400004911200c18024042c540ba8901e0140c2c881c0360070300317010b4488081ca0344074440040390804020b04044e40800c8465104151130800201705e0001c1d0080b0f426170240442070480380412406000600d84c00040030012100c45038082482c02d62040e0f00001400d08540c5408006c1d44148020b00041c80c169014904036003000d440102402000300009180070429101030b500c810100135001c82b4043c02503c016400103003001411001441c0001140102d2401407040d8880c2800e01c1154001c00d1071015800000e0400300210b4035011007500a443d40000300b940c0c4490ba40d0b290864200b1a1400490005c5c4900c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 666473156 1250 666471906 666471917
    0x4030804062a0c0507060e0607060507020106090c17010f120b1801141509190902030a02060406031d07060509010f02120a120f0b0306060d06150305060714040501 71
    0xc850766000d0280c030015154102c2c90084031906640081c065a1404109820f55180d84015a503130034a1410240b00b904110100100418404041c0c0c0321901190740c01c507408600002e042c1d0f41e0100c01c034010002c2d034014001560820881e003120a81c071200d026816036030142400c05590703886032100c200e6212841144d01e6811208444130100c0d14000d01564403654403004100ca5500b1070300301ca4211211207800c4038a0f045d4a8041c0b10742041301c010002000e030030a44181443d070805580b81e8034160251400c8420b00c64542520400f19141804880034007a8040d0425485503103c0001401800b003820394140c9010041480003450300300000c0720012a0401c1e1105c0c1d20303003180701004680d40040c1c00200340a510940d1042d1460741d100d80010715030040969100c841a5442c1d00015041d1090400541107007810304080c5402a68042000394112004589000c05400e90b40340050140841040d04041d2030610600001407140105030688903144507a58141300403244200e1340f2950145000d07282c0040e2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 666474406 1250 666473156 666473161
    0x603022e03090f0f1a0a020c0703080307020c0a170d1805100207080a060b0f0609030d0e0111070e01210b070c0201050706020a0908010b010203040b07020438031005040308 75
    0x1e000380d124030307901030264400b004034155580f500c042c1c0c02030080c0704650700724680503d84c0110303150300111034121360300035002e40c90840e0b0020090750351401404080e08042c000804a804680200320340ca81103070025100e60003195031400002c2001014000761091401500d9010417024860481070038100c28016101800354103100501048481400f40310b400d40c4104500421034600c104044021548a940c0103d161003c15040c000a00c106035400c83c001c1c01e05201c1c0e1551a94045031201d807015441c90b0464080e07585100407144601d5041c482c030390901440b20b01040040c00440f0b110705035001042d440300134000609144014410307810001e13260f91001004910114460001000003a0051510a0600816440b8a42240e0141c00400d02152019100f000652402c4c0120400c0300003d0000d0360810f807500d07510345040c0c0304c4c9110080c403881e40c2d140542d0302d418882011040802c0100c2c82403080c0078890550101c008084810790384648600c2e00c4e4902c00301a2030117110701c202e42c503903104031094 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 666475656 1250 666474406 666474499
    0x5040c050f070303200903070b040302180702010b15030108060106080103120c0204270b240f180c0703080a06030f230d0504030201031d030702120f060109060302 71
    0xb5000080201c1c20107864000c80c0400e0f51a4061075a8409a0b06802c0c030780c0c541d00c040c1018640125640100441c19090208201507603808a01d804290800c10401c049542d68880c101d004008829005901132403a2000000b942c1030710003d181030318210402c030390380307070362541c0003034600c01400d01c0014070000c50304929400081c8945c1942601c1c52000d00b0101e21301290030341d040240c00c103102c8000d0074084174008140902051031300a982015001c1798420351410750070004013074500c11071802805903e0240c083c00050b10f0791244100e100c6295000c09e01c03541014105168103920031642580000e03071075004074030030308110710421040b02d82c007501d030807440181942c2d6038000390311104400031419200845556008400c0c0080f600e50006a45d603180d84505510024040f11b090b4034005d12001c0d40d184c03140c46000c10000465118680441d501c81c54101035845007031405181070746500c041d0007410000529103969801080c1901c0c801c840c1c050302c45000e81c42440004002c02001e0300c00605500015190 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 666476906 1250 666475656 666475687
    0x1050405031e040f090209041409100e070b04030804080f0c060a08190c09050102100506030a0201112811060315130b0402040b190f02030405090a3305040c05 69
    0x10b903003030000010304140d91482e02c0d1a6000c43c40d48444004d5030000b0310844075281a104080400202002038002e50800c3e40c0d5032a0703507440200e11005150fa5030943e0360f00300e080400160000748090862255110381b03078071f0404216040780c8200765040c0b00e41414502040d03800702d4654100f6101404903800d040480b001200c1c10103018002000f0003a01000030345408a0700d0084900801c01030b190701e6034903072626000a1034a6441005540003610302018442d5075500414104a915024170f020844c94800c89051803e183c1401c0301d00c03942001c131448110200c008030311100b1403a801030288004480074102030209510003213640301c1d002c00740c10810410034501081c0380400b00c01107034000685240190041001c0341e000b604940150701c0d012560a4140810074030050084201d031810707a1300240c01c40320281d900c2c0500d0280724441c08102c0e0010b041c2007115130000d14140e071461890640240400141000002036040740c002d622150345000c622401d050080744004059656564a850110002c0c480b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 666478156 1250 666476906 666476947
    0xb0403050f0d021308210f032805010303080c0304150f02091c0b100803070f03020c15031014010c03121407090e061c020409030216060c050c030105040503 68
    0x40c404002d100d408114000ca102401382e9000426407000d1560800082a1a001d5040c20f90030303440300e4221001407000d42580a0b82d2030220601c01e03003500c90725440ca6002c05500c45041c403000400c681032040d8410f0502c0c1d080f25040b40c0c020349850205071a0030000051030b2000700c80c060809039401241508041659000d0705450115034001401c00044500040203007881c21030144026024031241c50500c81541429500407410f441c008040c2032410812039101c1c0074400c07010304940b2000b00d1400900d8000d110082d0f00307600c0140350305c64143d203030b011503450391b00b0503100b030008400030803c040749401210703646201c0944142c5400402c0341059508444554503140c42905498861070300f809051410b0108901079000f0303898620036141001381e0001c4019009040a04c201180300c650003424110040b10f0309a02d80542e0041030303510480c10142d18002d00031603015002400c8005c0011040c1e4080c3c100da208034800d101341d0f207022401404042c02e83e807003a2006041500200174084006018071030885 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 666479406 1250 666478156 666478177
    0x609262a0a0b010b090a0510080105150f030a0c031404053c0601150804020f04020723010213080703080a050a120213090e0d0c02131103161404030b040305 68
    0x30318807002030340c6105000000382c0c031003220560045841003941c6440c0303800c003014090542d044d0350710001c21380b402440c04038180701e00750088001799100c03207201a1045c101d0b2091842d20248694a0904a0f01c2030300500c040d400020001c1d00d4408008002843c80344d00c41c1c01160000001c00602c01b4203001d054400c1203040002c1580781d040c0e4070280984495140003103140555070064440e0b580340c000182013003012020003070f04000b40c4100b0400180da42c0c2d18444074021041e20f005031244440e24100703104c40f0b103400d0074020100358070b025081080c3d01500240654100004e01e5809140d44000d01542e82d141400018107041040c01798250b502e10030005440c1da840607190003031200e00c1908030f10089a0198002440860306070002744410324890040c4080b506201005003209061120000c2010003213078402841140d0401040f00c0d041c1d80d5800c140c05882c580b85455980c2d0800e0000a0b12448210704801d005c640b00003500b00e180700c01c1c0016102101e030441081c0d9042d5540c0c1d90f00b140c4680c030200703c12 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 666480656 1250 666479406 666479413
    0xb0a0b0102101401051503100b070807050609250e01090b0a170c041a0f0103110d0c030e100606020a121407050f0106051002070b160609262a 62
    0xc251102c02401500101d54036000b0721a62541050b003400403008071240000c8818000b0018021801f11180c4400115241c2003040d54a803902c42c50103a9031071048000c094002c4c41004240800000c01084104001c00d1040c10000c864002501070f02c000c00343c9110f070111001d0000010041c0c5a4141c0050f800442c000b0070045140ba04d0f0710f2030b1148400e400100d803103076502c650b62514240c20300c0d1081c944902171802c0c1c00e4988e41402c03800900081100c080741810103071100030210400d4580030584404405084080c400c07401e041c80d0060080001c0c01000c02c4510401065813803c40c079a2082000750f40b4107034060801c0c100c040e00c80c00d08884240002c00100907414101e401600c4000c4060234045215401409a059819079001e00351809a0852407044001c125032410703040c0c00046081c100c602004803d911000154595140c0112282c0050803030360414464000700461743d20340d100704c1c0d009001c207a01100c00c4840200300500440e02013925140d00421400c07020303a91a0200b40c0414103c1c07084 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 666481906 1250 666480656 666480673
    0x90b09040b0a090e0609060c0702090c0a0201110f07061109150c0c030a030e0126010522022d09010507111c05030406030b22050c070c08030405010305130b0a0b0102 72
    0x4101204d1100350100e180307811400034080b50070002d01013140c00c010091503031030921509400082c4000b0340a07218400c40c44000070f07c0500c0034001e40081f4194601d090240341c41d00410401a4510790200004684141c5070404c0000104525419038000314000391041b00c910000e54040000340c0d00c100d040d2565031080d441240c440c0e0380d00300003140d0082d1095450800341d165540c009800126651043c111724541820908201c03c0c84045040c11154110b42030348941011041100071754905c0f14401c002640000790030004c1c03523600e40c401c154910414100059030707800300200103064090307581d0b41800120200603c102090304264910b2008200030a030100d503025002a00168201c00c1d241200c03150404901000301075094401c0e0b481c25442034403807000600400f10000010120b20401d00c00f46541d41000ca40280000c005842419500040002d8070f00d4a4105095072034205104181c006030a24000a5820f00d60000068402c0d030320180003191912248020400707811410203140c11441020103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 666483156 1250 666481906 666481919
    0x516030e0f070603140109140f060112090803040b070f12020d0605060304060605040b04091106030a060503030307090f151707030b06161e120e0a03062a090b09040b0a 73
    0xc604000c004585002401700c3c1402144403030340c801640441c4400c0d00d41030381c2d00d40c00c0442e02d12040d4440d180b00c09150380c0b5915032006076801800049561034941c0f0f0400000b081040d003100642c00303140103180c202213550310100c080fa40075041d4201000021410700007180b01d03405a80107801c2c540150880881c07890348030b00115844c4d4104031010717904140c80d001c0411480c02c0034411200300074070648042c400c0c41c0d0380e41c5820340b80070700d0b04159078064400040051483c41450b80500f01030080141500d599080820000700001224007900c44004d024000016100d000c0d510700f080000515200c441d04c440040d410304079160b000400e041c0038181c0b58004094156102001005545005001000d1812250034100c49626803421080ca07251440030001020035650021800c0e010801e240c600201120301001c00c0600d452a4002440981000001da1035010761002281148204801a41c0d50b44a4410101c420010a20807603021440c200045511400e0a40140e141c801e0f016050700003590b604c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 666484406 1250 666483156 666483163
    0x60105070803190b09010b0a0e041d0d090602150103030807090e01090c02060f040b0103150f110306040507090501051c090c0608091b130e0109050f0f0705040516030e0f 74
    0x5500c0509540f1902a0700b01180b0f441c03203483c581c050241c1d0314007215818018102503a101e803842c04014001e543e81039104a50f0b41c0c0e04204600301603946950b00d00030307540e409282d83e1050b100902003c5942c01d1404207506200084400c2000880100301c0702a07480c5890942d0a120b019106200f04601d421000c00d4402900303070030034000e004030a40000e580590802c001d041c07000181c001010b2803034050902000c01e80c1d14981c141580e0b004030012030419035080c5240c00a2840c600707100081e9040503550301c0d040b115034014522601c002c0c0d40c00c0c08166607d0b1000c6601828501aa6000c148107000003409603403440203101614454a800042c0c1d060300c5d03101c108204d0240d0307100c80c2c0000c4403403042200840e4103110304c1130400068000b00251011034000150005900c00d12825829035810300f2800800c425001030414582010503a40007030901d61003240c507000011001d0455119404d00040c00c2d0800d4419107201d0940418401145a501c0f50200c0180100f40c2e54410300703200303100020500b80c2092 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 666485656 1250 666484406 666484411
    0x7020105090a240528020f0d050315030606032d030f0d0b090712052d01061b05030301050d02010c0c0f050103110702180a0e030403061a03070501020a0b060105070803 73
    0x200c1d4410203800b5481150101c158000b11441c204013041c0400180001d5450000c48507402109007407112540400c422850a015158041c501e40f003803125030444140c1240c010340c0120140454044504d10039000d0581d281404d80307610703405500c050f000e0b1803403241e03a0001e0607205001c1602c80c11000310003500300b41303140c0010002005c4c401c8002034080200c03e80f40328a800341401130350500814a0608005043d1300c48091071035250a0b10b450005240500091040741c50300408480c0b91002000300105807a01d241c00d010f550080b910300940c0b040015921385003040003e900500540c5141c0c28481800490302500000320306000d048848000001d83d0b4805041c0a065a91a640d1245191100050968200410140109008209070005030310b0b08002c1c581c21141030a002092519070103201001040ba426080e50381c1d0101041c080100015608042044213481d0042c2044003910400c140e03c40210f07115250159002c0c0ca80b610000361101841c0ba071020301410031b1410158141c54428466008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 666486906 1250 666485656 666485669
    0xb090922080d1401050612040305041a090102070803160f0507080102030c0c07060801060c060b13021308011508030909070c060230010b090f0a080708010507082a07020105090a 77
    0x104002c490000903110709005800b402803035041c40c0d4035200110300544240554809117400210000c1d0926014000312801022284069084a41101020802500010750b0b50340140640742c000a410040001038074002c0c07a101c01e4030b246141c41d40d91951480c82540c075086aa900412500140850007032018500c03881d440c50070b0175983c01c00e03151090b0404039280c10400501200c04010701c21641d03c80e4000e5503199002d040068100d00c20700000340c2d01c0083c40303801071403280002421081d207120546500c040315207200007800b00c90704900040c1c0c5121101d010341c5025500501224820307140c60b1250316004100c50900300550f250503110300050741c1c4480c441007610a0003002d24100703011610001c031442c131030616440c1840e5040000b6404c486c49a108031500c11100d10f110288259140681140101024001c960305680e64030700050207844200e0718032022a034800001580c1103d1951001e0404000070300b05286010003449100c403d4000c035106078100003041c0302c520711a444282c00c41014210 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 666488156 1250 666486906 666486923
    0x5010c0c090f0e12031e040321020a030f0219140417010204030201080109150510050d09050c091003030801091116061a100806091e28060b090922 64
    0x284102034514141d01d001070038000302010010050340c0402000c000c40c6803e1b6028168a0325161410300301d42d0744c4c5c040d051142c00c2c03a40700044c200c54552554010440441203850a0141c42c01c1581210100d0040003c0e400a850141085246c40c1d80f280034070030342842e0081c01880c1000d8a03031403c01412180407006420503075001078144107540e000b2110794010604a4024070020014001d4a4103082c0c451003101e0180164040d20720066008e08251400c4000b900402c028418a904007543d5540102444900034142680070031024407942440303200740c80e01905d51600f00d902c0c00190728014250700e51140407010060010036503412407520303030911044c00f0b00004910703500591100c00c07441c0d8450140c80d00c01c030007090b102c3d110b568001c00c2080c0c2c8a130088810001d0341e900d4008405558901c00c5840e2180c3c20301c0760400c80c40c8070324006060b600da0280d80130380b15034030302d030058100483d5910b02401c100c101c010300c01e81c2001d141200126034440783e500321900c045010941c00580080403014101d40750304 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 666489406 1250 666488156 666488171
    0x70311030304081c0606053a0203010915031a0c0403060c0c0c050906030705042004170c240c07050a230301050609130c0509010608180705030705010c0c090f 69
    0x20704404e01000c100509610800486190000240c030900c04c01d4840c4d040321404002c00040c000004815004580e005e064000c521040040b003070000354802d004441c03500c3d2800c042e02c6100400c4d408007100741c030b0307001d00904515103000040d111507120090074502c0c008401c01001c80010306c5070040051404d0151a000502512031514566980702a040036004034140ca0802070180e5000504d401102c4090f0782c00030f1903103801340141d01c0003c5e611549080348200050005803003004117030b012081451510540e103d03072021a04100c07020744211740c0346000c2c0c8503220000280c0a0100c006090403a1620129914680d030717040403510090703044d1b0061050200e4000140c0c42d810b4540700394001c42900b24000c0000f03140c406d0000711b0485003d070001d00c4218101d5125410003403080b00174406044011f0a94545603907031840200301300d40464108480c540c41c0015040040d00014220040c0c81c00200a40030007030421004582c04d040b000000c5c2c071903401d02d07600000e042c0d648c2d1242034150030310208081510b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 666490656 1250 666489406 666489427
    0x3170a0905070e1e04050d0e0f0603151f08070f17041202010c050c07120c0306050a1e022b0f0513020102010b0d320f0a05010b100c02040207031103030408 68
    0x1080c0076280203032410114010000080c5010403401f102c3c20644c10070301000100400070a0100c0304414485410000000c05d002400a03440c1c000341c01c0b890203d508280c0c0d00715a1040705e90001514403050007040d03958000c80d5400d4096054802210000d01d41140300740d10100c031500c6e1512040e5010f07240920203a4143d003400d136082c0581c0c200c1e0070050400c1c0c2e1408514269265682d8403d21400740000c41d000503d50030400304041d030350b0055810007024031813410070742d5030140202040381c80700300c0b00712101070212864681402910071701c1900b08804028030180402510500654906552201e0780d508080d102142081c402c050180d10001d01311100d00c1c0092001a0840d99020781e0b01d48164402e8031075000003858804039040344540081e80e155030b20303403910a11a03c1400c6031441c2c91680200d6916031001000055904030241c00741e002801100101c50902039094610341c4801d0001c1c1602425102501b400d400405d001c510a10701610410341c1614039074210b030805da6041b01c601e14001081c0100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 666491906 1250 666490656 666490681
    0x30103060f0915060905090c01020a0602030711070b0310050d0b0f070e03150405060c040e0c0702030c100e09010b0a0c0803040203150c0a080702120304200406120b090a03170a0905070e 81
    0x503540061402e108c403a00040e5940d007601384000d01082c0c0003c00a5001403255a000101c86400f070121900f650f1905d02d446210f403c101d0300307603802c101041000515464003011400c841c0382c01243c2c208454550112210181d50004c1200040c000b0114803500c10740c4080049407c524a82030f03074084181070500d06181004009050401781c00c2c01031105000784100c0b44400d03900003441e50313985603580c0391034404079050a01c604034241d8000040d0101660840c6c0150790f008640d002200c40f00c0241ea245c100160040c010080b00c0b0700020441c9102e900050414001190041d0008085883c40c1c010031030b102010b030b01e0403102410381000100302d05c0b0545e5004142c2e030750041c2132400544a013240c41c5e851280140801000034000343c10411209072a0151000d11000b640030141c0140300c1148c071214a186190704240048a009400c00005001c003400410200c1c0625499030f6040050008001a0030039550080c10341c0811507921003461002401c01c20407000101035031002e081d420710f01240ba502c1d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 666493156 1250 666491906 666491911
    0x140c09010201140402011e020f0102030408091c0c05040b010e03072904030f150906151701110403062a12060503150c1332030a0305030103060f0915060905 68
    0x81d60000d030f0144401030303070410071902d404541005009082000418100d240c088800304648842d407000080c042400100c000a140c1010151940304031050010a00c80f01420445c82c003414115641070309000340d285ca42c00c01c401400052400035040031194000a04114180e405059180407844400c60a074170224180544a1100c1c5101b40c1820b1550302e80007100361010000400840485203841503002c82c0e40c1c00b8000f0301ea000181003009003100e018116102c03044e8081c0c080c2420380d41901040380c4c901405290a0820001c5280f03040c03900e581d07103aa003e807a9080e084c15044030004400603108201740100f640640341541d404170505a482c00c030b1800c550707442d08094040c1c1c102803600c245a0403851a10b03034002444038402e0780c0d50819021360145092071a08000c1c1605410072000c3e4a100d216090a0003070949100c09420745a4513800701a540d9441203c014040f90b814801040440c000780c1c02030036020380400e000700b8542c0403990799003040039a1030600500c990b6100c400388802c5525214491f0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 666494406 1250 666493156 666493181
    0x20a03180503030c031b12010315060f0e07050405030d0905040501120521090307030302070503060702010516050a0c0b0408070c0b030c09280f14030304050a0501050d140c09010201 79
    0x1550300069844094880c84010076500751010000080340b8a45a55034403c0e40d0601c08000a585400558040222004003848203452540c01c44840d1455000b00c1d1060408451041001c01d111503d03000c0d0307041c41d002000340011f0900c40280710000303250700c0910440c994100140c1c2d400744030b50f0030101000120341043e040f8070a03055240100c240061070004564061880e5109841e010801400850740e461050500320354140c0503080c0004100b68001441e9003c0d41c2084080c0c07102075546120413822200201c0c0c4ca4802d884862080150707542c080d1000300401ca443d0700d8044911615919200c4040c50251403c64641e03500185203028080c1a0380d01801500c0004085403131820080c01340354007406400c031460300c1015446280c6d80c80c00640401400032a00c11980320815a6980254401c00c0b0410b01c5010a0005c02d141264903e25010007200d056400c018202b100c0c06007042c00440b041e07040421119200740c1e455100d440c224040350a035034810023144450580d40d0b0000c3c4002400e40342580c5071030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 666495656 1250 666494406 666494441
    0xe100518160c03051213020a090b0f100903081b010c050711090415020f07140a0201090e06010c0b07020118080d0c02070f1203171017240a02090a09020a03 68
    0x10300010307610008991101c802c0f4003903445c0f10389552403913904400fa01e082c02544840b80349000141d05010360401ca00060b0202e4075818000c14600a200f0110740e00480c801c001808080144005081c0c040074203001ea100303141d035908080110b19050b007124a00b11300d03500882d4010a07071104118201c2110b1a0300003041e1181c045a091640c0c9540e6190581d92400c034101d500840c5c4924000b18100544e1502c42d040380030701d1040c500604d1425185c021294003030703000804070071000c940482100200d9000301c4040e0342c1d01c3c0451915890315411200c0c00341c0180215500e500216513000220103074105840d0041021599030036007059000308940d40d000d4202c040d500318201c10864070303e96591041c1120481440402442d400d482c0840c3e032003516207043c0d41500704100900090f00c1034800564140d459004482650750440c51202c1e5a81006d40320040d110f0301004000b02d5190f000900c038640040c0e8a50015041085031000505a032025412181401d82d0104106040395810b0160041002c24140d80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 666496906 1250 666495656 666495677
    0x4030c210206190b030a0822120204150e040b0709090e0303010b0a020a05030a030603150b3a03080a0501060305040206070f030504030f06021315090e10051816 70
    0x82c0d01c0b824000c14854100c042444007030072801880d04090309402005064a0030111a032516004c182c00c500d000340c242c1080740070b60240c015004107540b02900c648020407a000d0f401c65081002401d000950713034002c0f65580c000010340300d401008050040c0e100d080d01707084a1a1017180141121041c1d170200700442d040409204170250084100c90555404080c025a00c40e500c030420303403401c4540345004142d0300c8006030300c00710a603045e4070201c25130303105050502184040041070804e03180051190750b404079466032040035000c06604481c1c90004038209040450090700204540040b5194064010802d041c0401c03403c22000c0c0302d80d601400301d03802c1c10446800c09402107900386c0600782008080c00e120140c40d5052501980940b0002d55010310034400001007843c221020b500706070802c00d46022102004102a0202c20a071280d0301e00c545d0b05c41e507079103103444800158010301a248070709443c0385200108050315462040700c5030382c4500801066909050080c402008a030502c1e01e001c00068000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 666498156 1250 666496906 666496973
    0xe0303011215060e192f0904060803033105060c313213140709051005031b0306040e0109051c030e0c0d14030304030c 52
    0x310728022a4100760307001e0030300d4100c540c60801840190000740041e48058104114417452443e0b961180070707101e6040c0302d04141240312580e80014401d415003052558240300325a015036001030a0260720040c40071800035500ca240a0646c0d0042e61003241c80f0400e190305900525408111484404407010040b02c48800754940c180ca448001d0050000d480e00003418a150956001450180100802981d000e008c50001400c0e2038840720b201c0c07125035100c0340c0313030040100c03282c0a15041029008032000608841e410100071040004500040c8160754a0305203007421507a441c0614410300590f294140301604200400424010018800d01004010010001259800003001118602c0c10394090346984500740040c0c0034000407400f188141d80b03040300c1039040c008000380801456a844500320540307042c081048040e42d82104082400b81e004000c40ba600c2c3c20000c5d20511030307501450b500043c90301001c0d045400d40d80251010750000c1c980c41d0f8100c044c441007415400810100070a0540500da0480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 666499406 1250 666498156 666498179
    0x20405041227060503071e09052b030e0d0602072303030c12063f07050f120115090608060c0304120e060405060f040e0a0c0518190602030d0e030301 65
    0x641e104002001c40444c2c1e1047c06000107031001000c11784c01d0045040900d40007054022640b0801e44946c20460f01000008074030160440c28107a10008100da080050b20103a0702025018415034201400361440008074405201a10840d0720480d012200317410f80341ea4004869000404501c1039800800a2201410300007084510a482c50812095556203007000207000816038804a8030b11744404400c1c2280c54141d00002c0310007801040301c1482e00c000c0f400110f036907036024090550071400d0b80082030003038a400c030002d50442c12540700100b8004240700d0308450820166014042c5191985014080904180410341c4d00c1401c0c03911003800c40c0b038103803076082d4003c0302009500241b2801d04800d000c25210081181c02400d0058040c66644800c0d0801607100e0780701d4441c0c4401d035003030b060110300340030b005014007001c3d24038595505003025041d103803a4000000f520603882d801112020300110200d40c0104c41c00080040790081d60b01c035080c48220500b990712101d60981c41d60030800040c486900000d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 666500656 1250 666499406 666499409
    0x18470d1a01090317040b0a05071a01061b0c0f0303092903160905090c090a080303133c1a010503100b1203031f0909050d080a09020405041227 62
    0x3160405424a00000308403902c0b031031b00841c0b080e550010702c0e0403006030040010a41075104020441ca40940a031601d8900311003801202d0020f11417000d01c0003980b10200383c1d940300c1401006440c0c0e4191b6544882c405c20700145c0c2c4118040b61500004000c40780c0c1c82ea4164154100c10303201d0b0402466110003000881c8070040c1010700040a4000c040c4031144500c0c2c85401810014041e050305062a04540c00c80d6045010b0061041c2c0c002c0b0300121700080c000c410759000301540c1400c00a0318400d03030791f40b0040c50300b01c201e03041d8480c07224240c0c1051941141d090080c01040e00542010603404e80c1424110000c0c401d5401005d500c81000400498030005070340c2490081d409800154010f0801c00910880c81c00f011821841c071020050044040703d0741d2403c11461001c4c403124800c141c0e5001d84c60180c40d804403020704250004c0519070701c0c15004102070380c0d0011038401c0c00210030700e940e400681210b001b900c054071801100e582501800f500310780100018007100c89230300982014404087c4000c1042d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 666501906 1250 666500656 666500663
    0x705090f01082d01090b0a1802030c0906180f0103031b02010f030b0d15060501021c0504091e0207140709020f040513020c0d02030a18470d1a010903 65
    0x4007000d6030480001901c070f101c01e00c04030400a111016403818043d40100041d02e004550714070300b510903044864401080a2116406000b42c038003121604100000160300030005030700107603071500111928041c13130341c464400c0050000300d600d554110705006243c4545200e5031105094000c043d800540c1e0800b0340380310031000600d008a910713140200812556444d0b00c0c070033800c100e09005140d1401c01c0c0d903048a01618001ea0846a000d86000141c040044242482a0204500700800c1c0505010360300301c2e02c440150040c00f50a055060380d0644d0883e0b01c0590207840000c130007000e401d20f090043c0100350007403589406c05d50609160b0740601645208034403405e0310a0306d1303032980f050065140ea010f492030007250506480c81886a14006900c1c1d41c010444240001d054100b1002c210280400030310a480501c0d20b541540c4d01400c40c20524003106001c54005070700700300340c500b01d96082e0b10b18120318503600602070b5407110300c0500d800060302e20428454110801004001c1d80a90b03004586c0d0b41100d81 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 666503156 1250 666501906 666501943
    0x6090c0c0f01230f0f1512010209040e0111120705190206060405060609030d050d2003010807060c080403032105090a030809070e060d030c06020a03020a11071a0d0605120705090f0108 80
    0x20743c80804041040c00101107500030440000c40808101c0c127602500000c03006031002c1c040b810004a0344e5080b03508242d40038010350014040c44002401d042d1046503c20030604015207020408950b4841c003842e21080713500141c1c4050108102410726008044e040750003501d13560306046800300026201c0c0c11420504081060100380304105240c243c10a00581403141c04c0810300340098050201d0b15442405003000c81c1c805c440001a01038854003c08541c190040c1c00f00d81000d0556070100d0300a1506100030300040021170700b480d030001252084a00900801000745410b149515001d00300c2e042c01009414141c200c05420440419000c102d2039226004886942d5604c0c154038040d10b0b4400c0800c0040c0a0f50b00c04590312a00981582c02031582040c6500c50080c0600050116076441ca020f010303d2001a014440025100101c0c201070301d41c4000040780858450742b1180403500703400c5034015407811940710040c00c100d103081941c000303038100d14031b001035420940c180301405580e20548016004000d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 666504406 1250 666503156 666503161
    0x8071407050a02060d0c02070f08100f0f110a02011a030309041d03030f06040608030a0e1c051005041704080d0c060212240a0302010806090c0c0f01230f0f 68
    0x50030b10450351050390082001d901c0341400401d5400402c040200313240540702c0c9640104031040b40c01d415600f212407410080445200c40c25403400900788a20f400e0036025250310040c0c0b0200201e0041d42202800a4503058803017010040c02802c0d50b441e0300d1401511103c0c0203a5400680700481101c002c903400b52404520a0820100700003401c2d03403103070b1351401c500011007444141c03241032103078601961085a0502c6104c0c0c8074014a40c991250b04035001c04600026407801880c24880001c0d98040705544450040c0c502c1900c80c9814001c1502d90010703030994580800c010004008214810080d00b008054105420312a145648a1441ca151814852109107040400c8801e80481d4030200d40d401002d0085d003030140b5501c6402280c002c43c504401c4035031601441d18249251a46e040700d0b0142c1d40c080060b00c5403018400c2040e4090011250400104401001c01c0c40401c9000d03101c00c40580009001c82401c4505203e588040342074002080380e0300203010001c040c05900c2034010024915441194 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 666505656 1250 666504406 666504413
    0xc21070509060a0504030303050c0408030304140705180a0f050903070305090f130506030606010f230c0304060f08060406030b010b030601020703200a0f0509010b0a0201060b12090d08071407 83
    0x7401039114003603001e40002000400320354000090011a482502c00780083e84071000341e18143e001d08d0041c070015500a100040220380a54480d624002c017400544400302d4481002c03404040e0310002600e4cc2c00c107440305105103032002707110741c040c04e8001c04801c0005041214640b5128411984090304000000c1100c4000c1d580342025444240310080050385900c0c0e40c994120042d10080710418842c1c0122400034041794050841903e481b00c440d074501c040140d128100e107661918810a40c001c1c41ca050101d154103450400c01080035041d140c03100c003006900c0340c0d00206030b0840240390600550509104100045a60020031b0540381307040601522580c0340070040789440701d42d501c00f03000c0312500300303806105008804070b842440109031101c880741510f030300020840c22114450950851180c0c001003148410300c5029140b0b41c01c442c400480c00a0340c0781030082454101c400d94600c030748030303020520601d0541042074480300f0280b410605a80d14110401400c0440c1034001c9103081c01c030004182042 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 666506906 1250 666505656 666505667
    0x20307060c080f07112106010909080412110a080c0d0f021807030e0f0105060f010f0c060c05040f4a0901090506070804050d200f0f060c2107 62
    0x7500f90000c0745403104000d06241c00d0309034103c03041034000c1800c0481c505010346105908144800000000c14190341f9044d0000b00400b2105000c2e14415070078000881d521241c40c41940500b80140c00400780701c0201000c03c0603401c901c1d440313001294002244201281c98002c90003101039003180c4e025280c076515001007555030030748100d40102c0c40f100c54204007a8a403d03502c80c104080c0200304a032084880c049160f82218001d403086617021110b09107803442c0d036110380d008243c004201c3c0350084414560707039aa007066410280e915408210082014403070744804031158401400303120b60a4509595148001d00c0001034120741c843d0544819050100d14000840740048207045c00c5a03402503841c00e01c00d0705000344441c40c1c00b22058002c08000c10380c40351007014041d02682d000b00c09071461102685054401080412084840083c65104000750381c400740045510100c13004040c020b8800c1b44070a02d41020002400e240021070180030108409014207040e206c94808040d0351201c03a25261f03001d542 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 666508156 1250 666506906 666506917
    0x3040c03032a050d090b090f0d03030b0a0e090d0c031b06061d0103060e03040510260106260c0f0c03070c120b0a0501050f0f0d0b070203070519020307060c08 69
    0x40d0074076450703210700300000044c4003c80809141e4412100d1a120110540c092003a4443c055021940280b550081d150400c0019185880780c10001081c0c0c40c5640030030244100340d440a4528407110302040803040c418000700304460040c0c50a00482441d81c0d0b0003400300074002c0e150065040c07070504101c00b000b05503404030010340040144d072101c04a18011844801c1002d02040350042d05264100c0072000c1d000094a0030b8640084c4183d1754105040d10840c0d035030389803d020000c18423401c80580d104103501d4441e24064021a52120701607890090a039412010f6038048004034041e2808025444103000c00361000480c92101c0c0680e20b00e0030842040c9107002d81400644811b030354410018080382c0c40b980c0c9105c0684a94403075203051b07441c003203d001100d07400d2082d550401c081110404081c580030170b040c020954010907410b0700183d41c1d00d42002041d0101c4080c0c01503840000d0380024403004120094400010940781d54020605502083e260b02482c420740341400a1a07411104200c00c0c24140d84 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 666509406 1250 666508156 666508217
    0xb030f010518010e010c0503010e0709120609062301060507030c0b090d021501211e03080711210a05040e0a0c0908190b07090513150b03040c0303 64
    0x614200a0300b00000b9503129004035425602c1d03d40030301c42d4040b040c010940c4407012030f140c0b81d04503860310402c00c00340040104240108025031202141e40c2e411414174404107170017541d001514200030f150003401c503103480d030140903104072400a00340c3d00741440c0b841a064900e240381c8261030b51818641901d0b840c42075440241504403203030811107101400a80001982c02643c01c50700b0440e1282c0c07880403280310078087c981203d031071096040c00c404000220340404500c5041a017407910342c03064000ca09003c000d50101c00142d59031050198150b80016130700800c0900c0d00240040c4003101800ca041d002082c40c23581e03c1044007003039800259002c0c07030685005003c04d02c0302c1001c5140102c0d68000030204010084d011a050320b2011510382c20004240c0d103100c642ca02c203412140d4041c0c03540d81c08418000c1030a070821070b09100c0030506440300f050589091011040104100b00521200b80d03454890b9002441001c40910400c0049004840900122034150030100c000c0b0950001058207040154800d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 666510656 1250 666509406 666509411
    0x20d020c060a0e0c190e0709050316061d130902030a0b04050a0c06080c070f060b0a06030504050c012309032b0f1107091109120d0801080d0c03030b030f01 68
    0x5042c981210708196410310644008845490030401824410307403162569082070b0300180245101201801e81140362410540412641ea1000a00c3c0c012000741c0881c02071a40c1608001b0143c1024030401c590b0589200a409201f01e80c0228109000c40c0305d08001e19902c810741d41007551000c2c050b200c40c290f0020500045858241842c990b144441d01c0c0449204659000010ba55032090020703034000c04414002c0c600c1e10a1503120304030449042441564040d40d01d0820b0791160b500e070040c040040c001c50b01d0100e95468a401c10300d041c01d048400302030520454072030700c0410703000383c1c0c0c01000c0300c41c0e803030342c0c0b50340c5036940310001c40d107028042803612056070880c9800032960031391480d0645224101e41e0b110380c0201103040044441e045240c41c1d40e8801d03403118400f4040c0074460b40005820b10400c600560901c41c5500002e890401d0004000c00305820a13411241c2441e8451026809808400700400300100a0308004291302c4200c100541010f03542c0c01d5140d0f03182d805000030a248003454009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 666511906 1250 666510656 666510661
    0x1103010605030103120804020a141305091608030c060126150412030b090610050d0501032625050a020d0809011701030807060506010c080f0d0f0902030a06020d020c06 73
    0x342941d4421300040d034010340520343d81c0c6081481500c181d44507c0c2c1c040c1401c0e264034503103440c00c079403a00c1c1490305640c8a00714081e1403d00a00c0c52040d18401c4a1110003455003500c0500109162003490b08070100c540c20801c1202286800000e40a0440e84041c4110511045021190600d601c43c00342c11400790280030303082c04800780407154031806180034040491300016411001d40899699850442d080300742c00000070305900e880302c4071380702000003400e0541c545481915000c040324401d0300101c41d00c1403c240c1c12406194001b2007440012200d643c29407600910480c044400000c03d06803080e0182246550310400005114040d00f03164090480103000100f480c0c030304500e80220499900203a4102e1000c514481c8040c5400e040f00e421452817071605900d6140c080c050b103802407249045c040781404150004440c0402400104580b651321a19106001c105206546400c1e02e0100c00d6807d0015181c00369401044e50030b40a0380c00000183d0b11080103600c10003a0003401c0407a03106008803002c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 666513156 1250 666511906 666511919
    0x801020a020a21090501030b010c060908221404090303180b06040b040938040311010c0801060215041707110f0d0521040e160801091e050a110301 64
    0x10a1005070b80b09030280c0400c083c180c3c003581022103140d081480040c01c010420002035009074040c128804042c9802070300070035203441c3c0c4000d5401002048403480c0001409003491100c0e032080e100d15241c1d00c2004100746140c9903021a0340c460180e0000d00c11960340720300b0780415010790f220100400011000880c1381010b41000c48070640100c880c1c50280d42030002410031031400d4842c0c8041d02d58420760075101c90070090f81c2d00848458124401a0503034a00c1000b01c0301d2410103420600c241c1c030070340e1215285601d0445960a440c511203100043c040d001e03006104482d00464221007205e502d1039443c40e241d0740c40c01c000360800c81d0b0704c0840718825400110b903c117000c010461005c4031102625800001c071140c00a0000c08030a4910150640c0c2151580c0a01310a10100348820309100240303150520781c40c0c0c032060140400c19903950300b80440300800308034030030b4100d00c140d40140700038141000200c04c01d116a01a04000761408000e0700da540b4001200300045600004030408451041603c96071940c6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 666514406 1250 666513156 666513163
    0xa0b060d1e03030b010816030906060302040e030703020d09060c02100e060f090f0604270902060a171503070b09010918051012020303090402030c070b070306051002120f070c0801020a02 81
    0xba0002410050408a40d501900c0040d000c0e48902d100f400990003d998201c0c0100114402110000e403a14400009a6240c0c05407000d00724007400595035520742458040c0ca401e00388540d8100b03200e810a0100002d9401011940441e50140d41c80f404420300302104542c10020a00d1007036002401044001c03c3c5940c00000d421840001d4030041443c0440c071381004100e014501ca03450034243c08500c017900325018200c8010380c40c0e100d03600110704420b007070b40002c0c41074014412080c00141b6100301e00d00c00065580055402071300003031400440c0ca0840010984403803036402600c550401c0000c4031080342e4405c09000d0003c00c42d85a08950200c190040000a8802a5102083d01c3c0811402107400541c80d040e002030107500030000d500e040c0810041c00701a400042038408030b00010322001e4041050080c85030310440c02030b900082c44d2800d000c20025001c00d90082c20003154400128100c4454030f00044036000d01c4803100050322400b840c035040b1400c5616401c64107480d4008500c850340648c001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 666515656 1250 666514406 666514463
    0x20a0309140319030b0a141206130227040809010c0803010b0301081e1b0f0d060c020d171b07050d031a0d0201080a051f03030801080c040b030a0b060d 66
    0x2c02d0142d6840c040c4030402c0701a40e00c5411740301e500c40070700e4200700104c09a880c1c0400703107280090007140b000d480c968459410198202c4440700c0080c8419030701411403402c1e80c002d00303400c0e02d01030446000a50a14014050880041009000c01c000045011803a801002680d0010b6402440d03d0383e607684412840c54150028800c02549100d0b48400e400e80182503800e40d00b03c1c6a840008040819a0f01d24100d500b07640c100d00742d6004454800000c0090301c0c1c41080c618101d01a49000c00e8640310100e0003480d01103200ca5207010407440b01490943d05141c402c0783c41e0400c0c0e003944003040c074088209419409101d1808010414030482c40c0d075040381da4060b00f0000e00c0d6010440383c00340f0321844030240b00c01c3c0ca101e9080280040d0640d00020030002140c2c0c8081d0300004040700702200c4132400580c644150302c203030b00f090f0049a2041c004000040d0200048070700b08000384d80912040c1c2954000c82d0380c0d181d48080c0200206d05031700c00584e01c0d4840390070210a094100c83d21001e08071910400302d4080e0901c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 666516906 1250 666515656 666515677
    0x9040203161d09010c121e020d1a240f0c0a0f0303111c020c0708070f09110708091203130e160804030203181302040605120109061206020a03091403 65
    0x42c040003c5081a040c8203446140074251540f201d20070188806200524140085007030701e01089541d00c0d1945103502c0a042d006032540000a2003409410b0707040c05118046114902c110031292403411010390507030340441147c501c0000191950000940726200d40034911640900b44907036403550007480007101c03003409154080d07123082103040c2096aa126052042e15120f00c5910591038900e450003200d54002c180f002038101c165440d890301d90b41c072a030403d006c42c0c2c402c0a030204005401e1042d103d940c490f040034894008076403880c04d0b03031582d42c0e5282c9020741810b0390b200b080d9454401c660750742e082c001c40318101e5186200070316a6032192031041807000c055079410141c18040390880b07180e9004104950060b134260b0001c60420445415580315212010b00503500510a03204e0000c1038a10340c00a0720181640c2d403103140d02c8080320100c1030304c0c00d10142c0c01030b810030342800c2040006004070440d42a2544d0001c00141c2d941584010a43c00b4103046030009000140101681800183c044007800c8025423 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 666518156 1250 666516906 666516959
    0x5160210200a051e0123160912120203040b03012303010c0206160c080d021e070b0f040807050f0a03030b04060e0118110d1e02070b04020904020316 65
    0x40c4400c03265516900a070000b81940e004c42c0032460504008442d410002400781c001041c01c020f07079000040c0c60002003030030b640b014101d281400701ca01803001c10440449036070b1500105013403400503006078010110401401c681c00d4140a00301152003481180d004c2e1000e1000c0796604d503543c440c200e8140d14800310240940198102e007039950715042c02802e012840700d5004080c1c9440c0d0101c8041543c5001d04030800340100c0d4071b0b201001500201c050402c42d0b840701d0005886c2c58101c0348001201581d000d01a071100d070200040310029903c20101e581040314442100010307525483e020303080744160903010305144a9540c580030074201c00500400030a00c650b50910882e10b54409003c05d440c3e0354012443c4603804000103004600320100840c2c1005440203000c03440c000712250003a855480507100030070b56520f46404032510402e12003101d11941407840214906038643d11380307089140016000038410089400402c042d540c04000003411600c42044408400d0741c1c03480ca26002c048040d0a002ea02030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 666519406 1250 666518156 666518207
    0x5030c0c0a050112050a2403020f03060603150606040b180316050a09090807080c061b0f1b0a080a0203121f0e0a09050d2111090105160210 61
    0x4001074000201d410603118141900c144000c9400038000041c6803c4415550b08902d490540b003010f41c0006503840142040701141c1540140403e41d40c098030303918000e501000501209440024040361101c001c80c0d841c552070b485000000705c1d103120716400340200000215a02d41800c00001c030b8ac000f60710045003110b5601705090840d0526010507c512a8801820785e0100050511a041240c042e80318000c0e161901d0400e6844090340d80250162115580c000b00c1000b0014890640d006040485001c603103041c400d58036100d01042c4901d40c00d006001207042503000300d42e8002c00c183d0140070b82c407081c0031781c032618090700c025540d410001145010054840100e11a030350000c80c2141c3e4040004079400300c20341000300035070940d034001d410500030a80d501e1151010071400e004036148a98a582ca020304203501c4d01202c22440461101b00c100603190500e002410789440c022903109550a080c07090b12842c4050b10028180f00c1003a01070340111008101b44006076201000441091464002480b003c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 666520656 1250 666519406 666519409
    0xa12120e010912350f01120f29150319110105071401021809061c021507060609090c1e0302090411031912020a02060405121905030c0c 59
    0x21200c6520281c2524620107904040b40d03c250f43c54500480301c1d01002e103001e069440403e0400d14103141d440708404002c021720101c20411001a0f0050851481c008400742c1d854460f003408130341c0303020700070420b0861094041d013801080d0708141d1410300c80340080140e881c160300106c9040a0368007002d446401002e44007240d90b03040c04140b110703e5800042c0b056103001c4070f100545240e444180c06480881449070190340c014001d0008102000034461240490140a810b0000a000180041e440342d44204009943d01e031100c290b0454007074040b0391000310510151350381801880360040250403282401e4010840e24283d0300042e08441c40f803140706860565802010300e003140c2804d02e107042800d284004101525202c100b064000c5e00540f01e070454101d103840000d2900300c0d1030825085400007039410000303000d181c0740e40b041c40b070340580042c0c50f001c0015400941c003845a4040c0318840d0300007002c0e8480c040401c00c1810460048918180c1c0e000e213031810005d0b62604110360000892040c29100f0740305 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 666521906 1250 666520656 666520661
    0x20d0b07020601170703052a0d03020703060c09180c0e0423060303030108030f07111f090506031e150d05060f010603061206021c0213030606080706200a12120e01 71
    0x446e60010040e0419034510149034540003e40d03094032a1604000010b07842d240c1d036540300a107526100c0d80040015919504e080c0c0c0607610700602d070324284020a00208003048100c031400c181041411030000e124015840191022603024881e940c1081c030703025094905403c0b4801e03020002c1444101404681e80342810503070b807480240540c042541061080b6001110303044060f080301c030f01c9214407041c04019040881c44a0980f03081c0b4103003402840c103040c2003058204c0e85260244c02c09859040c80d40c80d1103000d00058240c0364804603003400c030b020005850600403e8070801c1d0b2240c020600c40142c0b4442c1001982d6000a03189280300e0361880b400066000c0c003c2c0705080440d02c950703500b13010080e126220180207400243da4285c02c0403d00c0c1c0040703110040c1e440201603484c10134540d000340a046007010800c84000e60000c5140c5e51220300248807042d0000d140302070b40900754a6600078082d207070683c03c0c2001c405000003411030405075003504255800040000c204414150304000100e6040721107801e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 666523156 1250 666521906 666521909
    0x41b08010e0c0d0f140307080d0c030e0a02031b01050c010c050702130605090613021b0609120c0304032307060302030601111504080a0905130e190c050607020d0b070206011707 77
    0x1004011001400081c0662610100c017203505002c1d2410f19040e0b488502c644d51064856408150790f47e29403075812038044c4298449001c0480041c40940519404260b50f03081c461458032031017812a9034002c6980c461002c81e845041450000d004204003090040d1a070381015004920868030540104240303c03c0c0c0c802c20084510040110f4400e45600051056400c0007100006c02e9507002c1041481c2542c00208418030207c1d0344009103010b2404011003400c1c805a40550f1901180411a0388814800001554241da41050240e030b04a214062008008107441c062601c2c00c0c05601000180e150705640514032540d003c2e21106140c0501aa4090701c80342030460945007101101c1c046408a429013000c0c3c01e00c001c09042c10b00304a03482d68001091100c880d043c6000e6961550701d85e0100c3d50040c441030300f2850300f4000501e00501c0a568000c0050907601a85001b03400c041000400d641e00d0005070203417180c0061038926641440da0303000f501c036102402646040403200680301441c10b8000740a80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 666524406 1250 666523156 666523163
    0x3121602090718061407120e010206130308180304120803010608151c1103120403050d080702100b010c02040515030601150e0105090d02030f030703030606050a050d05041b08010e0c0d 80
    0x70f2286052490684084182640e01c6040d00014421540014502030490340031081c2d03621420714045090000a1070250024a0071260000600791035000a81141d1929000040716202808102e85041085d103140601e07801481c00c1c05461084100b4400c2c620010350607201070341d507014100d954042061500f0160020256000703400e0075581140d80c5024500d0b40360640c400e0510ba00034042c681c00107407502c510600c0d40c1e806000001010002c00c00204240c146103641d9041403c6240390900c0e01070348800d0640600f01c481c0d611403601040980c420480c0600440d8010810045800c00400381d01030134040400303d03030091050f0310000c555141e9252403022054225035134244501110001140d0941121514540101c000801500140d4081c045d811600303030301c040103503101d5607182002030540b1915072201090000c20400007041c42d90200c102d812101c0d00314404175041e120351510307000007021030701d485010f5850440e001c40d580311f040d044441810300300c0b02210f680368600c1c2d01700400040c1810008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 666525656 1250 666524406 666524447
    0x818062401030b0f0f010309050717151e180d08010303030c03050c0f0c0a0203011b090905010303050904230c1c0501050f0909071d010501030c0203090a14031216020907 74
    0xa003164034001d0380b407000c858810307d0301242c030720300a41d1403615020060b000451003151040501e8810401040220000488034103656440d0400c0b440100c04200100b03241c20f55400d00a0004402e104600450005075000c0c20849401c07921f00c010080c006070080c001280064240030944900c244680a2540124004040140b500e100c4400106490744050301038100da014802d0b034800580d40070b1040740d40184034100d140088549c00b0340000c15502081c0c214060f004d2401c0014000709034444d0584d48100c00c00e032400107280c130143d45040b490f400142c00c0d50750030590100400c401090440d02424021740701d00c290110041c082c00455003038401c03d008868101c00c181c1c40c0d0400c1868104c2145401c81003036015901c0721502d4108042101010382080400300c14108010051541e151250940b241c4141c03014508028071400040c43c8089148903880305a94220802d03601a942480351911030301c1c0a448683d41c0706441f8141d141d401c42c00400070392240d1300920001e2a20b90240e161203100c2080292030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 666526906 1250 666525656 666525679
    0xa090501030b0f04060e010311060301032d021903030315080606060a271401030b030606010e1c0f0501050a0c050a0c050703080325021209010818062401030b 69
    0x1100141542c000d4603510000e445510801c0380c84511901c0080e2503190f290b40e400e50b055050013144098040030550007590100010000700388444123540d500502c1401610161800844460b8084c4540c40087d5005126004210442030b0060409003128400d450601c41d0580c00a11100032850b00c0c403641c178dd10342121000842501c2c2c5140101549011401c005944425a4010f1801f114071824411161040800203004100301a01001010903091a040c01800100d030086510b44c10702a1000341031110f40c0862160903a04c8041d8481203540c0e801548440e52602c4c189900440c20300c00050700d955113014003044c0108840c0c0149007103a03031140c4445140c0a04030300202c0e581c4a17080400c0c1c48900842e0404400605440d00650003203243c3c0c070061000b00304030100500340c0110084800250345c031020352082c00070a80c0042d6130380100e00f401c1060341980c0c0c100707000070ba030201d40702096030030301640b801c203c524051500d00455551040d180c856032800302e400107508480d888940141e00c40c480e507c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 666528156 1250 666526906 666526909
    0xb030f01020c0c3007140415121109070201090212060408030c0c01020d050a020415020703020109120317040b10080d0804060b030109231212070c021c03030b10050a0905 74
    0xa0703080741110321a149a004140d01094081c03080300000041c001d0342000d481046280c0c00d01d046e01c2c40703110701141d04000d07e4140c085c40140e9a49140b013a09a1440a2000380003844044603c4403500704005d031040002c1c1c54400d80090082c8140c520491203202c03444044000303960001443c80c8103079881034100d80f07140c48101c400395981e080303030300452260740d020020040b0561550041074050601c2c8d810240c0c48504020740c0151614a82954000b158860802040580c7c0c0c456805011030303191342c800901c11003940c1801c0300c92004d11103010361070350340d1401407008111511007254480c800d40c18810720504c0c0c507409030340d4036107901180700c0000404480205000c15031503070000000d041e005000046140550399000d102a01c104184040342058241034005807030103001c0750394035425481d0100c2c075251a851041c071284101900c42c004118030008040d04546401d10000c401d0008110215111004c510b0024007901c040140301d4012038140e030b207a00c8014002c4d0140c03622050980c9031144035909050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 666529406 1250 666528156 666528169
    0x3060b0f0406080405070807030b06010908030307091401032007060606090b2a0f160b09010203071b0506040320040203040b064b01110a0b1005090a0b030f01020c0c 72
    0x28010385d02409030140004150341d04012200046d4480c00b1803035108c1c5010000075003500703070705d50191010f60010000c01c140d456008030898282d91143c00c0c041c010880c4040101c0007031070709100110300784000181854003201c4e502c0160000900c102014010303140c407013000300c1e140c0041c2d1040c00e4000906206031060301034000c00c48042104106440c4100d22400801070345800441c40c800c40707603a040080b045510b00c0d48000c01e0b03c05042d501c6089440d1448a00000395603124454018019040e404c1e103400e8024a184d140200500c0002c00c0c26845507100d00b4810308000c8101007100300807504170000740440c109402560b225030340001d05003100c0d035103110a02c1100750400040d1402c40d86040000c0115801c0c02c541598010007000050a6100c480044143e03040d80700069241800760a1403052a40c1c800001c55030b042a60055034500681c4a4114144d04400c45e9004030354400004010000d6190165201c5901c2c61812002c946110355104500e074201e00c1105240004da03086030684150314103010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 666530656 1250 666529406 666529411
    0x207020a09020d0b0d0b0a0e19020103021b0f0d0806100c0b040204060308220506130314030d060b0c1b060f0a0c0501051815010e0a090212060f0703060b0f040608 71
    0x10f00e0102d01c4030601070010f414040700075400c0710300408950a00c140c0401c1440782281c050f0152004240d42c1000814254000100c140005e04241e000a081351300340d01e40a80184c40d00c519001259890b59a4440450300c0301d000d04040400920f540000412038501524a088000316607291002d80c08065184e0300a040c0000303109980183e1a03000010004801300c0091401d910140a01c0b400408450800113108a59601c510f01c074060500501e4084400c4a91907011282d101038012071210110214506600400d48501066403400800240c00c0e86441e00070800700591805598110f00064080c680c2c20850100041d003015081c01824110090400106039010503410081421200c81c0d4801e801d40e40d04403000310303180000424410b00000208010b40c001710510000e003080b903061036908a08000018209101a501e4006a80964a4512107141164011130584040b89030400004d840600c065500b400040d241c21701c001030070300000c811b5408003010010343c149000d140c154110303101c0102 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 666531906 1250 666530656 666530677
    0x101202010507021003020309070e04080d0c4b02070e0601090f141005030c0a0311040e0a1406040603020a05090c0c030409140c07020d020108042301020d0608010207020a0902 76
    0x40140001690383e030254126002030f10f175005a500d02d400340300542080d4960380035840710703040304042c8000a000d95043c1c0f06031034984000002d282405480465140c18400c0307445100b20030f41903450070f0401c0c000300d6003240030303403154400100d4245400d500718000c1300e1a104d0a0043e000f091061096040301080948c1143c014034100605944851035021401078550042c081324860900540317040c127001d020500f901d016401e01c18203602c0c102881020340e10610190fa41056520b2200c0c2005804800580b406424039491003090342c034040a8280081a0030a05d041e03078041114009601c2d443c141c003600040da42c0c0a425220340c2d170f240105010150401030207140c2030100600950912081c01c0000d08002d280007507003c1000a4001c00c90303010b100d070190480843c2101000b080b80903840d40f00d542c0040d0742c5d0a1a220910b541c0d6400c00c940c00800f400e220226105086611608404054024050b008a4203000300203a56a03202c00500301d10074041c0007504004041001c0082054a0340540030b403404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 666533156 1250 666531906 666531917
    0x3070e090a0219182003010b030103080901020106031217060f061c021b16090203010f15140307090302030c03060103031b0f29090c03071a0c010606170f10120201 71
    0x8440603440c00c0a0040032406412640d0b03901c1204125041c0b102ca1118580600c80170b5155506041d050800c51005000c064660600003c1c4030405034400d505c840c00031500118180708100c402d1400800141d16010711001c0300300004045042841c1500002c1c074031841c0200038500e00102c041145555680320b038041101558248440621580300c603600150a618520203042e9901c00b8038000c400902240d0031a84140e0301c144010700584000076100e0f4161018810b13103480f54a54400c0445090440100340307410307240c010060041e0290890282401d40e0704c00c41c00c1c1c0740c1c400289002d00d40da442c0c0900c00500068544803d43c01c1c0951041668541640140402c02c10414141c650f400303221070b0000703840643c425444951035001d62031403010380c00c100e2100190055600035000240d56404900642c500603103d00e00743c1c01d02c03591a43c105d03000f0340000300c028048199900c40c0644804291529034102111000004054003035940c040d5110785040910450783d141445240b0300c1524a24004034140710 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 666534406 1250 666533156 666533159
    0x16030f0b03030406270308091c0219080d0302031005091f061205070f0e061c090b04050105090307050d08060a081036080d060e0103030201020903070e090a0219 70
    0x31802e0008001401e401c2c0c49940503250045500403035410300300c800e45032489a0700c0050001038007030011680c0101c012549090b2200814107800004015140000d50003400d0038a0a03802440408502080307450820540c1e510410200c4280d0030703844212106501304502010900140c6000302d007243e00400041d500900d101c0000080c1c0c590b1000701d4100601180d5400c105185c140c56170701440d0388c060f40c646442d0081c6d080c0c1c076001502e00102c1c0002d1034803680300070030440300d00d1425401c40130401d4081d19061050040c0790501c8001113a080c0d500380c440d5428040010f0702008000203d402040e884001048a42c107000700c111070600001d03000070381c0b2150078107000828840400035071045c218440700010720000b030119441c44c0000344003003150524414202e00340341401c8c00b200c1c86e04110f400a8074035079141c400018010041c0099000000440028000807080c90307415070140015682c150202d9030141d4440f00b2804401208540c0029103504c091002001401c00c0d900517010440741c2000070040b00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 666535656 1250 666534406 666534409
    0x42405040302180406051302010203031504020d1109030606040b090a0e010209040504060b09011a121b04180b1c03031802030714180106020d050a170106090e0f16030f0b 74
    0x74031480c3c01c000818031180705100a01101e0300c40c403500208002c51503038458010354000313503ca000040480c0010401d030044204d03517132942e4046039035180060a08010120346500409041d4009040d0580030b8810b800004003c2d0038180b00c4d40c008000001c0100f80f899076101e02900252103001c00c8800b50795024412800c042c1c880307005a50142c2c1c490400880c11b50140340900002d110305078000081c0800e1200b401c1924040390b012100c021491001e19152591680c02040c1c80400c9280c0d69160710100190014556840c901c1030380310008040b100340041100f0f58204280150910541c004030110041c12a000902a80c0702c265644501c65008006000c1c0781c0019040c00303c541d02003490301010214600c410320708082501d41d5903021604501c09541080e40085d034134118208000280200001d9640c0c03101d0060000d00304010000366500c003107684486004144010500c224001006030001054090610304191072154051f040300c0e000c9809118030803000783c81001415221aa51501c4041d041d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 666536906 1250 666535656 666535669
    0xf070611040e0405010b090708180c10020102030603060a0c1425030e040f060f0b030711030a0f1205040506060114090306011706090d020a06020d06050d050703031103042405040302 79
    0x2d1210301d00100303461402c0d0074010300b520b80b070103081e0b8070800016007004150350304001000d4001c4081781c107488120280c014034034039100040d03e044d81d00c55220240d07500032590540043d84505010b0f025a0300c5625045407540940d00d420007114085030124141c084c00320b0000c0e024100c844036218030001c516184c40000543c1001e045800d400241c84480715181d1030600b405207000700e411984040010514101c0100c20546c2a0701981510716000030100d000e1600c24442c0c010380500000542ea0341d01520a00a44242c9200404001161201100704040c01c19842514820341d04103015260b103589140044643c0d0740a4080310510140602080045443c1003140318064404c001da4450300d51501c20b801ca1612000803d6642190b20a4280c0d0b0b41d00366010804900c0326502240150b1200d1300300e441c0d5406007289030400d5400007051843c00303052010001e4140100e9000791580040c40304040c41854403882640a10350803080020074030380c42020204101c440e081c3d404e1178940e080548942c0010381 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 666538156 1250 666536906 666536909
    0x203010c1412062d0103060617060d0503070804140a050915090603011b0903141204090e0328030e0c010207060c0c030b0103081306020c090a0f140c1317030f07061104 73
    0x1070030107130125a030741e5804d031244c240500654200100801d04002074594850b000402d403a000d41d444040d48402c001080007580d60300d980c0945681d4a40e600d640c2804c0b0300d040401d0441c1c0c411002042e000405041c0865002d014a13070106a2854840070003060010001010381440e0b0550369035181082c50980b80d421800f02d010040e41c1e91543c00703145040c100b6109e03400f201e42017041d800160003000c0c0b040e141002c8400b1501c600394049040043c080c4454194007030b42c6403c82400350410486245410742d00e118182f099607a85080042241c0004856074035440340381f42c1d0b13000da8400d8400740306060091001424451050076281c01e46a161360350903058410a034000c030b400a10101c1c0c01050050422000c4000d01440c1c401014000e0340540028040c420207009240d9461b03440c0c3c010710003c009a08002d00d4020301a8185c0818100040c1502d4103a028400c550103901c5140d001060380042c2c20180c0d00c018031a600150f0620301040c410595940c0024400c0762155610040075280a9254000d0f00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 666539406 1250 666538156 666538219
    0x30f010f050105040b010804031d0402030708180a02013f0b0a0602010506030d08061804031e14041509080706020a0b090a0c0918050111070203010c141206 68
    0xc0d44041040e1460161007041c0c0045110380d05000455500ba41d200c0c034040e40c0035805240201c403800b501c079403140400791442c00003600300380000708000e402604401c40c01c6c00350000710b0800c1d4000351011a80c54035901582002400901c2400d807400f810320f829121202001d0f40f95620a902e46d4080071001d504c9096a10160b9440703846400403a003a1801410860027460703140001d200c03615140c400a0f8442c403500e4483d0082c03081a10100e605078841081c00041040000c01c200d150341000e040c043d0400122041540c0034540040790111a544540ca00b6000c10182100090602d820600c04400d800b01c05032011040140c000400183c125003004a00001c20068001e8021881c81d0300f880c15080c18000c0140241d039000c1d8088900141004400da01210400c1c0310000d04800181c91981d4025210400505298205940841e108420400402d8482d20880007000386400d0703600103461200d503940c0000f0039800280085241843c000c3c0180f036100e503000700080c0419800205810400c0113554000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 666540656 1250 666539406 666539411
    0x1207060501080c0307030c0e070903120306050f0a12080a1e050d151412010b06180301050105010201091e0204140414010606030509030f0d1104031208060607021c050705030f01 77
    0x4201440e018030003082c40003c20b0f405810124116242e050700c0700f4061045541c0071034030000064000b881003c050f4040c1d03a00c00290051200302c0c0b440180508618010544111a9018012818135010700741c0300031100c16031190020a80540c803100b80c550054040d036028442c0c619401800142d0745108800c501c000c9840e440d031182880402c010032542d10a514551842c1d050405000d194a02803800014480464075000000b241c4580507001d81105286603810001c00310b4000160701c10310701c648004401c01e030001c03c456a603901c012803d0751441140584540d80340d2103802200d404028440500c980040c1010030003510b4075900d02035082048400743d6505124005000c11801c0170300402c00181418501400203040890019881c0d02c40c2d40c0504804080005c0c1980700c0340c1130342c0c200960b165028012240c840743d40341001800300380d640e09004005070003103001072a04c0c50700200f0303111010b4020317000300b030a030040049120740c00300482800d44203445507050021b01a03504010038030045c5840e0001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 666541906 1250 666540656 666540659
    0x16170f042606010515031902030a0c0e031c0c080702060d02030f0f01060e10030e0a0606060f0201110306040b01020c030105040804080114011208160c080601030b13020a0e06031207060501 82
    0x1c0c00700680c60300080c0303503900901c004110035500da840070344a810315114800c0d52521050320382c900300029607a101880700c1c004000c01c4124140c607405911304800b1500d524918040582c201a2601d11040e65a2074107100c094004000c2131103000b1041e0118400e0700d5007450f18000b600000d045401480d40b0503c60f5130000100540341c651100d00c960800c2d002e040c4440c4130750610b6000b070556130b14101e01601a0510f8001c141c8814480e410a401010804056484411385400d1040c0546000e014240c0810b00b5803192044882c814440c921041038020300081c1540c55000402c0050b100c804540f80c1144207501952803070b9502031141c1801288901c0304556160f25001840d800d50308886000d201d8101c0c000010041d542035603111031695580a6040e41d5181340c0c205890b100d44096007009001120340040108010304000340c0141642d015080c4035000e03940b400e00034107047c03c0031880290030003a010030800802c6005070001d0382189000b8151848807042505480c016005108255020b0351650f00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 666543156 1250 666541906 666541949
    0x304170c0f06070b070503191107060608030f04232e020a050a060e0a0503070803010f0b2503020705150403060506090f0f04020a0b0a080a060b16170f04 67
    0x40c5540d48081c2a904503051000d240c8481902040c014026018814000b0005101050b07207500c40d40318018100d410450702074958a540c550780c000e154101da409140080c04034031140d0010680d40c4000c504141c032840c00d070800f4640719031201700031200c0c024083c0b104407003035041e0b84600704105c01804060022651030000200b00810003582d06020080d0f402402c24080400d6000c104003c107d900160040b82e121404034803140750401e8070340003038068040890700c5810402618011030481d00e05241080304281c48035500040340c800c82e99811401c1c1084102041071044841c1c118a074039000340191403441d603070340d4041005c1d620a514140742c00c100024082c0304021680c440d05800c864155011426464154003940011002070221480030f18000e001804541e18602c0000c081c10440e92403648800c45040b02402c10303c1c0580d90134501604020000c00c06080c0b210036100c8a80d60003103000110f99594450165071080d103148505007650420440c070310049000001d01c024014521081d174000d01c1e128 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 666544406 1250 666543156 666543169
    0xf0406080402011d0315060a12050a03020f07060e01030911060a03061a030f040f1e151d120a0216031a240402030c07050618070f030c0603020c0304170c 67
    0xf00074002d00c04904c0240107890008420881e40032030381d88040151207400c0090902002d56201d00c01540700c541c202c5040040110351100140e10036001c89030030084a0244d00e80301c114601410000481d603030b41c60010380d031281c1c0090380650302070081189003058880c0810515070005401c8008207480e044104110441903c00144c4440b94980303040c194104101c0c03101c0d0b00c0c0c1c00600094175000d04020080c0500c0400d0040141c02c680d0104400340d080c441e0301d48402d01c2d03544082c80302d5202e4680041203100f1083c41510320480d070898005040d21910400c5c20101507005140f680086119a1b91000f2005410f04e600f94051030040c0710124110311403c1d1441c0c0212401085101030381e00d82549801161100c901001244008a0780541c6a558070016000070340180356020380305101ea0340c14040e489641c0011440054294010b8a602589071000c03540b481c2c05030720009081d0310035031200b0440e15109038003a04611103000d0a99191503a0794041442100e080c10a0203610703041b40c042c9800500d00b45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 666545656 1250 666544406 666544427
    0x60412021b090406110c0105040303060f0e16031505060f071218030f1a0f0103020102122a1e0d0f0908210405030a06050a1d070b0903030f040608040201 67
    0x2a000000c0084054045028524043c00082c0140c0d21003e21440002e50503041c0c1e2a0143c8002c003c11084c5410b00303000300601807510410030071002140b408121092a105000d118242450740d00036400b003409800c0780103002006452203250700d280c502140c6039440c5801003604da1040e046040c0c0340c85a50400c0481040d088154a013440b0000f640a00c0a000c1902d503102103e4101980041410301d900700031000c1944403148003c0034080000b0401e14041d081c0c0e1560580e8002c0e030841d0321001030603000460760311400000203980d0100c00000009078000401040c611104031041c0d8180703150b14114041020700051004505400c810f2140d941207034420544014014686002e40c0c0c505d00e015180f42d103130a852280c40f502c0600f016030f0303a84680a4403080700d00810000e02143d0702c030303d0141007000c010b007020384036011081d09000038010510302040142c0401091f0802034052185010700c596015404485090381500083c446401407501031400f8100801c503e13120300703e80b441c1510004000e074112 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 666546762 1106 666545656 666545683
    0x15050c0703031103130204020c03090d0c03060b0306010f170f07061809050603031902101503050c01031103011a040503070303050720060f0a0e0306041202 68
    0x82402440040c0c002d42c2c0c204030f4004804105429484203450311840f08080e86a818090b00d015801420ba84800b4412a4034000d589004951548440c910070340d1491800c800800510655000c1c080030514200e015100540c10401c481440001038042c01207000e10700d01e40e96824890802294010101702812a0201e03607035000014040035140c1c5181410201c44c0c440024800c00500030207001c2d00004000e942040048a80d160034228401c5001e021840b601d601c6462a42c5980719000c00c01240e05041240981107040540c03600032900d0440b41018540880c1142c41c107c4c14003580d05480d045142060f69203a04608400c1c18005c07500256814060302c100041010f40140c0104111840341070700000c4080011070105904840d550000d402078000c01c41141e003801e030440203001c0c2c001d550420342c0201801c9804285003120840d001c40f11100c201540c06481c580400200700c00042 = true := by decide +kernel

theorem cover : BRFrame.Cov 666366906 666546762 := by
  have h0 := BRFrame.cov_init 666366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 666366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 666366906 ≤ n) (h2 : n < 666546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
