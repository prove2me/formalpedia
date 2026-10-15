-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4441
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:37:19.317189+00:00
-- url     : https://prove2.me/submissions/5ce6489a-653e-4171-9c82-5593f560770c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 798561151 ≤ n < 798741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 798562401 1250 798561151 798561191
    0x9030a0f1404030606171605210a061514060d0209060d06080c010e010203070321090c24020d2a0f110f0f03060109110f04180506060304151a04 63
    0x592100481e0b400750390301d90440400d5100d03001a00d40c60b447d518600c0d2100700189054100c4000c02454064000000242001c00000c041d69108040c01b003080d0003007a41045e07541465a02102e01d04010140c1c0b1400c90341d8482c1101d140042c00040141c842c014640450194003641c20f44220041c078066002c81c40100000e002c0301c0c034070300036685e090303010b50510012070f141e00452900034081084034009000100108400ca1411060301e01c00050880003511030b0082c041480c0d201100b0304140c0138200b08506083c0701d04081542d60340c0018244545001001048014540c4031400c050b00d22095840400000300030220005400c0300c294140d080381d03410080301305460000401d1282403201522442c504240109426250000b000b4108aa103406045c101070502c180188000318400c101402821816001401c082e0046000b0100f040d419001d84004440015103420b104150510402000500c01c6d80c070140441c21640012500b01c42810700303013001c00020040b00b507100741401420000c4040301c0d101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 798563651 1250 798562401 798562409
    0x110a08070b010f030b070f0e060a11191203150515030a05060a060504060c080909130c0906050604050f03010f02211806070c0c080a0b090c0909030a0f1404030606 71
    0x7908141e643e460704442000ca0911000344000c03110800182d106002e96240320341401c0c40d007020104003002c20001001d035403200946401040e06524002c1c00e80e00100148100c483d00c021007000c1c080816291410b0303200d000b0446604150304c810280c0035151107405c54000400010b820380114003640c0060b01d113550000c8a0705002c2078540000100146801820807086070100c2c0c46442c541343c1891320031540c07026584016900700300d0422503400e0300e484610090744035141c42c0e81e0141d01c45001d0b2806144410256000c000120b0a1070b80a026540c0d80c1b4089908590040395000400d000300004a80980040302150710310901c00705e583c80e100aa0942c03004004805200051195951002810409410004440416401940020362140c01014100c4145014802d00c405050351006141c1ca0301242c40700071640d400b650000d00140402c1000401c000c800c003110034441c2c1d40342079500950b41e806202951400c10150740b01410500d40030300c55030340316041d01d40c41403650740380c072400c1082c003400032440703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 798564901 1250 798563651 798563663
    0x220204051e0a14011202040e061602160510081806010b0c0d18090207050a0f030c020f0405070806090a02250c0b180d0201030f0207030e010e06040f090c110a0807 71
    0x40041c01c811603d10509900350407100c02d090f5a039081c0560500440d08001040fa002039075030365124281102001024419007407904d102050701c520b00307002800d04841601149200d2001e000501c00755032903001240d4030514500e4040c5d00790350707010a04d54052401c070640520b14010030002180ca40c400c40002c0866110060888401e07010162040303a0950030450103000d1098100d2041c0f143c040c1640041003198080d00031a030107944030b0b403528030817005580f5048005c02e0001e0021400c505024a8690941c070045604101c0c07843e010300b000d441d00340b00810b954070440d02c00c00060544411a415284080f000f0799021f1540203000600c12100e040c1103900762140c510020002545280e1a0100c400d05003030044c0050303100329128107101e400a42040200d061641302c03c06458001074a20103001010b0003960355031440c03500d91300003401d801070f08011540104000c101c1844074090180544044850141d000510302c2400c810884400c00340100c4000389000e80000710007031003101005402401e010368 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 798566151 1250 798564901 798564961
    0x30607050715050402010311040602150c09031902040e0717061503100207020402040b030a09060c0306081e0c060a050c0106140d02010c02041410030b090604020102030322020405 78
    0x11000e503900e0266a000074108045200c410140302d06a81120350024410705011400b07101e030b030628440300c0e0080c0d00311000607800007881003225064000c2c0b46820000648040d481d0200c4400803070344502a5850100d1000c00a437035a40846d1555805481c1c0d10030703e1070075104020f485003980859020381039201c04a5110b40004503c85004440f210900c4420040c01001c415242070458406508011801e0381e1166007400001003040003a00214801c80c14508001040f0145240410444440c14500d00426240502c24000d03241c00144403420484070140708000da6200511192400d00d01400c12500040702241101c40280c00c00e02420783c4000801c02400b1030382d02c4201000a800d000619203501105100c5210003650044801d040c3c03060006c2c1c0040b03180a00ca060020704407000780c6401c0340806403a002003007032001d044169a0880b81e003c02900140c1410b4000075501c0c0001307444980b0800300d2499140b0070018060008500030341c081e05c2813009203080c2079070f4404004042e00c1203000c0310030300d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 798567401 1250 798566151 798566161
    0x5040306050f0114310203010611060103240609020a0809070e1b0a050d0603050d2307020f0a120302010204140303161e1406010305162426060306 64
    0xd02e060603280a81e03481e85403014141e041000c08601030302e055403411082c5010840f03d0301c100d15172184802540b0300150740c07035151507801041c0540e2a540302510b60001d000600010361340d40030340329002e25100d040490500d203012207000200300b6542f2002d14644000b6055032100c3e040217010303104041c100144d40f01035940700c0d90f600c0011011100384052071815100d4041a01c8002c0144c05e86044c80d242503804c00118a554000700c40c40e980007900e19a211054400d0417950003605000c84064440c1410340d1454a04040c500340c0c012034400070311909401b00e10041580b01c1c00110001000b60341c05603070000b111410301074003c1d032190140b070389680101420120f80c1e00700041207401d02d0320340d107000b80c03408412034850505940030524404010340b4013416403000714041c0050000310000030380142000e0f51640c90403910340000c000646d1620f907510181000101c011500142c901c1284101c880405d200a81d01152982140e14041c0c1d002d03005400c00c426080d000008040c4985001c1e030846200e92a1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 798568651 1250 798567401 798567421
    0x60313140d12021c051f090c0504031115070c0f0b04030206180a2c0106030510090e0102090d050a0212010e0c0114071a0a051f03060209120d0504030605 67
    0x10940310300000c0b603440b0a18001e203906a038000d00c070740510800c41a21044418104030241e4106a8064200a18080c00c0f80c880d400b0f4441c0319401803000841c20030000c9010702c3d000d05903001d06c1c44050a1070f015a500c0c40d025071903428100e95660121000207540c0d81c8c2c2d45c9445424410940103c040f0442c401d400401d1401c1500e08a0f025240c008040071b0501140381518107045128070303203007034020141c20000120120b550801405001c81a01c60801405482c0103280c0e00400581c032001c1094184424807030303d0180b001816040d074a1050010525503c4c01511501a109500c0c02e250405141008002440741c04150813074000d100b04c40000f1020343c01c0761103e00b42c0d9002a0b00c038000760084110094951f016001443c03a0341101501c10703003802d184d03840c0c442441c511043d050601003484010420065402d101d9140c0c4a01024202d8030031042c161800c42106080e03000040c403990340020541d0043d560041564001d0440c2d030300b103903050800c4880042258210b031000301e810303508041c017240090711 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 798569901 1250 798568651 798568663
    0x402040b0f041e0b09060d110d02091815121f0b010f0207051e01170703020c120403030203030406022223040902090f0408190206010f06030c02060c03100506031314 72
    0x1130140c1440c10102070a0410001c0d42c8017148101d541607650b01d5181100c50041c0140400c1031f141c2000680720780725282401507a140c02072140a01500220800c903c0e1609c1070102d0b00082000e54405a0715100c055501d4503050340403e40d400c0101510000d60341ca041c6980010040c00b000b0399460b180c0043d185400d03aa20181402180d90000c2c0c4041040b01c80b4102c040191100d94051500c40c003800548040b15010100544505001070780005500340d110f4810040e81000b140744103015460307c0d00d540ca0007922030002400050a164001500500045180081182420b8000145d00401e0303a10100309406100042454110701d41c280210801840c007403141c6454a6000750030fa080c6555125510220303801c0091085a1030f050900500701600e031174049100715030000c0c0d0000c2c0300030350400030100c480040991100041600386144843c6550b404500c1c03503000a01050800d440c0d8030380200c2e180d06070030a0707007010b50090404010040c0790450710402000da20300410a9040754407282201070f48481e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 798571151 1250 798569901 798569909
    0xa080c070615091410030809010306120c08010605030303041203181203050f09010b011407020114070803010f050d0809010305090705131a0f030a08030402150703020109170901020a030e0402040b0f041e 88
    0x2c0140700c17040020418800091001f0401490700090360b68036842000020300e0818001d0380c060610701000d0003100000d100303000281c02d04500841c15850169030b181200748d18008811b04044d1030b414003000032411150700c002e85c0c660003041d5054100507000000d000381000c640c240c410030710703540200d6010b80040c410402c4110701a540c0240e02c41c4115004034480e40a841d08070b04104003041485019041003001e072100c0d03071103140c40a607603500d0302800d0196021203811031032245450240070400200709c6011200300450078240482c0c140da80c1031500c0e0410440740d0105400241500710034680340e01036404444150194100340750030744610010300000c1c04c0c0604019405500075400480400d02000180d60700c40e10041055190b0455621500a541c2010004902503912643c0740c07405c0044182c10f81a4a07026071003058248036000000035512070302e4072405014000400c500599980701c0c2c3c1c0444014007018085a59a51040e1140d0041ea91003481401e501100d888101740420005104e58011a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 798572401 1250 798571151 798571171
    0x60c33050106140d090507080a0c030b0603030406052a12040914010b07150902041806051e0105010c06020c0a05070302090906010b03010b03061809010507091205030a080c0706150914 80
    0x35080301c4c4050011300006030f069034180b1907410300040c4c0794010001d40043c0c1d84910402c0e1405480c503d0141c0200c240500035501c42d410a00050000b80e501005a4030180c403015041014088030000f5403000c01200100400396024150701c04017041a1800144126003028800700560418072030007044a603800c0c0030300c03180340200300720301808148001c440c2c0d03030082c115160015105200364001801c031107074082d054030078200710010017061005922805074801001000240800701140042c18400c1c01400340d1414014036403811003e0000d9941644c50009a5038202c0d100320704281012941d413940341c070040340320f0001030001400380c44d804681e640c1256134103e4030908603400c00d51403d85030703000100050303013220624004604040c0345e2030409000d00c410600020740c90420783e0001781410381d950003c0001c1d9440071440e80001310700000f1a10a2141403800400c50349610852555500c80d801d8007030843c0d41081401c44600000f2410a401c031919200100808000d15400f03000d1010101c41034960 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 798573651 1250 798572401 798572407
    0x4051003020c0f030307080103120318081602040e0a0b060d0803010302100e03032a0a240608031902160509061320030603070506040f060c3305010614 66
    0x4414025000b901c40b1120b168196141c07140885074140c0782d44c10848501000814620042003448071024420641080c1c601c2c1c18020b9121030103417503c5400c41404004c00825002a007815000b04c820003001c4500e17401001400410030b00b84085541d2880700d001540d0014110b404140c2501e030028000024550100728035045071710359000c205126481c0f04101c028001a1403010030547e0342400100450070513501d05c1c510b459810424500c1880e82104004403a501909103040402e0020280a001d4009062040582c4100702c1070800900050751180c400e84c8004980d8520100c00100752108121056080720500204103200d0000b40165100d65034018903c1000302d001c0d402e100030201c01c00000d5007000b151350055409004001c085070f034112501610040284105441e06209010003050200c807201d042505000c1c0a9042d540184644824045074110840402441c0050a08030902c40d14011212503080011000d221180c0c00c94180baa81ca44000130038980d0042a110a100c001e0700080c0d81 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 798574901 1250 798573651 798573679
    0xb041706070203031905060312030711061614180d0f060c08160e043c1512051c0504030312050108060c0c0a0f08190206090a0f020d02130b12030405 65
    0x10041c600941183d406000d09c2c0e150404601032074000f54002c141e284d4401621aa00d0f25401c1d040c0303980503027410155111601d0720403405520030708024000c60640e44580c4c1e500f01c0210000c0e02c6017424a4403e800c08440d4076807400f40070100c02d85941d118090001440782001105040720150303401ca400104100281e84c42d03407035582c4070b9010038a5006000d48005003440e000022443e02e00141a10340107201c0c00d1041030640c2c164045071404900c142240e050145444150803d030000403d401a0842003612000718401c0c00010024548803480054508030702500c000d10040c000d03030207800160081035450200f4280c00711280314850480d50301002400b4683c45410703030992030358808841d002252141c0115600400c0b43d402240032094481c19003a5540c0490301c00c0314000c0c4503044401c000355004041080005040410140030095000c403c01c02c40803c18400113405091440019401014410050350b12003880d0b80031110604c412696200300540110216580e48228003030306030030006101c4040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 798576151 1250 798574901 798574951
    0xf170105101119140c04050c0306100210020408060604050601020a030905150f0c0102030702010507050c1903050f0a0f020708010b1309050a080703120506010f0206041b0b04170607020303 82
    0xb108180080a43c2c02107900c0e41500e0007588000c2c1c10039540030340000b441c03039014001006038030b5480c5801e0313506010038949280d0f46402400004c0080703009a5a000c014070085200340080c0c0e8040810394421500e40d6200d238104d03580c070403003121030500652030000440c10759070000525416966060303440d19500b83c00c2005001120792603240f403130103083c0c040c41860030081185000e030141e41d1185000507100e1030011030080c203582c4068480020701c50100140e1140071004103c580c880804082c04100d44521494129007a100c0e0098541040d00082406180380703902c98018070704200540e08692035a5100d0111a00300c2d080500d810354408000c2c078078001c0c070242a4001200311400341c4117540301c20405454148666018010840c0001c4031850060710100c111301c21181c01076000c0c64a100540f144040180d0740780d10241002d4548005080d0380903e020700c0c100b446028042100c441e40c1c541c1d9840b00c02c401082420800100b10b030280800141c80d0700d00c000181c0b485480c4450190109000c0a1041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 798577401 1250 798576151 798576167
    0x2031204121410060315060f0b0406030e1f05040507080f0c010c0204060506040308070c0f051309020d02041d07091a1c0f03200a021302160c060f17010510 68
    0x41c001c240100c00c09501980010704c1200000c0d40a0100412110306104c07240003101c6c074503041a102c4694a10007404a41034480994064540a040001780103200e103004070f03e48410810f0708a41400c900000d0031a110554015900803032065049804054a8035251510380030506c135051425400041e10b169a0761294840381d0300c6c94009040010610748400c0440c51641c000d070401d50303d0805c00509a8100070444580000400140e0300c15007803141401c0000300d10218400d1480c9400341c44042200c20355540b403000c080120380c024420070444145000051b54a04501075604403805949400a148180c40c01055164076402090820901110701005100b451403007011141c202d8505200300010702a10010b2609402501c07504810400c214185010a4005c0614009a0000f40c000030045c1c0f280c200c0240ea00014000140e00d07010f40746502e821541c07216001034010b2032400030000d02c0541103441a102c0000303075a65100c51110300100d041c0c010f030b001c1c41103503001001c101c0101c59640c402c441d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 798578651 1250 798577401 798577433
    0x605011e05190908060a0e0d020f0a0201030507120f0501051e1c0309081207120e010c020906131e0e0a031b11120106051c230c031501030203120412 65
    0x2054400c6030319a01060300c0c3c014201da80a042c6d40e6140070360400c0c00c40c2007003ca00704620901c010480c08104140c01c0f0b4551000c184000d0602d501c81002c030f18200e0040d102899903e040a000300407222002c211500030345028071031075025280142c00a0601c21540c0090321302d00d080604550808162211a030500c2141003105a04000402c000828455014480c1c0d0801c40811800152681028107104a152405000300400c3c8007040c4080d80311a41c12641051091b03404840250140c0c0d248004900c502c6012035030359510b80d20f03040c260060581c625204540b40e90848104108810146030b1060380c030340460502501190a14280110110800c0300008601e071083e424031603201400c0000c10380303500c280100e480700b5075141e000500660070800071080344c131210303040c400d8289031207070b103c0744502082c087d0035090803040c5070b02c0b1100e0440104042142d108000e81120400e210072031046100303103000e00040740309000f001101034000d4440e005607015100d1003e683c00c01b4072076a66070420303540f6650340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 798579901 1250 798578651 798578657
    0x10c02031f09080a0903021314070f1404031a0604020301050d06020315120d0807020105062223040c05040204150f030b0310090c0504020c0a031101060b07060605011e0519 75
    0x142c8000a2402c1c1e000d421400c2039502c2e001e82c1c45045104024214035664a10b070b03100d52901d01c204843e038905011a076000100390400350301c01001c0c400b040320500f09a50340d01304016030003d800000c00402c00030b070b50048003603540307620900c2c1c60301010003090344801e106480c3d1040f180211400400d000e45d00a5420200005100c00c01414460110b0340d5010703500448401500300524070515a40c01085296209107188002c0040740740c000001105141d00141d04006250007e51522100340143e100044051a2065481400d007000004419003442158115000101c040000441d03061038002e0781c00b0b445895482540c0301c0c900710300866010440703404120030541c851800000a440034080310081c441c81d0300340401c01c80321509114150700c80607840640203a20400c8142400c610100d903048034142e06d0b10701440004500c1e24598090030301782d00b00169002c0001599010031282da8800c6c01183d0f030a880f43c014601d0441c90210fa001c81d502c10040129000304140020307031010640307440900d01c2d541 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 798581151 1250 798579901 798579911
    0x60f0729071715030d0e04090816030228170d090b090f0a05030919151701092c01090803090c09010b0705030a05130302040207030c0c05010c02031f 65
    0x90080c480840c0c0c00c0c0c03019004111545a41402101e41e801d0342c0e42d1003d444040562014141c0c4003003580c07490008000360401c11202005c201607a01d83c1c0040a03074503003008203203845080d800e00d126140d4224000850144c821040a04490b100150304d900105100d404100b0a80c0502d880b121600001c813008a030300c3c001c0400c404560f2003000e00c81c0503055401004100c039076151041d000d038039008495000311b00e42e5112a480d10005040081180c203110816510342000c041440d1503c0a0f002040e00000100300342260340c00883c590286a202c001090384581404a903a01e944201c219044503400310501114202003220707540010300446150440d100c0000354180d000d442d40155a04141c0b04100241c0192000600520341a0095405806c0a0b0051842c1600594504c3d13501c0c0b00e0340000900703000d80030603000074013a0b0f00098030b0011a000b5005541d500172524000740300742c0001408440440c0c82c0c60011031694070403440940603e42c0603008142ea00c40c0b41035822089100040454a103540340c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 798582401 1250 798581151 798581213
    0x70311030a0b15040e0408070f02090403020c09010b1216140a120c020607020307062c0f01060b0a0905040f02070f080a080105030a1208060d08180a05060f07 69
    0x1000298459110301d200041e5020b01001001281c2c1c032980e51940c4000001d000501c400705205611642066028904966a502a241660744c9094401011758042014006c0100f410f40118050280032400c807130014207684c0b1001194203078041c5a007014000d08500780000c0740350440003150010900b407400c1c00304410000071840310a580c00146520f0000d01d10b00c9000384080c8030384c0501d9441c04114000751486141a250095486c010640050550364840700c800e00c600160b03040e5420340b01501000e40c0814910a598656601c400c0410b03000690b00e0110b000862800f4142034490110507580c07800c0d1442e24180802004d0600d08807045c00e500c0c0e00300001c2e1300003034006200000b518800c104203500d030109079001400d0800168405030281e0070203030391b98001560a4801d4902034031142030482c0a901c0d081e0210b410100c501e500208911400510409007074000e101d1010400340c00c0300c0c0c24007590340392014810315000783e0b1101003010101303201c020000754a4860080d220320302d440c82a0280031903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 798583651 1250 798582401 798582431
    0x9060f041b08100c030609111c020f0f0c0c040c12091e050c030f010501060819090609052a0d120c080d0f05061903110f120d0f0c08040e0703 62
    0x120181e451080d03441300d15070384c0c998243c0a504000c104801041020760500050004244075400341352040406884889a04070034039410744010036100c014554032540421041000341d4049004041c46e4803402c040d003601d07807505004038100b400e40c07035031800e84000000700c0700d0000d089440c404039014200044d001d00c540b8608041c1d510740c6070151000344640c00d00081418140b00480301c171601c103641404014008250020449600413005080c80031840c80c0404091005110b4050000c0125003420720560a00500203143d402c2240c086840082e1003101440c81804440c00d4480036401c903e1905444000c242804189001154207051081d0040c0301030351703030701016802403881d1000d02d540d13080101c9070f401d80c502c100c540c010760070f03101d0200c0303a4400c4140005d503d031681300c000d2003090800540780140c0c8038007111a6003600007400b441806845070700c02d00d03100d8442102c00000181c443c0041d841135485002c0500c00150051a2070341b4140c107040303400283c688014403001c285030305e4008603019880 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 798584901 1250 798583651 798583663
    0x1b0108150316151d100c02040515040e010603020114092b11060a0c060c030f020c0c030d021203041412030c0d06050139050607090e09060f041b08 64
    0x18042c2240720318107054100500300c1034208400c08106130104001002204000a038400040403107081c035a43e90f9a8804541408990780000d410504000134030040040742c446071001800116014401110300e103001c9404c95a552001a001507101c4144020007407800700100140f803405043c0180d60b100c6a64001007010f100217407442001c1a5100103000d01191917040a4404070454500713180c6601c103d4014030301c9480c01c202425240c0e40c1c3c1203040b000d5010740e0100c48995080d200c155141c0d1000780d40340d911703034440b0b2111501134001c40c00c041510b40d1021031008448500c2811142c1540c55039200c0c2d161f800750070201d9903118801c0803450031000300d1203c0514803c06613240300300d030386104400e1450180c64103a03201d107040c44140d00d41c00070b6444900240c41203c51210511580b0310b01c412800c00d01c2d01030b0003500a04140a45004c0c80042d6a11003900c0c0243c95049441d0f80701926190143c13503998100f15513a51031460004080f40009400000d03078134145080d80420080c250f240d10103581005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 798586151 1250 798584901 798584923
    0xc05190b0a060e0408070303020a020709051e0c12010e0c0921010b0d02010207090e0c0607060c0912050d0f0e1306050109170c0105071e0605181b01081503 68
    0x114000c000c1040864060059602403c1041660703600c500f0681ea44d1022030082910040c24140c020940e004075900c2000144001c000e407080a00403401c00141d040c0d80441c0418042082e58403150000b021006444122420b83d100706040c0b5006038a0281c0b1403d11700c002405200100504000c000c00c90344d51204040d01444107405026042c6001042e040c1c01c60313403117503041402400030700300440142c0c5c5c011800808031205ca50340841c0c0c0d000041c80040c03c0c1104c0c4000242e000700046403050602c101a07200600034802030720b94600090310340d0042e10300b02803040e200900c04d60000028003500c1d840382c03541c526000658181039800b04103400006070012181e42c2c22003203541e903070301040100d980e000031203134000c000f21001d80c1800710f80311a05644030140f014109041c0080050883e0800805414190002402c400314844071011450a100500b8040e5030800c200384803442280020f8001080640c1702c0b886080403185e2400389000199a07106009100d41030030300782d9402680e40d070b80f070602110940d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 798587401 1250 798586151 798586163
    0xe031b0a0c3201170603120412030806012c010c150506041a0f10022a01030f0608030a120605060d060e100f031401200d0c020c0f010c0519 61
    0x720650595004082d44010140302c41c1c120822888119903089074090040d480528001d42c5566a55804207140c0821300d41a1110110002000204407038000c5c04040d109210b961004480d40754a0f00440700354100c803042d122522a400c00e0346155042c50a44640c0d81d81040c103101041456549600408050844a52054540314402c0251600c0e2520404914041c0e00d904c0c50301d010342e14000700e640c0540940c800b42c0203044000401c854140204030b02c00400502d0441c048641110001099036012101e4449000c81d06000041d00300c8140343c000d500c161911200214140703200141c040f14003103145c0a1f04036400755181c0c400325481d180c000050040c01c482c0da2010401a203407000b1801c801000a0100600d1014024280400c40c1458100411241c01800c6204070242c01e03000b032401400d003088224840e54048442821042007e0f02500401c146094200315070095032009076210702148100e2a4020740038000400190b0151408201d220701481c11100804030b5400081c8100b0ba45490589007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 798588651 1250 798587401 798587429
    0x304060b04050c132306070606030f030c03020c01022410090e010606080f09030a0809030909010f080d180510170a0b0a080c09040201050d0207051b030106090e031b0a0c 74
    0x60312039512132850042c404032140c41012541c0e41c500910604854903014892800040c484084c4505500001c004d59080b0301a903490007810714001c3e1604050110480140c0100c041e035030259800410a40c0c0c0301020010754080d203000d51764884107aa8402080381003401004500414081b546114142c0301e400010300029100c0e09150010b0518140148440b100310003078000c02c000700201000f9242c10b00c1503405c1c51402034a810101c0c0d402d500842407695000140c4600024030b0020041c3c07200103c0d4000f41c19144841290b81040300c2802c40c10f80643c040e030000e404100a00d0030005801018a00146440143e140e007000700c0541584003550043d603a00e880740505d01c080d1a003842c4580081c0b41840041802080000c04255036120041001e81800b0000c00d00d071154074001d07011503844c185d0140944200141e03036809080004001c0a00da4082d40c40c1c000701040022142c4603008100300a000150704240441c0d51051400c01c1c0340d15506a00e0152110280004400314490f0010748512049486 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 798589901 1250 798588651 798588667
    0x150e131509051f0e03030c04090e030f0c06010603050603010e0c010e0d0c03060606021212040816021804061802010801142b03021209010c0f06020903120c06010f0e010b0304060b04050c 81
    0x41a44d000030030402d5190010414409060740d61000c41c2c0072503001c20408620402001300032800e50086400d40c10422200142054484030040b500070705a400300c0c0c80c01c1046440380400d050882d00e5102580c0780d0340e407000d10b1510301903004040710000c0f01c4009104100443d080d40e1018280301d01a882110700d0b64840c1403e20507680c050240080100b141020a42441c0e1070702c0c910705d5400401742c80074141440024801d460303c082d18a2031450150050b004402011001690f229407200488040d00d90a20303150510b40c40c2c02c0180075050245405a44d14800b590910201007086004070340013981c4180e44590800407000c1c669201045049805070041c0441d4080c200a800c1815036910055440e004014000082c0c0c0c101d000700040355002421042503c0492402c80300074441c91000d03660520500e1a84007084444030020030041c21000140c0340d2603645d8681c0b45101d509a401442c00041c609001800404030f610040c40d8003500964000c180030021101003011500c0c203135600c01c4131740c0340066005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 798591151 1250 798589901 798589963
    0x303090606120a0b09100608160e1608130204180b07020303041a060a1a070606050d03081605130609051f020c040f140a150e13150905 59
    0x3070340220305607000340e00300741c501010640b2803031505030081800e02900049040d400341009800b062215403401000110340350494155101c614941c80045a03d4004020070019003d41400b40600400324140000715070700a81907548600003003050344001950304075100540d0b160301a03400051400c2c0800d15032a211130038030a0038041e00071301075020b541c000c01c18880095207480d018a0a660340c080005801e8545000080506600340c2c07045610001e603500e060740e8130ad01e140080c40001d105490801005a9a20a000746800244000f50110707004100196240002c54490107406007946802441c0c415404050b00101000d60442c500041500c0024002418444080050110320a00142c011400100000e40c2c1d100d401c0c40f11400b807911000c000100c028140c1240d070031009401e40c09a840e280010859008140c2e0728440d102c911840940051030900940a40303006108541070703d818984131781c607040000c0c180c0c925081882039a541c0440e000c617405018451003814219641e0784004580a015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 798592401 1250 798591151 798591163
    0x111c0201090e1608070e090903181909150306020d06060f110a02011412010b030a240b0f070803040b07020708070e04021002070b0a03090b011a030612010b12030309 72
    0x540b141d00c41c1d920a01156110a1000d050300850510b800d00d03855443c401c3c200c8105400104c029003107480d1a06004940c0703008009003c43c041201c035240700415125080208010110580b0402121180c000340026812504684c408400710800d10b210b10750740343d8540381240d0000d8400d01e20107940702001c0c404654848542c0b400d1034100e241c10613012021800040c0c581c01d8042c0020f06100070810098a000c0c45442502d0314403680b011107484541e51501d00d4030041d031088038100d001a1809200d00720060104904130701250200d101420a82d081507080622a405100245a0b54000303000e00743c0043d490600a40c411031166003248550304091030040c2c6094129000316805800c491000c2c4484101070f0401c83c0d101303804940400d03603040301c0d09060303041c40215005204104c00006918401d80e030150041c4080f28855018942940c1c0d80303c520030720001011140e10521a0100042002031404908040304046c06100000b501010070b000210302c00394000e203414180d0008010000a0b010034400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 798593651 1250 798592401 798592409
    0x90a0504020906121c210c080f10090e0c090105061c0b06042c0c0a0903030f21060305010e06160c05010608070b04240e0d111c020109 59
    0x105000a04107540000d1414500800d068041d5224071032054005004210650860020711201e84a0360b00c2000001c00740c04460700c080e001c2c41c4030889601076441d02d5106020a100144d40c46020740c0e201e0881c0d0005046003c0d0a050164000500c0400c11300014440c420072040c0020041c181c000d10842030104c2c26605070321143c460182445486c0c0420a00c1000002010340c030540011408080c100040441c0a0340e0445584103110004c0000030369005411240d2002d001c0710128600d5881a240c44454481c088146000030088001040003d005294400003001a410710030020400d84180144241e50181c1131544162100010402c1c48820711134541c8003074403400500090b00c2c051003990b0141d06503010394020840303c5071010081c49001c2d407000025100c00781c1625440c540c0c400c420a01c0740c210b4004c02880c1201d00c03223141d088640b130400b00c6034a50400e45614800344003010030080b5007141c00009855507004100343c1e03525966003100d8081805901803000e0302c144103500006141c0d10760360308 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 798594901 1250 798593651 798593671
    0x601170d0906090b090a0e101d090a02060705011409010c141e130315150503010533030a12020c1801090f0e0a0302250302060f0c030c0a0b0609 63
    0x512102d54031a55400a88100202a075034548403074000ca0380040d4aa4005101e859003001401140180710380c60800f1100080748211486840d24543c0f0f004400a8a0700d8109511000c00c0c0d10050a003100900780c01400b840000a11141c0c0302e9000b04a00c00454440704240d40d90f955035104950003480880c143c00200c80d6090919070a03100d0004070320340c908901c0312590801305402c602200a5601400a554418400b200144c2ca05000304007804005000c1130180c0c0c41180081000d0905104080c81264410041c42d0500c01602c0684000b82e01440006010026050808813230781381080103c5c031581c40350000061001084600906001007a00b01910440340304070500d4100c80c00c0c4100605642c0350400c00a03910085418810052071096004803540c011070140c041415004103000754040000c4001540c1c600c3c180c141059202301301d010080d4481828080041550500d2016021080b035074011249010034400c2d01d1440c1c10200742040702c0000c0400204005418000d200c15086030b0701c88 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 798596151 1250 798594901 798594917
    0x406050117030418050c160309050f09040b13030e0a0e040c0905281b0c060b12100b0a08070b0c0c0307031a1504050109200c06010e0907080601170d 65
    0x2100d02c04d0b82c1c100740d0080300301585a4010507103aa08810032158074010a810310712101c0c001d4038000d000001c1c1741c41054843c0c81c168a603c68103050100156110315440300b0030044070b9540720300072002101012015000c001041c811100e00d0b80790036455801914410b040d8903210b00e00303440c02544071510303074215a01d501d04203806d0140b4480740107a41e0030034090320414080318a14465851004102155020168441c0424082d04a071b802c0202004280d01420341480207801c000c00380408150225101000c5901402e40000d000c05541d01c0f80c840c007807000308a003151f6643d13400c3d154a0301000d034019080c104000103a410100800308180307030003110141d02a2800a245032980210701d1b10703c0d0910300703161188000003030460408028032000c0b500700400401039940c442911300000c0c8000120f003002c041845840483c0038640034261101110000c00614041c1e00f490600d031900200076010003194803d40c0000300708940c0c240505406003c0801d0101c007421240c0c0107461801c24062400030602c0051 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 798597401 1250 798596151 798596159
    0x70c08030c18100c0b190f0504021f020613170d14090a03080609071b080a0207080a0803010b09010909020c0d20060703050c13080a05210304030c110904060501170304 73
    0x104d200510b510340c10484162941d070b12081080081b401628a01e0000c1d0314050000d0740e000c0300d9902044c0518000d448841c0c0140f140d0301081c038075080d10034413180564015400140c1e40ca001d0b0715241d10291160040820400700c0d01543d1066805c04650181c0154507480b010401c1c108c0038440c20741c4192300c00000c0030104c11644001d041035030081d0013140110541c1000405c1c1710301952030441e00ca80d0b25160301c90514024100914a0740042ea0154018040c80300e00003425040082d40d2201a84c000c40100e1869207092070300c0c03a03c0d50000c1506414001e1104001400001c00e101801a410241c0e02501301003081c410020f258030390140014250030038003003a0341641038000070410350042035810006002d031104002240180100088004a00541d11001c102c00c00003090a208640c8180b0455280d0490070030840d0f03010629601070403401d0303028000140407a02c500b601400c410b0040c8803094034190568003190101c0021201611225155401040303146010040c03120714000b014080e504050030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 798598651 1250 798597401 798597407
    0x1e0b041518020904060e070206181f0f060806070302030604060603050f0a1a061c0c0504052b08160308011401020a0f0c08070807150f08010e070c08030c1810 69
    0x4a00c001e68500d0303038085551001c1d030302c842e80140080d00305020404018901958000c0d07665000300e0f03400d484000080365641d640d0200181d02441003504105018003680800d40381e5008016200d0004120b544907000090203220a1144c0c50040c04d00c0d5401603900d1800c1d00601040d2200c640c4070004140c9400200103c5000e20390015030001800380b030124080d040c00294846045c08412484d42c4660002222400034600380802440d11000d051f052000808004040d90b65004521455421184c2d1004042070b6075199000314044040f404180032107040103844804007500000301000b401240001808141600700c00c8190040664407403045076040001d0000b520b40030540c40c020710114008514804100c8400e240e0005484428100d80c0350340c0d5201b0703010340d842d2614458002451808841c10b607120780304811100c00750130b0716202c1c0d603856460310f9010088010020007920800008840d000b00207078110303000314080e00c1001c01c040e407078140801c0e40480310002d00183e1449030301e81540c00002160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 798599901 1250 798598651 798598679
    0x1020d0e030a080a1808150f090a0b010603092001020d050708131203030b0306100b0c030c0f01023015030a02190501020d090f0e07020a0b0109050f070c030e12011e0b0415 75
    0x46d1b050300303001e061380f159689c0d9460690103240060850300410f0020800682c594071041142e8007800c42480c0da10f044614103038160341e02c9401c00d0f0068102407107504070700c0e00807802001c004c0d20400096141188064050f82d01d2001a001640c0c002c128400503428164580144611910201d009e0201820a9800e10304407416906c81c0072084080440c518204240034401d50f11482540340a4804054030003407124001d60196500781c106012036000c00c10781800c6602e4820104064110201060301c45031340102c1c098040e00030044c0d062050312104001030302c0381138403110509821440100754500b060006401e05c05034110b18020000707095020420f41d8001918842100c1d119540301030603894404040741004001d41000d060512200c000049a0100d03602140c800c0041901d1038003240c07a01e0300d04460300340094601400180803c1d84a44072850a40d10701c1c8400c824030f4000281c00300800000c03042c580c1a4042001d0604e68592202d03010781000d00908140031401808020410b052107003400c41c5d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 798601151 1250 798599901 798599911
    0x604150f1710091509022a06040b0a1805030c060a1a0609060703090302061603020c01031a010e0604050d05030d0605010302130b181c021305010501020d0e030a080a180815 75
    0x7a1580641c03144c0e880702110f10303006005105010f44d601c42e1403c8402c1110b6054805001c40b584143c0f00e00c2c00850808141340c0d00888d40100510340030f84550102001a2a40038541c10b2525000002100001c50800060007545c408101810162034003401e04001c59950340c0c07094843c00c2c0b0140c00020070b5130780c1d0002c580c030980080b251a03486007421f040c11999203000c2c0c0c0000350000f2001a0803003070500382513800320130b0341d209030b08690704407c0b8003004405640600107101204103c00030003004542c090303a1000174006001d000c26040581c1c4100045c03521012890a03966500001000041e0030100e0240e5405404c1c00e0905510b4000360303a8052280500c076200d50071075404042198414280203685491101c00020003100301700d18240ca82407203140c0760350030480c401d48030744100804580d040e0142c2c40c1241c4058000e000c1ca984281c000b136803050b41c182041580b41c014200c071600007815107800760800052643d519984804480d1040c0c00d80d000940028a8a5015000b0b130100e848044446590103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 798602401 1250 798601151 798601169
    0x602030904050a0609050c0c0c010215040210020a05061008061803070b070311040b040504240b07020f030d17070903240f0504081309050c0f090604150f1710 69
    0x1542c0d16140c140051295401c1040206c1c02e19091100c0010b03004050481780c01b5900503502929090f0005a03070311482402c04070403180c4440e0020f0050711349038111420b3780c03003c0d0060703c031002181c0e80c41500f000c0341100e01030740d1511101d0741071101404c04c10007241c1c03181140c9108400710b548003201c55520702078214001d125480e00000140c07100d11035001a580102c000c1307409501c50341c560540482c590410b005642c0501d140918100400306004201122483c0d11011035203414204403c641031a0f101090503a007102254000801c152400c00c2084000368550b038810320b00114824088d01d070041e026110b0320070050311290078408903003405d440440410900104051880d6821440d50141c4405111082468034041c01c010038400040010f0070b14071500c910031f0a05a440d425100300700c43c019174002c50b5001040c010011038000060003010111401011281820759941991081d2a49841c40344009006030740075020094004c00c621141c0809011000c40900c2c0204040c1c1c0703030400c40d10480c0e0759 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 798603651 1250 798602401 798602411
    0x1e02090904120c05030703020105070e0f0d08031003081201080601061d010806281719020d0204020c03040f03021815090703151412060108060a05061915080f010602030904 75
    0xc982c0541c864103e0143e01c0741c2941d440c0c1400c0c4c20040d0082508a0340040401d01d160103482ca41e01d0301c0b140307102c1c02035001801202c0451168032400aa500001d203203a80e0070380009804404550302601800000079050b21348451903060040d60384c189541030380610306200080c04050302140150410050300740782072030203031101c2c0d4902c000200001072000d070600485044805001001c48204601d400341c96807404030907035040c810350450782e0304d64034131a134a02c1840840e400303a0014a00008002c3d0200d000030800350510700c2200440d41542d00c2640040400c0442000420031804c0840e01d0210104580c0340c1e066851a150b90812a00000490340500c100080400500a0b034040d0b404003c0300e04481d501c8145c00d80d200d02650105003a01c00140c2d204200c803180c040001100040ca0070305894102000d04081d803140030a0001400003e0302481c2d104600640740c64011102e00350300c500402c81d0103901c460b1410129009021800c0140c15180c1200001c001401610303000400c40d01c0700e440640b40054 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 798604901 1250 798603651 798603683
    0x50301090201050d0209061b062a0a05130306020412050c0103090b0a020306010c050712112e03020408161805010312110102092106010b0408061603020702040f1e02090904 75
    0x1f1891094164803542c03800d0404403030078051030002e031492003421000010541801e103540d00c0c8403021081c09607000712200812111032414440d00150a14402603610344112507203a03a20402070380c1058002400040d4005011401c0c814200f201310450031082c2820004102e60351100e9404450041c00210003580002c0841c455034410111340345041d4101e4260f810315a11084910501c0c80a04002d0320056a00307261003040c0d141185030b181c24251070802001a01c0e050400075402506102c0303c0307009040e821b1000064002050101c84641554028400c510a00f850442e901000c8001005030215141c1001800001e4400c500b80b202100c460403c018010b070102120f0337000e48600c1c01d00b20740107010005a0010103070044020f001e41c10760401546c11503a03d5a80c881c10364081d41c825401c082e0b000c100459103909000b003404500c03004624026203454540c4d00801e05030303440706a540744199541d40c11800101544601d504800070110f0040d80b80c59060f00001d1100080500b0203400c161121400e11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 798606151 1250 798604901 798604909
    0x218011d090a0b0324072109210509010206040206130305010908211506030c040b031503010f0209010804140a0b0103034e1805010207020406050301090201050d0209 72
    0x20318440e00289001d100c0c1c500841c0d4480079107407522030307940030784038010001220041c440c11489004014580070049952284001c03503140c4a540c0409207185400c0c0e4140340c0701e081500070448898005d12080d46070280d00c64502e4901c04500d05a10104101800f050426a9001c50281d4206404489550b00d540a0490011100d112648024069032902d2192420440366002905000416504019400c40c0e400854022a9403c5901102c0611001030200c0c007403402d08095034000040311040c1d0300f42a02c0c0e201b214659031003583d400c0c20301c401100000116103024043e078440351071041403c1d07080840500000c1d014100140000700741101e80214452076440170003c0c407140c21703044120840956503a050241a0030f80d203489412078455540f0010300d80c5861a0290300300b400300026201d0310200c2901c83d101c00e410030020b0401c01640c075805865075461003c451300c12840d0188000681c4c1d290a4410401250f07281d50100e8000d9040001200150307030440199a0050032a400c05030707031094000009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 798607401 1250 798606151 798606197
    0xf030228083702070e0a050f0a0c0e0a080f0d030e0706200d1214070e06030601030b10200d0c0212030f0706020309062a07140d081603021801 62
    0x500550b08141400c1d010103a00044500403100180c0d040c40c0030380c64100902c003d4400498002190740f03055008a0032201e595032003440c00d58610300c0c00c1c01c041c070604000201e40c0c91031644403040690203260600f4011038144a10000c925442c1030402100c0104104283c88071031901c01c203810300c90000c8000301c8402e0241c1c0015400300440040e2426500c982001800e128400003000c2032940ca440240e011071180034007080e01039011919040c021414240412003268030052040c0d04058840d02172810301c0e11500148001c4554a03180e483d14416808130030000040c00d40701040165200c800c0c00000e0a070491000c011050f01500c918209084d40600f0354614483c14178802143e190010340d000511545901541c05084090250340031612042e000c56600050b04058020103c071180014040000c01c00c01000010300c2800844c9400060040e500e08107244e00c0c0d42c15010440c02420442d001a88400580408129040450a00b020081c1916901c111182d80505103c074440519181d5140781c3c0103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 798608651 1250 798607401 798607477
    0x41b1b030912050114090f0606100e040e0c010e030715051308030f040f05010507031d0406180b040b01020f060a1109120d0e03010b06070b070302070f03022808 70
    0x4400c0b0b800c2a0703142280c024030028640e0f0f01e9100850740440e0340c0c420b020a610311152069401442951074000c100062400001c05c03110500104e1829041103440d68003401204039800f174050030780c2c5482180050014203400d100c40b171181d004000d0601c00c03a40c1c520042c6410f00d2a61400c9038031802c0c20301329402c8810050f004401c440c072021a10030341c0c0d201801c0080007514007907210444501c1e40d500054415000f0307004004e0100350307903207112a40d16405c011400c40b5010001c2000c82d00325030350b407140f0422441c585a4695465229001c009190600d8003807a01000030a1000700031711120020460344810700130702042d07101074841c0b80c3c11413045c0300c4030b066554540c80240313001014803d070381206170358040300c0c2c9003080131401d20030095080785818406c1c07a590703801c058140c40c907000040d0390311441d64600603c40341c02d06909200740004144441c02424036544690028000c120460461140603644019803240484c04e00190000190308641070b44c91413201c2c15003c0380d6160341034403d0b004d80d03142015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 798609901 1250 798608651 798608669
    0xd09090b090a0b0621041505090312071e021b090105030d030b030a0b0115020105010609050a1e09021b0606090402010f050918132109030f060f0614041b1b0309 70
    0x90a05a6201e14a2502c6c00b96204d9400015510500c80390729007034600480c0e15528540041c0500b002c06c0c498540d21540c00307401841d0404159016891145140a01401c440d006038004850340e15050b401c4801038400c44812100d60403658500400255603140f80d058590425844002002d070b1510b0800c030b0f51001603400b5104604940e101c1a44c4910b0050101c6240010340c03d0900015245024401400544034040c210915050070801c04a4160804003880000c66000ca0b0300000c032449284080d2030024070581c027004600d03400c00307282d0b450300d600501303058414051003007403000603a00320400c5004c284240c1881600d91851600040c1070548420341450b1202a074420400d00e40640400b03108075500c58810b150001c540c000340400d09041d038010314030200310b007864240040f403100da1003407508500c50b43c2c0120b0200b26030080107090302d0080e803142c54450300481c40c0070f2007890240284000041a6000c1b0820a078422200920350100c10a84559484580c10400e090501c9030202d0b2003d880315003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 798611151 1250 798609901 798609937
    0xa05010e070608151c0c0306110c010506011d0f03150c190206010f031103010209090414010f0e061b04080a0305070605070e010c060e0c0603151002030a02100c0309020d050d09090b090a0b06 83
    0x3109c8a015a80030700b5000300f85500c0c220000b6403540c044c1c002c40003c1c2029007000d045070700c201c1c07041c4400034000d000c0d420f90601c24140c241600402c59412940301e803c145119944803d0080521000309445004082c2550050030040c404078200035040740440e41c001503450740780000100801d0082c894641401d0f0040e2004041005002c400000180c0301401c81e0001c0010017101c0d01c03481e04517107a00307084a8103608822301240d0324011485a15030683d001e080c0840c40c1a83d204142850840302400403800300d040414180306125003481403990001d180d0070601705108090000034945009080014603580c0d0b22078480f90104010840c01c0880c00010741120f90760309010020207a8a100c441c40d43e1f1280f441000c21640e0140302200b0b864243c2c4181d00145034124203400b51101801401c0d0015080603681d910a1015a0710107aa075414030303004030041c14140511600c0200040d525800141c20213007421524400750300c48910481d40321048080c0081c0d8403070314600103155032003440c01d0100030442d01c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 798612401 1250 798611151 798611171
    0xc1602041a091f1e050a060e0a0902040806040204150801090c031407080303310b041a06151e0f181507140a05010e070608151c0c0306 59
    0x10400032410392100b1a1860740c240c0d0b0383e8403d04260001103c810224070300350107080040c0345049a4003060b410700044890003e035201c80100307454070744c00d13400038000540440b09a04c5d01d05128810b60050304a1540a500e02400c00c0082a9192030161009002d1950307416031041c101d00c851601c01c00b5220140080c48004124180280495200c4c00203442414010082d1207180000103003520456850750051421983c58240302c0006808103c072050404040c1800c50000d103100c001000505403040791500801d0a19090203000390225040a250045112090107215629900c01c00c11b01d12141006940e9034080c0002c0b0403c0c0401400f00c0d0303811134000700e07001c03030b40a02c602c001d80a903003124200c1c0560300c5c031040c00308001c40c1c451003011595280708121600210341d4414003404001c0800d400c98103040e1039a900e40342100c44c010499200d036000854140103017984014400d8004114440e800080f10145000401101c4085016450082114402c50800c991084280019604020108403510780 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 798613651 1250 798612401 798612431
    0xa080c09041d1614101b020a03120809010606140a02031303030e090a05040818270a0c0e03030d0507112509052406070b0406141e0c160204 61
    0x10500d40420075580c1501040340d452441c40441113070001000b1000c4405041e0302510200011004454996110a010380c0541c80b509400030056115040c070303000e050010040104103c1015102400ca0b0341003040801443e64062102c0160302010041103686100540e41641303076115550810024107072802000040c103801122844246601b6103000c48a03958955903074046480c11a00281810070521841c02d070002140c8048604910180c8150200341c13283e20172030f41d00c1500390251602c00319507004000c180156805031818602503424141c079021000c00000c1d48a0062080c52040c00740c2e92800203401c14403604a110381070a1030030940344c101d8401c10720403a040300c504003c80455032000b0b00020300f2030050b101e014031803888030511412450036030030310022205d5045083d90340083c00384030300340214214114250056200352000165035400703080100f01d02e08000c0444000454402020b244a034a000e45c540d804040d203488580e880d00070300341c0384118003001d00c40a500705241298814030032003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 798614901 1250 798613651 798613663
    0xf0924021b03030f090d020307031d0316151d0607050a0c080304090b0909100906270218130b0402150f0d0f0c0f080c0c0d0c12050a080c09041d 63
    0x400904503484c9070740b50b21141c0d98030400c9803500001684204180000700388155200b50202100040b8100d6403251180003d140c02c0013031806085135000b2440800029002d00410348042140f4101095690101e450311980520b507010058001c000000310401000000d106280c203190380301d072840fa03a8549400200f5500c0e0800d02410207038602c1c00360643c040c4d181c010201841585441c0c001d00000d0b245114590141031060350444600d5100c00181107811003915114080c0c81800c11511001000d6004200100e2400030104240c42c4812040c0f00400c030080a1201c0740f19045540761155454074800309420600100c3d140b61050004070b00c0e00e802e020010003e00800f002288144142c1c801440401d003110480b9100c0b00c00708070707020000c0722521b01070009590b100d0402e612650400e00c05840450412941b1211580090281c504441c200710b0018000000c240303076407a007942801940711001d012110043c00c002804903011400e0103465072036411020703014051516054040e6011320440d0b0b9103117 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 798616151 1250 798614901 798614911
    0x702030604031d0109050d06150503030309010f05010e01050d12170403120b0a081c03090c060206040c0b12060d141b011205041e230703060f0924021b0303 68
    0x758401d101000298070034045842075820050043d201040e47d80c0c1c9800042c00c140c40e00703a02144c15004000341c0c5036801c0c00035500c0380d950000041420f40c4401c0c040c004842e0160000880000194018012a160b80c1800003105900c1070491402001c0e0320019141d006942000608055010041108240d070000c45034125620b624020310960b1440c0d0104121002c0034056030940d58003441080e5400448c40450025010b00b03810006044211900c40d0b010111540d008200503070300c6a41800104003c5207100c1c0300400e40e801031276092084055180703400d000f01410942c4956803250100b000d010505e80c142a0815488046400d121241c0401e90380c40074040a40a000c21110480516090740602410f0300c06c40e400310540048007480d100c141c0d03200c070318580240d031803101c3c0040702c5915080359145030f140a4423032801000b20900c4c501d0860181c4a000b03555a0520b0300703014022000410240481640c03074040c48400640040040c1510002e00072940c1e03080809280301c0d00802c4004020001354051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 798617401 1250 798616151 798616187
    0x10501031110020d020d050a0c0c0905010e1b07060b0f2e030c05091c0c080601090c090501080a09150f0b120102090114090117070509011107120b0a02070203060403 72
    0xc2003001003684c03210160102c00c005038000c500044141e0303101e02c0080440a895082801c10174050343c0360b13211256202e408c00d6040683e40c0d001409480400041164814150880200c0e00b102c000381012840c052203c2c01805c150f100d110309001d03940d640003404101503028120010300ea50016100c030079200079141c42d014500e22240c01c1420640b003405502c001c0c6410351581480c05112006012002241d84040c4003a04801d0b10910009440341040c0e400912984000348525410a2400e5007251807400e80c0c0c1d0b05100b030038141042180d801244140e0b0204910a0001e003681050920741c200c0e039140d0101030520750bd0030030005514030641d485500c1c1c54006075400a00c6c0301401221034201d02c07400360300501080080e00040b001c0301600e0000c00d603100061400406102118281030a010307000c0d241940403440c00b040340c860650384040d5494618043d40020071005151502e42072100c0c3d502348024110480e418005020150950100c0304416805002c880c1689090b0400400300c4912101076080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 798618651 1250 798617401 798617419
    0x3111002281407080c07030204051317040509010306200a0c05010f0e191e030c03022103011511150106090e0603060a0905010e0a140d020615010315080105010311 71
    0x8000d200d446040701900b4240d900e54038101103500c601c0c0d4140c000581100d59449080004001a26135020700c502440003140e080b10344140514105030103185c5208815105c4005100400055803110345150450f6003082c40020250175070282801228450180c1c9510f509002802c000100c0d403100d0704c0da07081400343c0d00070800e900c8920700c1d44080e152410900441c650021164070042c0060003400c00040d84500d09091491145005005074401d50000c150041115424400c00b0b1580501107150b1004083c591044206811050031355680810300800661441480902c01d8140c00b40081c0c0c440c08525204031070340302807042c0021940c203000b40515000240c252400244000800041301d009443c0140502190740e600d4884000400100c14103581f03641d203682d4860788044040c050080450b0040341131201441c0011605480d084d08100300404660066041040c0c440d080305558446900910340410b64080103024089070080e40d40211000e5481c1600000421540b001100415a400d44507018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 798619901 1250 798618651 798618727
    0x50d0e040504260714150106080906040b131713120c0e040303090b15040e0c01021209281401050a050306150408030408060f09010b01020a03111002 65
    0x1054071000d0790000c0100c000141c0041d0001812581d00c03c10640a080c3c5a00f001495100d081c035030558603000ca580c40e040b0361800034046003406203a44c0981185d060680f038900300700d010595107900003400500205010300200c1d074414032694800100a80182c0410603600c6564234969580e0700c1410394805542c02d10394002818581c2d030810100194101d005d80c10a245440d800d9100c110f0001c00440415960702005000180700008a90041030b440740d40040ca032407010244030803511002d254010a038400700c03420041e683e0002e10350541d50050000540c440a421003c540b12954040450a100c20707540c841d1280c3c05684c643c000211008000d428080700201001074400b4800c1d200f00380000342c0b0810000ba07040c204400241c1204250403440c0f03140682e03481d0240e0460300203400c810b80d144c0044042c01888904100c00c2c940000f0a08002c00c41d180709440003031750b21092a18000d060040342008540d080e4814800b500f454444101d040d0754078060849000c0d104080d150070001e041a02d260001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 798621151 1250 798619901 798619909
    0x2120123010e06010c03050d0f091506170705040b06131d0a11030106030e0a020a080304030b0c2503021006030308040623010504110f0f090a09090209040b09150103050d0e 75
    0xb03401400180c4404810081544084410798407190f400825203856525170740e080003d61003403d04183c091507015158000c41741a00023901e525900080305280000d41000b10f030703440421004102c070401c850010b0380048400204403e4040d20030351002e201207a1400140400d030f220110080806a2054903450303a1700d010000048580c1c000c1040c00c1c9000a0005200c203902a502c848003c0c40c0000071181040c0c0241d0002d4000340e034503008200150404101001080390007101540c0040404c07201509000f08844200c00050310b401a031404401540308010901d03000b80b1035044003601040c018850709c0c0c0c40742009402c020303042c1c40403204079240031481800002040103440319113215514002259207880f0401c0302400c2c10a00a00d5041c01c1040b001e0440c2e00000001c114480343c6892580e101c140030410008190344541c8080e1009041106038401030350b540c0f0308203602540c80207400031a81c4a140c0040c2c0b61030540c0d5030a454004041c000071090040010700500c1d00c416a503584100c0d50b00041c248 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 798622401 1250 798621151 798621179
    0xf090303150103090201050c06100603060504021e0723010c08070c050a0308060301060b0315010906020f0a0615031211010e161203051216080703020a17040212012301 73
    0x494908400701d058040c5620a4000c4040b80d0300514103030781004001318140e42031110903038062108504540301044416090b01840005002c210340850a01020201003040c0318100e60014a800314000b411008100c1c140032110000d10b52045445420f00d03071031400500034102040d103180410003402c0011606413261034407058142c0d200e000303481c61200d16a0b043d1441c09018245a90654070303508081110941040507500c03580c0c1c241c010352181200c4800251250030103410490842d0000d041ca80c0109000149c10281140d01481c0000d29007448a0701c1e454400040d00300070901001c4801e801105540007580d40c070240b49460080080e0141f41a03025550000d076074842c000c2c85c8508804102c14060030700c1600b0703004d0182c10001d10301940e4045c014501282252100c11000e6607038079400d0100e500800c1c1950107500c038101140340c0807042001a00d42c060440150034240c8071800000e0440d100d60910700110305400000740b08001e0007400349480c2c117240c440c840051008107800043d00e03208480321 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 798623651 1250 798622401 798622411
    0x306270302010c080105041a01030c031b080f1008031b0c090f041a071403091e060a0c140301031b09020f071b0303140d11031008010b221503020402120f090303 70
    0x1402d800c240d1810015005082d8401203c4d09155484641841800d410114114400781d00c2d91440e501d80707019002c0703400d030050141c002940145c0c001030911c1036032000804c650010207030b09661000c40007014130003840e100403074034426000103030601840941c0308110f00030341c062031041c06031207290724207501d00b2800c401003200c8840c006145100c99444510900e402140c0010000c0c043e640c14400325807082001e190309081c007000329400f5500300000c102c60b61240f14410501468071064809040c01041031340d01040c00040d1005e01c1c0600d00044050158502d603000704180d0009640b030b58000307540488282c00a420503030300c1400041c040b80703210b0600403c0109a95054030b402824001840d904001c076086000c59041e12a65221159185842c01e0040d610031880c9171140c007504e03424028120709442d0401900e80c040c0301031584606e203807008400032403151100ca01002408941410840d8031507001680065041440007071103560643e40d8241340ca20518001c1e500c00425128400780c142e907071200701c80c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 798624901 1250 798623651 798623681
    0x606010e030c0f040204030b010b04081005010f031722050103180203060109020309031b010b01030b0301150b030a06122003030f030604020f0408100608061806010306270302010c08010504 82
    0x75094964035040c04026030500002c4c000505150712030307542006c0c0c1c50082c1c1007000d000002003401c01018804100007942c40094040030300442d4940034210703072000003502000b01201520802020006030312b4003510340f1020a8907052070989112420307450b0400c5d040c000d0350f002a0070000411082c05400c4e500c111400e03406802401c5603864010300000a4001421681603030004201000100c070501d100e580c00340002c4e1000244c03804840c030015085800c003918a42c043d0341410311022202d4900c0348a901103940000400343e60340d03544101c0034020b000d244c0000c0c1c05110000040c41c02d01070f5a140f000301401e452428074040ea10050101540d9024900c280784400408000050302c81c10950090324000306030070f881604194844007010f041207113a06d100c14900341d03207480070004900e0401035035401410b02c00800307001706542200540c48010501000c1c0006407104440301280d003414000c05a00c800d011074000941c603461038000e02a00030785a441001405840000c91245490300c9580d409800600e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 798626151 1250 798624901 798624913
    0xa11070f0f0b0a0212130e0109060e0630060604050c030f130303020d2f09030a030c020a03050a0b0915010f06030c170c093f190605010501020606010e03 67
    0x2d9080b0381640a441c4540c1113015006244421040320303009000620122020692541e08041e0720082c1c868050b1301c10b03041142001000c00a20014031801c41d00414113568108040318880400e10030310001458503e2601d40e0290041c03906c1030007044150144004503010b002948941c00b11425900041d24035441c149101c0b400b00b44a00c28180014103106d00c079040250034503076030100c2d1504a4240b40c81743c9102400e00340c880ca80603103015880030310102280b2401c606082e03815000c43d907100c1c9044001414011019401030942d511200407000465015040300c8a002180c50f0115540720f069605510070702c00d030300e41c2c012510100c41250313059680003422071018501e8401708070050600c1c40180014423801e06141c554043e05c41c0c0805100b08421000141d8524407103091042035486d0b80310140401e40e440b088410740c06441c01001e0015081c81105002481d50184614100800110065003004000100700108840c1c0d8104904842c400d03002c0d110213075504801034500b03912078840240d040d0050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 798627401 1250 798626151 798626159
    0x180801020c100605090f1f0b0c011d0c01031e050406020a0206070306030302033903091504120b06120a0302071a0c15130515090d05070c030206070303110a11070f0f 72
    0x124820302c7e030000003040088851540c5652000c0049200c2d080030200100021344c030b8401038000d006074202e402c0106405519405070300d00641d2600e0b10302c00a213040548070340c80070110310754056080c20781c040810020811030605280400080d40030400300005070280c20002542c6a0180c8210710480790150040c2d0316004450708060030840e5804800ca8102c0710308260340f800c9000d60a4280c4008070b441b00159914000d4408000700000c124266198283c803c100610100105240fa909601d901400c440200c1c1c427003400281c000c0e5028032410b10940309108002d0245030b80003034942d007150301514031404002885501c448451080c3c100445003a0b00c55040807003a6262403810b00c2e800b401c00a15040900340e01c3e03503000d007001100d01c480710039260603101788540c1090502000760804082e003401c3d89004100e96402c02101c030a803001070b22032480400e150080c14040e4110306140c070b1107124959a10b03d044500601000310101001a0b1807040880210300b104200416800341c41924810008140c60 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 798628651 1250 798627401 798627421
    0x709201201030807020a031e020a09020a02071401020f0d05070b0c190c0203120720010c1a0c12011509090c05070f0f05010608071e0b1207180801020c10060509 70
    0x900321b07004000404000301180c1206031548080741010702c240c929817400d00400c500c0e600d4940001d070341d041c4100010000281c0005009084030801a510248829204010303405c10003030007030000035401241d42a104441e07220000340b00ca1032203940e0030166030302c0720683d00d40c0368040d006000918401c1c01e43c462003d980a418a002198401421258041548151042503400c4520115004d01402040c050714080c1c22508019801084c80c5c480c116049070303100d4a004200e181d071000413694108000c6950481c043d81129140301c4150007155495a403807103400768400f00c0040440005040c040c010614030528020485034503400e41e20300b414454291143c16010030000400c0301c001c000440200d0000d1340c00e014080080400e81c000c3c110f040c2c50701c510070309104c524480c641d0071a0700c10790342408116851000c0c1d550a0b42501d881000070741d14290140c591007106089201c115a60720350000d00c00405400030700c23040c0d80380001c0d2010b06511020034800e461041c0140fa520002c1b000006000d116 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 798629901 1250 798628651 798628657
    0x60b03150f0a080f030c0f010e06013003121401050f0f030709150314060103050d0e010c0516060e06030c0d091505090a1a0f01090b0604050307092012010308 69
    0x100c000d000c9408195030b41a858603016030180f440301319030004035003111801414016001680c1042000707004a0340d401d602180c45010500425445a080c40300009145422a04480e0f5140034980d00b00c488043c181805461043d05815080304a82441d42d00d89200410800d010b0480384041c000c0b201d9907103503808128011000340c001c0c90305840f0340c240000b1803085034041c0d05054856100300103419800c6003405d02c18141e8001510b1a01d5002600410006600041e0040c1301c0009151040c2c001600c00f004807480503044102420b40e10406400e04054645151000c04403003040d06c841d0092000c9009102c03050100b101d11280845061045044e112090307000324203050300c1241e402032403440843c030580c02c6a07400d8820440c9684840e002c0c0301040941c0c0125024100420f030f2048891a2518900703402d1001401499881502e51000003a00c0d11900c060750040e02c0c004041ea03441d9900d89469000030310501c10000362003002202618840c864442c11102445004003900c20141c0c210745680900e98 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 798631151 1250 798629901 798629929
    0x606210b0607020406090f18031704061b03060f060207080c1c0816110108060603071808010204170c0a030c0303050906090d03120e0304150e0d06050f0a060b0315 71
    0xc03008000c0c41d00113a54511504c4060620300c9000165000200521800c683d48a180818125002c85031100426001980b003182d900c98240481c0b07440e603551603c98013515400611103c00c40c028034012181e503406030000015900d51106242c81c1654a0074100d0b662010351180403124ac003d40c518001070b081c0003c5c01100c40c895040d030b459084455a4440c9040d0340903480d42c5400064800e503175820880420314810141c4001d1800c0e080c1030405100185280c81b001d8510700a001610045116190481c14090002d09110008545442d03541d48040c1e445018106044928010307500400c80e1482c040080c1c0d82540c0d00401c0f50243c1d241155020303500f6510ac40c0113140e02200c18802d9103401d41c1d448002c3c640d40340c4070744d85004100d030892880b2401e07568800c0c203401072138005000c24005122407803040ca8003210545068851125854049843c0390070304080900490300340802c001b611164090301c0da00603070000200300a2181d481d0000c02d4940029100c014480d45101a4143d503403400014403400d00b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 798632401 1250 798631151 798631159
    0x7021c0506281119051801020105010513020a020c130606020705120717030705013204151e02040821030121030201140103060f0f02090603070305040c1505030103060606210b 76
    0x4001d000304d41801c250140c0d401840042e000094507051141c2c41240c400c0e25210a0000348081d50601e800102412000c0700050b60159002c10802062842000014403c0d58003901c1442e01644030001e213409803200d8003484006d886031090000d0282020415081c0b9039114402800d43c8509100501c10200306146014003584000d10010000c02d00030b115a0700c2d2009043c0402502d00b00c03000544040c00350340030041c2200c03a219020840840d0700c800c100809111507540014200d94048413401310161100c0349210b44a101060100f8180310005017000c030b905625a104c03003030819203002c941481c802405860040c00c10f14200415480880002a075028400d0001161408007510031124002090340300760b51187d1241c00703c030202072880c4501c030b10f00840d10300f0070340c54107003404017007102840040c017400101b40d5a10001028024130341d0110000e006400701d14000030f00c40c190000c0040c0c00a00060b280346140040000e010760045031130112031804055000c40143e1038410880040620306003031508 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 798633651 1250 798632401 798632407
    0x120527101d0d0f05030c0615040b0d080a0306091505040e0609250b210604090b0420030a05011a01110a0f021f0302280504031707021c05062811 63
    0xa14140041e020f46d01c01c4c0c1c40100030910307040010f41c1c0803019079007805d8043d9282c0a132101b0700d07480320000d40000c21b800010207582c0e0601004c0450040006912076903440340b800c0c1c00e0002002c01d8160000c211201164280100d0010b20142511307600700f901c81000c10750203d80c3c42c800340411810302813011340742c00f4001c82c00301c0c1e9034011903409a4050b484140d141e00c92030f20174050310012501d145820090a40b4200b0001d803443da64120040d00240c000b820704034401c40f60f03031820328945003001a4104060152280c0051700c1c900203018104008200b0350940c10072100a007294801c0400c551203a00d6240108540205611a036282c07900305e003000c0e600b0103220390041d940c10745000c0346d80210307000507600181d440040c49103144c80401c0081c007005010900140c40d05600da441019581683d80060450b05071000841403081c0d00e205414000350000e000e40b111745000425980c0c4845614001c0017039800741c0c1e03182c04900340c2d401e800c2c1d0825900740032120b20080c00464107034403c401030f409410f00c41e4a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 798634901 1250 798633651 798633653
    0x5010b1b1207050c0306180d110a02040c110c04020313080d1103090d02190503040605030901140a05010323072102031b03150f04120527101d0d0f 64
    0x20709921408066509900407900c1c8109030904200040c6c1c000f417552056815031510180300c0c1d4503603d85034080c904201c01c04013100307283d071020f000198a117030b4010801c201c0c1c19052240540141c0725905c4041c070701d00508110300e0050a040c02144c0c850105103095051180c01c0741d461481c00e8211400c0ca10071b00765a0241c031052050290b00941c09251154018041c0d41e0302054002c0ca40b100c2c01407044482c2207286030000004000106482c15200c03141016622640c07100342c55401401c40010104041c100071040c80103000341b0381e000d103042e02e0003600304500b010000c1500d11004021b85100d4641c42e48403007010031000342c01440300240300c0912114039200700c0c01038000034503040400b000d000003050b101c400403065140402002800100c820101c81700d40c50b1050031050311010040010b02074a40c0750b946490305d43d00c610100e448502400315001c90050382c6400000354a0014100c280c080d031030300710505e40418092103070301103520740b11000929041004403d201040b982c0720401c4900c0440d1030b8881d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 798636151 1250 798634901 798634933
    0x105130f0302190b090f1603020d14010c0e0a14010819090b040b01062c06030c070b070306030501060602010b03070314150a0203040b161709030f041d010905010b1b 72
    0x80c2d80e0b805064a01241d0610032006401c0c0340d80134401000640c030450300040c821f00c1042d814400c40390100c4540c1e0404100707060501c0c1c0720000380d034080465440e100c480c443c90354102207500401181a920311881603284c4039102c510500302507803280400d01300320002d03590b0207000c804040030b5501140c001c11402c50541d10840307000ca040e202190032440240050100c2588003202c2000d04411055840c0001500083c601d09e0404486030580500340010004004422000c112601182d106680d1760302c80c50003210040080c0b00d6400119425401e200700021454814002e10341200070050141280a20716610100e1a034540d00313141246008040708841101d442c0984c0c18130400e1944009652454246481c50844000800c81c1041d211345000c0290040d40c007a000101c054034180034028240c0714080503a207103000b08800c1c94450403001401180d040c5850007038217400d030300d031000020160b40c0700c0c1085800e0300c90034040c45690317410501101d0384040c5280081d081b141810000d840001d080c184001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 798637401 1250 798636151 798636193
    0x180604150b03030d0e013206011e0809100203100506071b0303050409140c0406080a1b020c03120406050a0c111c02091b0901120e0f01140106020105130f0302 69
    0x601380c450381c55030918000c00f070a00801c8544643c54000e190441c42c0400100400200b01800003444160000024010b90091001c4a00000d00c0c540c250117200c0c552000a28141003210220700034058100042c40d814032034002e0364050408040e00c03454960502050007403075005943e050b14950300c00d588500b4150305092800340994042da648580e2141804858015074920070104040c0010320700401c5400036024083d00e041e1103091500c11600e0301c0c0d061000000d011142e00b501003203101c0b8445220b00350740000d20200f00c028140c4c01d403000040d26a03412021802035100d00e0021880400c2852042c85c8140e000300c0c0341034072600141d99645404804a01d002c81403240007010034000360070103000e5142082100754072401440217601e44200405148500f8083d00034158188020806070f00452140d0760018070460f044c02084076036096460300c909001e4001d030582940c980c3d10004c0003080991060107a10f214088424800b026014140d4505401c1c0342c9100040d411801000c103140c440000310192 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 798638651 1250 798637401 798637417
    0x210204020d0501051f0c03080a0207050d020615010206040c030308091c031d0316082b09020109050a14130e061f0909030914030102040302060706050f180604150b0303 73
    0x40301e604000920003000c41840502d404440800d04072400039900000b0000e0b081e0741417512340060303164402d14030080d01078180e0040c1140550040301440d5680050301c9449180c400c1624a1084448401643c40762008e0307a014110540b600303010b0020038000c40d0001c1e0003c840100b210568036000c00e072401c010034420034030000a40c035a440c02c00281e501e4204000180700701001345181c90107800c241c0c44100603008005003591400300b02c6450380d82c02e030700c000b1500c25500d10300ca0108a8480030300e000200741c1100200e0128001a401103060f041c50b155041c15218070b250384126000454007040981c6042c4500100d005440d02d002406d0904280501c0b4022078204644c65010542c0f00d01c0c100404816401c1003091501c1c00000d10080f80e4020440c404884040107840f4405141c40042800391085410180d0044400501101005600d501040c41914640c042810544952511220b902407000c0e000b9000d60000010401003421078407103c61903a0002070000d41e8000304400310381141c1190003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 798639901 1250 798638651 798638677
    0x120c040b06071202160b0c061614070308040c09060e010303082211040c05090d030507110a0e0108060106032c01150b04061106010605122d0402040e06040c21020402 72
    0x505042c2c01c1c16066818060440d1b4400c0a043c03079440100c0e150740e072400524209042850a40d640941c42c0a10101070004c0840d07060140c0d9902c450030040c2c8a4041030301c0c02c58000702001c00000301d25000c0e218030341c1510454a501c8070340e6441c40e101103c0011019206100c000180c038209906105074070b240c0300701c0034840c40b100d0b940e400000040100316503c41c02031106001081003100041e82c0c0c0d6000710f0b0101603050401548131515400c00021519050b941c07550050242100030402d54802004c0038100d0358040105d500030303a209c110413400d50300401280140c0480110081500c4803049403030030141d0103441d00002e900f801d0a10000a900c2142e400208040d80c00103040c03102d0f81d480a0f420341062070035401040b055140c550700078003038442d440845510015160204420324102c2d118a0180007031102c070b081c66504042c001d1884001c003650204d10131480c00e0811407000901184003489070f600b0040300c080b0a80307052041811440c46059400c40c88140c11403a20059485201809003280301030f0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 798641151 1250 798639901 798639913
    0x14090303180310050907151202040b1923160b07030213140a121401020f09040615120e010f110c0d0219150b0616020906120c040b06071202 61
    0x41d00341414043c008608202e400d051104014160307000080c2c1700d045900c222951a035182010f070085406e40d02d100403440303120740001000140082d1a001814029030700b0321500f89450105003041d01c4142900903a128a403440304844861701006001400340414514402100303c0c1d42641c0b0120454012038807540400c0d4081100f00300c1c4d0116081c4500030b0038804440010740c0c0508000a000314440748118240c4e04054800390040040002802c0350070096400299200c03010403403004031581140c0710b030728001c615080d8001249040440003002c101030b0b94071626a41602c0030f405a01401120f15a408190340361081607080b06814461101c1460719041c0d01602c400600c4c0485080003c0b05c0045021544103120301410024020b9040a03103540c01240d60728000384072028400506420800030b58040000b246118501e06c0c03032985140c80c60300c02c440602060341c0389010040e8242d420050210b003580301c103a95001c0360406920216507910000e2405041c6025607440c80f41c0d151500d25200d0040c1c01c08 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 798642401 1250 798641151 798641197
    0x224042d03180303020a0818030a0c030537140a1104050601090602030a180e010b1804020c070308030405160305030408060627070903050d0509011b05060714090303 72
    0x18042c02e4414154050182c580d451614000e550b4290b011010b0040e40d0001642a420705120000c05002580581600c9905295040c150005100341c801a1154012542145c3c900d184901100c42c02c0c1c1c240e190054015210080c0051103d015803c045500d459840e100f01c0d008a800c000f8040381034410240003180040e9801030200752000a01018140a200d450a100340b50b0044203440303005070603151160044240c1480c0f07030600b14656000408008082c0c1c00882e40c481010001c1595191090601090701a030905010072485004050072051b00201070500001d9880030040d50401c0c01101101d070a852602c2066a50100c03a900031a00c5a000017810031080d0030501c500380c0d000314100d0703120381c030340d0044500a11001c14500700e00d071200c0822000100410300540c00c40000e940c0187c00c0ba5400680c0e41000f5000340d20228800d40403442d1003107a00304032158440c1010509912102510241c2c403030010a885886040c07800b0000c00030140f2914000d500c7c100003400b41e901510144d0120404a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 798643651 1250 798642401 798642407
    0x241d01020f011b18050a061d060a03020304062a030f0b03010c030902030d0804020d080a0c060516020106050a080706050f071203050415050412081b030a0504120224042d03 75
    0x3640c10481189050138100969500c890340d440441c0d20310b0400204800b004408182c0d182e10840340e580e4441d0303000c42d400d44802c0d07240d4051803056106080c01c0102104010643c0418040c0c1280400c2c01740c0310b07184800140b4030170b4110311481e06401101040700b5040000082c00e42d441290701400090f914201507043d07190410156600c0341542c240f00600307042c140c010940c05451880c01500707031000068420041445100d0741880e280e00700714200a103082201e02c0d10f1900e046015180015030070080c0c04101441d25540060458212000030035013149080340c280e4058000c20414800030700c09000000218040c10038400c4468019540055540b405203402407021000360f4903003010a207880200000112155240f2069050a06154132941d541c500311140005a041c102c0b11202c0020042c0007000780541c010601507803003112120741e1018525412607640c074469007200c1c4426150001d40c00e24140d5001050741180c041d80140f190300c5c0e022840109400d0070111450448950f91124009140d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 798644901 1250 798643651 798643667
    0xe0f0d080f07051603050d140f0c0c0606040c0c0215030f0709140909012706060942032004060501090b1c06030c241d01020f011b 57
    0x80c046841c0145820100c100500c40d028020b45130344010716900c9941e05060084050302c00f80703040c0c090280602c0c0548008070340009010745601c1c0303480c0f03002c0010682c00c500715030554140c20300740ca00500d103030707034600c0d042102030143c402420050001904d20600540c0301d424070702c450b031a6000d100d182d480c1000c03056600c1c0010000d214104011003c00b00b44805060f800f140340c2071181c00c450542040d103850003000e00600310303140320601c030b031103440045443d240d05900004107031070140000300710595541b0112030540d6008080c0e014000d015001c2422145100406040c0d0380504107500c050803620400c040b443d48541d50401d44130107100d0306000da080640c0400c00c03000040300369024407907180b501c00041e0a2100c070380561150750b0b0b004112421984a18a14040300810b61001440756139524200210b20380181d01038041150941160b03810b00308403c14094164003000e1380c624421904210500086041001c2050b046002e075080700881c10034240500581c04c410500041c00091503034401500d403070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 798646151 1250 798644901 798644911
    0xb070f02010605280801020d060905011e030b040f122d0503160201020f0f031b03041e020f0a0603050105010f021203070e0604150804020901120c06030b01030e0f0d08 73
    0x603040401c14403654440e403c0d030380341c2130144111030501003088041c20040d8000a0b0064502d541c17000c540c210350303c4c0040e0486070440f030314a04d08101503620f8480324200d240003100c03a80354100700201d040001801d0080110f502034020000e040c03c2005965a16400880d05414040016041e1416410300c040100205152402d4028200c6008000300400340280c0401420000c15070001100300d014a4000c1d0101d5400c0b150740d07002d003941c9000b03034071402280f0f41040c6d40342d0020000081c031003503219070100c080f680101d411000b021140c1c021a03c034240e107108000b000320b0308034214210300c00316a220329681001606840d1004502c0d50f050000040c080b0350400c280004550051112500300010341c2e003102d800040d10304d04018144481c4020031402d20842c4e0101c0d0a90400260f401070a0381d00014003802103100322f52900c0071f42d0340d640502d003080380c550078054442c014020003080411300990000259600c18100400c6441034501c8241c140001c0c06900600d580041c8800c110740c0c0e5111140075408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 798647401 1250 798646151 798646153
    0x61103130308031008060405250b160b1602030f070c03140708060c0a0c11030316031d0402181311040609080c04020a0804080d14090a050f0607020c010302090f0a030b070f02 76
    0xc2c50140c4488e941c548070318044c00004100071468104403900c0c22804000b508a07000b209564045442900019602d40e210596000e44000017088602d50a141c10544c6580298019410a000d610402d105540070545c102d502072030404001000590420450900c98000406009400d10b4000c000c1e081c90002803030015205010807010060b9a046080e2084180e00b080c0c0f1040d112102d500483c2c03551003039041015204c00c0c201494010554000d0100c10040d10030112014242c90407410710090b405082d018a221144e004400109400c0460543d103502d403000001040d80e81d00303244078000650044e0001000071318101414050040200240c460200b02581c0031441d260107010010640301020300300404001e00040c0200e01d06170150000140d400d200481080541001c5000d41c3c1d0b00d941440d4101c0f0240665068115011400300d00d60303101d14115000b4181c034048080c0114029488609003562006805e19a904682c885040d080051032003a03080300080d040000e405405040008203500031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 798648651 1250 798647401 798647413
    0xc010e03090117090712051605030c0117060109051e090606070206091203130e0624030118110f0a11120403061e1401170105090304061103130308031008 67
    0x6664001c00d40c0ca0b041c1e50021100005840b69040b190030401d06620409540040e03419842c188000810628a146203108d421882c5503514000d144d201c41c0e000c1c00a50200e045c1030b2607007820f45c2d000d02544c3e48c0103105141407440c0e15114000070307402c0d0010b800d4030b05200d8040b80d0040030303a0400c1d03261039805ca00100c852a04100e00c0b0750000b61584101b800c454042c15018020b800d5074601001903403414803002102d0290300342c07102d00040100204407021031040c1c4840001404030b0303050b50381009040b5010005c8515580c01e0525213500c4440f076881002c40c680d6282d0710b00003400340c0000130340140780069100555890106100178000c1d0114170519126820002104402254040444e003c480c1e22840104146006a420141c40c80b444400d0503c82420064804d080745030bc022010f0680e101e03800307510000c0741e2400c189801c071181140d51020540c420070040c01f40354010912181062601402c6919080101c10041160001035008449076036000c4188441e2080c0c0b0030070540a09450001406 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 798649901 1250 798648651 798648667
    0x1f0f1d0a0603090807240c26062101020309010b0a0609091119030b0118030f0b1023030c1507030c0c0503150f09061317040e0406020c010e03 62
    0x162000c5621901052658540710401081820400e4401c01074110120055103000340416600d544000c00182240516050045062900400d0131020341134070310141410050f21240c45140b101005400140d0103907660300d0b203c1494200c10710b100040b9100800158a80c01c06002081c252510002d0081c400c075004e07081806aa1b40c80526441203516002c00450140d01c4640307440e480740300703812a2100c0722400c8a103190701c0c03640540015546200030707681c2c50000e8800040303035813100280d0300000740401d42c82c26a280104007101152608614800d10600d9025a640340d010000710741c0c6448001045494260340c1007902d01800b015640c0003050740c14100c084910801c0000038464014010140040a84014280446041a0005802c6c064121007000c140d00d083c001e00201c0454501140041001c0011041040814020f004404401307000c5c0040040f603a038000810036900140d10807200500c4001100000f03500b065008d80d01a0b0310060340d0703010f545c5642d8292400401582e500d60700400c4020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 798651151 1250 798649901 798649909
    0x100e0406060206091005070905060c030a0806011e0509120f07150c0c0501261e060301020a050a0c03020102090312040816080d0f03020702030115080706110a030507021f0f1d 76
    0x1805c40c1c59480000031640c0e1070712400c0c1c070024003940001d80c020034082080301c50700c04000010047c4500079158a04280d9503500110b480303000f80b500c00742d0703100074442c2011030060144010f0b00900c00e00514070404c40c01001b25a910300a00350180c00301650110303a00f003101c9043c02d1441d6009580d03910b0810750080058844248003001441200d042024050000e0310f04858025404681c84803442591100d00380304001d0340f9406049141d4006d05402e01c80861602e00c1d051080354a41c3c090f64503514104030200e0400c1e5184034004038283d056540803c5501801d641c140041d14124044011080d1120300f001040c41c034000d0704c00e0102810240d220418130001d5000030b01c0c10f50300040c83c5045a4020700c1c00c0c4c3c1c218068011701034000d403d5800c180036001010321880d800d0080d103181008032011565285411200e504203003078402500d40003c2568000700c0d100308014050140007504072000c80360100700000307442030007000e03240001d52400024007000d5440ae600c0d0f0300c0a490010b88450f001c0c0b00d03000003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 798652401 1250 798651151 798651163
    0xc171204140d060f02030601090b0405101b060204032301230a0603060f0219090605030402011b0506091005071103030c0d062303010b01090b07020f0a05100e040606020609 75
    0x40459554240c40e070400d6aa03048071480001e03a01400138070900e419a19180c0107500183e810b58040b0710340000109000d0041d00680d41110001414140f03014040c1906036269010b003980c0c1111504641c070030402140365030008000840c81200021a02da02d420000c0a1032941207244043c1a41404402112401c0c4508403040590500362241001e4641760080d0000b01190381c4000d24440c01c000714078516007460b03405044004840c0c0e0292010000e0798008a80c0b5101c02e002d080c021500c14804034002d54403c64480c10b01080310f144c1d0001301c9030181c45a1f89001e030101d45600350b99215101d40b00224a46000b407a402c00c0060400750b104c29201d07490b964480c0401011a20703441c40c00b00d41d41d00704c4009038000714010151080d040344036400850a02c03080c0e800440700c00740650700344446403040307512544070582101e90000340f51b42807021503420400718070711058200380c2c0000700450120700d560b2045a51303811200030303444401c414588170040c001652203d510803819500203c0c208007a000c400b140f8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 798653651 1250 798652401 798652409
    0x60806180601180f14040212010b0f09040f020a1101110409090213180506011401080703021c020a0509040b060909041203091b06080f070e010e0d0605040c171204 71
    0x8140c0003556108012030301000480383c0300c03811400d04100090001602240300e02a00c4c0003102e240b0801406030f09020503441000c1c015840c50042d50010002c0c840104d003d4040d9036070f05d503070451800c22002c00107420b440c094078005150603400074420504a4111803d88410f9921400130f121408051912500600031481420355043d00d070f00006045643d0840003040600b8601da00308543d05a2590429550ba00000100c543d0f21071140081801d0302031024103141e807881692400700c20756821004034080d40001f2400c90420000800b009030b0341a09002520075113185590302621220160304200590303611040ea06e02900c020404844161100c4405560080e00f00c2c1584e4500051000308a00030800c60030060460002100c000761b003168038414800c1241c0031566078030850784940c10084841101503900c04042440c10496100c954000c000c4001d076688001c24268241109888100035070f84112000c451040340040305004550720001d00d102c024000c40d004103984490229101600d02c03590203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 798654901 1250 798653651 798653689
    0x6040c1103041a07060203012d0f06050a0315150e0405040b06040e10050406020a0e180115052a0114010f0306050a0e010c0903060b010c15110c030a0c0302010501060806 74
    0x25043d00c010000110b440d001d600c91000c43d96580d40d80300030b000c030798020f90600650315a00d0f4101d0007542d0b00d1002d441c0940e520301c5440d040c0c8a15140e420340300c80c2d100c01c0010045c55100c0707200125440c121141c0070014001603401c04a4801c6400c0c0003040e12500b003906600c04d61600040c030000c02c000c507064660102040d103001820b601041d450390f203890340381d441e50703100e5a003007404120403c00250041c1c050f030076458031a840500a9082003040e00d03a5a00340a002ca2215040104501061484100c62440090800300d1402c1710700740380301060390b000d0703012008000288104c080c152032003445803601200803080c0d50411035042c18494041c1c0307a0340d4800605410f8868000c00c400b00c070b0a5012260a20401000f004650580100604030060754881501c01034a402c0851216500400b6510040d13980642c0314501c010700390200c0002080940ca112440d0181030048414808041005108042c0c07552140c410448040c40d0090959105030002b0040202c0304003440307103070f03211080e121a442c80071038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 798656151 1250 798654901 798654929
    0x2071a060d0f0302010b0f0405040f03030f1b05090907090501080403030e1906091407120209180d18050420090d0204020d0c020f01050c121506030f06040c110304 71
    0x10000d4400d1965000182c0680d84010001040640550000155103025248000580e10070740070001242d0007160081e00d607000084504000a08c00c4d80719104851715844002402859803200082b00c00034454880081440050040c00c1031400c160020b0380900c1d1303807620f0340849052100081c21a4809000101456114000800c8000007809280306204c0081c03040314480c81315042c07a1000d015004400d40b0b80c040200c0440000c0740010492038103540c00c19802d14852840e503400d02c030540c00c000308550744450032000b07400741400c410b02002e0110201da548034401ca40100306284510052a40228072940c41c0011200c00b05a50299043c2146184c5001588800b41d0f0004503038041503030305000394024400240030ba1240380b01c0d480200c072800344d54201c2d01d103030000201c410b080301c0013a2180e6225100c2407104074400500d0301100c0307500020394880a402145240d0100304d00d6001652460a00240c110401106003018032a1350034401d200d180a00c0520088840d5580300d10540c080d0210030750400b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 798657401 1250 798656151 798656161
    0x4140a031205280e010e01020106050a170c0d030c03110c031c051306030e011113090b1f030603060e061311190b040807120b0a1805250902071a 63
    0x11100c10312400e0001910150f102034840d005000a010880c8640406c001050b001c1b03041d44144103030740070381d40c2c06030080311202c2c20318164000a0b4404049200c0e103101e2000c04030071644684000c02c0c8060710981720036000d201c0174900a4041245004080c016070b000169640c01a500011130f680400281001101920700300d44045a051080e032102c1c4510000f014800200241c1c164042d070307441d416410003040001e5151303082120f0b038451020b26801480d01d6003000d00c040183c55003c0002003c0c028403400f49500800c0e00102ca1641d04100d002c00300707039902c0c010402e02604c0d008151080c0244c00c090480c1c0c0c41c001c0a0403094045c2c05034003a0155800408c400f52688581c0705001c2e04500907061101c22a03030302c43c05103580f40d02c14010511035004540c40040c0e00800d01d8001c01c24154000070114290b540c40783d80b100200141300c48040f00301c0318080010042003040c04105101032002000441103406803140c1c0c40ca25403d40d021120582c41044034002095402c030404040d40000c0710101056110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 798658651 1250 798657401 798657427
    0x142803080310120308040b070f05030c13030b191a03031204051617070b09061801090506192a02010e0a0e0906010807060507020f19170304140a031205 66
    0x80d004000c0b50703443d0041c0841450b400441c2c840c4290721900c00d0013078542c2c8400b0101c0b099500070b1540e82c0401e8007070000c5161441301101502c08100c40e603003681c248941d6a25070b040a900706440b0a40384400042c00307415003400a001c3c01e030941e4043c10000140085a4020a03641e128034a0403010382c1c0c0c0060003080800000380007070b0b154055500030038042a41c403000c050611072811250071405100c1c400300043d0031040601902e40ba0003000741441c6c204010035150420302d022090352141001144200400d11b0b80d100701c05400c00c49085002032030003030402c01c40070f0000d03030941b090340046e8502034142100700402050300c000c140341d081c81c08022440541c00400d1541c007854110300d40c0482c4840c01c20840c140c0c005441ca042710150022940c10342e941b004103030303424814600041e4128900d00540031403820403030115824011003c094ac12810395a150f0020384804503004005503420000d410002880404880046180201c030001e600c40e2665841e10a0000c40784840414450003049490560b1382e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 798659901 1250 798658651 798658681
    0x3030c0201120f020f09030106091a01080403210209090603010b0a050d050106030b040503191e050f070c080c100e0321070803010e010302150a021f0f061428030803 72
    0x4103e0107544a4104030001c44103a040100d81c14020b40ca4981c002500d170f482401100320900c1c224840e00303942d02407080111050308000b0019014485042d8020407000000c0c0340c05041491000c0340142c85110300f40c2044001007024000c1c902c02e03814013800d6a000e40e54801245c00311482110f641003a84010701e0070501400641c0c0c005440018503008204c14003802000401802e01c40101c6082c4922030309100351819508a444020221920144c80104500410040035011014000300d4144050f03961b507039400302c100e0f820407030407500072040e048840d0030b00c00c4000c40c401c1400e0400c10141c106c4c0b0004aa62024001e001074440a50100400e5450182c00212811103800c403151623620341c0c46000e0352155800c00c0c84100c0c000c5a242030300002d103070780c20800e580c6040c886034042d04c9200307040c02030720a40350401d2010110307041d940d030340c85109003170346101d010024401020300c058824a100e0402c20740413410400680003c0045c0491402da44070800c051b42900e9014038901d407240c03105c2c1c2800040034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 798661151 1250 798659901 798659921
    0x2a0a0204050a0e1e03270603090109052e09020a030b0a0b01120912030506030705030312090c0a0b04121e0305030f24211504030e0301050103030c020112 67
    0x149410709008000080350002c146207040300045660241600800d2498907000d498050740c1500103000d03a400c2c0e0008062071100e926480d8011803050079004001503083c2d4429103034810319070354615150040040c240010f0310301821210140c440c034400e002070280213030030802264107080e544000f40300465868040b0040910782003003840d507881ca441d0400d40000c02200301c04501140f041d210003101c0007028014203498a60000540010205a00c0c0c181c1c041c0070060b00c0d0a5040c0030b84074001c00c03e5103040020301443c0050401044007030801903407460034252001511800340d810306806000410f40782c4104c0d4103d0303541a070210884134031360809400054560402d4845444a00d00c55828168400c000d903000b0305850100c10110307141e007080c54100c0c01650495403900000f4401a100ca40340c805411500245040c240c03003040d04a00001c2c80c1000c819491320141d00415200b84014140c0c020f07004100040300740d00800c1194190749014007104c100c0b4100a04104245208030710641c4030340c112626031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 798662401 1250 798661151 798661159
    0x20607061b051b190f0215160c0e0615130b0a0801090f0e07090c02011404050a050f070b030a0209040b0a0e0a11161403041505040f08032a0a02 63
    0x621824540244180c0c030035140700707000f88003118004200c000042454132100241000314410200c02c0c0d5106000800200402d0341d0044201c0d950800c40c0084c54003c1070343d0b9074641c103181c10011440c5040e4043e90507030f4001188ac804d403c0b0030440c058542201c030060400c81d1480341e0b80c440603000444501a103081d004414001804541e80c404d858112844906889009906000346800341600f20215248800b00001d42c1d80b00150030481c00c00c50398840368981d8154400400c408a84101c0c0050b800c1c0d0544044a0740d0307008480b1401804003e100e1042e0401d003c4019028a6141480741155800080d011000140d40001c9200707559a60754010000e0541c05848050300032780e03e4a44802e401d000301d41f08000181003d2000c201044898101c0d20082005449003007040615100e20790040070300d1011041900c000c1101150001c00200901c1d814515070303481a1340d450402400100d42c400305e51010905030b1003800f1500c000b401210000d10034511a90030440480304481059203044000d4030b0207900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 798663651 1250 798662401 798662441
    0x2031c09030311030715050c04030206040315050603030c030405221b031a0d08090406050a24110606150415030e0714010f1103090a1805070e0d02060706 67
    0x10280d04240ca100440e070283d190380700c0c0107011101e07080d140e2240480040c0040422503000c101103069900280d000004080c1032030a040c0c59034041007055210390810360780040c0c60000130458010724024507030b0003542600603609001034180b02c15a64000c0d0300559101d00c2c084070403101d144042010980d40d07841e01140902601e004d500044441c40d440319030040003c5d04100c81307100c120445140c1c11120745401382802d200341c0d040c0c3d21009025000102d01c2540551185000142ca07943c0f0340c1280f018000614220603204102c914106460f90310410f40028002549501020000c1c0828860342c0054244c3d03c84014445812190b615849143c105551088031044100c4103207074158003070100203004004980c1455110301c030540c0ca03140c48014060011307036500c485104c405d210b8009190146004000c42c0e003030010700800134800c010aa0040d5142c030980d220400e0031100a07008854001e00c43c0e09042c030001c8500c9002c40d402814914029006904c0000e01c0c2c01007002651280300001c8035082d000311 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 798664901 1250 798663651 798663703
    0xf01020d1505210c04230105060306031b0d080712030606080105060304030f120216020909030f160302070e0103060c0813020609120a050a0f1a06060d09140601170f07050d0b040203 79
    0x1440030030821181307418801d9000042501e003052012a401580001c00030101c500de8207080b0803500140142950b041024000a00b00040068002e0038485201e05000443c0d081c04100041c00ca580d9544800308010402004105e152500421240c1082e01860003101103600c240c01601ca0405014804044920003c0c01003500680d413006400282c4c0b084601d81007588802d000d490f0780303018031000310401800070841004408031180d000e00e01944030780103982101d56036840c1440d4054007640166a103075203540f4048500f60340141c4682c0d00c0341c8558400c01d80000e00da00442c00500a000b03000e4000c00a4080c1442c500d601040300001c0540d002c0101c03260120b091030038290740d01070803104560790305208030895150749a02d0503240c403415000d0003030303130800c1a00854103010b0881090151140021520b4101c001d04080c40034134080d09010600c0301c00c218415a15138945030196141c1c880d1034020034410b10440e694050f00440080e040025202d142d20750303000103030401c000c4801c000034040b10b07650001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 798666151 1250 798664901 798664931
    0xc0607060207110a081b0f0a0e090a06090614070f0e091e04080a031503050a02090402060d0212010602100207030e040f1413020414090a120509030f01020d1505210c04 73
    0x1a903030118000c0c58001716000100380504c0780f06207e0800e03800a881c52081c054002030221082c1d003c02414110b45110040da211003080350b00c0c0c458203845445d114446044403416544907507401c10800d181012a400b41c283d4001c0049400f80c039458440c8481001081100702030800d002e81c04120000c58484500341441d04a070b89030703c007401040109041c854020003a03072080c0660411240c00001405220300c03240d08000650000400880e0310080500401c0c421403000e101500c1500c820f01d0651420307505009010b46080010080c0c00040b078010016000001d80c003d90340d8800704810750f40428648100500b480c0275003001495080004100020040d50303400440c00088464025a400c01207408422514100c4400c100d511144035031102c01c01c0c600061740102c502100011f5413824606110381c2c0f00000e400e0580c00752945090740e401098103002d40c1c2d240e110b112480d03d000c2c0c844003076aa1408011170313074010940c0202080d4031141c501d41c4410140610030b0f0304403004000d00801200000d0f21142c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 798667401 1250 798666151 798666163
    0xd0f0311040f0f050f031c210b090a061a0903010f14150307030b061c050d0c02090a0e0c01142a0f0a0203121303080412050f0c0607060207110a08 64
    0x503620740383c841c150002c4c041c107001032641c0031280080d000d45040031208042502034620540039000b003080300041520509a01c49810f4840d01c00311102041e40084281001044c88000c0d000a828925220003001200011403144121840d444075003621141d0010000b0b00406880352410b80c0076042c01c0e841c1d2005040209032501c80c42d40c10b0443d036200c0c241501031550741e0403540002050700311404049801440c1101c400700700b0b00d0400018038142c0515503109420301c0c481c2d02070040440c040c0810f190031441c04c11011503025482d84006c00001e002d07a43e04c241e907442c0c14203500c1c0c103019901e00b95141c0054440304650303d90b44080480701c0600d212195600907131a1034030801040d401480c0f8680401c0c400032441400e5690006c0050045248020100d80503903c410a00c0d24482030100b0000000f804031800b5000400002c802118040c1a50400a04002954552039041d400c070038440f1015a0b5110280d4000c5600404016114001841e012817054040034413680d01001d4590002511b403000074031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 798668651 1250 798667401 798667409
    0x150b01091a0703050702061c0509010b0d021c080d110307030e011b08061804080c0c010f1205041406090c040e0102071509020402070803070804020915030d0f0311040f 73
    0x103050445550324203400081003041034401010000300010000300c0e21407409002960300062855160160411180444020f0040404485520380040043c964000e2060307030b641ca181502d515015082c03550000700c0ca09a400140c000003400300584030240040302d001c0d03c208902c401402c1002d54010700b0100c00c00e8000301c40000000e42045045503c42c201800b642c0e8010311145901d036650b01c030204058403d507030300030300964200006504000005e104400018082c078016002c280d07031800d81015481c1458000b90f441814020b884100d81d042543c88020280010174200001600c1e849070701d8040c1401c80c126464800b90b120312028070580540100d440a0301e20320441c0c040041c00000c0c1415802d074000d5260281c02c0815250202d00c03001543c2c0c100c50012440280f0051402041d030703130741c5e64040d00180c4481c80012514410001141424420203800121010001c1031300002c40d4006941d40d6091001442001001441d0304500c42c069084081e035168820303c40b949039520340203041c0e030b1301f0b0092103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 798669901 1250 798668651 798668657
    0x4060203182b0c03050909040510020703210e10050405011803080603010c08060a170f01060b03090c0105040e041b0810021c09120507030212040b0306090a0b1003090f150b01 76
    0x1201d50300260241d04a804155415200c003420701b2840410448991001882680c3d240102480c2c00c0c0c1070700c4213200814600e4400c6d01d07000000b9140c0400700c03032048074141c000c00c9850b20f4260000e480c1e980008400c000d8040e81900841c3c03541ea180391281c0509401c0c0002e0355642900e410000c00c142e00310700c0551281c842503000b001f03200c581510858036500180e0b90703030750401e0121605011b445004100002d1090200044035400d00d40366210b5400c60300644d00201c2154004070910200d02e000340302000c0f1341042440d202e0f003440d08049004101c003101400080440c80118022103000b80e508283e200142400010b440003c0d080e00100f0000e50700114122014100362070320400700c20594401c102c0065000815a199030340413600556007a802101c0503401d5200d800c103041c0040024000410103004000b0000e038403410641309200c03103d0406042c0c08401820080701c41c03500c0c5c9403001014104419443d000c582c0109c142401400c0039010a40504400c050842e904a03248c1c06810112a00034213907 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 798671151 1250 798669901 798669973
    0xa05010509091c0e041508070302031606080112020f04060e0a0605031603030503071b150c05030f0609070c1704060e010f0c110604090c1d06120406020318 68
    0xa04064a4030064080c0e0b1609110200603d19414072a8110144425010300009515502000d02c0041418945e00000c1150701c80348042c000c5040501168141074110982290755901b0041d0140020310140140780305d030350084482106558444942e00c00c1c607040908100025074842508404122046070b2910f9801d041070350000b614240080c0b4070441000b100c0026010700d040d903604684561018103500e013003106841203c040e0109030140383c0c06880c45400c0b5241840440c401400685100c00044400c0c440240f0802100c0603004a0755548044111410140750350b4100080d1403840a001024140c107045080c0d041e0b000030500300420559215444003403100e80760400440d00c1181c40f200304030003e980c80d06110002641010948100b44005041d1401c003a22085004c044407a1003003218001500e1003880d444110552170740c0720340c015054610502e0b2400000c02c1801c14440a400180226400000a42514421170050340c03540506c006076021400c0c004000c1524900c118403a2403e0130b140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 798672401 1250 798671151 798671161
    0x1819170a1b05061210080634050a0e01092c091c030f090b070c0b0105030c0315060d020405040c0e16080a09030207030507090614060f070818090a05010509 68
    0x1c812440448100420035441c0c1002c42d80c0040e001d220142c480c030385400d2441c10101d050403090040714411405107240161050b1248010045009043d101d106507044980700414995413000444840c1041070a1251a05021030b004031216510f035481030240349118400740d040310b12100a44201c0d11001c288004198407000c00240e250340d6001000040303010115480c0325002d01942210304503038400e0f03a0010b8081704646416000000c12202034000482d00050482080005240c09016080035001401d8254034000840c1e07554444003000c0d000211858005200d0740c0c0e5190780114000c0d4058418403c0741080d14112900050718000d600e074035001407000442d900c044407980c9000700056a01c8070080c4d1141314040c402450a40380940c21401408004008100c08116100c010044030b4800034501c1d1820034580304a08410110512540c010090360401032040c00644d0400ba8100102c50358421240c9050100b0f44ca982e070b01550460031910400400e0800b41d4419812101c05443c20041940d030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 798673651 1250 798672401 798672443
    0x5221a130e0606240a17072a06112d0702091311030105041101140415050901110d0201090218132006040909050f031819170a 55
    0x20303407190201c45034400c00003e1080e04c0d190049250700398030369074000c0000c00c9007940c0448a900400600c0085105146100d16840e603841d1030590004040c5000e0894090400c44012103403d000c0299008904150748402449120303840354035640d1710250850707a00c02100070816455608004c00400c0c0c55070703108106902003001403c450b03000340e00070700d114040d84d01c4489858219000550649e080c416854180348079403424803030390740224012001c110751640100300040101000e034120015040c802e103c10402401d461858080a03991800c00355252030154004840c504c0d02150706204502c60021071000b15901944524400b034020358404255401e1411110080c41c0c0c150741040382cbe1222aa00c10000c40d580c1446049000a0713292480554418240024600d41164000006031940c42c080a010000c0801c02c9405070111500594240082c1c1e85d1429044541c00003501e0080185502410801001100880c0038201212803c014905061000f030340d1061081001c03103d45080d00b90040074550 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 798674901 1250 798673651 798673661
    0x412020f0604150902030d1112040302131d0604030908060f0601020c012a1401181a0c1b0d0e060c030a0309020a15020318010305010f05221a13 63
    0x4110014051a1920343e1118041450062007840d4681e5464a40d40184e0302841905582c0809030343c0e810b40341c04c074030f45003a090400c10500c036011204108810401a100c00c0040e00c2d41081c41c0d080002c60b201030740000e5000b200c0f150074480352030140000300410181c114111200b81c2e550072080354020390b24004000060141941c12601691060070720204961054101061000c0402000c40c41d094070b5880100002d4401d0300201c1c1c4002c152900003440400034419922400d4130800346490319103143d00d039601ca00202604c031401150040300001d803005061030403074060b07602d00b0350b10340c40d198040140a600e03043c10640b002c000408071410718407a864200c1c20340315a48000c0024624050b01c0c24002c0e0001c001c0e03102d04a03042110008001803120101e050142040c807290040c554807488405200d60307400c03001c1c0d2541d041c1032070b1000500214030707400c45104c281c1e00141d95105250310914503940e1138094080c2c18400481c00c00d007803100031035241140c0b090f4181c1d05442c6103502118210440d01515 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 798676151 1250 798674901 798674923
    0x30c100504081b070b1303140303010e04020607080412080721050a1d06210c030103050307120e121b030604080d09021306060c0c05031504080901020c090f041202 71
    0x82c2d02031088018880702c043c115011001840300303c46100b59507110030045a006480e0451586408120805c14000d41c00030a80000810704017039481c5605094030600c4807000648064002c8001040420400404a085501411080341948039480030340c03400618581c8034a2003100c0c4400c3c5a41c12007400508914641c580c10074a440d010305050904008503101280403c3c0076403440c4405a046c840c1e074032420014441e42802d100360050181048201404d03602c0082c143c864125010030040012490200c01d5038000c640c04000c240f5075020392001100c0049202d80740d540c0c0b04014041c180005000054580407113114419098804180d200c01c26031124000c403006010b50b23804020314440d0700d100ba4407000340148028007101c035800038280e8503800c0300c080340c03c44c000bc10360136582c440034840da042c8104000c243c11001040320003000007020342c201a000d40010002600450051100d80c001d1280c41040c8070b000d0650601440e000c9080c00060809640030341e8001203a125007120b080c07001c00c80300c0042c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 798677401 1250 798676151 798676163
    0x3090606040e010b09270a0f38012108041514040e0a05060d0f020427061407020109020d0b1f0e09070501260411030708030c100504 58
    0x540d56000a01c005005007020720b042c0d81d580d51041d00600d0ba07920304440d0140700c1500003296102800808140d410003006213007040e581c0410301c1c3e80000f9200007600c2112aa0100003e800383ca11100381c50070711601e80c01040e00d5400c01c1c0740c1941081415451080c100c95803e8400d000554445805401d07405407071030040c00625082106120118840d000000d26240e545400c4400e901541e81000c107075041608409003446880b014001c1201080c080c0c6034201130119440d100c3e0284a0303550341a540309003a80203025903150b0101c01000c418286440710303030307442c040110304001b1034601c0d2403002400c840300c62154542c618004159070301e00c148100c41880d94081d00c034046104103620340b905094401008040741c590030b050b150b0b00c0c0008031034032400184805418055141050f544190410380389400450401070f00c0c050b101c05140013040d008007113940742c40e6810f0301c685941c02c1c001c5410352000b14064040c801c4010001b41400d0000003000649890800d0b54460720a0406500030360398162005005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 798678651 1250 798677401 798677413
    0xf09070b074101051b0d110403140f010c050306010f0806032b180f0611030f070c2d21020d030203130b040e06060f07060c0906030e030c1908040f0e1602030309 70
    0xc402d40d99107c1e000040c13a0702c02c0710b414250340369120714815030002c14610052b000313903c0c1d400c40c14034240544420318020b41480740c114941080000e000b8000d03100010200026000071400c1510284001a0a0211060743c03030301c8000c1c01c030400c0001120710310600d000101c12a400c0c4c00203008503000325080e101350200c85054075152903401c448225165820f0205404204950760000801400421400b0b11a84010340a10b00d040d4038203400d404200d1503000102001e55442c0d000e51810070b034500c25141c14518160f400c0c45883c40304840e80002800081d00318131007030803583c1856000405800071580076035408500305c2c0c9801914050340101c3c070541007105c84007030200380f0320300e01180901b01c5282c4a00000e81083c0042e240c600039200c001242001080c04030809110343e0341c0c1401680e0042c480b200042d85410058484103680d40d240501060141200031515010041b00c6001c80e00188148445041c140e502c521902102d26810354808522a514010407a29940080b06492080c00401c3c00740c4a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 798679901 1250 798678651 798678667
    0x100e15032a040b2b06030c1e0524120105041107170307030b0d261e0c16170c04060308090925080f09070b074101051b 52
    0x100754011001d00141e4100348130030440762011607a00340080b00340108022605900e541070203131048150350440c0c0104580714200340500301c40ca0250030121482075960124240064112000c542c00420a846040b00300040351500000011340803810780c0c008a40410008901c0d00920000380308010009010303401d12070300c0198110744c1d50043e680c08002030401048280e400d000040920341080800c4403046400040000c0005094010320303441c0c1985180076103080c2c424080d44017100491a802e40445000240c01145c0f040b0510000314945404c0c04141600345e03c841c140d130403442070048100c88a00c80d64107508414501030180c10100d07a04031107101c2c41d19802009205105a000340302400840e500c080c0742c0e80c0b02c004036180e0009201d4607900c41d900d030f00341104811560381c400b400c1c510f225400711000b44441350501040701d900e590700c0300f90310440c000004900744810241202201e6003250000044d02102c0014013030f0304506004400800c05943c45401e50405c0c03001052a0490718501484412 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 798681151 1250 798679901 798679919
    0x504051c060b010519080603070515030702210d021e03070f080a140c160b0705040611010b0906061b1509011b0807050a0e031b0a09060302010e100e15032a04 69
    0x40d41047d800340642e820b29417504d021030101242e580d103510005100104000480e6818482d00500c01261b01c00c0040c20041403840100b28004c001c000b80855600161840750500100484007814241c0d24130103131a403030180030203044880a1300705240444e0b01d02001407071401c0303e071096a50003d10070445040c540c803940e02100503900b141c82c0c0140d00d000f8520101c0003199032040d41c2032040040740c0da980d656505200e002001d0403901c0f5520307407040e8182400300e0015686c21504542c0a0415142d654461100c009032842c0031104a569280500a0401104600d01c2e070b04801440307404c08000170f00490000c032034941044c05000760504001468240481d48551180000306501c015901e401068070110000003405c0580e000201e60503403440059004250030200500740003408103950800c41d162954001a00c1c07800120a41c500c90310f1100c020403a954060b80c0064032164002d8110212294420121305680e4016079100b000750f90621103401c00792540140c48602040340a60042c01c0030714040c0c0300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 798682401 1250 798681151 798681167
    0x601030f02010c05010f060602070503030f03040305030709030b162a14070801021204030311070c06081914061c032c0d030203090a0e01050d11010504051c060b010519 73
    0x120304103d000ca4038607011803030034043e03100c0c0541908800a001c0d07152070000392500d0003660101c3e0207074100b4082104a07120300401c0d00d0344540c250410907601d540c0d000c02140c44043d650070040442904c4002d00106100207407103140807040c907484111000703c031040c1c40540da18800448100480000840700e00165022001202c2a01c21034122694951211005401e980006101c0078807500c0c0703402008141a894081d401030190000728a510301020390300c802c0340441d0103000d408103002c503050209030801510420502d0000d4480d0041289004040c03000c0900741054031558480d001800c0c3c0389203003002008014101e035525407074208110509840c400c5019510200307468400c0300c80340b0700c0d122130784904414048251081d400b03503030b4501804c1c0c100b25940c2c070741340c000600100c000401130000b6150101e00c1c52030355402100e81024105072070b00489080c450b03500702d05d801c40c004405144002446d9080c20001038031601081c48040400da00440e02c5010b40c0100c83e4910103940800112a4007500b00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 798683651 1250 798682401 798682403
    0x11b050d12180b150d05030f07170703050a1403090709050903041a070b0a0b01050a031509020f0d06090c020c06160c1d0f04021011010b130b03120c0601030f 69
    0x1000c581d00d100741c12024032030300d0460403d582e452031082c20400c110380001a144100354084034140a03d900c0364071056524040c00400c400382c400f0005921081c4810300c40e084914101c02c0f4000c035994030740d5140c001c0254200c813080b500801c1181c1c1002c1c1580709001d0640c0e101e99800c0780209151490544000042c1001908407100c3c2d000400c400703c2d0b004142c5140c0480109151040c640d103c40d107241401d000040100642800e81c6440442d0381d90307270b0388442144d05600d01440c1c04038402141e0800c00341d000d2490307409448090b02c0041c034500c0300700341174018110422030754804104080d55898038000307844031341840030010f82015140d40503914008019051020490300c41044440d425a625034003402c6503000a8609520403410340c140c501520080c0381e2080d03480e61210031600382503010443e08003240c0c2e003820034010b4442c0061140310096214403081200140525121003100400303000400114010394000e001d06001d41031030f12082002c840700381803203c00030308482c8c0c40c41c0c492429100c48170030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 798684901 1250 798683651 798683687
    0xe010603032c1c0317070c0803190507020601051503060603040b0910020d020711041505060d1e0b01080f0705040b090d02060d0b100c020a090b0d02060a030605011b050d 74
    0x41800025112944400b02260040f032004061907020f060192400643c3c2d55a04003083c8410104510254061000519107034420809922520340d401d80c54641c0c011441e036480981c0c60a41013003011917001809074100c0d501500c01d03a10501c481d10700c1614901c42184c0281e041740e0704101040c000741200042541c009490300a0b914440d0060391014142e0388a40346441c031390f5401051744401d12283c0001a007081200701d41c104404510440380340b401d82c009101d0944503c4012624850311640758000a0420440645054420002502a134020003200002c203001130007800c0004c140008421046000307141c940c440c282050701c1c004600b016a07001c003003005d40141045130a84010389500340070346040c041c0d100c00030502003088424040c1c004020140901000092040b81c40540c50b1404424244d03480d401012505a40325404103114444c40da100030f4005400183d5010360380d5040d400b2605031102669002d100c1c0d9129507034011409040000640250403202441c110b860240308140c3d00401640 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 798686151 1250 798684901 798684977
    0x10c02030a0c1a04080a110f040c090315050c16020102160303120c140706090606270e010b180a0b150703110a0308010e04080708030c0903010e01060303 67
    0x1601180c10a414000e04642c0c1c14107210060007400742000400301500751500480f0308080c94142c195603144011040a04a828000ca00740761540b03400500b0540058003520a201111041800401c021f81d1840280c070b850501c031041d040000303142c0c002e490080420441c03d90030501041c000725002c00110501324150b100e154000554842d10100441c02035000b0b4541c80c403001e559056040c1038441801070304013008104002e802c040150a003c1e50384046c0c001000240100d200d10341400107200039000610000040420010504022062041d01440c0b1003000c2c880c80104410302d5083e1403128007007a84c451851140c1c0550100328a284980c1720242c0d000203d407034840d11000c510b4043d24448904015400026149c0a0541100305402404a601300030043c0851a4400405075001801038040e0341e4101c2001c1001d0140c400f05890071160401011a0340b400e000c900c1c6145a80200440c0e4003a50030040c02d46800e6a0620482044036059110f45507409088242c072030b00d44404090384100c150b1a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 798687401 1250 798686151 798686153
    0x412120201090b0c041d0420040b0901090b031e06280504060e07080703170a0c060c02070e162106081902040b0901120f06020f120f060d110d02010c 65
    0x41007030203000c3c0d009800b4082c0d03106d0515140c07111000c0100ca00c0051010b030041171100149400200c0201c0700c1c0d603240600318040074400010007a0200c012115413000042e400840c1c6101103600c426208c00045088502500926415001d801c612944880141e041800001e09403032404403501c00741d40aa14800c4d91001c245003010b011600c3c260b0741901c40700d030303180036844181c0d0080006d403000d086143c000340640e0f860b55442400340d00c3c0217a4102c012001c00700b542a9810301510000a40c10380c880e405010b00402c4102c000e41d01d42081c49000048240b05000c9594082c4001d0070040b9a0b1a582e94140800110200801e20308201e601c0000508d68404002a0086042c070201c040950300c00c241d80c1c2402c030789004000c1a0b0f0629074103c0d1003000450700421100c0c07201c0b0003000c440341e4440c844914000b002c3c14040024006c92503905000d0b2000039110a06039402c0c0768261080701c104055a5241e201c00c820b01400549010700142284038900f003421407031426000c0000c80910514107901d00e41d8003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 798688651 1250 798687401 798687413
    0xb031b0418030e060702270405210702150403020a0e06030d050406201608011d030423060f04030503030402031b060d15240e0d2012010203010803040e0c041212020109 73
    0x5c1481c2d007c0740030b000303c148001c0000502000e2401890100c0c03180219064500300b500c1480348500081c400d03840703015002c42040c89281030340c0081d600140521003285c1d5031003a503207840c00100c8900d48240109084154400d0056054400303880696560814151915000100741045e5082444e00c0744202034042040c00003a046c494080e0519500104a1607502c071103030150b4441e01d20702740c00540c0003800140007804000007031410603009501c8800c130840c0303c0d40101d00b0900c0b80304128248204002808400d1080010040d03000d0752080e011104e000c50001c40403200c0740b094204080c3e21142c1041049080c400345d8110311101038544450410859441c40d071402c19059a0910609019200d556100341d641c005240001c8541c054038800104010303940c40017100c000e810207010000020080502084e1a004070101031148484000c545ea235850b56025562a0454869110400d480e40c002030182c01c1c140040d10700300c1c1c0c9109942401044a5551885100c440380d400104644d82c2d00c11000c08104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 798689901 1250 798688651 798688699
    0x30b0a0806090a030914030619020c01090804060e0d0b150a05030d0e1807080a050703022a01060b0f03070c0212010501060c230c130b031b0418030e060702 68
    0x8002c0d00500e0000c04502d00908400c0c8590f202c2400100605d4141c401c549020801a50281e23003403141c01890712031a140c1c4402402681f003e62920741c030300501d07041045414001042501e88030385540c0400c001da03004104060944603001410400010b0100341c039404410b004020100000f401d080c0500e4442020915000d10043d4480020700380c095250b504c0d0524001c803401226405412800500d00084003804440c0c4c080c100480c0540d64100003480c40c3d219605482c407968499500c410703000c3c0802d00e00344458410b03803229080c6500c5c1c10000612030f0366010807101c007000084402825596401010307206824103200503030b0040c03411200403464003020701c2528045c1000d91100d002e4400a402d1501c012101101c0000790034a1000c01108214400510703031500500c12100a400d0781810684138020302440000150588a903541350090784007030001540d900401039401308100c0d012052440e02407410050040e000c256070012078542801c0c9000103203002c0740040c21100c46481c4180080d80e4140d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 798691151 1250 798689901 798689911
    0xa02040c030e101b1103090904030c0b19060b070c050906010c150504051b0607121b0c171606030507030b0a0305030307080603070515030a2007170a080106030b0a0806 73
    0x44e80d990004250520b50310282500b12810318004500c04d0700020255520b01c40c0b103000c103124070701c003400040406200e4403201308400e500c2443c28a00d0306001180e0900706201c422400710b202d00300742022a4041d56601501d182c00c0c1c00c0003408001501e8001480104000603008504010f5a29401c0c008542d04514440240c1351540d400240c83c60641042801e041091000d6400702d4005d05280c40c00769112070075900070540180c0c20300103001200d00140d50700111980c3c81d0710124041004c03071050000e6400314604565984928050048003082816290080110304054007a982c03902405814480d0788110340c05002402c000500c800801e000910100e0030380c2c0102ca80758030000800012644c0600c00d01d401007416002841414140000640c46000603e001c0c3d02c040b01c044005801d9261135080722410034213225110700c00400c0310f6808172059019003030503a200c0c4283c9a520301014006411244954056035880303040780d003402022005040b10401d400c2e40310720f00b4280801c9400d07041c42030501503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 798692401 1250 798691151 798691183
    0xe03150610140c030310080601060c170306040902030d020a05010b0a03020619050d0212010510080103081608070605071112120601030f020d0e07090f0b1503130b01270e0a02040c030e 80
    0xb0b40b4011f0858a4000160030000800020070f58000024203100000395844002e518040e40f6070740c4120209008181c40c02002c0d506d8880d00c4038100c990303074011070f00603038041c0204000d21100e010303502030101034002d51200030341024003000b00002d010103444040600d002c40303251131498084460a00c1c1c00380d8004c828040f01080d02080104094680920050f4481d442414003d920350700d1510380326200d000c1c8080080d5280d41d8110a601004842c5e4110342e807035988000d040105041101d0002c2003400c10f120390320020712030700c41c42c0c1d20005459030540700c085402d00306911550b5100001140a84078810704103807200d40034824444039080030301909240002d0880102a0700f0701e8004560107035000d90210303203041c51804000c3c0415458105035186640980c005d071a0740d948400203c00c0381c0c0148480d010300400c0441c0004201c02807401c2942c001103a250b09a282034030705006540003151f214090300310560380950303940c20050400703800001080d619418005965148104407504059803c5404194 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 798693651 1250 798692401 798692431
    0xb03061f0e160801060f091502070513021206031507031d012a050403050604080702180c040e0c04061d0301021909080d0c0803040327060e03150610140c0303 69
    0xb21684a21010f00400c00c81c03514800b0002e04183c06000e1584a00464407206d10556042031114020010040204070140c90084040c020a40c000002d400141500500d2032a01300440c425203800601a030f0034080f0001d1203049074952103403e40050590b4050b17441e43e03813080c0c100d8a0a00d202803264000044141c800602158034040c81c103040f29044040003c1405000c0c00240b004c1900016116482a80001d00c2d075991601030001640040b1120861880c1d0702d07007041004640d40d0900c0140003250700100389100c5548800c800c0103c14001d501440c00000c00700b0074012021401020802c0150401400041c5000e1107d5800490100b000c18580003050b0400010800d00030100f041c10328070020b0703103840040400d00307942d010001d2201403c05020041c040705113880c4c500300760004c400456100581000c0103076071602c01510108900380d02900c80c4c0070381c004686c00c14001148452013041c006215a4a18a48010589201401c501e92615141041c40400c131214004c10045002c0d4a080140c81c41c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 798694901 1250 798693651 798693691
    0x1306171923070806120a14010906181101090b0d0b0d0b0a060602100614010c170403061d0601050603061018030302060103170405010806060703110a1103010f0b03061f0e 74
    0xd04000940907a004078a01d2120010360703100410b070300c1da101d41d00c1800b025142c01541f0801e03000d02000d21000d440e0910308440c042051a40c0f034403029500e07100e10321001c19986403100544400c0650b104891035000d0070040c0541e00800c42c0e000100d0729900a11f00c08904100e07880d6042441400c50f0f100300740c02d503915814444150100800742c4031007084102405424140210b5105c000c050503002c40c1030101c0c146884003002440102000410194800c0c07075142c5030343e8103107a0060010310b0f10b0342520045600c0c020035a80008940300c0d06890f40900803a24580341c6800b40540000314141580400c0310740382d102c54981200d100400003d50081e40244155419800c05c0036000d40788a805004495007008100000d0341c011a0340e03a400034007160066260b41d054142900c0c41510102480010300540403000c003000b9071405a0b1202a000390000c000a660009014040b41e00072125103606a116800150081030b4803c00d02d049510503891120031507582d04c0391102c9104c42911800005440094048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 798696151 1250 798694901 798694907
    0x51902061e090a08161e1d06090105060703081504090209100e0903070b0103020d021201023910090c08060405030d050703180314091005130617192307 66
    0x20302504014014192400494007203081c030303031710314802c500303000d02c104020211013150380960320001d1400c541903140102e00640c4200009004841c07070b0f482292a1400820907040c204140c0d89426410344a038843d544503a8078400121080d03403129540242c0301c0b102980161a0a04011302841c038824801030818200a40c0f8049100d000f081e400032030b030040c440c5201041c440d59140b411240c040d28256030000241c0042074002011024200d6558000603054080d44910104215032a0904145018040c4981c0140c02d500c006c5003a152600e50000d410701240c62003a81c010b10b0b11900c60014000d03036650300d210180c2080b90864054401b6040441c00c890702090501840e40d04c0f400d1890200b04c085000c5009a00454450401808000c0c260505c1010500c54208071400014010444246541c0c0780380000e202e544009000c03512400e884800081c114001c100d0b5a51805142c003002c4803e41d580804a0b071100c0c6011050320030f1a88503400b030400f8030040d108508240011441c0d5050030300d4182006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 798697401 1250 798696151 798696169
    0x31c06060509130f09061814030c070b0f040503120403060b040203040206030411012f070e09060417040e040f05010e0c010f11010b090f0403110a051902061e09 70
    0x10006015040154000c0355464071074000f84807424880026203a0101d144d1040149180c0f400241544c0c0340062000010382c091000015461040385d0404000a140b40c0c05a2240500004407940c2e602520051103002c02d032801800c20950121162420150b840c00002c0c503024800c0005403a58030300203410300030b000c024000d0b0180741500359815442c40c103096012176210311000b8070240c00181c0c0481d185100c0d030310803420403140c49180324404540f600c0c0b13141c1c0d400c030740e038400c0015800c0d520951000007640002d202d03440703208a003044080e00646e5901d44440c8482020340c41c5480b500380b403c00011030f5041c0a14541401140502c489400c0c03086ca619107282103411114500d5400d5104101c042d5990780e01152501c0310160364503000710308600500c21140500b01da65503855220b00b44204008424000b0784a15104a000740d4076070440300740c5680e42a0301d4034200000584185c001d11010f0381c6110704407050749a42ca2000d0710301032901030701d401c00b00361141c0300e00508042d039080052403400c81d01d408501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 798698651 1250 798697401 798697409
    0x305120112030203040e0a0f050403020106140409050d0c0c0806250509090a0e070e090c0301150b0703080403140d0b0a05010e0a051c05250e0c1b0c03031c06 69
    0xc2003007082260346001e541ca009600c00d004039452030000050a005480e004800f036001c080d081400349040505d03000c0d01a2503a030084a4210070788a81c0c11910345443d0240c03007680c582020180c8001c24a101d41203801c82d060007403d440d0501e0440d40026003400070403415206003492a481007a0f00310002100041c507d004104100300322041c03020b0140703a034400c0120b94101ca10310000241104280f5107160505003260b001c111080e0101c4100301202102003400d01c01e51104800802044110038010000b05901e4040d03003250322018070071a40003d0141d81d003160070600904105a1204604040303001b2644017400828040d034603180340c000705003421011036000c4c0c002400d0200070a10100c0216503550781c507100d0248a2038016418200c800182050400f0303044d0440180d5080e0392804120241040010504010b00c0800401c0001c0d45c8800381c810900400d803404003545031034040c01201400c1d1424841d00c0341103012703c1c0b00149240e6420001840c44200714401c0e4042c2070050b901c40e0040b40c07841d0384 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 798699901 1250 798698651 798698669
    0x501120207030e121c0302090a0f060906030b0609040e032a0a030311090303031305060a0b10050903160f0807120f02010807090e250309083403051201 66
    0x850100002e07040819030034032040035103a0b5100001c8044132a482c0c40c8482400440d103001c2031220000c840e5064008040b1100c09441c4a204580d840005800750442c911840d0000350541c8001c0c0030252003908032500401c4000d044600b050005000501140c10340091a0300715800040d42c1201c402c640440540400c902480b5520310945e20003266403241e05100c401400c0503664005144a602504281d400d100b40c0a4200ea86030b18018800c50200380b11780e001925280b0444000480101c41400782d4034040202078071421003014201029500e540100760403550500802204264242d00314002d80000e01c62060030200d02407070403000a0400d03102e40c11a805d502a019282004245038101680720302382e083c6004803c1c6c1d5a03607907040711600503540250402000f4402070040e1240344d84144d0440510306158a100d1035000b440a030100ea070444001000c2c0c000034009440700a1020004506191200302c0c01000350100c00030b5580070104148084000c1003008c545140ca907901c0600c0c49014140d160b0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 798701151 1250 798699901 798699907
    0x90f13061b180608183412110411091806040c1704030c03091502010204031a10030b090709020705010e061f14060d09050f060604021c090609020604090605011202 71
    0x14001c2200714010218805c010a10400700e07510740e010030911040559190340e151034070100580254030102070001c141501c00410002040c101e40c111400e04686920034592000300720020103000107020b01c0da800300c03540c0005000f420681d46503284002522450f500318a102c920b0310208000403901034001e41c008014600c16103801c1108001c220a4019806041c000383c400d995140442d10305100d0340100290014030141c409400350150003410507288100710344a10080b00403c002c807132070740c100c941d003210303030b40c0001c2c104042014450074a800400b110250f5a5441e1100c0780c08050740c0c4221002c4a0301c0e9503505032244140428488203420000e1b141d10409039178010702c3c0040303514000d8080d050184c4081c0b201c9500c1079442e102210150185000240507030005402c180303071141d0358007850880900968000450524061081700e131150030905043c82c40e03900c03000c2c40c1c4004103031503001240c2007a44d80e80030310b000d0707601d510241c4000d00c0c088002081d020b0906000408001e0881e40c8000583e0040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 798702401 1250 798701151 798701159
    0xf050604140a11040e07050a1d070e3106030b010807050306010501020d030c030b090403020604260a0c020301090606030506090111030708012d15030b0f090f13061b18 73
    0x39035040f0386110070456001c5014802c0240f054102902035000c070b40e001d01010000030b01054004101100380070031403222001ca95450405032080d40300403021951000440c4c0c01a0001c0d030001c08944444c14660060001c040450700351715003117401640040c0e40440203000104500c240c2080048098802500a001c080d4500301c0080e648103043e912038030030702d40c40e20f9400c0c16003846540310000c040c40c000c10303a00c018141410041d4840c00d056070192031080d41350400c082c6003180c0c082c030400f100c00804801450700611801c21203481c009040104e03499502c4410042c0818542d000d07540c042c42c0190064480c078248600300700e007100d201001410410b44144200100c00b42c0008540d81101c021101c0809035072115401e04840013003261040207a200e202c40d0105041144240c0301056031115242000104c81d00c1c020001114100c0040503800011440050104407000c25600e0308180b26610b01c001400d010303a915010b0303810703069203022a03a00b1005560b01c3c032030b400640708005d4a6441c4419040c2c07410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 798703651 1250 798702401 798702413
    0x6120f0a0e030a02211201230607030309030f021f020705010b060a0e1315051e042a02070503060c0c0a080f0a03061d0c031803070b0f0c0a02030a031104030f050604140a 74
    0xc1403049101107192014504003164a408c054020b951009064036030b03a8220303150190090500b10426400103040c0100e103882030b400001c0c7c1308500c4005101c1c404610401d800140083d41c40400110b42030b54803030420803010745800028007a055036a84400829800381400d10051001902c1418000d506118854a0981c03c07810240191081600e42422542d2414924102d10a6610344103821030b10f0700d4100d209444403022035140e241c00302002d400c600081000c1c1242d48150707074055198150400d00c0440c005500b074100074203800040d00306607100129562a100501c1d0441548001b400c440000c0082009a0501c6100c000e401681140a5042d048824000038400014200c0c0a0307040000041004030f80c2c0c0400b40020301c3d41d000100c0781d84000a103040380c8071810a880b10207078103640c00c01003100c204050094036180000340d4000c508009540c7d104802400b01e036089541c07040b104205c04808284031003202e05070369024200403c15800c052400a4040f070108054201e10f130444554000040c0e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 798704901 1250 798703651 798703687
    0xa08070305150c030721060b070b240102150411150408060a0603051b03010f0207060204090c17240405091509030a051606060e090a1106120f0a0e030a0221 68
    0x1003483d4640920a2099a41b2030007442e0f9508204291180801c5403410130080e403680c1445903501c40d0319000003412000000c0c0d69451403007a02c42c090b811443c0c900d0400e0181152003980700c5c0c040c0d03200340c5da903103180c5010800c2e07040030420001d201107001034144090303d41000507940048141e0401c201c8a455902d60507102d0603100c01e5984107110000c0583c40075078003500310032202030030140119501c2c451443c10b00000d50003403113599205070800c585c8000342c1c1d00a56402c1e001c1903840480104582c1c4820a041040d00103040c02c80c02e44000d805030b0040398946100d1540314001c40c2c001003038486100b503101d51000d100100010315030b0380108401c095480d44803081d0b505111b0007000c000d4010f1080e14110000c0c240a8100303581007401d0108005040d0350000f182030226000303402d000904942c0c18107021451043c4501c541c0400f45110100e00403804402c2c0503984600c100c3c000041422400d01d00500310f9104040103001684000d840d110001c800e14006a500d840041403c1e03e000c0d00c61010110b501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 798706151 1250 798704901 798704927
    0x1051905040911040e010b0f060a08010b0d060b270f0a210614060a06030e06010b030606070c06090510180504050c12040614010801050f0c090a08070305150c0307 71
    0x1502e4500700010820508882058a08014410b0065802100c8514000c02050403454854103e1200c059a241050001c80e10b0400e042c3e6030b5a200d60303007070030880d43c4a68007038000601031594402c80010b41036400000b81044d4003101041760005414400d03400303200301c415035000d40310780003040300c152030b55560004100480301c0251200542c8414450811500e11200c00060056410300407581d00380c4c1e111805051060b1401c44241c00516210300003101150301c0040d6810407544010b00500400211002a60748094010075103460070300c4903610440c07264100c3e408400480c002c45400e100a00c0e210b036a0a540b401286845a03860184007a100c04100301c520a250240e0364400100b4805201c001c115445244a4003138600e00d030a06240120081104140d09180e02c80d84c90004140c0c120706028440c0260b040c0c4090070425210710362145c0b41d40c0d220f400229400041d0f424005413420040c4881c3c0d0046005030f02a1040c0708183d4001414801b00400202c1240000c00800c490300e13030480c94041e610 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 798707401 1250 798706151 798706159
    0x71106071107050d05010204090606140711220c0206090c0102150709150e130603080a14090a061112031605031e010909050114010b0702040b0301021b0a0b01051905 72
    0x420030041d100ca050400742d401094020072540c03484402d11605400404c1104c12800f020000701c3d0fa10041200d010141882c100c00344d500410505020400320340381180c40b501c000b0903840c40b0030b4011009000b005500c010b0811480d8071240d0410410341c041c4501640406440081c0407041000c0300000c0d141e04000c0c110300c8800c420107001c03c030b0207440b0345d484901401f09503903c3c8000103040c01c00035000f82c1040e050248103900340290788160007024011481140d500c03800940c14447c2c020819540d8003407400c80c4c0c0c14035074000e000030703581540e50a0b25440145201c0d01c5901c1203a192051480c00d010003001004080c1c0c03002c00c00c5c001ba103401c4088229092100d468202e03203903140c2d92005801d040d2910b00c00c03900029904c0011500c10300c903603c84101d4034071601c001c205045040741c180c0e0400c4030900c5440710303480080c00f90380058107081d000381070421802000149440c50560788952031103c1d500703041c2c425074008091501005410b19a0038050841125920407140c04500741952801850060390b0103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 798708651 1250 798707401 798707417
    0xf0b0d08070c030b1906061b0b07210b190506041701230702060709060e010e010207031b0f080105060603070e0f031f0f02090a031e06090b0a0507110607 67
    0xe12115034250360140d98400f0706201380741070800119030301004520f80c400d1a28038051002078281e0140380a04100400e0580c85141c0108640345c1411381e45004104400348040016940445c266051a4110203502c420000910b03c940100b889294060001e03c918007041c0090300740001d82d40e407020f950447e0200c0341480c1c8800520309644d40507240030f115090303040c280480070703040c00741007441c000b4442d08641c0d0272209139175034262007195104828031071100495610f003564042c0b54815608120400e0301130044410040d925034942519001b03411555a44d6450554240301c1d0008550746a002070918030002c2c00242401703000541d851002900e01c0043c003a201031a11486d844603114209908401400c0d55000400300a544681e64840c19810800781c1c40c100d00b14841040600c01c1d200708180280c10600b0003821a40c885000c0c00540c109000c07061402210640050603e0084050061041c031807501e05080030000c1d0002d8030405406801446400040041c141d0800980c580d40082a0318260b20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 798709901 1250 798708651 798708653
    0x302160b030114040b0a171212190515041d120309060c0a0503010e100b0c1b030d0e06130e15010e10020a061512061509200705070512100f0b0d0807 65
    0x302d8823070203091180c20003402098002d84030416100c458850f0303d03170290624080c58800008000c03680100d4255004407500c1d036001e0404c1c2010ba1010582c4030070401d00a80f60b030381c0d00c3e500b00e01d03107000c3d030200c3c4810400000420080f04c506006860308000c12009441c00c00000c40406070141c0814000d08817481e501c1700c00244828100c0b0810801000c1081c441c80d0b4940881140c2d0382c6543c2c608100b03220484980b08030b09200d06000540c1901c085059948401c0c100381d03441007064962041d2105062010000d102048001c04000e1050103909003006c40320607981c14038009402038800e40002d074403e00b04940c15007031081c0c012a40510059010000045116074009001000c0100350054080c906802002d0b0003000115030040492140f0600134152035540e5200c9001610709001100311207444c03c0b401da4004040c170002500d00c0074802e100b6a23002c140c4403000700c0c030280385600c030441242e4060421890074422504c1a071480c1d206400040c01824803440c041100c086201700024018080010800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 798711151 1250 798709901 798709903
    0xf03100b0406170a120905030c011407210206061005120a060305060702070e010e0606070212010e16170c0609011206090504030309120507030c0b040302160b030114040b0a17 76
    0xa019091282500f540c4216100405588981c420001c40c0d0410b503020f40b04402c0d5004510340c0c400c852008005003041d802500045500b02c4102c0300c03140c0300003020b21107140050008500000703449141d100340100d03480301440080ca8050041c0005000e51103690340446c10039032020449030020440c00e0803d2460301c4030315184000f030040f17510250240c022041400031566006c03070880212030780ca0059000b90b9032580880c541901c000d0740c5c00e6078414000c1040384010700f401060710142c41c2d10703d000050000100745501c2d00b0306082c00e81550400000b40000d005040c81840c014001e00d0714840244075210052010402905c41c201100d0705204a04071241c44040b940d820680140c0958201445517080900e8040e000d003a01c1c2e407045400c0141540e008881500c1581583d002a800d40d983c1c140c01c07202602c8070944400c000d8025003c5014040480041c10301c00c075003005c01054011015a625803400c10204500030f09056002c1c0b00e40d0600e100e08446950f50406681521500303206e4a0424003030b8a402 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 798712401 1250 798711151 798711161
    0x30e03030c1005060112060e0f071b061b0c0f1506080f01060515190507081215040f06140909011d0109021306030308132a030c050f03100b04 62
    0xc0c01144500b0781c0c000d0441c05035400983c0141002e803950548039101100341000d5641c680900c890a000c4800040e00e10f0a60035840d41e000030550900440c0c40c140c21404594590801c0c0b4162440d035115107200001031100d0085100c0071503685000401400030740d0f50322921000c03815010b41445d00c00703010748100040d290300040041c843c110031543cae176201128103140070740144e1051511444505030480320414411b0b00b10350814004880c0c912107481c2c140c5094515412100060317402240500044040d04212554140140259601514603101c20400c00043d2510701102e4101d8504050003005200d030013070031f860801d1500b12110b000c0380d0b45a11403940101111041c0071000744003190000a43d0f00c2c1948001d2085009455000d03089042d8400300702541c1040c070001780080c00390400100805801401e0981d064413400d49146624400c0101c8848041c040100342001c800c140c008000300b00c3c03600d5260004002c20341c0c40928400c4048000381e00c8d4042102150040341c0c0f5860300244139680d035880 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 798713651 1250 798712401 798712417
    0x5070302070f03021e28140a2105031c1a0415090b0303090a0303111b09040f05210d0506042a0212070602030103030e01030b0f040b0402040e0a090203070603020f030103030e0303 78
    0x110118040c440d41d000c0c3c00d80100d84907d0707029403108059084a4140041c002043c0c0782c60107a000d0099040380d4446003040d000c6881900d240c001808403102d08482c501089520a10319000403400d40c41a42c0f00504e880e40e55881c07103202c1c600e002203034801c0b510411200d2040315100d60340000c00c030405002080c00c0d40718a040740b6038024081400030041540040c0548a8081c1b004c00702e81c09901400441d03400c05003455a50703640140720000260000c0e03024400f0107200e62049060b0740c910080368100e8080720701e02e00c042d82a442008075848100c51038900c10107500c40801c560500002c60000301c1140c4040d8210342038100821891001c410050082080050800d046141c50b41d4a1a460501c1d1000750420f0001320001011202645441d607c240103c0503050740040401800c02810420030005100000b240c80d0826002c1c00b0015513020760201b00d41c031818609c500803650791403a104041c10030364540c021a082c9403040c01010a40c0100030b059a06495042c105075454103103c81c0024654015281 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 798714901 1250 798713651 798713689
    0x2070b0108060f0a09030207031101031b120b0a0320060f0d0b0f030d021002030901060e0a1b0c0c120c030813060f021207060b1f05070302070f03021e 66
    0x180709000082c1d020310880a4508981840c1c580e240070600382d40b0041c4011700103901c03040081c03000c00c180e00402540300005050024142d80d0080d040700f61141041c11078030104042da50a011500c009018050420714101d510a024138115a161020030003000c1840841ca41102483c0b841c80d142c420440c1c0040a082da403c0c0d0303c440500d50400c014003004c0c991140078808100701d1003400d050015080000c80c2040d0090003080321030b01c440340000e400050525402d9034030303944000f5808a110340000d016140c0c2c00c0d80031400e0780564080c0803092503d60001410002203212081c00b00351504280000d841045610661035441f40c00c04550308000c40d00040c001d20380005840100c1c04e2580751071030031140d503919844c0c101c1e03c2103d405d90301d443c0d141444d1050f41004028180c0001c1c010703488210384400040440e420002d00003880c02022014520120108200103032100501d03030100040700007800200c118035074050035603002c140c511200030202000700380300c82d200e6101c40d600c5840c5100c6080e9051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 798716151 1250 798714901 798714923
    0x30519081b0a020f1804020108070522080f0d02070b090a050603150411161115030103050601030c0b0306010f0807090b1306030501170319050c010f0501170c01021b040207 75
    0x71500c5441d50b0042a0803440350190008001d503500300000707140c00860610900320895502c40d00113489a400c010502c400708641007002400100c0d1070b00c48028140c19220b0191640703410800d01515102000040b180030f58004411038200c0383d40001d544041c0c68404505607107402c03894002c07800e00802600000d61000c408800c10601012403000841494400c49007441440413070509030306d80c1c1c8501410309018800d0041c203000828019200007000d01009001c603102d1102c0b03a00303c8070341500283c00444841c1c0042c1e0042045c07021703204161001c1c0284880d9580f850520700000b0702100c080e6200d0723805012626000407200c81c000c14800c0c0042641c0d200c1e01e6a121105403201d6412a03042c001e1001191030b180001c1415950300e200309281075204401585000d0b000d4284645418002d0b070200108001040343d00880c400038052201da0002000000c2081d506040c0b500c842d05480b801204070341ea00100700010181c1e4000795001c20070100200c940e0403045000041000303031082d600d020b0301502da62 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 798717401 1250 798716151 798716197
    0x314011b0f0201150303080601051b0a1208010f0f151b0c170102030c03010902092d01030c30020d09080309120408061b070614010501020708010603051908 68
    0x8840d95282076103a9000300010248100c0d007100700c0c501c82c0030103000a2000c0001079010b500034001009024420114109900b128504c1c56140034007460048402c8614a070802c41501d800481e0b0030301500c14100a065050704160b18500310502c0b0b445000540070702c1c64006003640c2d00132181d240d1000100300704070b800e030b8000d410040c00d105454407698442d02580f0400710000201842524000e5100318441803850746040080b4000c3d411000c0e0082d400244903607944208803a54072003509240a0f80c161384491710301040094201c070072040b1240b00740400780500c20f902505030200300c0d05c83d420096000d2410441a43c12100a0141c00c001603500d07481d1001c000b080c0290b880166201b5581c800c120381c1700003d560400e0400c2d0003540701d640260303401b40c00425429510001c2c9000310a07903030318a03142041c0c0c8548415040e02c0c40109001d092840e14001404070796030502c442009403000800038081c851450f6240c55544c40482484034070246071401e60b00411400343e003142c1c108101031029405a0b211 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 798718651 1250 798717401 798717407
    0x31e0c08071415010f060e0a032a09060311040902030a14010605060a02030301090606020705030304030305030601120501030602090a0b03060102030d051e0f2505030a1509110711060903070314011b 86
    0xc0c0600040c583c085900081c0452080c003d40721400700150013401d07000e00e9691944141300c10180070a4240040301080d01e402b0f0f240042c0d50009100d21000070448520b5400c09150705419000002d024030b040c1046200941c07000139081306800e07804400595943c00a516080c0101040e070040d6602160003e961242a036000010b0f5040e2030004104200555440000760703940c00c1c3e240725142d0150800e000070000f1a000b4405507034804818140180c0302200c100304103003156003d8100322403e5a0108219034a4100910041d001d0700c00110003e140d4144600042c0d66401112102c0302410307110400500300c2440d15140e0010800e524514101c2400c210b21441c02564040701e9100004100306030a0404200e003000e04002c6668584903d0320355102c2c0c0c420700000c3e11031789042e400c02929050f0006080e0001c2e11800e5944d000400c011602c0300428508445048041091548540b20500503041c05542c086040e000b00d0303511403410031016900800d400c0c0500745003080e9603440310040e4428105203070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 798719901 1250 798718651 798718693
    0xe01020f0703090f03020d14010b060a17071404141203070501050f090a0f320d0e06030439060905011e080609130605040f031e0c080714 60
    0x88603456a400494850204013001a824071010358408090441c503004030f005442c160703407402d21903000406c50a40c0b210100d5001d0b8441c0f104000001d01e0941c3c01e90307a0700c40d0701c0d01080e0090928030b4003112484a0100b08141030160b4082e05455036003002101d6850780e40d1920802e1240203000030b503621940c00742400703402081c088610f10b8100c501c1400242504001013015000e40d9441502600300c50200e8503036002c1100d4084460011144004201810301e042e5140c85907030b802c4c524000c01407040b150390020a041041d6240274040c0105000b4400041c411800110300c401c280700303d0a28100320780550407290f01000c00b842c848612801004600d107548003c22000380c4000ba00c4078150f1303094011120a03aa842022803100140400740410000e00d0800401c50704024030241c11032240b003550721500d00700c4500b541c00312121150b000014007016041444880c1d05030700120f178a00750200078840504240c1762840d00070030710030000500d4420400c03003000d10046003200f00215141d0000c90110380800072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 798721151 1250 798719901 798719903
    0x40f030609060606051603050a0e061603020115180207171908013002010e10090e1003080a30020306010e030705220204030b070203191b150e01020f07 66
    0xb0b0304210001c04ea0340e004004456120104a11840c4104110f450842d2182c2000892400708061030b9041100c0703940300f6000c1c0064044a071881445070446140181c21031f80062504142050407000401080c2c10303040360400004e40c9140c0250382c40e1050324185400030b00d08860003e51441c00b1a802c800e161100319104100c100350344440d901a40c842060300300e07003c030040640c40030101114841da1440340034803a5001035841070400c84035608079200050109100c800d407440c00500b05100c20422a0f01030700b0340a07048610300503003007005c6007982c680c12414811403030b640040c8001c01c0014000c80c0316540000c4030030154901c84041141001c111074019601c01d45d902800181d20b4041030200b46008220001100c000030510104518241000385045d00e0044010605507401d00c030001c00314420003041840780c4010b90103190b079490b50351841680300042d607031000c04229481c804480e0310401b00715040b2103140c02a030ba4091440038001038002a0816400314103071540080782010011101c280648079172 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 798722401 1250 798721151 798721163
    0x5090309041a2e0e09131104020c011a0612010314070b0f030405010b010908061504090b0a090302060705120117030c010912090e0c07060504050f2415010c110105040f030609 76
    0x405100031080324013500b040c4e22207511444000100b40300d8284000d40c3d9412912442c80740c80c031500340c07400040403070300401c0091031140d458054050300c881c50b820000701d00c1201143e403141821081064482800d005002c014120002103110323358508040150708020061035070015500d00c0d49440d804160f8006480454143d82881004442580502c400360244c82503100108150307500c890f101079103048200041500310340d80e45100c5000c9a90101030a2040c026031601042038090b5103802482c1c280c00810180c10842d00b0301c043c0300307404080340c030b0281150a1a0985070016a1842c0c1c00c50031442544240302d22503103400512802c001c41a1040150034002e911884101d03940c421402036080301c21208000380300c80820140e00020020703801305800501030f00880d080305415241903441c01c50203105111034401e06541031621030040c0100d20342d101244000c204100d5180301e002138110040100014030902102d28800c03040c0c2d20481c00d6038020302c048000c405c1540e0ba0703410010000e089800c001e41d20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 798723651 1250 798722401 798722479
    0x1e060604180b092b021c120603050304060809120405010c030e0d03020f210d11040b040602010204081006050d0b04170a1805040203010308030f040c03080d02090307060305090309041a 80
    0x1103140c075145003580f0f03541c0e50041c00395040c08980034041c506c050200c02c410701012803140c9544100c544200005544a17800440c2c1e590304201c4090310300c0400404038080c0740d200f8005103045807030240507a000c8940c20309044404202510301994403c030700311501c6410460f103401420505a0000712804908400c00c00e0b6061001070161508010000300902ca000d4081000700030700c42d02c400d81c4101000301300700c0001810130b900d5104a504e607030301581c04580103039000300301400380d2141440300600032a40304504102d60b62800b8082001811000300c058684c00d01e250009082c0f016000d00650410a00d0001c5541c0c0c8200d00e0b405814100e40038503039115070b01c000300c1c0407032a07041510860741a00d400c118154210f030f8400c03000c1c000700318005100f2500c0c140500740010001d10001e018081c518416000075803035403a000706062601c0281c0d0700400030142000e05100300e4480100c216175060106541c00720f1030004907003406014080c00703103a486d0071506460004021300500703040300c2007803015840d000d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 798724901 1250 798723651 798723703
    0xa1e0519022a15090a0b040b030907120f0201120e0601060224070212030a020d06030c170c01120903180b120106080c04050103021c1103091e060604180b09 68
    0x61402d818020540d000580c00d0b240828a5503098041c1c001220014070300c0c451a601c2e0403800300b40e6040356004160500c404001e1162140080c800800500480b0507070180012260321402c120000303090b0088d05103c0340c180020001001038200035410b488c6141120082c0d61f444078020340d02c0440b141809610254a4605400c0b0b401c0040700302d020f007800d54020450503250401006407030380090041c0d15055400c010041c29010ba9015400065014141e01040300d40351240d5500d10b91003020840c1e099030444030b81c050150303800521040503920921000a1079807158601544c90f0700421040040650143c030340003d62218090003011003d007445080e400d141d0b0784840583f020202a038904a000c8024401401954400e5003d04040d00f014020040030b90645521101110010485000342990010401a081d00d08121040b240404c4e032030034601c5446100009529410083c000c1c520860310b54844c0b600e01440e5a441d0f549080d00050181c00600709912502c2e901e03c0001c207013480110f01003441c89 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 798726151 1250 798724901 798724963
    0x80f0f030c06072d0503100501030209010f0f0c1a061005070302060112020a09050906010314030a02150903090303190206061c030c0804090207060618020a1e051902 72
    0xc5004000c00c000381040e86a8a9042c0c81c02100b04006135606003540d03034502c48410300080e03280350583c00da45074280d90b414176034184180e0400b150031943c1410b00402c420007243c0d0380b05080981c402164580401840e88107403080301e001440880203014212282014003000c0040036140d03008050031246203132500445d4506682d540600817024015800130001000840c000000d0303001814401040e410540340c40d80e0440c0210341c400c1e00ca4103c690b01c40d100500401200000d8011030510f80c5000354107040c41c0c08002947c521a800000c200c03240c102d0007088240d8070410940b01d0a8600505070f82d11160f0f030425214611001b07074201c000512038400072075004d00f4022144440842d02e01d10500003442701c0e881c25a4180c0b250381d000c9803460790410002a46511500c00380500520401e00070950703d162a4a481c00c50480c46030340c4e46010b02c10003104001e160841000d0342500d50020100d071940003c000c040d42c143c0107000d0903845440c038100c4540805540400d0303280f8844040040c0c1203259414070000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 798727401 1250 798726151 798726157
    0x32d02040e0f1306020f07080403060b0111011a01030b030f06090d1701031101030203040201020c0a080c03240402010c030225170d02120c010603050307120206090f030d020304030507020a080f0f03 86
    0x10860543d6425403c0c020502c103400400341410514840ba02e8001caa07a02c0c042c0940c060703801503540d03d41d80c4440b18955a4050311040c503136480013000707003c0e50040304200d800310400100741c1c134145a6216680b05241d1001d0085a018445403001d807100c034a001000141c940d400c0d40342100005078038011041401c0c410440c41c0e4162500f021b00d2100141400340190000d500140c07040c3d0540c440c40090001594a00030b241002d841c40d080a030403103000c0c4000340361070112807800c1004e44400260320300000ca030000c41508da1003502481c01e2401d101d03c0e0b040c00da0070082ca40342c0040c4010442d0240070000001c4d01180030481b26040109078100c00042000b54880514507440380050b04005041241c5081d0309000d405105509030002a1882d940d43c0d40f035180da48079000494074224000a042c42cad640c2c05026a5500c4407020028002400381c0b030030100d85074450b2098504440354080003033401c0c18418030903110a5540a404440700c10f840382d280c1603549010f949250b115100e500e400d150303407007000700c20f03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 798728651 1250 798727401 798727411
    0x41b08030f04140607052e05090606091306050a0204060e0102011506080a060504091a010608010639050115050f0604030b0406021e0a0305060d12032d02040e0f 70
    0xc541400e00b0901c1d15554103203100300450340f0803418040d1030b0102e1414403000002003244a440b0406041140c6004110800880d400b210a1301e803104215141c4802b04045034000c1048034601503030fa46d44010403c2d101d40d12880030344514981010800740000c10b60091040d2445a00d81d02400c0b90950300480c03d8491102000c03000c4044072804210050152500036040201c040b03010524030b840b00c0c0420704807104040c1c03d541c1e85608120700040c40c9000c0b04458090105840e00d60255814450054012501030151588004201008083c0d04460b0320a000c114019003045c0b610700c0c4254100140a0b0018180d12107131050940000946403608050b054403026026081c1c2e42410b20f076072210000b86800400959000c2d03020010000110480500100c21051012503140c075001007560007402c80d00000c1280e402000c2c280d1508000c541c0e025584101b80920f4900840d00300306d4000c0c904036034003100b540074034400c141a2000710088129000f07041540e0200b40400416501c01c007522104100c1a18 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 798729901 1250 798728651 798728677
    0x50604140405071214010906090b06040608190603050a0b0c0301050f060d09050a0b0a1401270915090b0c040b0a08070203070f0b010503060609092a030303041b0803 72
    0x84400302604280d000964404414201202008600100c11040e0741010141c1a02e5010880c010f0104d110702e0300c10031010b0b10203964200199242d4401150080c802e13805800d0600001e03000041c0044030074040c03c401004826001c6c00904d644e071a1a03030340d81c0525042190508210000588004408000e49040300c00092001130b594441e001402020707031080c0080e1140c00d484a07004804103804001c1c02810350305c82c1002c40e0041c90980500d134210388100403901c000b1141c00e00100085d044a0580319440280035004401007080c0c018142c00034500108024240c0303034030039a000e8010300c181c1d0100d0041d5000380b20303c1d610350b500e41c40c11500500c07c601500080c10014040ca4514603c110100c551101c55801100c0c80e02d00d140c0c0b00c078000c140c90a44200d840d00402c10051005041c14407200d90480c405460a2241381040070748103454641030303200c0c40811840507480703000d081c211207540c42000c0d00203410350381e82e402d240c1019400c21101101c4000c408036030000004420000108913000002c0c608 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 798731151 1250 798729901 798729929
    0x50307030f05043212190e10080c090a031101030f06030804030318180204140102160e09030d0e0106030611130b0a03090602221707121407060216050604 67
    0xc03d08400c4e454546520042d1100200e000d8000100300b0403d46035000091024aa00c0c0c900b08a248034091210385020010400b07011055041502c40b1070300e0541c4540c131401c1c030b0050303913440e03940b032035020b020301201150b00140440001050152210208180403001c0c0ea05000080d1010303180303c2a16014480101041400c100802c0824840d0600c8440346446c0b410307503221940d8a00e4008070340c00840b03440b00807184e030005041001942c0c1c10350f00d1a01e42170070b0020b030064812041172000d5904035403041d03032140c1c141ca40005090040c1842124852003051204000320300e10301c44428020125404101c41e018502070342a05103650743e030305813091180010022007403142807590143e1395410200403070082c19112075009000a6070380c0040e11003a01d4124911927982c50400c4012044a050b0384a1100c1480100000b00c0603c40420941d081e150328428884448441d46000c044100f030100103507115020350704012420035130103d614501d1002440c403410382c03552100c0030494944158800d00e15011511 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 798732401 1250 798731151 798731183
    0x9140a0b010201020c120a091401020d0c050106080a0b220b1306060b0a111c0e010810050409050f01060510080609060d05061f08010c080708100302030a03050307030f0504 75
    0x20350802444420103100260a140d0442080780ca01041d0b5202e580d072451000c6203000c036165000c001c110003012560011032142c036411002030340303401400460790100030b240311207402440700035009030008060f001c007241e00709012403e20400030038068404003070a84a10003000c841458404010429541000d584481502d642980c8000c41c0e1086104440c0c0075181d03580007585d18401400790036407503500c2e00c4403c0c0c441c00041e482e5090404102940011407440d9481080c139980c0016000b085800a0a000e0132070f0b2505960020746920f65030106511500f06282d00301042000304030b0b0031140b51000003d1101c0b64a0b1410807040c44240d0b049100000d44080c00180c85207044a0303059000701c030217044014030f0080c40d2506420302c00110b400240345072515030000c0c081c405c2c07412004010b0180354000c00045203101d6000384100c10141c264410002c5540100b140c0c8456801c081b402164000c0c02c4950181031490701800c1c50708211000402320f4a400b1211021441d103005252050f544003503040d0b140420 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 798733651 1250 798732401 798732421
    0x301030c0b130b070305090306060103060b0f07150e030910030501060e100c050d08181207030f12061404050f0402150d0212090105040c060228020f04051f0914 70
    0x44140c0d100718401c4020000607a0036041001072403128041d0351500d47ea0100b1781c0a041c5001c40c0034007078a040503e04035041011f07e07030483c20380c0c4000071944c052542c1c84506040c144405c13a0f111140981240c90030b018180304010001c028a00904255000345001211a8080e811900240700b9940810115860000d144c500361103c80020f840078246000034094039151146409c00320400d20300031440c41703402d0001500044201082000c0034000510401960300c00884503800b500d0001420700c01d0810120440c540203540c01d01800217808810040c0b160354030000219142414a00e501846c0f4010200b515545004a043e04c50f41d000340c61692820100940d401403a40200d20700c00c6c0f410b500303110020f100c5280c2584076014020b074200104081c10241054103140030303154481401e552104418401480920616810020001703440323001c030402031700219240801140080d86e20034038000c2002201d000c800c1d41000c801c806007602c20030854454610000300caa2840010540f4020b210015000f10f01b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 798734901 1250 798733651 798733657
    0x7061106150103020d06120c1701180f1e06061d0903090f060d0e07081b0d1202030f0403060203091b06070602030406090b09060415141302030106150f02070b0301030c0b 74
    0x201104d800607906941c0da0703003140e5816a07200c1c1100c00c00100642040b0110000b2803000400c0d10140003008254451207284d0310642c5041c00003400060144c2c04cd80900c105407124492400c0c3c0c00c075100d0354881c104d1501070300a06460007060714450780e0500d80040459101403ca2140c0f4108000f1171070100034208000070400603619040d44110200300c40c00101c81030703016030950510060010001e01d07042001803420219401c422654a0301017005036000c0340d5800b10b0044100b038018054100765002d50900b2400d621820ba000b444180c0005000410000d036a8004d42c410420201a210f45409010700a4010940a400e0943c03044040c000175002c1020341c1d00035500240b1841000030b405000799a8440c41d41c00032180814580c001c0000c00090255980c80203a03c0c8078245402c11548031203444188410b040030b84440f00c100d02c030003001070454800350301c004003a01000e43c601284425511008103170501403001180140141032000038211031344015607050326800060750440310700301020766510750 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 798736151 1250 798734901 798734917
    0x9070f05090f040606260f0610050607050c0324090c0108010b0d0207140114150607030c030c35040311060f1b0105180f07031e020a080706110615010302 67
    0x10b540c81d1701c0043c501c1585001000c0d15201c10f1150884000020602424421442e981d03958a41080040008104404040d0415120b0488005450b402c460500c00c0c5030a101c1401c1c1c6805115101981c040c21815015012070184040035890140d5105c035240c0f03440ba042d048400d4041145800140000d925400240c00f00c00c03201e000c010300b82016a180c0c510150050900840365941d1010b441c00c10280f41040190700c4100c110351440d11000f60008503507107108000c000381c00c204404114400301442220358414850301f0140c000c1d500044800c00849945410354454074035070170040345000c90240f50058501700c94001c0d03102c0b03946080301d100307102981e4403100707403070540141c208064070014060002c1906060b07221000040e1519144203404007100456503011080d40c042a00b1401039000002e07040d0542e5807003200540013000b8840c00c2c690003440440700a51141d41d511010514860018030038080303c0b03a03079071000c000f604040c0e15907842c0c440540704403000140d55070b21145a03500a40007400da807 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 798737401 1250 798736151 798736163
    0xb070b0c03060d08042d0303091202010c020409060c080114010c0b13050f0102030106093309050402120603010c080403020a0b1b0f1b0c0604090b030a0203060f09070f05090f04 77
    0x2458856132031110550003500481c101c0c4400300003140000045a5400c00c404c041443c0310340c9031701d05640b0702910030030301ca201d03249803030000c5403840085911490105011031790251042c48100c0303461500902030029607080e40000b0300d0701d070000078a40423440d020700384d0488103031254030a00443d6102c9403940040100490a0400a9450341000070b104000c40044040c3c880300041e284d5040c88801804a10161700144a10b0062444036195107801c00071000d000e001c0c02007602c02d5502500041e03807000255401168064030101e00048081c0e80c2d10340403446181c04900070000c18843c0e40054031000e130141c90203001640880340440c00218482059a004025010017409a5814040442283e80603000d6484607442c0446c403030f00a0060a100c49030005050b0000d02414890700011580d0760003103126040b41640c4800b4010b0faa0b44080c0a0b010700960080d0555010345010741c4176042d03511060383d03811002d210340301d400920580348503000300907030340c000b4850b0055440b210b084140d503610143c001e90f40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 798738651 1250 798737401 798737419
    0x609030f11120318060307050a111e0703020103051b0717072108060109030b06010327050703031e1d1804031809050903040302040c02030d02040608060a0b070b0c0306 73
    0xc69555803015910041e042c030021603840203841c9221044403506070311280103a401344148008103801c88269000481945082c8904d2180144106d14102480b45410901e0b2614144414440c0b00414140c003038034001c3c2c806110b40d486501000c3d08a079018010101030038018440c2000180440c55000400c000050340c0e0783c107001250b2610f0072555102264540070703c001b0b2421141d001d0704048400d9002c40309003444e1000c40c0c6144c880d03220100700140700a041540d03c0e00090003100740d090318590140c800401d80f00c00d0448518040360313205a84e010039130100c0c0071483c00d070120b1001d0440c20440b100c526514519940240301c2502110080352650f05c0e4000d255503050f1556404540240b03201e14000d903a0301030704042c2c240200060005030f40200c10564144810042510400412102200d506540000e40c104400b1000c900318020903080840d600c1c000100094840e600062031030050f5070864504559070799990354090a407058507401040c01c801e01c0c0c005080154200041d5900503c094480c0c64 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 798739901 1250 798738651 798738683
    0xf071d06070f0c0f091d011406040e0f030f090103051b07020d030c0b0a0c201f021b011b0e18150a06050c010f090816031709100b03070609030f 63
    0x3244190a0300105c0945c4e0703541e1358400c5403030441703c0528008182e41000700203d105078001d0600b0014010152400b440e190202d1000c6040100035004101603040300742c1c0d40700d41003040401c000d50b00180e0b816001908003404616608484400281c0411902490501d490169402c2c00403503010400250240550b8603c81e0010651121402d0f01c107a401c0d071350026100000c01c0d40506000c0310002d00d0001707241c52440c0c030242c135000011341c4005508072000e99080d40094a0360f10002e4410042803038001c1403001c204076140038054000002c0c09050780c1c120002e00700480d80880700005007044507503102c8580800c2040340c107003100c1060b0b0020040b4007921245074401008c40e403000c05c140c2c041c5000030360018011252260030b01c1042107034001d0040030700403110309807150f00c098051100407a1001b00402e4402c42058010842c001e82d82100c0204899249040c0c01003e07224101d103552594898100241c031280c42ca008644542a07030401e0300e40c4948030b8115112030700c252454000841d880d40e05036080203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 798741007 1106 798739901 798739919
    0x21c110f0403030302070f060c02061914070c171602040e03030c032e0e0702010c020f10090302030403080414120c15070f0b0f071d06070f0c 62
    0x1740c5c9030281030402c1c1c2e4901511202c010403503132800c8401c00c0d400d50041881442100121048020419824601c600b03a90070030700342d203604c0c00c541000504424054032a05500e903000307402c0385804031304240300103020350701000e1102c1001e090110881c1c118a05070041582c2d0312440d0001e9801c40c08c181d0303c10900350201910125100410710402c4442c0d00360b4242540882008880800e0351550311408008515000d4400b0070055013416426801180002a51581642408000c007005400c1c014182c0003850124811000c40c00200400004950184040c1c0054107203042d0740c012070311030807082001c0084107860094158001e8150707040d155440d0524a100103030011051a581c06041c80c00c0811315080c864002c0c408440c100521012030034501e0294481d041c9522034484400030304044403149072445101c103a01c000f0070001d0900145008a1000000707102d03480003542586c80305c28003 = true := by decide +kernel

theorem cover : BRFrame.Cov 798561151 798741007 := by
  have h0 := BRFrame.cov_init 798561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 798561151 ≤ n) (h2 : n < 798741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
