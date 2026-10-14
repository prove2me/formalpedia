-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3427
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:37:35.467192+00:00
-- url     : https://prove2.me/submissions/cf53288c-ad88-4a8a-b32a-2e8e48ba29eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 616187050 ≤ n < 616366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 616188300 1250 616187050 616187057
    0xc08041404110c030708030408090301060f0e0906090309060d020f04060915050403050303130f0f060515030a051011130f17012a110f0f01270305070201171006 70
    0x2c0c03682c0c401080c403041d260000c00d480d01951a2010698481c42c2980c03005008851081d410300829040351024840d42c0c0282c84c2c0d1841d8040c0302c0b4145241e03594070400c000c0088032150b000000308448103101100352a000d0740140e4011b0744400010b4041c0019024440c440c480354000450001a81c075403021840c021200c000b260301e152080d02100c21206441503002c003600a1703200b0008034000060800e48035410500a58400060780c8076070396001010795545006446694841003401a103c00b0840c3c1454544011401007428508661395240ca038224403d1211480c6d544011402900c044c40084610f403000140d20a880301c0d8540f445c0c40e019800324007483c541c844141c1c602800181051040003214180141091405082050303007003c1551b5480c48101045000034006100050030841306d60313100d5a8101509103500662090381c00c50b1010206000c044240c000b14801340c1c45800b034030300c000e5500762a01e90707502c015500040e15400b00f080e0307600950750801020030500141c000440401c0d10466613 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 616189550 1250 616188300 616188311
    0xa0b0f0403030b0a060509150f070b07090609030209040204090611040306201206090705162904020a06110a020d1104060e06031b040e0609160815070507030c08041404 73
    0x1340b0443e40307283d000d0500407910802c8000c440c0c7c076011044400f1481a255128038007404101a42c0140d04840b40450358080031605004c10340e9000340011018000910300545c01901c0c45d000104a0500035101070f001da90b80d40c4802082c00415081060803081140401c0e955036500e1403c50b001f042240d4181902d02190100415080100b00403602140b5448044c16040d84440003041585040503010405219003008190005603000001c1400301d4012601c03202c0311120f503921041c0751002d203408a44904c0d10103042100690b61650b0341070541c0d003540740043c10004151a404d2409882000c042d602c1482c020f1700208000c003072801d0080f5540195800e11400d60b132101c030780d2040141aa1560350513000f6414810440c0008503038004098001080402d110340703540c0c40c450801605075211021071300900c1d104d107100314454040030000c011910040c8140040d00d5001d00302654090025420440300040c0c03442494858103140541c1d03a003000801d5603482e0340780015854858051502070180d800d06 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 616190800 1250 616189550 616189571
    0x1350621071502030a0f030c170c0d1404030f1d0a030804210c0510030f0e030703021513030318050d020105100812031609180225021806030a0b0f040303 67
    0x12081e503017414501d03101c02c410598010320030303000b03000080f200c0810840005103000310240303620352082c0245030031184240d95160a900311400e032510200048a00c0c03486105200010787c1c400d01e00d00c010420740c6403a60101004010311040c846030760008550201440380e0120a0042c400c009000311034001e000440100800c5c0c0004220b1918490060015620038004021a040071181d80c10000d11038a00040c110307055480d0001201d401000c10f2080380c0c4086004400c15030104001c0030402c1038030f0080e41080c50500464070401026440080c00c050300c41c1903900c28940c44604541b2910380c84400e0740d642c0c00031208024001c0070212002140c0108062002540800c0410354883c0703142c041c1c01980c910340ea081014100e100725142d04000b00162080e0001d00c0d00c0003802d1035001c61201100142e50b8031400c070312020b00408050600c4000407003420382d034001a51400e41d001c65458040749542215a510b030002070a1029102d03020f044020300500300f0502c0240e03802e10600c207070321980b030402030745000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 616192050 1250 616190800 616190803
    0x30510050102011a040c020708030318060702190f0c08060406050f0115141b030409020d0f180f0201020f0f0703290c0c120708070201350621071502 65
    0x100f11001e00121032400050f0018202500304800041e80c0b401190042580c0b89d11107880c0d50300481e00c41c0446541c11600c512116401e0022a400030418402007070440450034000206c2090503100514a6500500b20701c02c00000b040744000a0030040705442d400e20b82400e0480142100f00c80040100082c880041107260140880d0415001d859442d100700d030b01e0080c85860b96501100400941c511216240340c04080d0800090015021800380580c50f40f600b040c030320003511020200054440d08000040801c201624032006450f500100c00404000b03035400140d0504a1007000c40710180586030028800d12400a8890116480740398440c1010282054516406180c583d03400c00e01850b19010a9040d03c0030000303041035000d0706054600c0019001c2c00e405240c0e11a49007290f44031804101c41d0213540c0c0010038422040100c18403550a00c2e02c1844100c110a41510004060740003040460219154281c8003603440d81103080705030a0601d2107840c1ca40e9500c1c0e42c411144801520224109400d10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 616193300 1250 616192050 616192061
    0x51501030c050d0506030c0d051f18030318080c0a020f0906010e15160c08011d0c06070c0305010606030519090209040b09210901090807080c190b03010603051005010201 74
    0x1202e07580d140c00c2081415104001d42009080c180d85403003202c4904820b5500c1e07034003036a070f081d120300001c001d85000390300218040e060341d5081030885850003268035000d81403011100003103541454009a646420406c1403a10304a8900241403d200861400d0300d0360070005041810900845007099007e540c0805c10484210855000f800580e5041c0710300781604103860701a280819240440d800c01100401800181d0501e606c15a00b45000a00402080070207114080b105c226100c4085091644d802c581a52511104101400b5610000e501010300c03c4600000003e9580311000b40016a0794010090242806940c035500790403440c5040c030041440c51040c3c5400d143d01400101c01661940c80c0c64a040d50000c1621207030380503018101c0054056240e2101c06c41901c170801e01d448200001c0010145101c9d5002a0129846124280100800011010b65101c0c08948080e131021058040f480c802c5150362115020006c08000462000e81540255103e51100c60403100c0345592180124207035903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 616194550 1250 616193300 616193321
    0x3908190504031112040b1803121c0b030613170f040b0408060105060304261c0c0801060903030e0f0609030a06050604180b13084b031618030605150103 66
    0x22405c019200d8594071f20b01c0e1200d4807a0f030003426180e501c4607040910072598060840400c0700c0301a2000311030101800c0c8201c800103441503004001030300d13113202140c000002e103210240102000032495581004c0c454102c4d405100c800b0003413034880b0b546015071525038005000f094220301a1200119a605119050320f104640003454440d5610f07051500d4544100c912000b001540010083e10200018040e41d2086d456050300c00000c4410282c10001c102d0041a0011020803040540420100707034014807542040300110340f5060005550340010b241882048640f940500424000f0000e01076947d01c80d5105800a5034188800000c6000c1d504604601010081080c2c0c40200400c00c0e0622014000300c80728411000d05140c07000154041e0301d0005580c00d04581c401b1187c3c1004401d000c0345a0b035940200a2040d5020b01d051100300c1c1031003d02005000000ca0030b054807041c25414410021032002201c842e03010f030302042c0c0300e0900d400540000c440e50a1040100741002c2d0565202c1d00c103444241 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 616195800 1250 616194550 616194569
    0x512091503040602070609050604050d110d0315080106080609120a082403010f0207030311040e010302060d140112030e0108060a231003390819050403111204 69
    0x4500e0302014255500090001d9034890341c24000e100005ea141c0c407501c01c1a601440c02800c08c3d240605c1c2251800c1503500380c840801c0352284120b114220700088550900c034890401050032000b050740c0700c010a40c254000d0300c0541c01c0078000541c10340c011071035030f0081030700a003a9030340c103c041000000709129465950000460160009081c0b201100c424820710b48400d101400120b01c0c1c1380000d0070b5800301800d82c024203500040800405815200d1a02c0000d00c050b8010308080c6031030341e5010350310320520004e40030301000a5040d03000d81690384110802248440c1403000c41d45c680046d01c803400340410f03044001c540b0541080e52075600540d0b842d845a20010700002d101760425041250b5110313401c01d510070320006140444015a1104900001800e040d43e00184100490717100d40045a11a14051341941244144010713010886500154001e07550034074802589520000b040f00101e43c1c6109000c040c50041070104060f40100494038098146c030444c1c200c84881c4100c020244900d121f41000c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 616197050 1250 616195800 616195819
    0x1503010803070314070606060206150a0e060d050a12030b0f0301025d012102041e09050c09011d040212030c0a03080a0c08040201020307110301060b070f051209 70
    0x1d10694950107204d000c0e010701401c148140e525030040d50900d800200258101004204006158031500c9070040c200719140403840d8036100b0104c01540c005072810f809513010206960a2140c1000b0135001d0743e900c4040c203541c607031000e24000c00500203c01304600c11b00a0700b075886060310b030500075200d09860301c03003400802445840c805082e038581c082c4070721503140001321a43c0018400050044807241c00422255001c0242000d00c141c0c511705030401d81c0100e48481511402031507018540c00c40c1c1d9415035002170312039206009411030250300960002141e051021210800a01051080c51800d00b640d40d440c0070303620360701c09000c4081003034440c2145040300c1c00040d01620b05165404042112001640d03d45104c40b6946401c11405460650200300038005008003603105200344854507681d4030b031117001400c15900003520307881a500e01500300130449540d40705683d42980034000910381082c00700d60b01d4a0b1458881d80c000c80001c02501d00d8010010300b90509e01440045403003025004110811 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 616198300 1250 616197050 616197053
    0x3091b040b0603061014040b191103180a0f06030e01110a140f1216020c01030606091202030c030d0e18040201090b07113106050609040207060e030f09150301080307 72
    0x1a0b0140c17400d40f0104441c0f00304414044031000002d2020384030721504541da0f00201a10809030350b01022400003000f0415072120400358000c400c0d10041550700e8001380f0311030f80346000180002e442d50082c0c000b8052545001815941541c002e11800040400078403200410b4400c000e014083c4480850100c0e0300c1d081d500341c104102a00605804a9019220303003090511401707280c0941c01140c6c0c030040681d00000351000c50b50100803800c48c1810920307084c00b0359820010010010301d020301c41d444010107003880d401c1c11550140306100d074400700035045441c00e00404400424442c100c925039406840c031505500940b400003807070203100c1c640684a00426601d4980e2201e0907922584055945107110303022400e1603550410040003110b40d070b6101e4001141951070030780d26040b1103814110500d01d040340c204080d44840040d0781200b0002c0740c0058960400e41803200191201203081e0009020020f01c9103080d08210010304004141540c00300b09051040e00e0800c0d09200c28050960b450303005205180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 616199550 1250 616198300 616198309
    0x1912140108060f090d30050612241302030f01020409140105033309070914060120030f04300b0a0c1106100303030c0f1e02030f03091b040b060306 64
    0x8440020800c80740c8441c0554030022800c0070103401141b407907200d2051151314544144d120300f501d030301c0c4400b03800050300c101c8071503095a8059150801c03c0c24101e0000b4248400d108481c02d2150b0003400369050413002e0007040d8000e511a00486a00c3c5142a408013500745a912613107058a8014005117800d190403600c6404400c002c01040c451780d1202c62014844070108200d8134014059400207001a0f41480c900c2c2043d6407981004c218002000020844140c2c0e100d58082c0089640d000c1e44502e4005140030030b401c61280c40003865603010700140010b000c90202080c00541ca82e0b6107d6141c4030b00380c1e241c1c540e1038a07955000c0503120182580214909401c294030030702c013080e01424400070500c1060368160401d142150707021542c03075404204009054040c010b00210b811203252184012105e4000546101d040e0f106003a02001400c0d5541d00c2107008104840507050b60000007070301e92400f404250707940d0318510b05294240c10760a030341c03406a09050040d100f0a00000300b519045030341c0c000612 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 616200800 1250 616199550 616199567
    0x1e0c0d090c030c080c120c090702031306051c0519020f21071101060f06140d15030c0501030c05070b07170723040b1912140108060f090d 60
    0x580016500c0316203400044060803104011481000c40140c0945400e84050502c071505000078003403200f180803504100c2e40130400e103030b5202d411152190780b9103c03880100c0c41c41c000c008104080520101c4041a25a0050060000740d8100ba02d4501414030302401c46082d02c0301074038001d00940d8406c001029108180d00a480100c0e5004400b40c1400c0c0d06800040801407118010b130020300d9581c052244040d88240864400380f0400000c3c4400d5240a490400d8046a4847c00b02080703010351010340030303070001000c8030780301c140c0300c44284035050b02c9001d03051710011144011a0f100d40d40190000301c030350017800303004a40080c035210301d82009035a45881004040080809040000c504052801526000c9071640103603003d0b0344000310400000c81c5100e032030002484c03030031001e541803100708940091030b003c4401200b03003009608404514610255003c514a070090a602810a1410700d9030700c0080003900d041301c1c00e00040714945d0320390280c0c880301c0303c0c03050318400380b980c00860001d600c450140040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 616202050 1250 616200800 616200817
    0x10f030b03010f02090111120904090503070f11010206071e0e010e03060703150b1602010e01090b030a021c090510230412030507080907290a030f051e0c 67
    0x45200c0812a0009007110a40301031801200d60210740c0d9012540d1041020b5a40e444010080c00c5100c0b521106200c2402141d1065200355210803400041060030304c107640405031702003a0700c008100940350919201041300e040b580144204000101100e204610003a24102c420074621803408a0cc00100c40d0f107260140703444d0500188280110035130b01c0c1000b00c94454030351540d000824590b5014031046021407036200400003402070005901030710100460303150988c0c1c24204400142d16850040c0e40c0c1da0b98551045000d60300100c00c10a009141da0001c0002d144009102640c000081d200c180840e000381c080500298092040800200016400504c0400c3c00009150701400011002d0a41100803142100c00358034443c408042c0382e070140180754120909040007070302c0d40781003100303159154040d11071001e40c2a10b084100b415030804018444c512143c00c2c4105030b0700c101000c03014019000743d4440c21102131520000540030030494180c03a0018000511401d89500c0d5001c5a20396600003941 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 616203300 1250 616202050 616202057
    0x103060b0a0f0303080a110c061902090102030f0d11031305070f060e0915040606031b050a1e05090904080a080105010519051c02070b0109060f03080f07031101020d0905120a0e010f 79
    0x1e403c1f21844408040c00c000340e40d101c0201001c1c80c03c0b106600000700b060f0540e81d8880c3c01070008007903070f0307070084181c83c0801402110241c8440c81840b0071005002c54040406d83e0450000510641003403040d41000014007907000c403451184d4490103000702c4041b901c2070307600244864104104510708211483d40220b20035045250748414240018125000d5501070400b29984981400d9411014006d02c51f0082944c1015418114200f00151903115007035480d903841c076003c1300040e2105003d0026078850500c0540380c404d0b18501854103025a80c80040d040703011500716030000680d50300c10011242c121414080c0701101810098050f180d6800690f890010901c9025505103011801e00c05089038902a171129800e80d45440000d00484005411415001c070b00c0280c18070220b11424110740c1001402d0070700c15520409418125210500310f58400c405500000308803c803000f03d60030034105903001d0010341c2e40305882820301c4020b51094020007400b02c1d1058000e07603007940c0200f030058409015800c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 616204550 1250 616203300 616203311
    0x204020309100c05091e0d080d1803050301090f050124090305060a060e070503070e09191d0c0f1f3c020f07030602130f0e0103060b0a0f0303080a 64
    0x1154036058800082441c0002400070410101d50b18010282c0100d200044030200c00842074400451083d010610001c1c02a10000622100382515039024ad12440070310080c05202441525004001c0e84c0b0038824545c0c2c40d41000040c000ca45058846c0724101da541c001800801c10001c42d9064564001c0b510103414850f02d020000085101404600c1c030902160b4000100e0741c0c28044080010003001d04134004020041c0100142e103604402c00c1c2101403002c4400300c12079500c0c0d40541c2100a078003041000200d0801180812426400704004900c3e20103409446400c448201441001c059001c41281d103e481486e20400c00000031032071584000f01440c026180b003101d101140c1d00b10b1102141d03944021102002011144032441c0c0185112400c0c2c4003420841d80518812941d410b000d02020300745a900103000034104042c82c90f10b038018030140d8807140501c5e5680d424900d880000348420b61b40c42d403c0c01d950200619003100c5034000d50b0005182b095100703045460072100c00c0c5009210941450b60340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 616205800 1250 616204550 616204573
    0x6080c240912060f100e010e0a0e0d030b1201110415050702100e01090b03010b122e0509060d0503190e040216140f0d080c0910170f040f0204020309 65
    0x1040d10b202000a9000030809410300c40040482000000d081c1e54000300400e4040c428966050140c81c1111103092140445072203940d2141d00900582c0d15400091195083d078060321901900448018581214800341074010403a50368284c0700c0e010144820003a0070002071120b001481d1101d4008001803400b2400e20781554080f46043d20440400070200d18034034852201c56a002e02001c01512500e8a8a8110351600e5440c1c1118040d083d01a00648006030000d4942190300712000c0041140e46d416071102c84804486141298150044a00510111002034400d0401064485110380c0c00402545044014000da01417000c405503030710100800704403080440d5850340040d1141c1d240c45c485415101100f0318207810103c8841c0d0480c012504480278004840c4008680411082d6481c188031a031651100134101240c481c45c1011076000c84030000e21121503602194003400d040e64401c1079102c98541001c14111001d040710010424807150101000600703080d005160000c107440700311550482c44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 616207050 1250 616205800 616205809
    0x170d110102070618060b01030b01050304020607020d150f0e060601140a090302060f0d0e010903020601091a03010203010e01061d13020711031e010c030902092215060906080c2409 78
    0x1c0b90101c4d402c0910800400900c16940f1034144a00403d080401210b0003040000c3c0050000500280c41800e011521109546941511220321540a120469905511411040101001e403540c0e18a180740410fa2074011200190460055005840b1542d4001d2040310f03d64403a4170035003e410810520340e0700000184c490350040d1440c501c0d0700401b1521011a04209011502c80c82c4030b07401e07203032b04015000c00400d4000c80c4540c1940c3e014080482d40d03164441c00004004000310a541e0550301c00000000d201c603120010506803251640d616500300b4001c45209007000902c101d05070300040b0700c40c3c0c00c3d8011070781e5402401800d10800c0710001c1d000310200003d040000f488000c46001c95150840040da000070320815109a01c90301b030800c200d51076034001c00c54481c3d0007041e10b2104240e5030741500c00130344c03500c0c51400300300e6204031040703101c1c2d00081101e405000c403407003021003550406a010640c260045150700700b814001e01540c0740350017500d05608400f110070b40d08001c01c080400445009495 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 616208300 1250 616207050 616207061
    0x504030516050a173c070c0e0112030f0305060a030f05060603100212010306110702030d032307080a0504060f090501061701150303030c020129010801170d1101020706 73
    0x208003403e0758060b43d0400540c2c100c2200700300702040e0380802c2914007100b00395881e04450504140d01c0030081394401c082c82540f950184041070704c4240410568104400d846039542520b610f50320300c1507030740d0b641d2052500c41d111246004011640400d9101c558038865407100e9884000184545401a40c903207465030700510304241a0303943d800400420240341410401d00d101c0007055082103180c622981e0880301440410f0100a1016440baa00ca245609105050b40e03082a00101950010080c0c0c01e0050010440e22105600c0c09422400052554410ba41920300c10340c119203940c0001e9840007440d00081200a0003110242d03500c03060b41d40d0300400c0b807241d21a01c501c1200001442030a01d001882c00421042102e4416810265aa0a0340120540240482e0360604020134100300402c01070f800740100b00540c01d40407200c80d01407031056003a102840c5100c0310a0321000a5030340c0700e0000d00e104c5001050808401d601c00221000b4041c462200202154501c900050501010350b0f9100141e48 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 616209550 1250 616208300 616208303
    0xa03080d060806100302010e061b0303160e0904110d0611040501090506070804060c0602090913060c020607021e2a132702030c10080910060503030d0504030516 70
    0x1046040e1036404a22900016001e0803004100920f040855100d0345400c5000c0241040401d1843d64142c0d10f402c000c2d13a03404440c14a1604400c40c0d0141c01070380e01c1c0c004071040091303640d0384c20343c58a03201e015508590020802030003501503a500c9480e54104200390200094001803c1800721000c03c926114074844200001e01099545141c100010209580b580040d48241d01c100711850008810008503000c51b406400d01410040c02030a20074000d000324102a500140f280381000280440b843c1c050304218419441000a00110b0070220f944610885054000d6404032200c01e907840f142410546005080c501203400e51850000c0f51450840c51040c1c5002d440c0d4000c0c484c1400380340040300c801d0078142a002c00c0015489924078850036203104945404038607000a803039015900c0a0118100d9507e0140000c05600400305000b01407010448113686e0310302501541b02031407401801918111640103000b1400e000c12070f013810b001400060800c80500204100942280c0440c000107601c49 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 616210800 1250 616209550 616209563
    0x10b0307210b1806100e010507060204090f06090905060403030b1203040906081e03030c34111504050405060d1406040201090b0306090a11130f0305010e1c08060d020a03 74
    0x24140b0800e015142c0708048500201070019010024182c4510001d25240302983c80c05414010244005031007d11400c140036044900024001c0b81140154202c0c000710307500c0d1078080142907542c0300d001c0f04858504600400580201c0701040c0880d209800022620300c00808030030400c40c0095440b0301e1903200d03521074020103441c1d202c00c211505c014002c0c0140c4c48002d90703030080d507007060760302807501e900c401440d6012210700450429940b862601c0160a03d40600e5001c0d43c000c0c8030034039441e18500c0108022510100510310040c16420b003503420015450350350f00001d080c40d0501007000b01800340106040d070801551008440840d000603c001400900d80300504028102400010030302c0c0d55a8100c0d5151784020000d20403a62124490365034800000c80e0002010100070f00e80b55a184100c24590094424281c0c1c023194098200e6100000c807445080200690180180c66585412808903955201003041d00201040ca0041850540c0014010041c40710196640c2c00201100300a0704280c804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 616212050 1250 616210800 616210811
    0x160318091a0406080316030f05130905060306060f0310051306020406050408010b03060411010507050703080d0605010201290613050d030f080a0e0c06130f081f14010b030721 76
    0xda0070b040c40b80c04007809071840610b181922002240303241c40c0d601701001307041000c80e11006c0c030000d101d08166404003403410f051002c0c031955411004041c060540318688640500c0c8089501468120040c0001860103400380031500700341c0b070320480285030040c90103d100320403045070000195244020320140500341c5490b5100c40c00c1c4402c0d03908541100d40d68500951004003484045240341c100700c03d0340d50b17091810940d5840030340b41040c1090310580c0300404005002c2200104d8028607007109041e144203900030001c1c090503101885601c030f02004040e40007204034842c40701030b041c0325000f070038554039545100302d02680e40d1003c2620115806000c2d00024003082c0e00784485035105080940009036201f084c00f20040c00440b035512000140c0040c3d100305000242c40c4541081190004024400a01000581039a407031903151221501daa4108401c07060b040b144182074528416210041c0c10401746085503800d0500019a9030300c06402203050041c0b1940e010b031289000d8130403064180f00e001c8041072 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 616213300 1250 616212050 616212101
    0x21903050a02070b07052d100c110a120e010c08031009140609010603180f051c1103040501030902040906020313020a0923040f15060f090216031809 65
    0x149440e0350890703480700d00200029400300c0d40001d42c0768408100104c0b40b441e01d4001c2010010707180d400b41da00c0442d901411823603600d0542541d1000180b044151204410310454100091700c50002c1040101805040c0302d816003503e00c14918440020410304294a05250580354809e581d003084400c0903100b15039900c01c1c0400c0050f030040a0740042d00030040c400a061030000074a004074140142010581d40340060718280e420000000101c43d00684490142c401ea420081d0320b030002c0d104e40c00c0718400c543c40c0312002240b140380d40a2103000e41002640c2404d080400443c0078050070181607038010b88400f40f100c04100140f0003075004070400b92034481591fa6900c14000e21144c158040c5070310900d4114840c0a48400c41e069004100c2c40c82424030f415511442d0655020580e010702400392494006207404081a0ba071040c01610300541d100090913595580441c140c0c8142840300038415081d03031204000a000fa120034210b101a00d00d12860662980c90074000c807280c100b84c4070340e4100c14454443c2c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 616214550 1250 616213300 616213303
    0x120106030c0302072118030b0103051603120f1701120c050103020306060a1b1211060a05010f050d0302010b04050a0c080c1806070602040503010504060c031a0907030c021903050a02 79
    0x8110750301ca0070290300341907841e00c940818031006890101c80485440540d07105600c01c9072042c0c4207010300d0404205294803401e01c0d9650340c0c0d0901003102d4501c5044885260a99603154803011640d00011126006c285003104507a900704062540c07007406550700302030f00c1c802c1c580c1c113006010b0100b80c2c0010100c1822403c22140c610910303401f1906061040003400203035103d00044403849042403c0050010a500000c06c01e01000c2e030380050018a035103144415241e5103c0c0c541004030b59040b048820540303818180400302c400c288224000f5050188041005050031100000c10502a000006070b0b201d421010a05940084400344402566124100e0394190403403152504450a0304080b4244070451a51101c4040700b016054805c0c03102042d2202002560b4045030090b00026000740140d0900b880d03c50080c1c1007015000002c68285100c0031014041c0d451128519500200300501d1500c2c1c413541600106851203a840460042d54000005d544450305004000d82c440d03503616548269208009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 616215800 1250 616214550 616214561
    0x1f0c0c0e040201120e190305090603010329010f0e04050f0d020616054906030b06090f0c030a0603081201060306052413180c030b030a02010c1e0812010603 68
    0x4c940c0c80d080754020301c2000025243c1c2c030404403034440088804603090a403858040e107190240c3c080340020011040141f044150382e0402d14041458050302e85006a107400c1040034042c503100c2d00300050302042000109560150010b0250040d600003041c040d142c0d43c182006002d0600c05070340036206010350483c81054080348816185400d43c240340940e94100b0905c1e42d042e0003101c5500505111201c1c000c031a50884444c0f04107468400c86070840c004814001d0300e407034403040d54100b200d00001030b514101031840500c203440c012914040c0b0303030f2496020032540e0006020400201e58400b80803001941a4004210311403c421050546d585004c03001030a413a49a045980102c03032211101c48110450240801c506104840c15034403543d0b8004500507441090f4050200c0c1c180e01c48a050310110030764002c41241001c0c1c0d9041c0107104a60f4185aa90440d000000703000070510070300000441e401404031150813010020701c4104582a4695403101c0d000326104560003c000c4004001e82c82e00352041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 616217050 1250 616215800 616215827
    0x1804140f0114060d050f030c0a02130605090a05090f030d050a06090608190615180501141305060f060a0503100f12080a1202040902070b0f01051f0c0c0e040201 70
    0x3403000c44507040488100490160040e4001c450070300c00041006400c6c002240a444502c048076110600c1d60304455440340d50400c01d0380918500b5040f50000c04060180c8001d980c0050254521502d03200e80407801041c0003060400300c0e025044002d030b0303c210180020031580341d05000104003400c045414004036a1144d0042580034607001d0108811500031640761801c001d41d844540002105041c402c02411180c3c403045240e4503010000300d1804042001102004d140c8501000640e8030791500c100070380c44c803000b0f655004003203a840c000c04000303640025034040806804410644e9120f80415429045508a0000b08401008101174080000c1c02c2e43c00526030006044404c0303280503503480b05c1203503110307001c0c00502000510418150082c401d5041c41d024442046555940c1c80b05100025004103c003119172218070004960031404c3c07091028107a0724020401d40c2921000a100e9540480caa00c03d82e0074003801201a90202d02074022100091602000852181c9440e02c001880303081000e82 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 616218300 1250 616217050 616217053
    0x1e01080d0e060c120c01060f030c17211c02030408030603101103070327050f0c0105131403070e280903080f1803030103050f0c030307050a020d021804140f 68
    0x41e841410700054440d03142d45070711100170341d6803001d00076041c0501304542190390344803005440003041000806d10001107900c82a020454440c2c40c62115444041c04641c0c41c440d5404944016880000c00c0d0003003034070103525020300310510604003000050b600215000c3c4c2d0302e07410101c100003d6040901c01d4030320f00a2288010000459480740182d41804050510020107903600c440801030f5808000c6c01100c004030b0016080515100d1400700e030303115040812801d007400751030030080b0740b54043d20568246c0c41030780c500c40340014207054503103003180340201c0c2c0c295041c0700309000040c28418056025004070300e211020702c0014800d00000c0d0511001d4007840e10200d180000c80000300e0780c040f4105400c042e0b80842d010140c2c40700700d204c0b141d20304450b036030307503418000080000100403000806059080f00582501c00f414602002c041e200c3c000c0c444058160303003102c66030000500c0c0c4409080390f074502c000c1c588581101d01003201100340c0011102201c0c650488100e0a071400c00420500000025420 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 616219550 1250 616218300 616218307
    0xd09060207060203120a0b06160c08010b01080105060307020721120e0d060510090c020a050c03030307021c141b070e150f150a080714031e1e01080d0e06 67
    0x8000d40e00e05c00e804582c1d90241ca8000402d900e003000f904201140d0000030714003a11040340355903443c0c2541d101403045942c40083c0000160ba10418046c0b80c1c0001016180c0711171680c6031a0a003d01a44000d02800445c01141d6000c00e40041940300304821141160907a1000d83c0c0705d00d000d4902d2550080003030241f0868240e1211503a4520412030102640080b0110b507a03111020b1140a42002e500241402782c2010800106250300090f0076201c603000318101c0d100c00395031609043e1284410f8a1440c01600b003080985458a20240000c0d1400a1807038540c908001e1001050099000058024600844c420100780a2541000902c010f0f0400500765402803c1c43c04410000c1c11207001d80724010a100000390399259680840c1905e80400c01c441c0a584401340c071170080103094100d4088000c1014502d8094100e00b5081c19688100a1400d81000540e0124001c0030700001c01814000801c1240420500c0c040300a40b66900030040b600003420500601a005454405804003a5014800a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 616220800 1250 616219550 616219559
    0x6090a0c080c0a05061608040b070512090303090904030903020307061e02010605060d0f11121602030309030313080d110309010b01030905070905060105070b04030206040b060405040c0302060906070b01080d09060207 94
    0xa483ca40120b601c01c40300940da60a54121101c003070750702410050400341c00030a000070309104140c0202641e42c0b017681a50032040b100c5a410f00140030781c85103030390168824080e20640b401d001d103035150001d0180c00c00182490390f0743c0c0081d2820f42e1503000040040c01240002030f40026039420220082d02c41e0009110031814180492007034024201a14409503d88c6c2d0a03c3c2d40951740e61000010308d46146000d9541d001024040f4401e142c25910301e040480c0601c0184812071010056074003c04d0700001461964803258140808400018002e1790f4000c4100200003d14070716100c1d240711154003c0d1401c2d180c0c5840706c5d185084a10501240f070615050040c01c20000c0c6002c501c4d0310603511031250025542c0c603100012106806400402468941d01c0c006200c180340e00040d0329882248140e4200f0131980e16803052106070784099400409940b000c6405000510b450405015404005001a0306007a4503846402a81cac0003a070041489030810304c0309403030301c0d0b500800740d0000e081140014444180340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 616222050 1250 616220800 616220809
    0x7020d031d07030c050117010f091a06070506011712040e090313030503121003021c140109110907050304051009050c0603012c070c021309020306090a0c080c 69
    0x196841508050340c0c0c0c0544400c0100d0074034105204414481210809610303854000b40c1004503018442c04119942c3c01c4000440102c01254161100d030b800f40d0000c94500384022001c1c1400c101c002c4030350068034407228060b442c0c3c08007404050380120014031a1f54580207a00a25007900c494000454021400081900c00f4207011038089078110090a8000da454641341404c50199100144910500407030000520500201030b1014503082c2080300240d440d00c0811054840e664800207401601c010051984402103120320001c0358002c2d0941b0350550301a962090840c3ca1000c000c0351039041e40707445104107003400303410a54848828101580340d400c0a8440300d5a07603041c81841c02d16207446040040c10488103100900f001e6801030051501d80d6100c0c2000c4021103948141104810883c01e0310a103008040451180140b0464503401c465100c5a028001c5414581c17180c80d0740301c0c1c0c5a0700a2700043e00c2c108441d5110b1444c00000e800201c20300d00d82841000403c2e841003005a10600300c0c02c850750b44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 616223300 1250 616222050 616222063
    0x607030e0f0a12030e1507051011130b0d06030b01080703140c06090d0512040e0a1505011b06140703021e070209010b16061407230304080702150c031902060702 70
    0x1090b017841050300000400282d008aa81c081009203110b01040032003c01100052400503002440d50600c50500b0310101c1d95a45e008186000013003080b90741040050700d94190003820a06021000414800c3d1a80c031516054002070b0320403410303640100c0d0100240480c581d014100c40034041d0260a425485000107070081c050085070600c240d41e4000054108507042201ca100e0b00860304401d5110703659101c042c0c0c101102101d4058159040410203246080513084072010780b54142c42e000d00041551900000b0909940000c65006a58110484802816604031480b030f01c21643c000d65141040306042c0484041c60b541d503120200300348080700042c1d480c8000c0038103581303070104450b0301c03960340495000f154000058040c0c105480c0411800a402d0100c607124820001610380340021200b81c041c10b600d0202150541804050500c04600002c541ca801080072500090604c01401c0f502e082c200300b541c3c00300c01d02081a03031002880f082ca800c440c003000d400e031a03454000f612861800e100017030f44510313 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 616224550 1250 616223300 616223303
    0x801030b061c120509010818060c0d2c01060f03170d090b0f0105190602031917100915030302101d162d031203020403020607030e0f0a12 60
    0x32814140c60010310641602102e1250424640b803404560540040d14039031103910490700040300d400004001a0742e4000c440700581d60017004000070f65a4003c6407a0940005461440540d04c1d00c2c0c1d9000441c11503a420304c112048080c2c0101c003070703580303800460844030b2652014210380e114880400100d040344981035819080c28244075a40c40c0582940b000900c00d68000602001c150b80c144071414081541c40750584105460b4060f4800c0c804035680421704451040f0001a40304018040d01071840d440c480c1b80601d0a810850000004012155005171040720001e0030f41314402d0003000408428000c420481d050000b06031042810740d00c00075221386003507d103a82503c1d200c000115502811000c1842c1c00d0300303d902514113020949045c1c50504607035104000b1090480b42e407480d203811a41120144000c40780b10082c0400781b07076544954246030005140e0003031650038880000035842e54001402c20b40e2081c0c4d40d1500001a8104110409540c0c4100a02548000308280503900b140f0076062541c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 616225800 1250 616224550 616224559
    0xe0a0915021303020402041502211b1e0f0c041b0804020a0b18130e0d0809010e33060f01030b040b040207051606080f0103020d0311070b0406030c0801030b06 69
    0x11081d02442c140c1c0e02c1519480250041d10001e000500c0c15041c2080c805900d143e40e003950400041d0300540e5a030442081010200070b0010800100e80415010200740641c90000036074800001c00b08e0320302d41401c4140d02c54600741d040128255181c1000b0f10825503e00411901000b10445001c4032201012114006409121450000c24190b6071200421801081000741d0365613a01c4413070000c0a01c030f4400b0031540c0e0003000c20384450302090516008848201d11303030030024090401d2403078040b03c480300003a042540c00d5503580c0d0398002e2481e0a0000c5103071001c045a261081d9201c100c1c138000311400700b041c41050314900406000b043c1c4e8404022200d0303500d0910703002c0b5122007200f000900405038400c011b40d029100042c02c00400002180340c0321000e200481a03035400e0380e25072003a514038004a031100354032040c0c0300051006180140807000214024600100c1544000310b40a1504902d80c01004050001040070000903615008142002c2084c2c5044d00322035242d9911120081c0e030182166104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 616227050 1250 616225800 616225807
    0x307020d11031614010c090e04060b15042301110709020f13030605010911030903031b040e15090133030221151206070305060111030c0303010e0a091502 67
    0x901e80200107075800310003041034400035040b142c68810311601c00c0c0100e004085d42415501c290f114001c080c0b0030200d40107103587c141c003640c556841e000244005c41e00c3c107611402282c4400340761460b003c0a40042c000c801b100303480716200d1440b0301c00309002508005040000741d400031710a04d000441e0250860340300c08400340c0c40d06030311246107030030b405045001c0701241d02d0885e0000c01d00a498011130704031440000300700481d01898401c401d5511040b20203a0b60340e030040002c035000e00c0d155030b0f9000029651300c40c40da04003034803014550000c10342550a400f041103041d8080b00385180c076045590050080c1901c941e070f00006002e2600c0411014a003c404107914006003c08860086d011502c036680003441c02e40c2650b2581401800502059541d40b1151502c00c490341c02c203003400c809910989001c43c00038025036035031075001c17000390100814050402403841000210400100094441d0031110805103031a581060000c003014900180b64800040c1000e00e180e010a103024001c031215803010201594 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 616228300 1250 616227050 616227077
    0x40e24011205071e0e0907050a050a080411060708030a0e01050601020a1e1a04060b04050f0a020d0902030715110613080c0c0303030109020a1d090105060d0608011805060106050307020d 81
    0x70306201020583c0c0c00d00d42c504900d1801d007a4080003905c0d0400b01103400c00303007039103d800d412603045c054440b8810120340c00300802c40109024032a0036034800e03c40d80440c040d420340d0340007141442e040148115250900130061010031209401800d551081e10f00081081d0310b02440000d5451950804c003400951003115404800310000100b8005130740c00103600c558070f24000500c150890800c5406030b91f21480c1c803850f01c1c1580782c10b015550150140360303800d4bd45502c4110300c2c04002d602c898604580c5c190740ba5000e90058406104890082503600c001c40c81c20700d81410090722000d403841c00103d454120320b0130020740b40c4090003c3c00d00c20741c0010300580c8030b4001e14400c1d440c1c1a10b2404141e81840301000000b00309006030020b064201e51b80c0e4400307046c84284026090b501050a01c41076103c4043d00c01485a42000300203084171020211000c150640d07a81c42c02400c5070303601d090005189031010822800d200c801c004460040c0070900c1c1c810314514100000a4603690000c0159081045e8048001c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 616229550 1250 616228300 616228307
    0x304050c192309040f02090901090308010512100f06050a0906030f0320011e0c020105070f030f020f070609021002030a02032a150f0a09020d08030c0708040e2401120507 74
    0x41c08140e020307060880c3c038105414107800d002243c40301240304d0324410b0f0004021241c10300800111a80c1522904860390a1070308200078911070080065082c454015148405883c3d4092410000b024200001d82c903400c20051180d00e005540017040c006092240400000e14207130800d480103605880e058103c0034030510001d901d5800200194200c0d828003140114070310710100e40f6010604c1d001400c0107090b42d011026401c0c0e079002c9400c180811000340500b062680203400c03081c03041851340e00052034141541540c803400c1e0000304055030b040356500e05807011810060041d400481c0540000c0d42081c2180e0030003950791007034826a420352825441c0b001d41124107480516907003003100c41958098910140701a244000848241d04641c8040d0b002c510401010310485d542e003a00a804164240c00984803102d481c1d0000d0034804200704204424404116418013070000303003400c0020880d0500380003140b03003015107004440d26414101c00c2c00700321050381c00c454000d8203148456400b14140d41c1d00d41081d03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 616230800 1250 616229550 616229609
    0x604020d0b03030a1d0d050d0806032a0a060503061c020307050913020a09050603070b07110d05101b08011e03241404020a18061206020304050c19 64
    0x1c1d00b40c4004512441e01d80d8001c0744406183d424015442d81c40c498071405c00041b00550301d4042c00030781000d12180c00840c0b0580303c3c2030780850041d003281d080007101041036401d0b108044203410181d9010115190504c0c1c00d8444000412203841c0c0241141854000511120b22810a0084660658801c0760854400b48807000003041e00500c80020761030060603c84941084050480c1f144480a80111740c03140c0600c54ac41c081e00c1c0c040d0003015600e041606550301640840d600b41e4a00750702c1818194296910400c8905042c420405800c01d0b191080451065508100c149085400c02200c1d06094030b5200e5078540c110b802040c0c02c09011b82041d1641403041728503810180000e2160f40a0910060700c0c8207540107480016a002c000b90010304011048904040d100294003074807041080200c0140030071885c2d07000c4000311000078801da4642e0b200c01c0c0d02d1810307501101d100c1d0300802084280701c000e0203121402d02d005d460350140300c4183c0410a100c000f50b8000d40605801448001c410b249542100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 616232050 1250 616230800 616230821
    0x60809010b04060b0918250201060305060117060f090307080726270904020d0c0b0c060103030e040b0a05011112070506160c0f0609030c0501050f0f01060201020408060604020d 77
    0x402c003d40c0c031210030341c4541d401840c0650040c17820040e0100f000002c07a1480e0f01c2800020040785c9504440c2030854001d01101107100210364a4a401001183d824005c0a0080003050803840c45060341c4003509080c031600900f01404080060100040c0140100483c0c4295501882141e50b461292400404c01a84a140c00d2030000d1001942240070010000078a0304004440e00c221440a40290401c81e2900d5901d9054224104201003001400c101200202c5a486440804205615008203801a400894055289a1091b4010020f040d000548541070140c244c038103200c80c4100b1408251200140d00c0b1b0b00b1304003e41458034125130303001403090f0741c08035103140328042c0d40b942c1d0f40c20100e5503188141d80d00c0f081e142c0052001c1481320f01806904004540c0a00e03410b031200d40301d4581000401d00da44042c4c003402401011900003034420f05c501845001d41c180b03440440d05000b4000344282005070081000d42e8030411003071155450000381168030290485015a483c0450a040c90140c0b58000300c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 616233300 1250 616232050 616232059
    0x903182214220309182702010e0a052d060703050d06062307032003071101020f07031704030c0b04140d0b04020105160b011706180304060809010b 64
    0xc0e10100d03000d400312140600c09200460032480080c00d0300301052505042e00901086180000700300c3c8600c031002c8200801000744000544400fa9407070342c40c00c1c4070380c441d000c509882d030781d4413010445da00034502c01d45200e010b649000380325083c4030110f0000b00005500c0c0c44e07599180380a400c0800a082252905110050040c64807980b2600d4094002c1e08802c1d05140d2240c2810000b090700d0f03225007501c1c11010700700d0b0320220700c02001040748021071780000700550403c0142c5d04040401c1e00c0c88584000c03140111002195601140d00780f80300591401c40741d150443d003100d11006249080000c1440903240c2002088900311001d10030a0b07090b03c219070008001d24260000010010442005481110074450401c00c6481c896420051062071003d0020034041454001c10055403240000d44107100304c094400d217080400740c550310400c2009a010075202d400050741124001424800e0a070410480301e01403122105250107241c480c01140201420002c2c2a4000388900d4000d400c0112400310180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 616234550 1250 616233300 616233311
    0x302100810030c320102031b0a051204140a080606040b030106120804060f05070c180f051005031e060403080601020a0b040b060406060e0102060109020d0e060c03090609031822 77
    0x129080f4201385401402c9a030300002c9400041904002904000c500705a000c3e41c0340104101402c0c1c1c1c0c0c151100281905480380c0c0000c0c00c0010010000c4820b40400280117a88540c50515aa10144d1070003921501601003c44200280940000d0582d0041c20807035001c2024911200031070300400842c0c0c4143c0110080144420a0040d02c00061056030703401d0380c96134003d0081100170f0743c284c42900c600818150207020104070551102d090f580c08251010300110390f8450901400082d00c0040d0b030111546251590100b040d890200900e10701041c0300e280844080001d181125110000200081d0130302c0003810001c5c0d4160310078400c0280c00b95108408000d01c1c00d141c1422a500700c0112512400b540c81d182c808601c0314050120b821090784143d00425440e0f0a04c101d030006504054921000192030702026000316034240006403003240908241502c0b482d158890300e1800b0703405041c04400342c008000c04103149424078400c00340c1c204191203e80080721122614055a6240025803902500d0503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 616235800 1250 616234550 616234559
    0x240501180c2120031519030f02010807050d0c090905150a05060315100f0f090b0304200301020705060f010509010e01092711030f0d091a070503040602030a1101060302100810030c 78
    0x1448032820501d016900e9a9006e848540203c2070803640c0d020161030035468040d00e60056100c1c2c203456601c541c45251450600645885000c2a104959045404602d55004c00d200b8103140784a115030010403042035645081c3d409001c1500e0307402502031320b8043c041c0000005e0b6070310440000081d6030780020b0083d40f03081401040c0104030b0324075444440000340c0407400f80741c80d40b4801c00e14a400e940ca0745030300340d1444e11240d0303422040055881445114164682c0742101590f400c1c8041c2c980c85014401401040c40c20300840c84100c00141c1005100b0052031006001c0b4486a20b611419299841d4000a80c2901c0c402c0d0510300c0c0802c0c2c1c1044010100500542003007029070710307070307224035803000d50442c8e0740c000568421545800c000341400d400a410640c0c1000400209101d1a1103103409070001071901025032155415075000b42c1040300540d10004007902a42c3e4842500441c00e50613a008024144c1181d0014441030801140320341006860004100801500c030070500055900404510030256503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 616237050 1250 616235800 616235821
    0x60702061303050606040903050a080402011e0c0605090604261c1d0a020907031d070b03070906090b0708071e0b01140306090a240501180c212003 64
    0x100d01080fa050300036000480d526041c24014014081c1c3d250322158141a00e54004803031900c001001641003040c41d50340032240fa06a1010048040616921900862001c3c10070fa015100090108401c070b9012208001c007080650003404160340c0c20041c071900c41d21085268881e03c0c01480b80402c070070030041c0b03071400c00440300758800303105505000d210150503e8102c00c416280c0f07181440107504002c0c04000210070511a070320004c03654540c83c071348501100d26a1121454a04941c2000010003000000d000005800203d10401171815240c840045410704402d043d06016691005101800205244040010038002e03110650f201174128040d09419081800500a081c49481c4001000c00c0541c0c031203040225800d441001030000030926043c0640e07408100d42003d984459130305117140320101d0311071850b0251038000c100e198401d00252428040c0041102e498480101c20b12681c10741000d0700d0846907400c503515100c80ea0300083c41092803241001130b110100f4081c82c2c449000010407000445 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 616238300 1250 616237050 616237087
    0x8040b1306110d0804020f0103110304050102070309080a0f060b041d15100503031917090610091b030b0102010f0e0a0605010f1a0a0207050d050d1413050d0206070206 73
    0x8103681c40d045036800b1031800340e40300d5143c0448100040c01010018016041c0b010120b4420201071500140341c60140f079044032590400d81c0d040300d03d65000100c603418954800c4401018041d070074003a010381240707603849a90a020402000300301ba80c0380c0001c1d41803940d82c0d40c8403101081c2051502100001d460310186e841d400c3d80755490210014540c007240d01020481282c0041d941c01400440c03502040e0002044491350f1b002145040084103c0d0041142080d881c2e5a400340b050003004008900b80340700341008443c007030b41044e501e80780b5061038200040d000781040080114a030400003035096078100100c0c0908481420040390600b050303440fa4101500181aa4000340100300c20040c60b44c8a294402160b000d42c0311703004c121210a000000c41c954001d000b082c10030810300403520700f01d60f91008501c00224050b070980752600488101d501c015004600901043c4d03400405502e060030002a940000605024203401103070707044c40300c40454442d0022101b4164000306038035141c090383c5501c1a203a48 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 616239550 1250 616238300 616238309
    0xf120206100807140f0d17031503060f0a0911042f0403020d03050f070605100501030513200d05030c0d090f0f1a120114030d0905090f0408040b13 64
    0x3808400014100c40103e80d01c0150350584080140010300340040010241600104603841000f2080402c0001c080103094441ca60340e00414648915082c80404080e80c404a03425000e0382141c030402060282c402c060f168040d602000c0010443c0745402c110840c8014442d0302a0003519100c9600c1001a42844170020043d421400c0c4c180074881204840d0680241c4c07100a412440608061001a0080d030190003101000d095440c100302c0ca5407140e90982e001a82c3c2069a40800c403001d0155503810b02455a0242c6640810002c0181c03035917950f0110041050482800070710b010b4625402c1d9202d01081003600d4210040f41c2d203e640c609801a1140380721100400030801c00d0390001041034050354090b0444501000c1051841c0c90302034505580d08400d548101c9a0408224124000f01802c800361702a281140400144c2c01002d002d040c68403030300c0040c00082c450852820095035480d088540d900c864002c0c09250291207600d050415402103404c0b06c0c03091b00c00400c000030741d0401020307402c0844 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 616240800 1250 616239550 616239571
    0x30b18060a051605070507031e0c0306020306040b0603040c0506030c0f030a0507021606020d030903030f14010311030318100309050f06162c0a0503100b120c01021005040f120206 78
    0x8540c030b03510031349151042810043c2190445401040840c0b050306401102c0008001404c0c1d000915a1760075901e00403175002202c03aa9404820b016580c100352161110301c42c41030701d4907440c43c105903c2e1802c0d0485c142c85603502c41c5d48000000707505401c115003501c005034424200b850301d84c2800314a080180c03804448403001441158420381d0300104451425040380c40c2600070b40424050141c046010307200301d80d802d505142d01c2c1c4540f60901000307031042d481c01e582001c1282c403155041d0318042510015500440f40329503c14001070000707038000c02030140003d104403002000000001c0c030603000b40c02c1000300507100c0c0c000c150440755103640104055114031500700203115070041000d0244c84a1950108404c422070f280c50b0b4444100c2d00b910040e8055007401001285181c0d0f5031000a4900600c01092469554a40e03092032a00d04003148042101a80c140c0a0004c9c01030210000b1b54401803052003d03180d036103900c0401d0502c81c40030903d1644581044000e0440708400070065580c0000392100400c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 616242050 1250 616240800 616240831
    0x3390409050a0f020a090915030206030408030601030e2a0d0b0103151b1b03020a0b070c2609190b0a030207030e12030f0c0c031c020d020102040e01030b18060a05 71
    0x38200c00344210740c5c420300030f500c030074a00e01d0030b0104080040540722601c0c3d210700003820010000d0703616040134600c00c911444159503a0b00d1704500040583d148509032070461351100500c101c0c00820f003d4000d500c60300140701803a00c030a41c00002251003600e60350150034a200e01c4004424002a01c00740444c90410407802d0000d12a0302c80c001250f0214040504005203210034000c0018100307500e01d01c0c50900030720446840e07020944070846054800d440060210b4030300000fa0b403c0003281d83c4040300f0303603843e403100c0d89a944500301104060702c941101d0034400d4100e902e01d83c12044c820701021003d0f0400c1403605403036440b085000740c000d602100c001c2c1c0c0032801c2000a4041481c103504600c8180e04c0d043c000d141050401031070704950703402100044409020303003500341c43c0700e803010020b0307102c05000d0340410981c4800c2101c01038200b80c0c2961000c011039004000030300c405820075280f40c0c112a8000e031103003116a82c2d040c0d2030f66074811001c52003625000d002c0500000c420b03190481801405a86051000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 616243300 1250 616242050 616242071
    0x340314090118121a0c0703030b130c230c0715021501060503061c170c250905010b03090a1e02031f06080a020d0b040212120a0305010b03390409050a 65
    0x10458801c0317813002001c540070440303040020b01c00e40000400d5040a415103c900e007000c181e0303d0a58008000180c0014440703d8044400000c030080080c0c440712400d6007503c0c004080c1c6000c3e0322100540503505002c5c448454102e229072081011100f0358643c1e0710541000d58558030014001e900030768049205030300346001c500b401e0400e0340288190742e0788407480d9840c40a4040070340c00103401107403404129000700c1300b5034051130201440c0e04e080c4403408a50301d50043d08050f6071000f1501c040e0070008041c50280200131050b600003aa07007440035000002e102c01d103501060a100102c20a6038007c2d00750154405031440100480c1e0200c4142c003001c2d030144446900c5811055861038a1440a5030190710304111202044003854070907002800580044ca00320107145155203004030091741040718003030005084c00b01540c144500c0f0f000d8040c04803004d10b0341c00e0034a040c0c000485000e02c4907480710720356120142e1a20003030940200010f5419155510350f50764000540040900310f174040440e504102d82001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 616244550 1250 616243300 616243343
    0x10501050a0b0a0e2107080607021c08040f33180314120c1b0a03090303030f0f05070c0b0f0403090e04060e0334031409011812 56
    0x30503500004555403d008011008030b4220080c440003c4d0040c020b00c4111913a8140048213610064406008088030303440d0003041407802c0401054041150440c0e030101c019602c490015142420861070a04101d4543d420300940c05030070440d006001104000c81c800070940102c070f0901c80062141320404500800200e004255901203a400041d0008429440c00090042484607039603420781c82c4c02c03414071191660340086102c0035591010260000f084600c0f0402d210469840b90200110190410390015500034241d540070780001001d064580c0c1c1106d841e801107a014804400e44102d044c0040d0610400103445403900d010261351a1080000041031200a0000340f8000c5a065541442072407822280e2007540c600a402208c00b00c0e10381c5400380b0f10980400240c04199501002c1c3c011110702030991f400180420b09009003680001040e001c04039420040c00c0074924109003889030340300b005500403a00d090a04035448410074030743c3c901042d0040706064844d4450300c6080e100349500c0c080207041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 616245800 1250 616244550 616244569
    0x140f16031e020f09060409020423060d090303020705010603030e030706020c060a0509061c06050f03011e0e0c1c03021624050904090b040c1a07120c02150a0201050105 73
    0x3034038100e040c03600c101801c00c8940d0007800744456000f0000d091001c2e120010303450b90b010364040b444c00c5801040901c0360840034820b502d503540c0301220079041d080340030021070898001c16080ca0541c40e0b07903030315800070725000360115104594042c3c0204540c40e1a407030f02030b094442590300345000b0b200e08540803c3c0280001008014076500900d80e070b080001a01c0108c07129407001c5d00198100c4c20520180300c83d041e08203449000040780904c0445d09a04141c01d000701d4012814139548680e060a801c401441980302c08000e141a0454002c40e98096240e0700030b01e014041030940350010351610b5009001801005c3e00c050b0341c0c6c4a6403d079040040c2519100040e401140917901c101c1c00040c41a41e000b45081100c800c01c0d01c03050070510308106074000068129000c2c0d20056800c101c11004010801c428824010f0103081000b007503c2d0f000018100c80001130042041c010128030503100b0f81a0458015001c5280b6075078000e0080d4a0707521846803c00c007503040749812102541c00c0c803001050038a032003040d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 616247050 1250 616245800 616245821
    0x4050c060a08130c150f02010b1815030337090806010b1c0f0c2a08030c12040305040801050609011a09014d0a03080a140f1603 56
    0x90300015141c580f062068072030104030803500e16110140019900f405101c2d40c00103984217440e4404c82003140c010107401e44080198440c803038901c038488070440700c9200c00029007050b0b0120052094594031008a0b18521844000380701c11810000c00b0000003001d035502044680d810851040024a01481902d0310b100754080c0303980e25000300005101c0080c00501400f2204e21b00300c03405900090408220048408503000318000546135401c4010f0950048000d410005000102d101803051801da950400304d01854001c1020100002003202140f40b5010b0795603429000911941c1030506160103405a03005101b070b400d0b40e50074100080c8140c68030300c000b9070480d4140c0d03c0c5500d14220b048000c64555014001a9042c01024190203001290020000308844082208212026011a11480b020f0b45042c803400b8405102909507170208030102e44048207542c10305082c00140c403002d03105d40241030280c0c1048070418000041201002410800d18040d8040703106058213800c04010032400c0e18518100c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 616248300 1250 616247050 616247057
    0x3070c0906080a1202030702090717070f020718020405090a4a1c1d0a05180601142101211410050a0605010908030a0c030c03090b0d0504050c060a 64
    0x84580100b22898451300c4130001c80c1c410f0304e240031407940c00241202c600380c41d2003001820349030091942090190300103070001c07154100b405d004404294000e5442c2d8083c09180c80c042444501c80342c0985090301550013410008011036402c0c034107154000000c060240c5500c1044692102c070416240c8640020110f9007264081215658085d042c0608100245030b1001c08500c9440002c0409411501940490004943e64200c0c001d401d082d41207034045110a0451041c1039181d03040002d171741c03140c041420708810428a000365235501d0005840f240305041400043e80c10004d51024622680c0340382214404090f030145041d640c940b00704031280348200c146194048140301d880d002250a0032550102d150b040401c850750031380240c8024081d9201a40c2d09001c0b9030f00c6410600240d84c20904440c09016000001c50a220100d01c0041401c102c038640a8203102e403a4040206040c03141031800d018003a91042255291010300301c10300240412101a225401400c29a40b41d0703241c92421500d0f8411282d0707 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 616249550 1250 616248300 616248313
    0x2d07052a010219050a08010506070c03020d2f01092d030305070516032402040503010c0c061b02030a030c05070c0803070201030b01030605130222060801080d090b03162003070c090608 80
    0x8c1882016030003c5010364402d401d500c00000183d44006071403d000744902d070303213101d01400d40140e02400ca0000d0000c0b00310064901c0c4100740c0f66406101e0b0000c48920384401940d41c03500c0b00050340d842032141d240040317020011f0008001c1c142c0200040c05124851003c031402114401c40001c645001408010701c44c00000010003801785920101600ca0180702500510701951440043d08442c00000c955012460300e200d4281072110520a0448460500e5461800740000070710080d02d03440b41429543c02d0554608042c0019481002600c044a91080d044220a501e40708100d5403504401012030000e8101102121154481c1c094042154000f82060882840051018020f5040108801c1b4078a4440340c2c007046c41c5c2102d03a2240000e14003600c0e140709070350510030000c0c00c003540000f14134140415000104100e43c00c100c21603511201110740710307100f0400c464007103c0b0102d4051f100c020256034910301c01c5520320040000d0010b2440340120380d000320741d40d2881100340c0c1c1c030078030511101d5003049 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 616250800 1250 616249550 616249559
    0x9020301060503161206090b0306090307030e0d14060c0304060513020303040603110d021b1212010521070305030a0207230603040201090f09052d07052a010219050a0801 74
    0x70b400f0008200813a040142c100000740c200d0000b180c804d80d01040c9001d4450340107280e039003400c1c0071032501305d42c0c901c026606e88100391b00e010300400d02090b00355008000841c2540240300c5207101c608102d85402040d1503141c10884c07001492038006480a8906910300804144200032510510012070383c058051824140360940070b500910000a03613200754101081401c260100d5440104103c0c501c2c112803e0440b12800c01c0c5d549007072a001c00c900c00e410403c02c2503016405900525a0444400b114040e6180d00b403060720b0440758160031220a0984680310020040210200c01b8050a52865007210f110b580e603081e122441410301c80240103901c03191840c6020604004000b154024018101541c1c5d0581d02d074190f070f000c04c5095000440065442090284244060f100d040483d240400302032220007414101100743d40300580600b003030120008074a8140091040c4206916543d6101a01c2d01e4011f4030105002c2d40c0302d4103c1c11842c440c559103107034145005405540900702ca079903038081c882c1c1c00c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 616252050 1250 616250800 616250821
    0x1080906070f020106080f0a0c2319080a050705040506030c0603012102030a0302011a0915010e0312040e15040204080d051e1801090b0903120f070c0b0703020709020301060503 77
    0x40544038115501c98901241c6c1c200e040010300301d4100303580c0041038062031034208050405410b811800d8202582581e1100400b500c0381c801403c480d04445c000d030169103403540302d83d03445034592158000d4010100440140403020800008650080e101880165950001c0540311185001610b9000c8418401404223865511a0315000c0f528098224184242a00024900b26502e039007200141e440d690f00c0c0c050840301035070641401c10280d640d080c0b6810a860b44a030000800d072007190420000001920540c0c0d410884001286220032049540e25103e42c40006a0101110645040103000303040c405103080034800c0b0f0b000c480100c030203032102035440c60040310981d004e202008201d01d802128400c0340040070009124280017880e5603020030140d031001514040340c6901080c411442407144000c241c8000c40d910804207003010740350f640c4003241c0701d0101c032a004003031001d0300e00c0104520101d072043d03c1c0001003401c64042e4089540c1c26584400d60416441300b40034000000e102480411852131a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 616253300 1250 616252050 616252067
    0x406140306041401030b18120a05090d020603010801090506090307211205190e0c01090b2109030703021006050d02060309101b120902030d1103070b070507030306050108090607 77
    0xa0001c12090311203201898615405e820907034002d11200c042c0880c02103071030341201c4d07200003604c060b01401914032201c000074060015100140500003982e02034968403000c140d05820380c014581922544c440003940d0080841000441c1c20b0300c02c610100b081c109000080d10304441e440500124420712654049140041c0344415005100d036200c03603e001c40e06107020f0140b24a8408640a40c40112200c82d0340c2500c140d000e008195402040c00003950340d9007e01c0003002d66850441d050b07903c540c80c4030070404071512007001051140213541400b103040408002007510b94002c0c0c0c21110b01c0e48104603910100e0341a44201d0340d120440c04168070041c2816805198040d10101c240d4851704030801204d030941e134517180a2004601900c0010110a0700f00007040140c0011220820203442d80380d020940d60500c1c2c11406080c0240610b4111104100700210f4020381e80c01610102c0a0038094400341c03254100140440220342070607000b1844e07500c6005a503100b1581840240250b48550006440111 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 616254550 1250 616253300 616253311
    0xb2209030c0f03030f0501120f080306010c0807050c010305060a0b0403171902010b030f120d0f021b06010609170a030f2718060f09150509010306090507060504061403 73
    0x31850710504089118090710140c030074001d46010840720483c450700f400b25841600002d04541203554404081038258a91140b0654064440e0b65a511f44000607914502c0540008001d01c400240034001c0110104030904034000c00e0701d007405191920003c1000c401c00c5030160552a982c1403104202240c040c2400034805c01c0c0e000d201514100c03400b00203900c2202000160000b60b911201d80000c0d9060410080440400300c0707020303190887e07031410526014410f0518910b2942e03100c113254640c1408a40c111192480d00700c03d00d0060407621003c0d1a15040e00344260800705901000000c1d54a206140c0075455042000103002c28080325917007070b22480000c0c0d4034a010464661003061404001921405007043c5030141d8403003d034900410bc0015283c0a030003011040d0600c0010020504807003000b20a5842911001c500307082c40300b415180880d150340c46190b1024030440004280701e0160301001030a4011008c3c0e1b0000c98a4660a07243d610451040741d0024146031024041071701500b010b1354104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 616255800 1250 616254550 616254557
    0x10501051c0617150601050c37031701060e090601030507030906020406021b03010c020712031403070804050c01030b030304060e181512010c0c06020d0f060b0405040b220903 76
    0x584415a0f0301e103a20800e0800c14050344030803810a200d400350b6402c0e9502c05001d1800628180900300c0454407640c0c58902a280e03103a00a4085004403400e50050b009102c18604a0216800303d08004003040101e90124001580640011a42d58440c0d4011402180701900340c030100c1e00d60b00011001450014803d4041580e1907000b807000810b00c0c001040206034903401002000a0b840700501c03021640300100d44242e160a181c00703485038011800f041121040d03044102400080d04007070f20960310003400508200000000c10001641040c0030500039800b030f1080b40c40711600c920040d070403280300c1c0c10f00d594035510500007044880d11a08030868404009841101e1640380701d1002a100c1c881914600110822071017851093b040c04e00d100105580140000d100c1104a0440a03240c01c91480d005404c494000403d903a09211032b4100c03680003d0324010410009954854900541d0454001c01d8421401c00103140c0c43c5240c04181c10036a004980d602d11900a02414200d00030b0089000032801d2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 616257050 1250 616255800 616255811
    0x80307080c0f010c020102042111120f030403050607080901090b06061809132f1003230105131109060a020114010b090a09050f040f021530010501051c 66
    0x34290300b8004c00f400c024607500056121400e000d030b1500c607100032514541280c4003c40414000c6140d01c1b07410000d0110949980c04082c000440f5503003890765103405400380340710020b40001085000554240b00304002e59659099803180031720b95080e41c580c0c00d0041c0070441c13102c0c085101803500034010000c0d0414080c1e09201b42c141440401d080c00800c8440070640e440300700c1400d041c42145603254014a413a4a06000c000c111454907011070303040c00c050315001e400d40400440d1464026031100c042c12415401c01381001c807401115050351102409120700070b82074507140d00036040c46070184844c6400e2243c0c0d400d05040c0390805102964200905004c11592502e90a14282d0640074a10380a05103a04109035a050a401400214800340d4085481149490308205070341e446590383e50b400070f81c80344c05080c80c9419400015001d26072800004882c07000000e1100e48460200b41c0f80c800c408010b21103e180600c000c49403407a20909210780c0b070128a08100c8290401c1c1e4610f001d0010302501e0400041c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 616258300 1250 616257050 616257073
    0x40c0816030e0c030a0c0e220807020f06031501121802090a06090e0f010624030902030a051002070302010e0114010b07150f090308130c15020106080102030408071b080307080c 77
    0x60030b80180d100f51b5140030450300c144510007003103041d2079000400107080460f001d106071000b80041c111100141024001007a03481c110340c3c45d81c110001200d40100f203152a030a18508a0a55454182c0c03a1804100c0c940c202118a150303034081c1c01c0420f80000703003280b00b1856540a00001c0440200300311542952203001254907222846a4864011100001d0013001041d6180508540da80d030000040c1000c405462408854900302410910342c040c6800715000d045840443c0c68207480c05001021406442d0940d12070400c0c0794050052540aa030080c043d0380d441c044014201c4071082c004c61514000314006004482159005201e10b52082c00140c0c00c07031440c004c60fa41102c004142da84081074803001208245030388a030289402408a407000210519255281045440180b08541c8180c03014415103148134000e62054004224403402590b4070300e00381c98550786541c000881100d55111400010a000b0685000030060f1090500103502d0306a0548541d401c94000e00205141c07481400000750 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 616259550 1250 616258300 616258303
    0x7030c02010212010e010609060c0c06140c060f100b0f03010905040218040503070611130302010e0102030705241006020a06021308100501060206150d12020106031709040c0816030e0c03 81
    0x18005c200391024080d43c2d5040180c020f204c60000d9008408000300c0d01c5010b804940c2c0c4d104a00c040300d803d0b04201c8542180183d10f0200b5000361003c00100d03020b00740401540c9907901d282c29224491002d980001c140d1100040c07221800341b4510448068414401800384840b660f011030703002030000744602001d80c0030088101c0400f1003142d04448680020884404120260103030082010080300300303d0402c29108004808540309200c00b90400c0000e07118542164020b10031a0340c2640c20209070b0f81044144201103200d14402040b0b8030041e5000000981400074515030b10b4103039810359019041100c030395101d03100070750842c1c3c000c0010070b07c480d032000a00c00c070100081000800384141c081079640c9811000303424403100402d401d0320094003007020400d03039072160149141c5a90003009600300c5401e51004a00421880c0c00007800c42070b14104e01c0103030501140c09490341e440d0480e01800440a40d040469140405660180303c54101600f929007540c0250414081140200102d5440418002c0000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 616260800 1250 616259550 616259587
    0x20c1c050d02030a0e0405090a0210140406020c030712020a06300e06010905062107052e03230402010c02040c0e030c0a0503030a140d0218010206060a08030307030c020102 75
    0x2d68070000d01c801119800a0161601481c1120f003041140340005500303446520082000703104802c2c20320200201070007610407c00e141d1260070703811f0b00c55880311400303586c1e000c900c49183d04c43c1c03080060014160b0342008000c29580e5020f041d0b43e400d40d00d042c005844440401840544808041c1c500d645140c40aa41802c82000600408500d1400c500400c0e800c01c003044c0c000307070380c840d0426003002042d803151104917118991402d403d0544104c0488420b06100094004039440340021100c000d840710380007c004010310380c03a42008501c076182038055089071000468140c82100f0603103858410f2050035505540907006040a070802846a40040c0480c1c08040f4410041440291103481c42d003000c00400134113074000d84881a45905141c0005c0e524028400d0300420400d4003224024440582c40c2510005152800250340700c00c5038101500085800b03409450061050800055651810f08444c40880d404000039500d036817940355003180900304440b400e5040d90740810a80c028060b00b40d024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 616262050 1250 616260800 616260823
    0x1050a170f04020f04050705041e05120601050306101406070f1704140a0321210203160507200a0e101a030f063007140102010903020c1c05 61
    0xc007609440c091040080400844012901940c1740904108140c0d4114080310160f8160000c2105d142c0301401c940101034216401c140d410500a060001000c0d0b0009130b02070607141d044060751040d07a115001c04a40300068401c940200600001b0070045003050402840214007130203510290111035225a11100750245401200c0c0000180c2004203004e80407004070241c000311007411030f8500c0e5445062041c03042a8000e03040c810708902e0f00c04014003481201124003a03c40300d03055a202c000001e06d00a400c1112440d081034094842c41c84024420012030381c8240d40103400515a46a1001440083e00a1045180c00481d04180861064440100e03180710740050f04443c8551820820007800b401001c03074605d00200702c10700521969081280034a80c0c4458191100348c0e1031384026012a80701d401100140600b410039512201c94950045075005c10344108071794401d88030801d6001207080f035000322009001a00045041012860075000d030403041c0c080e035001c002404200b5120b00d130410b81180320 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 616263300 1250 616262050 616262071
    0x6040203120a08040206030a06080f0d0305070f0f1202040f170f060106120504020301020f0d0c02010b061c0e01020d021318020f030a050618180609010507090501050a17 74
    0x10001140340c1001009020120024282c1c1040d555903009460060081d0000b4800c10012001400801090b40420020070071041102d1681d0300f284c0240d0340b640d854102d83d1380003905100010301340b1401001401d180003901e940314203800f040e0003422200f442080c1d25104080781c00300000247c00342040d01a02c0580948070400c1e01d044041c14200e4944544103104582540000004007e0141c002505800c40c0d000b403d00811940d4403131000078028444e6030848100c0610214100000c06401c0d8082102030310780350000c0061058041c1000f50b030b8046c201c0b0b001d440342c40d40020b680c14005180c00600c94402800b00150501506041c004203a81121090410301d1860300307801c12820b00c8064411503002c04104003149030100107042416284402080044120344801c0401e895488403600869150b80f5043c0c19400c50070300c1c10110604102e4102028018031582020031118081880f032140036001580320401c000e454440103403403581202d5001d2081c016070800e449055070010100c148140e44410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 616264550 1250 616263300 616263313
    0x80706030e011107031202071704031b2706050603040317130c060c020f0a0b0418020f040501080603100e010c1b030206041506052119050c10050417 65
    0x141164640d000d80760a5a041c415a0140801640100d801490305131070003541c81c00b50700005401a00c51600c00900b080b480e0310100103004030400150041d280700e101308041d8138040c3d10710300c90f0441e400c2c003620b1640b4403950220440c00c845000c1201001012000c0461a030ba50359000542942048405130046181c194010641001e0404d5031a40030300d0301079120420742900d0316084a10b0915004e100103201040b44203400307640e070b05010203011080003018869002d450320100409500f040c45480072460030200c2d1121010184e000342d03000c10788000601b9007040d02d0000112181100078040c140c15020704a940303d0758400c10300844076400c0040c0000305441955402c000c0a281480b5004c0c0075039940d80c114240020380c04119940c003c0d800603089590b414502c8541c00c02051281e02546c2d00070b601c00a0005c2e0074071050002125440c003101075402e008000f1406109158014900a0880d00980306403007941c80e00d10041100126140b600b6810306495141480103c500d4402d5a080c6a0210 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 616265800 1250 616264550 616264559
    0xa0b0313080714151b0706180f06050601052502010e09040b150a0501080721020d05060a050906090c0708090a0617060415090e030c0109030903061515120b0a0807 71
    0xc101c0c822802c120190307142c610b031400820f0740000e05424180d041710054002a44414000650000e51450b20300c05d048401070301641c50b02009035950100220b484c41c4c1000c00080c9258002c1e4150340103c0b00090f180b00e00d21750500e03c0c0d07a00c1544071740000c03810f2000e420b80d1103d01d5100c0e00400c0f8030843c480c55440c00541450f440402d1340c2c03030403280068442c1110742010f005036603100300b100390444401e04020440d52004c0000e10078500301a01e04d4503441e440481d060a40d409290005402450141d400020325515541071240d480b01c12521aa089590000461007210170000102003d5001349034050600c03094800141c50741282d540006c00044d4800c04c141c04181011942c01d4100d10105e40803c12111809901002849a44661980c25580300e048035002041031040700c41c074851120003080400003d140262610849020a440c09450291841c0410000d000b04905032542e002000340300182e404001c65540220484540303d454880c0300102e41ca032035654410010f00711210140941c107080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 616267050 1250 616265800 616265803
    0x2130507111006050f040c020a0b10031109060f060d061206020301090b09060109060e0a030210030c11070302030601030f08090d030503060111030304020a12021f0f030e06060a0b0313080714 83
    0x240c682e5840032a241200070070044d9650031400702034040c1a0f4003c144c00b144000c040c1c1c2041f1004c000504450720392000c020b408001c02003c141640e20803403500c60741003000f4080c0059010119181fa42150951980100614121000d8802003000c2c2902185a5403100140e0701420303140c00040f81c6258001c40103204484040c01003401c0b0220550fa5482d042c0b400030b0000340703901c3d0340e0302c00d00080c03010f40152221703240c990710520308c05545c000d071607600d00c0d03055218014000c20b03c0494280015001b401b0030f07080e90b100070812204072600103005141503420343c0c8034564810005141110031060422800507241c0345d611481d10310b64040c0d140d580c2caa18003203001421207004002000c039142c20800812005035a034500400c155103c410791750b2445107491001c10000e80383d214140410790201200c0500890784480420728400c032998007805100a4640030780d656034401e40c0e600b640011f542500b84900e4086c40f0103141d015250000000c6074140e01e807074040c802d0f8415241900c2602071506142c001890 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 616268300 1250 616267050 616267063
    0x7110f1b0108130213020309010b150c072108030709090c03061514040e0901110304051b0907020c040504030e27010807080a030e01020703020a060f1d0f0402070213050711 75
    0x84910040c00943d01c19400070b081842c560005d00c44444d404004074400c1a025801820801e40142c1010a80940704818211940008a09036040d2251503404105009070564111000e400081d0b45410254580d4a204894000810080801000920006220b1207030300407968121030340e407400034035036007460b03004040c0685141340c020074050624644089004400200d40c1103d58604490119850701d1682c070740509516803401010000200c18032081c044089007204404001c01c0302d00003404884c03824815803840807522000560440c1c410050142483c0d0001036000e4406d203000c0c50241c11100c001403000c1c00b820031408413a420446603820789000308400078050400c84d4001d101c178910340041580e5410106100504014000040040590007003083c40d025640c010508200355444410040101081c00358400008e102071000100300c08124000e0408228090200d0074000540000c1c04044e50040c8001ca80044a1241082018600d881068092100341c0c0c5d403510f0074901d40c0d100500d08803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 616269550 1250 616268300 616268311
    0x100906092f06090a0b07050106030c030b1005150306010f020a0611040611010e0a081b1207050d0e0f0d0510050c04030c080c0f011202071403130608040b07110f1b0108 73
    0x40800003001d83c0e55440501c20308844c0809461992040385203400c902500f5030742e200600015040340c02108110000c0c0303000c0e1007000c030108503144081d6944200160b0070050b400c2c2101c5841c0403c0071500a500c03580c920404514540120b81c1c040c1c41d0759450303e007116080645280070b10780204041c041036600000001c13030412000c1c02032003050010704409403107104884000f0b01540c00050300103990301020158846a11044051b1050074600e4090306000707601444044039a401004010603410707002e000103544031100504008002080c05090044100da404400e0311284035504070fa400c424000c0c080e45215000305840c260307d5619528100600189581000140f9081181d032240a2345800d0742c1c4000080d02441c25094446422501200a1003081006809062031136120030543c14004012f01d1600100e01704001141d50341d560844031000d055800400d0310001c1c1d030108802a2140c14069a00f01402055807004803080124074507200070721043d003000001419400d41d032987c01200550f81301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 616270800 1250 616269550 616269559
    0x7030309050f1b090c0d0b010c050106080304060e060c070b0c0a0f0f031115070c0c0b1305090603030c060a021305091009050c09030d0f0327150e100906092f 69
    0x2403d014014085e24001c4480b80c60720103554004e401403980c4aa00c1c0020f010f9004002040b0f100d40f543c000700d450b41e00c20301031a004919035000c42000d9040c0b4408661442884002070301001c1d007001c000100a40c4034442c4c0c48040d10800013990701290300080e8950740ca521030790301c0e409544014600075141d081040c85001c80ca4200903074400b03182407029480e5600c0400b600c0c100c280110b40d80341c141f00500c081e4101c020744610105611440c140c1100700c1c402500d81c12600001c0d030383e8840040641e01e101e0858008140c0d049000400c521351601c1e0003030180400c0540d80c0205445c1c444006c81e8585904031001c07419603203030a00400880085214060f003009070301681da842c000c813031401b00b50344103890f005580c10004244402c1c00c6061080d80040c00c1c840f071018200c1424621006c0c4403008020204082c1c6650111424822000480d07100d802d141c07a1000c400b402c0d80174001504400108140a0141e6445484000d41d000044110048a80c0501c0e0075030401380080c041503203441e0510340890000d006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 616272050 1250 616270800 616270819
    0x200f0f06070206040f03300b12030f0310030b0906011e0303080c13030602030a291c05070e01170c04050907170c040f0b030d091a07030309050f1b 64
    0x700c6a0204000f644181c116400c2c0d042d000282c035044820003815001415250f100d00c0b402c0c0b00407508018884480010300f4408e005242c1620b003007000311000009600c110b82c1c810441ca170700340f128400245501a60310140212070f9640d035160300b4101c81044030a40000c0e041700d0014498909884100002082c1e10850300100d9030940e9000341510b48060040880c0407400301c2c80629540802c28243c01640c1e0100080d91a804c0c1a928440075018400441c24071100c42d003100c3e010320b035100006082030f0384000e203608440810291802e0721500e07031920513109400b44400c0450a4800141214000c050080340000c14601a01c0d03540c5c1008100e02c0400d20440c01d04060044004000441105881c01c903010916120a480040c42c80c2052022043e82c00034180850980154480da110040b019815400d64018840f60481156255503500030202c0c1740e284000184032400340b1300054200305206c0d06001403544140d0701ca00d4a030407443c0c01e42056a40c000c0c050514a000044140800b110041c0d80e9401e0303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 616273300 1250 616272050 616272061
    0xc0909141909080405060f1c0b01020d02060907060e0a08070816150905090a090b040f061d03041211030a2a0305060f370b1e040507200f0f06 62
    0xf0345104070310610b803140d180441d58202c510b5066048070303044403c0600c035480d1140d540d6061009081b040e0300e803a0241c041d448401b017070540040fa400e1320980489000d410050b09143c4190348403800004026007004d035210000c00c0f0143e0400c1440e000c2c044c4600106080c4a2103170003d4418400d80c1c2042e80d901018414141400e608407280e007050300c404039410314043c0d550b01e48440c000c012031071010309010304c0c2c04144070174040c0f40100001c40354042e480900c1102c1a110a018802c40150501c000d6603008000c2080860600b94083d000940b00385014200f81d83c1e807200107032600ca59a9000e8448000107450030ba400314441c00c004240d9641c0c000310001562858407995124800204a0080400c801c00002c07001c8400ca9140207411030180c86618030030356058950049800203604400c1d090b80303001d05035901890132084460825184a2900f601d03058140d090102a200151800080c480c0030101030f180d0f00381c402d06070020540988020161142804540c80c41d10b0210391124001d07402c08002d104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 616274550 1250 616273300 616273313
    0x12030c140105090d0c11330c0f010603170f12090607030f06060207090e01060b1c05090604081c0b0303160317071b0f050102030a14070915030c0909141909 68
    0x1741081e0481f20040e030f40d4414003582c030f40a036200010700da0622500442039049001c0c1c60103000140b00d80c4040f20700340380360002c02c54200c5500740409480b000c0442101e0701c500780418010600b00110001540c00c201a40c008402104029603003032040385c210300e0800c0074903036241c8140000107a0000c6d080c00440c5c0740138401f94591404c2e0150f074209903101c1070390b03000744002500000c0c010450403242c0ca0f41e03029289013a4065281030701c40c00d4801410400802c40d54080019024080d54000e081e1500e420070308262510700c07c030f000c124282400e4031813248040c5903405101400d80540c010900496800c003525000b010180f40b809907603070b00e4804105218510340c2c0419203207600d40ca200180003c071a103905103000d10f004d000c4c0c8018800d40c00001045600714050b00309845142d0303140f41c12055525100701c10340d0005098000d81651242510546070020301c02e402102d040151403d01c00b10498907030107aa42039078440c0c00c204180c02803060510038a04c8040442500542400c0c0041180700c5040c0c0d5404c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 616275800 1250 616274550 616274573
    0x607080402330a14070303060e09010203040c0e060d020405010803220e01050d020303070b010b19050903060c0307200312070912030e04180b040c0b1312030c140105090d0c 75
    0x6600d0454007180360f0341c4040c040c1c4010043c80d02004501c0340c80394030914000307010304000c0c0204260155020041155110140280c9015560007112510442e003000000d141000c4014a429031003245444ca22015031100d11510780a0120b00000d15686c40c002928a05421000104680c002104110420045484030325079810340340115000f0b4a00380032400080c1c654002c0690141a00c0101c000000d624056079008102c489443c00d061000e808002c00d0982e040d0080c1c010044e0150860000a170620704ea0704000c50b0f202d5068205880742d0910b48203915482500c400c44100303036a2001a03050540d01d0000030044d071045d210705e4002c01e0b40382001403000800401160023418030900075414807043d91960040401c1c2c0400000d00d096284a6041041c8101c006a5068821030007d400100780203004104440749140383d00c100348031440c517084502c2581002e01906804105410700c5080024095050140b60100c034880082014101400428140550702d4880c41c1840807006058000a0780c881e002c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 616277050 1250 616275800 616275889
    0x318060e09040c0e13020a0603050f04020409050f030403080702040e010605150c011103070c0c05030613020f1f090e132003070513060801150e0123030607080402 71
    0xd005522140f900c100346404540100501c21000c508000085a400c1c25480015000300c1d0f180680e07a07a9000203600b01c0303000f56040700300440f20100160142c145070b0000d00344070307104500301c6180c00c00b039010803403c50b080f0744c004940030040040c0000651a00e401a02007207995207000708111450100018540c0c14015548141d50f4800702b50100d8209081d4020180d080a000305c2a503289800c14000b004420051400c071086c003500000410b081c2000a03403a803050001142c4c82005d03a41ca6000c00c0309104034a0091b0f0f50180c0c04070013100a4000c0350080d011901c585071165000182848582c0321b502a004001d0004080c051112501103000b2001d40e19900c2c50700701c09081e00d4044400402c0c24a02a504610303040076200341400200071140e44610100c44000008111000301520a1032a40e0b0041c0b1580707a07042415001880f100d402c01000c0100c2d005041d907103007103141036840800e0524a0403240c807030104168000b08020b41c1008000c240000c03894202503701c04100c000038820110841310b6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 616278300 1250 616277050 616277059
    0xa0e0105090708040305090406060e130c1d0f100e03071a0d0203041a0708160804150e030409060e0709240f020a060608160f29040306180318060e 64
    0x41414076016a0447d40741e8440a0018000d8039120705c0c010b00107407500c54009002d00580c580d0411040d40754031804202c00d0940d81e400000032241c001e48000d08010122103a448200340d007406459a403044d0700318804845070780b50903a0a05035082098140007259220740c2501042c50310003001c4039450b008840101d000144016100c3d2201e0500e080842c51710680024040c80c42d03400d0080844c2c1000c43d80d07100c0c18003d940903040500092007260b08010039540200110b8016150a11114041e000709240400c2c0c141220304280e501c1c02014265102035104600001c2c81c0414070015561094102e400b5080d11000810340240d82d04103041403034490149107040000a5100307131800c0c1d209010800c0c0e1250070203024011607403107100c01c544403001c0031030703a41d10b2201c0e040c800159400c0c0480c20300c04070361110000441c0d100c2c025406407a0f03040e8851070390103952070400010000810034407460088a180100c018151311180c580909000384241c25034002ca460300340e04105441d84498580380d075440c00e59 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 616279550 1250 616278300 616278317
    0x501080a1e0f0501080a080415030b0310020403030f080708150a05031e010513020901031e0c03030507032a140109060914100507122d0b0a0e01050907 66
    0x182100501c20311092030414219103070640007400250308682009034015a080045903600c0e0385140c0d8841c1d20000041402405010800c16000c04083c070740c010388845c0c203002c6109000f61000a051140e148900116640d0215007841071503403000d2035981800460800300c400381000c4070003510807580145400c0c03011854400c420419101c0600880c000e00c0080c045440406502d051a00401c00182c0304800741e40c6410001143c0074805080407c40540240c2030f0344482e42140c0302c820004000b411004000543d940c031240001e40d034014007a0080d030107076984517111140c0749001841d445119900c051181c1d40c0c56417440f540c00d4490103000d10154807081c00320b0520030701c0c8200d60150040c5640070342440c0c540700c80f110601070030388010f004080c2c151040d81d0701043c660110404554003a0782840015007400d09801035a038042e4803107144000000c2c5100c9a030000b210142c01941103220085444a4951090360f845050009600004d802d000b400101e03258100000310302420740c001c1c6010200b14000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 616280800 1250 616279550 616279561
    0x31b0b04050f03150a02120901020a050901080709081005010608070c051218040e0c011101110313020303070c08010614040e0d0f12050f040209070503100e0612070e0411030304030309050108 83
    0x1c014032100d18413600c0c4180344c00d250071014540203400801d1100c41d00c02c8030800096501c501072007140e142078000d889860420804500441e5003c00040604003480300f070480105442c502046081001c2d03041190110340c1e581092001000c0510250510f41406001c0c074215002441c0132590303010050480f1601612400b0868451061070703000080241c0040c50700000240d41c000100300203804400a880380844007040c4550f8034200c0d0b02191b036039188200144045800f1405040015050500040c00c49040a107107441d0b20030440003541c40007665030b55600d420416090031030516141c8210859041150842141850344c442d08210744078400c00240a0407942042c0c01190380c0e42216610314000c0025241108070030040030400d40c3c1c240d11515840b00041e0344a80701d0f4048a104d41a01c904a0b102203203060010740003c0c2c009400c0640c04581c0030541d001c0c0200c100701c440c00504080008a50508190038032004690100c10118002e0700300b04018004640c100704400c045030820300e0b0416841da00d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 616282050 1250 616280800 616280803
    0x7050112060e0114091f0306090206040306020d0509010c020a0203070e130f0b09010f0b031504061b1d062d12130c0b09031e01020c070f031b0b04050f03 67
    0x3650802207416485000224132045640550603600105a60001c01c503120000d0204500100708071500f42030880360820710000303080b90840c0062a201a02490800d81c803607503400144d0300321040c4852407903030702d030100800301030f0900642405064500181c0180845500840d482d90064041c00003400c802c4404240072050308805030010b81d0f003054850010b001c1c0c610701111850001c0e030782c0e12a5982000f03001004808648035000051000a000340310304042c4038004080d01300d0040c0292111076a50103103910311481050b0105200c02d0a65030390aa03429000081048c80308a141c1e800c0c0214070a000200034540303070011390340400880c45c01407921030b41c4490b500c13056807040100080481c81d4410600c983c03d0b0031001c111440601c111034a8070700c5900e80c0015011400b5078030825605a0042c9401c00c0c00d803000d070351104c200002480002d460040d070340d24004d14200340e0364802541e00d01d5808080090000013041c010310100c008060242c1c40c1d00e4243c41c03001c1c602443c0921840742220f00441c01c100e550 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 616283300 1250 616282050 616282061
    0x10050a030902030f060f09010c02060118090204140c070b0a0b01050a080c04081509010c0c200a05040903020d270302120322090f060812030c0c06090d120506010207050112 75
    0x1407541145c4052414031b00b1001c00c00d03400c2d101c1c07402c59070070900d104038003d0010a13a94140d5031102000e512028070303108844042e2101d001c00b0382e0030696405885d8448203d80c615544100788244401d50307152411b1602d8030b000c1c0c000411100c4a28034000c00c0303d082c2c5c0e0784581101c0c5040380b14a80860300b500c41001070002481154003040c010300c1403501d103001c17030301c0103103072071b074810203142000300b10b0070301c00d81400e0340d440c40181d40003891071000ca2040140c41001c0c804400d80038402070710042d20941c4520218003102c001000c1500560700149001c00613641c052044040110411080c0808140e20005010413650034000248034900e16400c412034242c0820075a99440300244c180c07c01000b2004419a20854078041e52001c0c81c101100166a6031345802010100c44c0d000c0f000708800403c05003411101c1d00090b1084280e520308102c4084089400c02c001802400d107100507180211080c0400f17001e462191100c02e6030241002c0400078241e8000c40d1100c111082828030204850858024000524 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 616284550 1250 616283300 616283323
    0x61a03040320010501060306290c030904020c0f1e060708060d120306060207230d030207080703050714220507111b04050c1e0d150306021810050a03090203 68
    0xba04110b461081081500064100e03840c81d201000525110350005c03d8a0400c2203d00c0000f861f407900900c5201c420388001c090741c102e144207503403c01c01c8100000781603070b01c0b40744981d0303c0e0750140c4191500080140007031090600086001d030b1404d004c0c440ca00ba1181401819841071118440010b002502c0384280b501c1840d90000c10384c0c101c0c40e50000003034000d000c24000c110061050510114038040c4955140c0f40b903500c4004180c880310301c0542000039580d80c804080301180200d11000902d86c0003040900041d611902c068001d441c141090046d90998415840d44a1902c007040e007031203000f45c90036040c012002c100300414255214a000e80d124408400c0300585403240790180000800e030b2029540450a04542c144896141da40c6002c44e140200300591005540c1c0b01c1a4911280301000185601e4408103008200785503c076035010024249a4402c1c1c405030b4001444500030721031550288000d83c02190b0511581c60195001042c0e40501c10f04042410b580e401e50000b556000c200000c00359 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 616285800 1250 616284550 616284587
    0x6030b060d0603080705100c02072106140906060a0f090209011707030c11031206090a09200f0102060f1b04050d11120a03021504140d09060e04061a030403 68
    0x20f5681c0c075000344207520144003a00c1c0d9005c0d11301601104c2d00540100386182500e94007d2210318100010100350540400d203a50230000c503a0303000c6e8001120743c01264108182420942003610b00004040d04001008000a102d02a110014010f0f0380c90b0300c0014054909503036006807203840d01d00c010303107900b4007c0403060428000441080459a07040d08030141c81c00d41d41d540c034081c40c00e803103c801c1d50f2409010418098040007c001a0280c1800919541e00c60703c5001c01042403403140c0c0354242d81e16020b204642c92400c5031301000f4002e06012a8072449040e0a1009200600d800c104080b01e800000e0148455003080000300c1603084480c0c029140a03200c0100005c50031041307854801309642107040c83d14010344d81640400c642e00c1d404a85008195050340140c00c210f000700c2c1020700d25603801041111003c440100303030500803208100b2001018420b4a03881e40e0a428200301401401941058510031810710609010024250b02a1822400001c15258480d281e03072170181c0d004074401d415003406 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 616287050 1250 616285800 616285811
    0x601030b040f0b0102120c0a020123190e01020d09180e010e031b03040312030f060815010810150902090f0d1a06040b1c060b0d0506040b06010507020a06030b060d 71
    0xc44815406490103402c00d8003282c0e109200d082d8106c2d000d000305900c1e803900380c121030500300c05540603415005005c111101032081160745800700c3e034000e80190070306035020303400406108100d54020000b2010400309000a000c00111914002c0c20340c4d505004240c0311100d82e050b02040c0040b150440340b030b610b40f500000d1014200f0b035250250b5a400480c03241c42582c1d00711090301004100441118180c0c0d82044202d400c40c2d1b16000180c0141400ea07020800241e075030340c4001402c40c0c05002000900320380940516155160103645482d140300d2020080c002458080c0110204207400010402c485481c030000d030b200e0400d900042c00380743c4044d0305160041c100355400420071119000440b040d009011a01f190341c0c0b100414401191b42d14403201d0b402002c2c403094070708509603200d0303190620b5205070000700f500c030b480001054000c40301031012a001e511209c140030800030000003a40c0c0c03081d401e18006041249940001342c0c0303882d1921031201816510404080c4075250001210045d56071448140320 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 616288300 1250 616287050 616287071
    0xc0c170c0f0111030d05070c0f050a11061629011e080303040c030b191b0e0d020a0e1503160801051e19020c0d0f11030309030d050601030b04 62
    0x488942003984980300356aa056407605640c090008103528540701c0d40107604119031540c00030010030003d800b0600380036041001800281c504190032505600c00c0c0090328490f4000d2901890200b00740007503500c208003e0101d198002e40700c601c501c998a4208081d000341155440c543c40c000401e00c4200030480c1410300000c618020343c0758500620a130004c22107581c90b66500c2c100c6480703000941d802410344565400404c00b08001c54151138001e40c51014401c0350448884000040302d0104030030055600103410ba40c0c081c543c01c402803240c920029240e0030000000d640c00500380d03100500604001e44002c4000c00d068014034908c1400c0c850001d01160f000c08054002281403a01d548103103d2290700349030010341c03050360042c0c000d001d024108a821341c440e2204000e4a0840c0782d08030310704908a82c01c0c4206440200104148900100291190b0010a4908030010141c00401c102070f000c5502c1041402188280003003182d030000c10300d4000143c56154040102c02034004109010390160401c500440e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 616289550 1250 616288300 616288303
    0x2100509040b09090d0207080a0302030901030b01021504061508151f030609030c020a17061b07020a0b0c1603050312041109091501060309020a0b0a140d0501090b010305090d0c0c17 79
    0x4583d100c0c036007c45440c55500e01d080351360b440c0b801c90010016002800420020f501941000c4103c0005005440b422a6140340048110404842c01e851050b10340b407584031700404242a03e800742014802405100c60403510020200c0345c0a001d034078000341400f417007924282c00e101c64040507503440311042c4040411824001c1c625402400e0903403240c1c000301703000101020320b41014058041600c000e00043d90f50122025170381200b28042281c109030806c440c3c0016a03c0d201d1400160440110094030b444500d06807030710780f156201984401100544040c00420f0300041900d01014980000d02c00640e920310f080c00b04c01507a5002c09420007a120203100600902107011040d6020b620161089681d950504030180c40391882c1c042d401c501d21490500c6440b0b02100107100320380ea00c0c03c0c615031500318140c081c845a403196803030051159507103005000c0310000340950500c41c0024a820701c81ea08059441544490400c41c0d024180f180021011042000c500100340c000d12059404210b420004281765 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 616290800 1250 616289550 616289563
    0x601050405060f010e0904050f01150f050a1d04080909070309060b010801120f080f0403030215010803040311370303110a0b01061d0d0f0201081302100509040b0909 72
    0x452085080c0301c0080e2040c20041218080f0120503955488007103910740030300c110707500090815100d9002d580c400041030712090003003014822100340340d46515480c190010342d041425800031807045203010010417100c04640b585042da03001c1d07014140e80c030b41ca0350b140c003401c1442403002e2107400c550150208084960154400c150203070282c8000d0081500540045440c51824020300a8055160b10450b01040e000003a00000510521300d0510f801600d24480c0c072160410b41c030490041e4040c1ca0310211000500700f03141d005054440085003028103507682c078616148640c65660180c502d85110425080d40b80c080080c484034821000c0030701c1001c508080005144e40d0000b500807442100840d03c1c01080018101e08480e040b0020704032590074100700307c0e20701c07200d2101c0e8115460460000c2c044c40c0c0d51b805041d180f5510410806c01c0d4600b062001409510307005140f41c0303403200201c2d400302c0540c940c00381c03040044a0b1450500c3e604c0f55001d00280060180728404364001c4c031203908103c110400094030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 616292050 1250 616290800 616290809
    0x100915080703150b1b16170d0503130618021801300201110a2a0b030610110109060f05010f050613031b05040e2512121404080601 57
    0x1070029252508540f00e0040d400e100305030300914104203101d404485400c2c1c03407140c0e941c26425101c2034100d83c0205038000c400c9801c44103c078400f0070a5113955500c1040b80400d00203080c2095800c5150a90741090040030358000502074036215200e2403c02c4100c541c5010742e0341e500801c070584540d91380c90319468400b001d02880550092894040a004680c038007440c0c402e4040c6203900d105501542e00441e070410380a84840120711a103800e190000fa0401c0d0121035500e0030051a52507540c0400728801d0046095000510a040400501c0f0307003601c80301c08400340c01c100b900b4a1301c15592030760080e600501c0d040a01034a103a180c46032080c0c1140403508054100c0d071051503000002900c0c0c40804c400b0f07118490320250740c85009807040000502c0f81a40d044e400e401d81c200c00300300302c0e55000805e00356000b0403949046174000f0741c05d8000503a1501000784084002022219019084c26200d12120b46280d201800782041074040443d030300c1c40f4400401e0b40c0007480d42d58584455891403001d94030f550a014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 616293300 1250 616292050 616292057
    0xb0102010b0f130b0307150206060906010f020604022407050304030507050411160305160503190509010f080a0b061207031a060403230316020102070905151009150807 73
    0x240c01c0300c1032030a1001007211140041070741014100c0b100c8408001d02c0ca442400f50140140c9000183c259801141c0c0c100381c448a8018205500c0c004080004080703008260505004071040034900c000c2d800038400f82d0040e416200c030805401d081c40041c0d404803e00ca210342005800003803083c03c20801002034000c417441242118691502e075403c00c0b00f940c02150040c841c0e0b01c400e010b043c09090b11022031501950013820420320700403c8001c10004005010400d56250340300043c400e0f000c544010300d1840e103d40a180c1941080041000241001000c1c44044100005200032500c4104294030000c10300c0f0000703104030b584002d0194101400c0508856202c0801d1804004009070304d41030035030b2720070108018011031402c0e007159260604d103600c1504621a503100c0040d801c43e01d4000f08000c04d0800341c000b210251104080c800245000050380000c05014105401e1055122402e412618905402c0300d540000d0034138800110b585810552041000301e203403c4c22840d00076040b0b4640b9024500035034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 616294550 1250 616293300 616293311
    0xf01030902310b0102060712060b070b0402100f1409180a050702060a1b03022104140f0c0307030609030c0b07050406080a09031d0402090402041706060d0506071808010f0b010201 78
    0x2c03004990301a4200380c0540c02c01000a280c0174490050039251a00c050000100b590326401c18040321781100b20200c50003072000081c0410341c9464482894000213915003100345801c0c521b40244516111840d00030541004a26000d42d951011000300800c24502204a0b4070318103009443c0c0540010b580a80140c000c1d400480d000aaa80c026000d04034121010000c0290404000310000d40c00480b00328038091144c0314100e40070424140c40303070191780554920401071004407213150074001c0310701d40e0f62a550301144100700c144d02d02040100c1100c1d048400010701150750708054608071400803000709610380d0b01e010000d2aa8010740608152101a0364091b42651280100ea0445211941c00760201e01a181521055000c041d40001d141c44046e20150a0041d0f000c08182660403682207000320280c125940b00190004001d072590110080764540110b04090720349640b1900050540c0e0104040c0c150302046140d00c1c0032503a03005110b0603000300180304144020000600c81c1d190424015400d00703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 616295800 1250 616294550 616294639
    0xa060b030f0304030b0c040e1003020f01090e060907090e07050d060f05013908070611120112050a14010e10020307020c0108100e07080a05130807020f01030902 70
    0x4a4107240708005008501d01030940c2ca540d4480c40c1c00403c40450500c5c1084042284481c0c0d0040500840214a03030001e0305041d8810031801010200d001410082d0081040008204041151341c1103003064500b45000d84030030b039085070160040d0708840c2150400401b8040c10b643e10100400e44103090710300c10031106456010804c1c0c00c656030b02c101c88c000b5100800c4030b41610724404001c5200300300303241c0040d03501d41403181302107404201950607126110b001c40c41c0e0080c0051401f82d80c001d0300d140003440740b0303040d03810705041010035040c02005209480d0080e034000f000010005040f1058200031401c1c410040e824405000c1e06100003210760f140284803140d01e070440b180c02600d00406164024180d44c0322920300440743d1440c0244092103d41d1801000a030030204042c400c0e018600590b25004203182450303100d4155a4003070141000320000341303000c602041020050ba0700056040360780047c400e8900004034054807030010065448418045904c40c0848514805d101001d0070280d00200d600c000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 616297050 1250 616295800 616295803
    0x50604032d030f0305091c0306090f0e1f090204052404091110021204031208011202090f13060c02060a0c030605280b0307020c360603010f0504050a060b03 68
    0x155000740402e001d043c0380d003c40e9001c1c0e00180d50060000040b6003d02500078107500c0113004500d24980401d81d1090184441c2c17031680603001d6900c031814004e0080600c01503480d0340c0c40300050035505c03840e400405111681082600031a000e1a0020020301c03207410803201c2484000d00a00075420241c05000b5604003034101406814030203a007205040616603601014069540548880300007103014030500c0f2048003005c41c001d000514050350090303400b19030b070360400b8000ba401078104c9285205202980300060341d40344102070b4880e60060080300c0d15100c854008680100c0c1050040040d41000c05100e2499800502103220b540c03440010311128074407160680450701d960180300d070401641003240c100030010558074114214440c480322002991281280034580064800800613085140181c101d8130740440c0300a03003058040141c418880d0041c64000814040c510644d07803407007200c00040d00b103580a60003150100001001030140d1701c3c151615940700e8898000c00c80301e091606200603120b040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 616298300 1250 616297050 616297133
    0x70c050405151e0a08100207050c120601090b0f060a08040b01060507080d1112153f01020c011802091e0f04050a0210020c18070c060f0605060403 64
    0x1003d001e44140c600309450785058112881c0c0901e810544100c40050265020455007811038010b410043c2c4900300752400c0703801e00500d20002d51103208080f11030707006014003051150450741d5002c0005289030703140303012075034040e81c000701e07168011404505401c420703420000c3c00e4400d5120b00e800840e80e0303880c1c900c10740c1d140c0107144000c2e03d8100103100862b0055040d521000079040b104200300c4c18110307103015000c21a1822103c00c01c001c00001001d0b009030800b50302d0100940c241100780784915030451983c0702100c0c40070112292501200f0000500c141c02941241ca2040681c0c009008034000e00005001800d2070700381c201d001d4108200080c00303020011251648004a14005d2004c649070742d00b4620a05601810644241c003d1720315050050307540d405598481070140d00a0000f14000d1010043e00191705440780100030740d00c10801541550290150403040c1d030068000070800141036059004010700d41025800c03203800280842405031881c0c8281c510120104d940e0344170300240d41c05c109000e5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 616299550 1250 616298300 616298341
    0x10c020d050310050d200d030c0b0612030c0102090f0a080723100e13060303080c0a050706060b030103021201020c061503010f0c030f0e07080c01080912070c050405 72
    0x200003a210441a512034401140c01c4200d0452140c4000c1c0c45900082e8180061001201c443d08040300000c00d01c00060203c001e403103011145202c403000030392070103070400d02c41c6240200401d01560004215907150710280360410080800c590710b400e22042d880f4002d5101442d01131142c1006a2414043e14086c00601c00750b441003409050698a061507580b288072104810402080800150018640f038080f8003a501500030341e541740361036000c0d1043c00b02415141240e11205410182d050000c00c0c2c1004c2c01a811401010340140c1d611448c11046600d801150300c024181c60800f81c0000700c100c080e41c0075605a81c001c840d0100d20080c00b000803400c03441441c16100945c0c02403030004103100403107480c20806140c050300100c1d4203102e196402d421960103015040110350f41d00c8d121b0474441c40314494040c00147d003400610259081c400d40540c1c52500000d15810040400d000413442c40341885603d1503414880c129a032039000c02d25041407061418000d00d80540c2c030704000100c04003804205100c1c0307034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 616300800 1250 616299550 616299553
    0x515090d031a0d1e050f0601030201080f152701030f0b13110d080403060c09240c120917060603162102010201021306080402043b1509010e0609010c02 66
    0x189601d9441c1309207070120307035020b07039003908007513503180c00f1a4044c804d02444028a101401e525811403002400808002d000064600840400c002c0a00010038403190a11005c8035a22501c010003c004201100f00c0440300702c422007554000000c0014503042c003070845100356014405d83c1e69504402c3c650500d01d09010b030200c0c0340c1a1041001d410400043c1c0500c1d07008140c2c00340346c9600ca84500f0150380c1c0d404088800203c1000007005880c0070300c0b042006580b4008a1075400001720840101205112100540078010301c0c50610f401c2ca0085c89014000d0650303080544000ca4461a103d407a1441210030350f0003801092034400c00741c102844074030142c61070301d03000b407661801d07012030500004a040300490540d94200019220001400000d4005000564403114039103450700c14072040d81c102013802c4001c0050841c138444202d080c440c600c0401d210300c03005c1500142c00840d08a01c0d00340d103081400c400702c4c3d0103010301c002000103403c100c140100b20380c2103c12a071214042d00b0300b2030340b040003880c006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 616302050 1250 616300800 616300819
    0x31709060a0e0112090b160e1503100f0303020307030815011b02012106050102010f230405031303080d0509060c1c020915091f090509040515090d031a 66
    0xc0d0b03025811001c1011018509105440c0c8024144400c8402103003068400ca081c034402c000207841c4035200c00d003001e6020315000d09030804000c0450071041d41d99002010381400031001550b0012460310740ba0081510429100e0740540e02c0c20040c0d10380c0c1c0f2901e400d40000c1e0b10030740001e05507038401a070500c3c0f00406960f200d920f0302c682c905000d801250a0b604904000d02202204000030580403800d001c040002000901c841c94074001900f1640c03c83c8418640303604142850030000c00641408202501082e000d0545580314507005045100703059800c19216a80b0b8000b1051104c508081c01120000700d0040001d5102c1055a940d20031080383c491911140410520b403c2c5801c1c11078100309044c2c1c1260140c20070000000040100040303040c3d5042101002c0b500300314a18100241e401d900e41003120440c00c40c205031034024002d4443e40615401100c078031000c0b400b04036040148410803440314241c0c0031107051046060341c48802480394900040e042c216540f10145810810362490f11008191054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 616303300 1250 616302050 616302067
    0x80903090906010e0901090e0f071d0709090e030a17090601140d0f0b06010201241a07020d0b09010c0201020909130314040902030a06061e0c080912030403170906 71
    0x807203900140340350304114a40851900544039811745070b02a0020607c003203070032411501e00318900710240c068a2003943c0a201d0811103603203004c6c0f41c1402d040d40940110015030b64000c041e1081d001f00d0b40070310121888d00c1442d40c42e01c60f0200280921b0034141d070b600d8140143c0c202d81d03908403941c01d4034905800d0b003040c0010400d02c080311555000a42000e4101704440500e519a42c0e050441900d054440303082c44010070402d5a070a1080b280f10541048008160707030403008480703d19004500856801c2004404901428001d03101600c03c0140d00074036922a542080c54080e2240b0001c0c1c8064a4643c2420400085580180245c0301e2604000e05000350300d42e10501880e66074040c20f902502802015002d1802c00c1c00c88100510140c903036084003607a40c3c00d00004c04011100c155005004104621404618440d40130401c80d01c240481c0c604119140d8150515403158440c004495070311501c0c2c1c04099070a0300010000d0011680285200d414490030500040c1841c85150b00056000104200d11103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 616304550 1250 616303300 616303309
    0x1e090305150a0e0d1116121101141605010606081b09060912151015180509010f0306060515041a07061a031903021e2508060708090309 59
    0x20b07804942040d01050420a45822904281c200000400028005100404000810881c00c02542030100c445204039160071041000b84140c081c00400c0c908006400f00507903840ba80310780381c03e0000c01d10026601c0501c9011004408240c5e4012074840d4281400012407a000d144024850209211004481c0032607000a042d41c0d1b10a1100c0d6a1046091212416648514000c400100740c0030004040450705940401c1c0458002405450310a00020040c0100d0101d036403408240070032420807910f0200ca82062418450494014035000398031480000358080001c0d01350700480c0d018240411009448100380040150a100d210402e076000300010000c8844004001500e80c481404280c00c2014a5840e80c0c00c4d69100c02070810b1490035118058078a2800740084009541000d49100020440e5030300a5114400e007900118042c060350722001408a050003110400b02aa5180c69640800302080310321021943c003034003865204248c0010310742d6014140b224041d40380a002181028481810071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 616305800 1250 616304550 616304593
    0x307120e0303010e010e18070e090f0a05031306051215030a051f06060e09190b1c1e080409050606070803150306130c03060911101e090305 61
    0x4aa050340d189460312218400380042d501826440e4900c40786549000e0240d0712542c0041c2680b548158084124000094005071100840f03145441302550b0f6074078040560308181d480c110300d103124026004840d042040c084002e2a0724104900d41400c1980c031440d04440034000c580018902214130340101c0c1c4000401a82c001d40054000c04079542425503a5445080c0588400c031030500c0e2420050b228200443c50080f00068812441c10180103041701d40001c2505001030290b440c0c403190003804011503041a0400040b0007400361241c44000b801d2080c240403800c03801d500b0386141040701c8646141c0c4103540101000103401c04c040b1800e041c02c10512100420002d4181070303003c007040052a000a0082d80914424442c40c136441a0b400c071032009040c1002030092a44100d410b2402003030300014640b244203029250000400104d490350380c03401e0044000c840c031501354002d4280513650003065001c05144140004515540341030007210ba42683c1e1034a4502004010345c12181c3c03000700201020300b05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 616307050 1250 616305800 616305827
    0x303050103050f0706141b0f060613050c160224030609070e010507081305210c091909060609020f0a020c010509100f0e06130620060c07034b050307 65
    0x3081c0e090010087c81d280503504075509481c2d030002c0c8200400d81c40c1502030807401c01c500c84c50a011926000c0c1144c5090300c61060711000d50413001c030840065494003001c031107503800d40701800d04807928204102425074100301c428900c24901c542c00201400c0c461010140205010f84a00d810a281ca179100c0040d50000d50701014a000300d10700014180da144100207440c0d4203008025011001c10200709402c02078500002c03401740c2d41c1c031070900184940c8680041005030300c40000242c05042031410001500040e802010183c0c0007007182a01104402d0090102c940150211007542600b400191003500645181a41c4a40300346003001e40e05016414071104691546030540354150b0300340000c0e680390442c0c1d503101032112070840700740700941e00480c1c2118082c1d50385855110005c01c1d05100b40d03403844000c0c0901035655000c84c0d01400c05020740c4c804050030100003a54108000d42d100034100c0350284010840d0700b080030203070303e2500d11091400ca24032110669105072955440680988500c041c0100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 616308300 1250 616307050 616307077
    0x18020907021c0905090f0601021c0c0c0e19090314030a090f0303050108010e010e070306150905040b06180405151b0403060e07060f050901030506120102070303050103050f070614 78
    0x2684200004918191002c2500c07035100c507900d250a00c0d080c0803a80100411030244004034405120041c0c4e00003c0700710070064030500f8079185100c0640c00300d400f2203d200009062070b14200002c02d01c440b28088041c86030905280030030100b000b4840102c02d4854851000d400f10700d6401111700031142c0c082c001d5510074103400c00820f54130206ea0700c51a80203040ca0090300025038880041c080003200303000f46d00f00f08409000a000d07011101804980f10b04203840000c0c104c03030f901d100c100764005440056034020107201e0300401c0746107040c0c01e00b004004811241644514600090110049a840d207200d010b55041001071854010054044411007400342201c20030352404850600601031000041015522030280416142482c01d8030918064468000f1010320a0820100c000c19038014199805d0ba242442d0124850f00d420000c11b41c140310281e80070006500005040082c5a01500514100da210310220380d4050440e00c0031a480720b081d0b01441d40042d40c5c01844600a2008034094103c2450140b0f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 616309550 1250 616308300 616308313
    0xd180b090402033c010906081c18151214160909020a02031b06060d030e0f040e032109190203010b09040507030c05010512010e07170a091103011802090702 68
    0x41d62070813161403c0b40c18070580c0c2c1d02d0a84050948078522032040c0104800e130300a121582c14911001d40310401400805004031410f01c00440c2075104400e440410202c0c07004018100742c075400314011203060f041450b004181b0040d121111103229100d00030824245d00e06048030341d01c80e0301b00d09032402c0d039a079228020010700720700100e41c41c0210710040c070381981c0a400659844e200311500c0d00d485070000720399610035001030041003582d0302c810691840440e41454010000c0c0000e50003c1c8801301d00b0110301c0d420038940712410103050303c008010584d035200d1000624040300000010007030620110361a48450b00b000e810110458000c40315520b03114402000420b54088910100703003441d10444082d94194000c103420828014007001e414042c00080c03038040d2a05848405040c0c5104042c4100006d2455510016110034802e03015850124101c8604804a082c141c0b024000340040f58400c2e143c0541904241d0700703d10701441b0b42c040d032007842c0540c06034040c540d030208101807400030000015406001d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 616310800 1250 616309550 616309591
    0xf060913050c0403140d0c140106121515210201090306050a2304020618030a060e01051801020403050c04091403030906041205090a05060a0c0803090d180b09040203 72
    0x41c018988503440801c01c07503031074518504101d80070301d800d0810f100641d001181d209240a50000440d0505ca4206a00c0f00a003d071180d1640d004200b0365000c611000070119030041006517000f42034660b440c841c10148030305220710581001403680c074071400c075100c00b0454880d0301164034544228070035030050621900c12aa46e44401e0141d40044411802056a440c0c0043c80c20a9400c10f118007294281c1007c42c503468980d0200d25688607900143c2108100c6100c070340903564080003201f60746135002600703000c00c004041c0703041c2c040c01094402d29502c280884840d000c04405100742e8007141d030080b0080c17071120302441c10f000c01000028002d0f180240308100b6804010b0080000314003580c2c6090013000e580c0b40c582444011000319448010400200300b002d918665030346517034001a20000ca920f1640e400001e0020366086070036001c020900071011040200150002c10325000d006000e866200da00004d01128001c4801c05014100721b00c0d00c140304011882c20706a01660380301c00300d024000a00a0031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 616312050 1250 616310800 616310839
    0x815040222090809040c051813060504020a1806020307240207050304030b0118060e07030f0b030703210203070b070e031603230d0504050409020307030209041a10050f0609 75
    0x44002030b20001c0001800c08001e0070544a0160910380c20b1034118104400200b40c0d44014503230014103440b03a00c02524800c16100b5551000d0024107005204540d1001e0006003e030071031595442d140e15565856800083c114004801c0324010b42d44040f00d080601c500f42003041c4507c1920002602165080c032011001030070400090020b18000c40c5512819031410340d102d44c0c0d40d000382c1c6241c0056400d103a0100f1404c1481d510321078006c0c03503a00300071070910342c6010841c00030000701c4d042c0c42d03040c0b003100750000600c914400500099950304901b5660796101c407a042e65684a201401091441c148000980291103000a81401c8030000c043d504802e8a21000176104441307508241c030344004005a4503481d4040608407107903040c0120181669100b100d101a0060203180f10302c6018a458001e104c0840d81c091210a010319401024406241014140501c0d00050010310b12a000304043c01300d400c5c149440340d460200d80c0c0082c004e0001003044c0060042c0b5803c2260059000031180c504500701c05003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 616313300 1250 616312050 616312061
    0xe130510150512060109030f060c0e04061e050d230a150204090b010207060806270703020306010807080609180f0715020709110403141c03090c0815040222 68
    0x415035509072940141e6005011403c8080c010505004490404000040e460301c21001d04075000480000c001445200640c0ca9480b48000a40d2003494914040741125401c20184a900a948040c3d0051900c0d8410320540000c00074001d4145614840070080c844000c00b0b0265040c0b07514016a0105a1182d0340c5078403029242c00c00405150300072500f4848504284140c01c100042403006001061406101500c8540c000d00400c2c010080d0b003040340320382080c441003d004201112104141443d0019004000703400c15032703a00c2e00080c1ca5402007030007248907403074150107440024001243c94482c1e514180b107045070400110098000c03c4020b258810b4244000001030501007004d022004103a04000e040c841290030070701d012840d01c0d2000741034081c00c3d030a60302903070f5204001c022587c000c2103125141082040c001500c2e180c41d5a1000c101c194560420380c0710901c502a4100030a4407265010f40f5205c0c800400c4005000c190002005440d0814517289200701c15041c21000801c140e001c1426580d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 616314550 1250 616313300 616313339
    0xf300412110f01051908100b04120b0609011d1503011d0c060a02030301090e01020c0708030a1b030203070209041506060c151404060b060d1e0c0e130510 67
    0x41c05100c2a2840d08115000044106092a2003480c1409100e00362602100d2001900108214000002c0e01803201c80d456801601007244107030340720750b914125040701c241384c030314115962a124404a101810582e00042c16034080c11402c800703041091203010b4018000074401031580388003c0c02c65240303460130b2003801c5140140000710005111040b4001d85400c0b000c102013400b0302020462802030503404800da0741901c3d0041400310b180e000400c400e902901038021007880038042c001c40014100c50010081030f40ca516512410b03d49016014000764444003003d0280240e041000030300010b18100c866203601a104030880082400000b017000e00f100d42a801c054081118540341d0014000f180c40d41d03882d01501404240500350200081007003031000600001d01c05a01c4030310b01075481e03840c0801c1d1105100c1c580001c010f0b40880d55440403034504481c0110b0395152400c201c04602a10604c422102410060100c02540e0a944200e0000b8000102514a407589004001c220784180071f11402221 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 616315800 1250 616314550 616314563
    0xb1315140307051509090708090f0106050604050405040212030c10052a1605060a020423091311120307020a121104020c19140f300412 59
    0x120401611110502090341090502030500d03580488590380c006011800d60350261400300034122660b00d0f480c20350007003082d455409140f01c41042680d942c8191254400c450002c100c03100c000d101c181071402c9440078010140c10080410040c044c5003025089650050702c084c0042c80781c0c0c2084120306003107400070b0707004c0c0344260407440c000d0308000494050207070880f5a80000385000c0d07013a01c100070b400403400b42d40e04071ba1041c0801d42480f54210902c501c0303821a08101995094039166107190000e40c0180905003503101c48507046584180d42d2422151b070756402402c400000d03246c810000c140c443da1402d040b1503c101016010541c2c0e180c41841c0e03001c0103d400025a1980010700c1080015015074018916454241d03e660002c908014100b494445007035600503603408408811604000703008866844000740c43c501001000101c200b01240807840c407090b100764949441c0110746030034001054103605000c41a0822012171150180c403582a81e2100342850f0595481d41e03152408030701030003a01d24 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 616317050 1250 616315800 616315811
    0xb0f040e072c070804080f07030f0801090c0f030f0b04020f0d0b09040f080a17071718060a0e071508041a01150e0102011d010207120807020307080304060b13 69
    0x30000090610114104240c03000040c2502c41420703402100001d24502c1044a43c3e800304041c030012800712421052036885440d500c1400e414040c0a0610451103000002c40035800050201c0711413041e94101f108a540e0742d0300d80112040114003511403410145034103503490101250382d584a02c020900031080d07001044d12454400049001c0720964103005010312400001c01c000100070f480c40b00c800c140d0046103039454600b510303c1110590070000850080cad0313040f401070144998200c3e0201180f08040d5030404016074402c0d08912111903602d42454a5a02900c003140c01d4101c0f58000b10130f14039102c0220340c1416940c6203400741c400c003001142c0c00411002401c0c032043c8101c603800000c0c4400c108400300d000e0f514004c1c0020020b044100354000b0450090510b840c1603200707400580c0c001142e500c10304180440407000d05e000b0b500400044904401c1d036041d100015005564035840703a40c82d90091410701e0903e44517180d1a0348018411580c066998200000d107036280407050841c490b0100d000100e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 616318300 1250 616317050 616317059
    0x2508090a0905090d09030c09020f070b0408030405011a03121c060f030302070510052703010e10051003080708030a1401030809090703141f0e0a0203040c0b1c0b0f040e07 74
    0x81400184c0f0300c0342000b240e405c0a0010034800d10b14581111302210005070341c0d03984505440d40c20700a01c0030007044008007006002c1403210f0500514080c90141f0000c206031200307074049001000403105010b0b01a00242442da00c0c4c15594800392000040316080b031032000c944001c1c1c01040b600f458002003041d00c4888024418990304009c1340000c1d004c181c850038202c92076040c0240c51350003074005d040100317a0107e100507840e212403119000410030190003482070100e003d01c82030301c1d800e00d41305d6104110b107440009910615032404010440b1380216500e4500100c58427000d045a000801c62681c1a031101402d001c4c185074841c5150081d406102c5068841040508100c030040c00a4010704c00c00d41006003448204801a030f44e6601b00103010300000c14424a070400c2041c1c0c0303c80e5402481043e95620402c02c8000c0d081d0011485284503e0f5007450340754984401214a011b10b0700360303d4200c0c140d444142c040c10850703449204028070003000c2803040d010708000502550a0000c1000d000d4010190402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 616319550 1250 616318300 616318303
    0x606030b0703060b120408071a15060f0d15030b07050406030e0f250513050604060512100b1216030302060108070501120c091802031b2508090a090509 66
    0x50304842503140500503070340342c560a0813060189000401c001c0c2150070104080200880448404c10303400038103400f44840308400303606041c40c02c4990180044941e4514215407400404035002d4000303107407800d81040e41164155005100c0819500a00d200040011001c50312040c0740601c20503d070765407107544a09001c0020706641080c01c002500368002000d0350542080440c009000013108410a02e13240250f44007501d40b002e00d07510864014210700d0100c10f9030020341e04203501c144d1040e117080c048165100d051040c41119200000c660f50898800164a1041600805440300c002894821280404004a801c0075000c0700b10403c0710300700c1c0c8410010141c06005050040440d0005052002e2070103001811004280c000e003016140c1e90314003030710390a01030058440500300342c003501074000954006580003548180e0300301c60081d251102c600041c0d401c00044651124981d206c84214140050700702e0812440a841102d0302c580a020b000d032242c4400c0b200c00010701c141440407031142030a501c6503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 616320800 1250 616319550 616319573
    0x6010e130c03051b060412110103020d06080705100203070c0905040c03020603070503040212061b0f0c010e1b030a08070204020c070506030c070c0e090715020c0612061e150d090501020403060603 85
    0x145c06200240020005414442c0d40a41d115800440c08000161400300490003071142c03000904000e85811801b141581c0c000551b2015500c1c02d450403c0d1a060702d9006998078024035000500d140c1001c20f041c00000071703582045800903c600c024410301f980725400505030742c0044440800003903002c0f0070002545450303005941e107c0c11000150484d82401300b4115904107419495100d0200d00142000c0003c1d1410100d80000d8080c40003003005e00145440d460319602182a0046903413014810f0361039074500402c000f100d51b0360061010707250800c190b00344000b83d00300420901103409030340800a12903c80200841c031aa00d58101140d40da100c0d072502080c00030b155008201a64110350410881807000140c2d242500c004401022400107250422881c1c5102008030300d41000b000f2406503003c040113030040d4000d580071201480c10401012803840340e045000303981d0358803c803511084880c820909006041002600c100441c00b070b00f941c2c543c0740c03c0e6030043d030013221850b5840d902007040c400c1600d80d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 616322050 1250 616320800 616320853
    0x203100c17011401141207020c0102120309100b0d1208100906050303070803180708030a080a20090105130803090328060c120e2d06010e130c0305 64
    0x341d03400c1e506240d52525032940d00d240c15414400c5005000d13088000d03003c290340d52800800d81c06101844c045400a40311910f1882d40350140c45005003400c40030281c0c6080c0c906c200e0008000780a01d25001c07040902a1031044000c9821120f03142d114008248048184c60110700552076240720ba0600c2c00c010000c00307040c1d40c00040300070b1800e00c00b4031807a40d02100b00c0350f840f0f400c04030003508c036103c4035240c8205070303249441075195100f100400102c601000c030140c000c00030152944451079440b000c60200381d030040c006450211032404024038030042001c0180040e40010700d009400c0c2401190301c20080501904008010b900209408002d0714003040b1007248420510045103144008000c056010420200c0040144d9100c8078444442441405413000c600b019010511036921210122038030f6010203110300039014000c090304180e03602c4120f00f0030001030544009114a0307107064414460820042e0002c0c2842ca45c1c0d8003050040f444041e0200301650044016110b5907071003d200355091942e5020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 616323300 1250 616322050 616322087
    0xf030702160f030206030a20041203090e010b1c0b030307030e040506060f0d27030503150312070602030a15030804151b0308150a090b0901080303010e01150203070203100c 75
    0xb0500c010307103990341500d03003080c1803010110300c010582c4100d1b0040440f0301400304030303c100801c0c00540400f20a11a41079030780252141e000c82d40e1150b0000407030201c24011440019020418040d003002d00148000a00d865420700055000249000074110350180710190006034100d4510410351a0a22500e900708404841040c540f08150484540f035016100e6030100107640d400318280302c20044111840d5000e55246101c0d0019007501e405800ea4100703859040d00b4140030b02d80542c09003070005844441103080c0b00a14100441a501d150183d07200030000c1ea0141e48031581900b0818020f003072007003c8e41c070450601e0744903230a2050880f500b4500d106c1002c00c00c21400d0240041c0521a4a0403005a8041c60020b04a55444049403088013034001c0303103a005005420000744181860303201307036030741c801c11641a04103903a22412641e90740020b000d00c092420340c2c84010094170000140d892204249401601d00389081900042d041818928840c48066241c010194036903a100341d404200000c50b41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 616324550 1250 616323300 616323329
    0x80114030606061b0607030504050f06150d03030b030d0807021501140d08070212060711010e0303160c08030c0306090a0207030f050d06050402190311070b04170f03070216 75
    0xa503403214064007240c0510f2002544058110029912481072181c41e8201c4071a803d09200040007004216402e460301d01444600380a49000404c00701c6c02445800900c0504010010801025444408044040c50b95509a002407900e0a00481c4c0060409031110400762a207400b01a06082c0b003030a45240c8008100b00610484d501e0f20440304440000b80c8006840319418508062284900340019500c108130808502401d600010b9052150a6075590b0040c0f021001d030801d402d0311050007454105400920000d040d0b00e0005e2046080a04940b406003a00304090725138864030b910650300d00b00f101100000f040141c2c1000210765401805d1000214035180d07494600030070004045c03500c54100140003c5040f00d54003550020009018014011562010b0400c51600b120309132404070804682401040070313008040009440481e508443c008000740e8841e50b60071501c555291428036000c00503c004241e2a03100d001840c130680c0160000c00703140742e181c1031680382c103a00c940c0300d03145034000302d13 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 616325800 1250 616324550 616324589
    0xb09090a080412030522090c090605070206030c1c020c0d09050303180f150c0705040b0a0911070b01330909050604020405060a050418091e020d060606050a0801 70
    0x40111400c40d03a003840c03010a0110f252400f00c8042c401d0494200d10b1a4a1000c204550511142240f084034103510341000040500074090321810500d01c281d2000c910140310720005400c0900085500201c940f003c54034100e108250002004185080c01129960110703080326100800c1103c41d05552050a01413101c078500000650b0341d04c11a0072281c01d010800b6a0120b003510b500308100407400d030041c1070810410b20304899205c2504280d20098141c404c8403800146828036201e1440c260902034041d0303000c6c606043c00d1502510074220751941248042011790082004001024060680c40401c21500d00316a07039032030060b22101d050f905011420b04082c041c1d46400c41400c1d0103c555020000c24181e441000050003405140d00154012500180c902c4420f54020700900c04e5640c5540054501101d0200310411107400700c00c0140214910f018100c80d2020003030307030034840030301c0200505005207a40c0d450300c041d501c80380d2000000c95800700f9000c4107190094440c5000d0040ca5a41101c0135412 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 616327050 1250 616325800 616325813
    0x11040b0d060b0102070b0c0f0c150703081b0708071a2a1b0c011e02070902280e011d0d030e0a150206040303060b0304030e0f130f0b09090a 61
    0x4810009001c9680c1e020b601c0c401d64000e1051034028410b00303801d1516501d80c94101030301c0b0300440401001600071282141a10705d01880d070f402001040032300d19400c1004945c0c1c1a1740c09240a8200645d039000348205004150352503004016442c403661189880d681c262034105010038013008014220056882040360100d083d07880c00c036407004031103813110b03440300103040c6517015104948103000389044105c034858070180002190444082d0030703606d020f00f00c03148512038201103003110340600043c2c01c5800200103800c642c0d0003070318180c581182d000350104041b001840c0d03510221540e04c00801d5826070001020b44c2c100c80e00030345c0310f0782d441c600e202440079850002d40304440012005087c0501841d0201d11612215201d50280400c0c0c610b0040f00a18140b01a545402c1102d0807800030303042c210007081134181e03c01604e010f01d505072908501a207a00b000c01c0415207582045a41100560440100011440c01840b42035602d900c0c0005041c08603d0501c641c12000030140320050344459000d0000425 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 616328300 1250 616327050 616327069
    0x150319020d0e011103010608070807050f0a1209060f050a06080c0d081306110d03110a031d01090b010e0f19090203011401081c1b0f141911040b 63
    0x10a100010307552585041d90701c008050b40c1c01200003562a01030005200f04522000714140c6107240c5a01046c1da079000e0088481480462ba0580040c0023071105140c40400c0304003804900c059424401c52007640020b0722001c4a07070f180710a640003612100d1100010300244200e079000280030324140903076407c0829482d81c2d011400d4025008108180a1105001024040c0d400e020000d8001252480c1c0c0c03044000c00c003030044000700c042c038001c0b1090b0311000c80c040c1c400c03400a01805250941032041c8200154003c0540b11070b0b4540c04c81d241c4032a25001e140030f200b030041451141c0c83c130000d903504099a5003800c42000301049402d411032000c4c00b1000d4003444410000c500c40250204003849584042405011703801c490540c40c01c14080089030941001c02e0035803c6203c501c0101c40307003208540c800c81e0000e8008131003c45840c140d00061740410344044403e0074550040c2501030410369000e14075803810303401108400c4c6801512105034100a445204101d20307110498007445607a0740c26000072031592 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 616329550 1250 616328300 616328341
    0x60c020108040618081c0213090c0c150c260402060a0905041503050c01030504110f031e010e0708010603030807120e010c030203071b080403020402070302070806010f03021503 77
    0x110008080080d10f80148010500c940801c000c1c003c02441d112081ba0010704030020b28458000034102c070510b9500c00c0d034004000104000c4000c62510b4098801400f010002c94200403004100c0300100741c41c4108401002161782e00011042d154010052014101c0c194902203140c2100c142000e04406400d51034105070121402581c175011203906541d041019800b064000d4141045a404030301c42d0b401100c00c0383d004a080e200708501c1400110304507001110010f06882d100085840981040c41804400d12400750483d03103078454805540a010039200e100700100d03034513401da9502c680c0301440314a0040440307900074441982150b4002e004400c009162004102011003018007003107558100428a0b036000c402008403191242000303019600032107298000c5801142050300b03028410b85004500d80e04403a8603420300782150b080201a600920b415400c42c032584c600441c50800900405000340400e030550b0403803901d03520510043c40e24a1011443c21b810600401c4030b866904d130800030f620f4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 616330800 1250 616329550 616329557
    0x10050d051e031e0d050606280e0301020705060601020f07180915230c0405031011040f1514120a111306090f05040504020d06050a1407020a0615060c0201 67
    0x800c0041240b4500840c0800700c01038015030443e050400d0100002d220040942130305002d0342d43c03420705102551180301ca01441c2d41c500c032a00d0481c104400001c0806080c201d01d08400741e00d402c00d000a003a6080010199195002031041c028150380400256884030031100103001070070301c1d205c804501e000700f0b691400031340341e00e42c00000200103404034086404a2203840411942c4080c010503600e6114490030200e40854040120b07076000e901105071000c4560040050807032840d4821002e01030120744002d03100c2d000c1d040c0004601540d81d0542d850240c4500031400040d0007980d5030040c504005c500300301140010030072051199454843c80d031907006240f0500402c0885011100860345d20501c1c030b5400381040d540c000403941c9688450f404044030024110381c504143c40360300300011901c00380c030001d500c456513441403000039000d034000e541d0142d541880080e103084c5070300e00281140811100300700140c1210000000300030140c811810142105080c05484500b001c1c000780c0800b64911019060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 616332050 1250 616330800 616330843
    0xc0616030c150e0106050a0807030f020402160b1b13270501060c030e152a0a1401150305070b0705030f04030f1203020f07020d06090204050f10050d05 66
    0x515014041459500d5030020800710b0b14a020300d1600000d110252041180b9401c0000010701e80c582001c0d820191100706000d06059440d56460000440d02c000c0100e8000d0f4007030011481c4840060700352521140200020501e42c9041d0182400ca02c0b00320003017103408131040c081070302c0070001089618240c1d00c1000b81141c5c4810008401130001c5164401d108556007403a00106445a126081c00f40840c400d03240c1144c0011184100044141110340d142012402400703192404690702031a5070007101207903462808550610101c50070030341c1720001980e03030701c42e14216903501d8002403045010a44003210401140c0f401c1d03903a0291030ba0814455038a402c0070204c1c586040c0305060040714820038001e0441507841303075285000e200d000580041647c0855264517108819802030086889150b11943e007149410543d0342040341580041c8000e88441e591103202c100141c85500c503260144602c1c41c01f03ca120b1a00c00da90390543e24581d00040e0080b0f00850304880041e1001586910300080d6003042d412 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 616333300 1250 616332050 616332053
    0x5030d0b01093519060b0a06080f06010305071106280212010b2208070e010b0313470901020c120304050115030f1e0503090f04020d020d06080601080c0616 68
    0x313842100d0410076a4005140e906108100c050fa00242c000d60040da4a400d0203503590700151a40d90f011510007640105000008000b90701c01d5010740d500c410a0700385480d44603d00c070603103850241d0846070181d400301100c00b03110008500020781d210b2100d0741d080542c80d103107403090300d506150010b100c5c8201c0d141010548160101020807541460402c6249012a0b90b41c0d4003117042d9190342c1d42c03203452403410103a0004207502d0098400c40e44905440b600505800080d991b40c060030741a601d204000d42c9000c509103004118400b15030103d02004110000d06401d428008401c2800e0007130324110142e03104015940c0e016102046103030400c0d6102c1601ca40b00d69490400c94090890300400b10b164801d1b42030007004000d0340528416515005000901005405914940300000300140c054400c0c5d00a001014035490a03c10b0880c50003c042e0000d4108490455001d059801421903007080507264035091120f030340304000b914010840c5200404c1008800000b0501c01c0c031403040c6100d48405450513460 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 616334550 1250 616333300 616333303
    0x90e10060c0b0a0605060d020315100c14030409050a0c030605030c03070303080408120702160f0506031906080d090503011a01051c020903030715140c0a1b05030d0b010935 75
    0x101009015984c1e182d07d41c1c07241c40000d40c0100c5400000c1a04840020307000d00f0065480c0c200c1040d16114503000c901241c440040c004038054400c035840c80100000b140803402c42c05668012a0080d0700450220841c80029040d00c0c03c0c3d42000e4001c5d8003c000c440542e50b00002d00c5000c8a8050800b0102030721903042582407842403e4614a094547c01c0522003113690003d400c40101101c290340344a03082e102c644200c41c40c175143c8180c9600580a0003c1a21408022401400142c000d100064003540e296a802e0800c140c0100700c401240c1203590030005404d0070f0048030303124882680282d0a403640b240000c0c18500035152010311f0380402410f024808401396040391035901004080700d858503442e1524440c500903003242c84107014100403840d140a1aa0982039000391109c00d820350500c1c4628104448005034508880440b40c103400e0180f000c142d06000400b58284404004203c03203000034005446c900351075000109640c4098061540710310000300c3e0b10309400c41d42c010140c01c6a400e44405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 616335800 1250 616334550 616334561
    0x1b020f0607140c070303090f0f140906011e0206090d230c15040803180a0302060c090a0e09060403090509010b071b0b1602040b0402130909050a12090e10060c0b0a 71
    0x20f00c550700c5080008028580c10500c031030210765040e03841d904580d4a4074425541a1458880d0b594800302101d2038040070f00e000070704c4503404001850548107e610003c941130303011803414207180240e00032900384007504d4800e018420318240345081c811818081642007003070007181803032a030090701004150b54954103000d0140012500c00c0e40110400ca06060905140a900c251951001140404040d0340b602d0030209a900c8001e402d40c02600740c81d621280c0c1d40c021644200c2042d6400f0591035400719181444882050240e217420005205519042c54040c180304002e8004601c00c0704824010014550100110b608065001e51858a1441c00301c0070096419000d4204901c07240010690045008814104600d05c41c000c560501030014146d0a2004901c220690f65094080e800020b11508456070000d42d14944a102110b6081c17405441c0c0d05400044c81444d10001580420108202007169214a400400b1035040c001d0709072a00501a001c440c4c6100300914a8900030300059640c0c0156018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 616337050 1250 616335800 616335817
    0x904023a0b090f061909050907090606120e031c020d0501080a0b31050a06050a0b0f210d0513051f031503050111041d01033f031b020f060714 62
    0xd94040306c5d241e42195000c0c0c40101c590b10700c28454103800060042c214014607040f603a075a25080904080c00301080c0c040e00d00c10703140500d6071004104103445a0b880c6041c4900d840c0e10384200584669a4991b14000c0d1351060f48000c2940d803040e0507030404101a04104c581004000f644140360310217000701141d040742200303030155100852900c09c105201d004140740806038800c04042010380c0d1950641c5080710706048859402030600035580e01c0d03504102da041520102d03c10f0042a4000030082001d107020039440340b1a000800101e85000801d00c0c080320300c0c0c09008200c90110460710040e00c6070703003180e0241c01e01d003040640301c0c2802904040d13080a41400b07140c0001c001c0c0910016000d900d82d16501920641c0d800b208080c0380c41001185400c04107041c0c0e07611111840b4000d5511500d00c4d01410800d40800f0702d02007c4c0030454043c0722a103d142400040c0f07480204401a8500d003462420b42d80701050000e54100c540502301041c400300e0516400116401e20401400d500ca0540303c0c1402050203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 616338300 1250 616337050 616337089
    0xb2701150e100f030c09150e010e1302131403100c18060201020301080708010e0d2a0b070305090109051e0c041505030c1005030c0904023a0b090f06 65
    0x81d10442e01d51104040d003406000351001d000340d2509001c01c03512003049100d5001c1c00a03400b03803590446403040e5174645181c44145880d50441c204880010180540c6421000699030700144c1580610f00d42e2030b104005141c408a900480d8034030001080d200d03091080c4c0314036001d0f41c45901188071401000b10391540080c2225201200351248400f074000d43c402e009a01140c814501c000410707085c140501480d02c450400a4000c02c100d1080070340c0d407070140004503070407003050f042c8041c511006880d0b801010b42c040d0005000c68240144054200e4402400300b00035a41081584e1000c038400180030a1412503102c48406003480300030041c0d051080c41c6011a0707015080440d5108040068240390003a01c070b04500b0340320f842c200300c410000e1519104d10890081002840011002c031542c030b01800075038401420161821041420308642800c001c4103050f00900b90101c005082098a2003e41030000820804c0144450710030024440a20040c510b114120ae010001101901ca801c03468064122025 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 616339550 1250 616338300 616338319
    0x6030f140610030c17010204120804031b120b0601090b070501050411060412080a09150203210c04050616050304150225180603150b2701150e 62
    0x9400802454012180c0c00944101d901041da42d042c0c206051040325405014400e0f114500398800f080ba506290700000750b035500744400581c3d07042c8030ba199800c2a00c50010b8981c1c442c11440c05543c0500d00015924801d03441d010300f804140c00d1850100701c840e421030108100e69446400484024800d900090944000440c2d40401c00c07205401c010b0103a4840c01c40c51240329a248180981c41c00b1300e200d0342e100c040084030340c0c03130201d480c5000904a03d501440c0038100980c0340c218200d0b10140700190b1070016030000508c5800582580c3c104da25030071060001e9803a6003040307030311800180914000d003803256000049851a00820400c0c1e0240340354020107594840f80d80313055207400c1219161005015021380f214046558800102160001c180450f412103502d0401d01402140c5c3c0d101107410250302d0f9070304808130215078100c1036000250b68940380800c04c2803140090000e005031201f007030181270b8908144910806403aa07d020305403109070425031120142003108440103101c0c040c1e1301d41c001035403e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 616340800 1250 616339550 616339553
    0xb1204030341090307030507020913120915030504050c06130f0902122d0411031605010e0a15030b2101050601031103070207051c0b090601050f0307060210050a06030f 73
    0x8a004556002000708040e040e0f6400403120f07100c0c40303001001000104100408401481c0072410980c00443c0c10241200031203959a0b41081c0c03045201c400004034019443c00c000214070070101d014134404500d800c1c0480d05096855a45d41c6000140301031007002c0224400340303108090064a0300400c022401c1507201c69980714050001d501c4194515840050b1100080d114824400c107814004407200000404611000190f0f08102000d0b0040b5481c01841b06580510740c3c0410403041e003c000c00b10050303161460300001600c075802e10000e890055202c0e82041004210603603c00c07000750071908010515042850008503024a507221020300141c0c1001205094003055010328421842038030100040c14040c0710300a19030008455039401648114000c5c000713400e02c99103801c07e10304203564504542156580c1c0215194044910655a6102e40010031503460540c203001520b0800341c001d418124240b400094a445c100744030b140c2e6072a15040410b000b8017455224400a642203d28030154402c0c6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 616342050 1250 616340800 616340891
    0x603011502070803031b071505150108010611060a0b06040503030d0c0906030b130c050913091755030501050402130e0a020903010e0a0c0b12040303 65
    0x4150030000602c902c402c0402c0307844002003100e003d003c216000300c41c80f83c20581640c0c0340d51b100c05400c940704a44400007040c08402c50059501800106850750010300c010f500040180d44140d001200300041010000403411002c90300c9604a021000c0100d000900c0c0700120320180f089501280d0144400281e00e1444e0003d41d01c01042c540c080da4418949581da6a800c03000e9500c840100303607001d031042210701c804aa86500840c201d038800d0403c070f070424201c500080e8a003d646c40098500c10b031605070803001c1164030b00c01141c0418028030101d00b49011140040c0c81c1103291001c0c000c0c4141f83d103d8016814984907100381d010224000d200000b181400391a0340345145200e1064080307802e020021500f07192500a44200c0d01441c0508802c0b289480e1005116541c041c02c080e10560b8200407400c0c20340c41c20301800046020400040c0410020307131921485a03500d42d8050106280284810042d1141249002e5009901494007164802c148a045003280780c824801d8055201010300018080c040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 616343300 1250 616342050 616342079
    0x50307121202030405011409030111040801060302040e01150e13080315011b08031302010302041a09030d09030b04020d03020f010e070f060e1503190501120c090903120c0509060301 79
    0x224038107601c8540414031041e69207020701e0140718003150608107082070903800703100907100b4040020004540d007201642400c12551040e0010724469440d940c0034020342c20503004040e01151880b008010b012109290900040810702810706104212801318101e900808101420b06401c061080c0c1d590400c0941c401400c80c080b00b99501040b41000404140d0100c00540d42d5070301d801100c000d103543d5070b4948110f8507140000d8100e0600d82d090201062445400050307901c0309a082082a589410031070406250840c41c031040340400c02d000c00107000113041d5181464100d6030542e110904185103186c140e08100205e4103507005580b03800c0200101400004100048451f0705103204003290311800c2c01c407110114841ca080e0020844540001c09020b800002d5500102c03034030740755111180030b48600040d20002c2c0d00c0540c48040c007070b01d1401030000040e464130040444000c200822166a03070082c1c200062548440c3c0b4556441025103aa0350040c02152040000100255920341c3c482004030348121 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 616344550 1250 616343300 616343303
    0x1401021c1b0f031512060c02060f0907050126070315050a030503160c0b04031101080f0f06210109032613060e010b06041202180c0d051005030712 64
    0x90a04441000a101c08101e80d403911070316644020210041d1003095016140e40000209042091180010001d000012280103540300780c030041206032048500901e0404040c0c512443c005c01681841540c0c0000980003007210000e003030010300504207607040c042e048084900c45412055180c20480003d51540c81755015503031005044132640d8841c03080c020140203d000007403942d031040090f206801c109003000b078400c51150402d116040c0d2184540071031900290300488540480030100c2400d5031b0804d80541e480055011202d000d4500030b03d806081e001e01030901030140d072803000001c41034503041d01c0c1600d000758580c0081c04004054034004001c0d003042445030307060940d00c5880140525410a00e540200d0038007000b14010240d035200c20004000c941050660342d942d40301c295441e61034400190000f003005035080d4200180744d0050208150071025100e10421280701080120480e0400b038800300070f082c24000070980e96500d1100d1282189400c100c0e40752043c4640003e83d040d10305444070700c26 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 616345800 1250 616344550 616344607
    0x40509030306120d170c040f0608071e1e030e0f0c03100c170c040306051510020c061c020d1b0906030b09010e0411101206080a0b0103020904140102 65
    0x20070f191030741510348464680c1c860000b100f400800559800ba01882900100c030102e0341403801e6510544081d010600d50300c8074011400031010010080d4110440c0e03121230321030790380040c4089000721008140c104a002603c55200190b515803110714402c0d804007608402c10400c440c803000c040e2003440d0703907040f801728564802d1041c020b803480d08409034040c011840745151118a24801c0071031100c2c2030382070002d1108410780c00034003000022901c2030040a02032100c070b10000c1080c150b00400d008003404500901c0083d58000c0d8441a06620703031100700e031154445ca140720805100218140c0000c2d21407003000000582c02c01009840f04030007004040c0f510289078550501555a410058080e540114101903000020100402034942d00c00d1100c1d600030310404070050036062441c0041d003040020a00200040c451012140840b00d441c030503c40905100030003841581c038660790700c440090050200a021701c07004808a001c11150220304606880c40500030f540300c961342080112003035417440c2d026240 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 616347050 1250 616345800 616345819
    0x6020415030e06150d050a0309032901180207080f03060a121104050711160e070e0a05040c02010b03100e0606040506010f0f0e030d080a1113180b040509030306 70
    0x400e4028400c401c2181040c0c0090519542c0354010700c130004644084c0c07940c0200c1c04164a0000810a000442840f403003070b00c1d40754280f400c60a1904402155141d01d001c144000e151407103001080f04481c604580b4071003444450854140000c001901550790010106540421318070320a480d000c3c05140328550a99141c40c520784c1d6128034400052585001504000c00c0e04081c4080e41005d0704039980c00a80703403c111820b003400310956840e00580103030944c20410310340f00070b10011a212041c103802c00701c0c0b480d05c05001032081d0002400881e003071191a01c80c542d0380306903070700c0c1030700039084580c0464006042c1c40900450030a040301504846044264034010000007a100786000e104142c010041070350384010b080f00c0f9050564603254544990310911501c0400700d00c0f00c0c0d03004c00202c691005150f58480060502c85c08982c1501e015500f03540022800740812461341145588400440d000d0700e0a0420760120040b01c10010580c2c881d449411a00305020440744e00d400000440c0030b4241510021007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 616348300 1250 616347050 616347089
    0x41209080f0618121c0204030b090c0f01080912220810060509070503060f0d020604090e06060f01140a030204210b0906100b0d0e100c02072403050c0d09060204 70
    0x1143c43c5100000c0c0c0c001c8800780007040e00100700c618403511805c44098014501512519103090016048410100c5544031064602c12801c006400b040340802c203007801c62071820042d44054a608400003e400c20301c0c008118211520090540e103c1c1c6521150b100c1000d0369140c003820340d100d40075100128007040c204440019141040d9143e5485016250345840c259200c403800c000d419202851b10a80c05084080d03036502580d9514001c0c002481d92104c002160408001c14900380714000305418400c05000962440990b005060180380c881300b95007417551360740c2c10503051f002409160401010719400080d90000b4008041080703100c940240038040c020ba503050b040c1c542d54801141c072031000d291802420031491000038050901c224101e4000f18440c5c591142052070321602e04905103a0340e480714a9002c01079014801c41d0f001d0800b80030010811010407170785001d158506500c0c10100340d034610014684480d100c0a0f29404030584030180304035001400c051020b90428001c407049805c0b01d082a0343c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 616349550 1250 616348300 616348303
    0x705030d0f0503010605180310020a0e0307030c0504020f120f040303060e190213030204180b0c03090a03180e040c17010216110114030c180d0b041209080f0618 70
    0x18214050759488a28503824400216129044190052182a0004078200703003640d051102007062071240900684404103044028251000036170980e00a81195005002040d06810080e007600c600f0b440141e5141c58415404510b441402402d462000e216018040110089042c05024078000d80e400d01c00a52120207a4200380d03001d85551801c8980002c0c807502419164015001030440c21288800c49956500400d0580c5c990400a24400c0400000c600c204100303061483c0e000044940c00600b10f240204c4410341e11034942e40060140a10108048900042040030b8000b400042004058500b042c0c6841c80c050b54490056040c00804014485083e00c014400e561024600310104800304031947c9501e0810110030b118241045550404485a071081900031406800492842c0d40d486512180911151001d40346840c428483d1180302000b02c0d4100070501d0f04641c06c99800503030345045030310903140202c169100120501a05100c1c1c4410312010507060f00c04c994260001d94483e20301120385 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 616350800 1250 616349550 616349567
    0xd0801060e060910080a061a0d06120b04170d06060e1f0e09042a080105012106020306131a030c0a0605032a1c0c0e0a151b050705030d 59
    0x8a0b08641d90030b000e0581184508001780e008415100c0024800d51151004089a40c07030300710f40c1c4807603100080d441c400c0c000180b04447c02004079084c09006c06010b50b40d0700080100140c00640380b0010014400b056849c0310013280c55481001901f04841660380d140600035045c9000402d00c103500c00c02d084103a18220114465011080381d42c1c02003c86506401c11103012000340c420ba800e61801840200d80c8203410400c0d18200c0d00e540d010088141c985076545003940d10581242001a03020100030030a03169910f10480402e60054000d41c40b545c800000c00d0312520303ca520900140d04002d8501d00030300c1d441c2a031400402d402d409036000c03000c40e241489200301d414410070b40002c80800004541c1c0000c0703e0826070055001c140e04c50f0400c1e410140c0d1010781c001003400b46000204a071f00d1001c1394a0351003242840909814814083c2101c00b00040d8912820f124050740010340031450403010b0320a05450a0a0500c2c03500d901a600030760034070660310415800f0f4540a8810041c01000503401910034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 616352050 1250 616350800 616350817
    0x6030605061509010c0309030f0f0209090715050c030c01050a020415050c0a140f03120106110105060f01030b0a260c0910051509060c0d020714030a020904030e030d0801060e06 77
    0x10302d45000591001183c2c030320043c4401750100503002c100400001d0200070400181800b0b444140301440300350040060305400540740b2007440d40042420080501c5484260414252505141d910b643c00145018210b01c142c41c60708041d03510342401c0180281c1c080e805070040d10b283c41d452a505000b01201a280b41c41460403541040e403180507400c0000b50100c043e5800d800001d402e642a4001008200740b46811103e40d00b2000b49641d4014059030f40d200008100005250000b8842400e190b00441c40000624102c90704054840d00b0f00c055544408603100d005108080c000c041d0560900001200b0284ca540012264007c0c2c421803130581c0341c0705500300e02401c003040031242040e1420013084850241215003070300100e1306100d03401031541c4040142100e510a00090401c05144035002130428205402c40000103045008140003620300080400f940d6506484090703060315a0705080d600305500c0404141c2c14403030400030381c4207103501c44600d6048659a40745c440d20710140c00704101c00c42c01084079 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 616353300 1250 616352050 616352089
    0x70e060a0b2d04060203041a1b0f0114070512040c17011401050306043318050c0a08031e0c2b0c11240301080a020f0a0e07050c010f0f0603060506 64
    0xc1840352600c280c000e50704584236000d0340b0b07181040b040502003544030718000d0700c100c0ba08404000c2141000a00030f90040540c4c80360710000c64945003030003420500465031040301c0344001c84005400c101040c8240c5001d09010b40c540350002c01180e281c01d01814440742287d403603160341e01c0009103d050000700d0600070342e402801107003180701d0b26109548181d14a502940040c2000ca0405890340300c40c40b4102210540303000d226140350322410300038a03140110b0042c034020300848504001c00f403070100541d8600c0d1a5151071003c5400d20b14800400d5004811300d40c0018068500c01c2105143c001ca800c0049200e00784c500d401c50340c0c1d0f00c1026202c49410b41000f50941101e02d1150100d8641014130750700388013030441040d800302c00007490218260004d0b0041c4d5002d078481c0e41d00304150b11380030803001c030590001c0310300ca50070714140b01031240703c0400a80b214040c41008240c45e8001e030407e400c1002040d804190402144561040d01409005544000c0d00c915181c400410000e090881c11034031300401a40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 616354550 1250 616353300 616353307
    0xb01111e1b0a12050c04060303081f141306081203091c02030a2708010b010e061911030d1506080a0b0a18020c03031015020708070e060a0b2d04060203 66
    0x3103c001404190000480e040e0050341404c064070303075852046002450080d940d045451400803035420140512000c1078011a640e02000c0000c03000c18412900d00714010748132070003410359003d0400050912508a0741c81d5009110502140d04400405544a9022542210040c10742d03102c002c680b8119603507818005070000c06c2071240d450702618030b800e4050160a030b080b8040c4010350401340150700c181c00c41d028594603206a1252980d100c20b80c03034a0402d044841d6460600c011100d0300c00c9000748075100c028002486003d50001c035061055410745503c14009024032001c1c1c005011203047c1d28040c400c0032139000d40114444040a00c203860103610040c1043e4081d0303060030607075000d44411112a40101e5000c0000f103407817441c00d2014501600300e4040c1050058100101e0040c601c0c25011403104642c0609400c1194040000d0040104c030818078140c902902e4900c0800d9800d440d40d000703603507140000900110082c840d0303909520414040c02081c200181010381c94049841140704140050b441030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 616355800 1250 616354550 616354559
    0x120b1605040521100f0b2d010905120726060a050a02040b070501140f0c1207030b10080403020c03011a041d0a030918050402130b01111e1b0a 62
    0xd0b08042900c00502403c01e00f4400300d0358403450705501c2d1010102c010344a041c500c8144005020741d81e41e10104a0784046080f00c1c10b030200124079045441408000c005030880206640504000c00113424050321961010000d0310841e0350ba0306041c490b51002030102c41541e210206444100030404001101030300e2181c5440c0384030f00181c000907084d6180103500700710008411200704001c2c44a280305000106091281041007144d202e401810a400340c1e00b10004c00001c0c03640741c0200d0b440f079510160f021356a900d03208011002032003240b080c160406800ea09201800b500040810b126912075400ca5000780c81000506082e40d000000b4105441e43d0020000d40a150031342001032464a40c6004000d4052000f034101d103403008a18059001c180d804c07805020203088a40c0718040c003809400f0a100700d04160313001c250f0700071580c0440c040301030760b5000d40d03031841c0e101d0304031803200f03d200720110b0b04502e4001d492101208400214282603114003401030050341c402c2c2042c81c401e02c80041413054891303c1c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 616357050 1250 616355800 616355809
    0xd270c0801090f0f050c0918060f01050a0506070602090406090e0d0e01020303130317010308031006092111180105030c0d051203070507120914040b210c0a120b16050405 74
    0x3e440c00300d541d0700601b02007412035121070082d2440303100c02c0161030f102e140d01101418141030001c1c04003801d001141c030060040b07455101d07245c130481d042911503036600c001a013001c038000d0240792100b50303002c1d0400400055180c0b554110307400d407107421020740300580f2141c42c0c2076880007282e200712805030f0802d0001480ca4044c0105020307130349000341001f094811522100000100e000d82040b02c0c03c0501000380140118204101c0c0c0c007030032541c20f01d04a480e040121110306549603003039203040224040001c10400c00e1910948119201c040c10203101d0355810080603c40c080c090107020300911400305142c0b024582240408281c40c0c0090190009032644a0504000d80c4010200307400e0000c200705460000300c10813014402c42c1c000380d403461442820f2003403146402c21071042061113a03090540c42e07892aa9225005440da80801c030102140180c034106207800c00d506001e8484d440700a4031380c002808441d0320400b42d611885080d14a00b503603501001000303d400b01150740d40c0024070901045c0610b050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 616358300 1250 616357050 616357073
    0x10e04090c27050420010504030506010b310602060c04050a0b0705030903100c0e010c11010e0a0515030615040303080c031021020102070602120a050d270c0801090f 72
    0x74026014200b821020701c100d0680f5403d5504a03441c5283c00a51500b21401040416001300c00340703401e03441e040c69500e585907154410f01810000c0c500015415004a1001c5c0c42c619407103403440b0009001026402011083c2c03c030505c210703009406400c4c00180100041c404032829640020498601542410307100d013601c1c4c0001d48200c0e10741c4001c1010f1001a81c0404c00074030080310b4800c3c04a001036215400510348050300785001e050146c441d540c400000d141d00240c1c3d60407002881d0010651020500081d96018103a21180c0c211510001040c3c45507840d50041d88502001d4030202ca46400c64101c105c1b407480b90784400303030024100402007000c0c20080c1c0b000b5500220000c03d101c1540b40c44291034940c1c0680d1030032094140c440e5841442c21542c05000602c014116400541003c01c0400700d4107081d07101e180d810204010700010071b6820720055501c2a8010312558082c100007444c0012035007000c2c00e4408064400e246860340019480005006004101d81d2005100d642c0d1001592280ca6204 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 616359550 1250 616358300 616358339
    0x1012060b0a05040509100b0d0309380a0e03031216030e1606031a0a05120a06020a090f0902031b0c1507020c1309050601050d05030c120405010e04090c 66
    0x244050310004056a450244a015100c440060445030406d4240c4004494007405014090b0342e221a800c804070343c20407203e004590486034070601c503441e60504d00c80c0e419000006075800c42d480704121400400d031302c806007600051070b8581d809188041810556240161031002c0310b111500c10028412803005480c8004c5058070f4140440d403d2203c1d00030504000c80f505c0900c0350004800c100300304440c0c3c103010301080c079010b65810003101030344040811141f030898010280035000740301c00d484201d002000142d80040e000700d011502d40810540c010070102c2e840c442d035414544503542c0482c5d44c00e51842100d000c0e406d004040d980103e450b506c01c0540390450342116100d802030b9091140710b811300d0f0694034466035003940904101203003c0700300034140035421648400300749007005c0800002c4000604506607241101c54011000851a000386144107000b044130f094000d11000400c02200703007000d003060f04c038242c131100070505400062000315a030007903000e03000c203084080c1004400350b0a4420940b03907 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 616360800 1250 616359550 616359559
    0x3170403050106061713050a0b1302040509150f07081b120a150914040209060316060e09070e03032d07110307150f050a03060f08060f1012060b 63
    0x95881e210a03084607215400034001c40c2c1e4401d41084402c1d20840307001d900040b22420500c03500340ba0384480c1e40c1d82d0b48907140185540d2614012402001d2901d020550b05036001f4000d006614100c81c003c0e885030303600ca003d42c407109081c2c000314101400f1401420b114035000e640310a140c0c0c1e0351401b18001000030380000d40055104009020302c401c0e4a020040c071401c0c3c1014041600941101100c4d18110a948900c020303d1402801c889280250080030703030890b404680509107600c03018000b03414602018040700e11010003150000c0daa81c0c12843c0e07183c07002c6c02102c06581950728240141c038140034803440603515800c04c00015102e41d10603852401206485410400305002448211000c2d42c0161002d5a0800b260354464005141c1040244050100d00c52900040c00300400003a000f00200f0286905008010803800705151080c1d0204c1c00802081c480c126900e60780c0c001071600e4032020ba650301016004103001885901081010408072510705801d080c03610303100e894001c002c0400d05841c81c1e20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 616362050 1250 616360800 616360807
    0x3d0e0d0f050a08040f020d080a120c0903020609120601030c23090403050304170d090c1406091c0c090504030e040608070611100c031b0309020d06020921030309070617010317 76
    0x9038981d8815401054808e150060751142d0000f0f0291481c0c6140c207601c1019810b0200c000f0607617a0002a0f2411264141c892036102c2c80780b100001c86d499003151041c000f0340700b1100000107020140c01c811044407500b400304103040e84007804942ca8030101540d04d58100e0b03075603808074001034072450040d54841c0c00f85002900c0c46c2400540a0b0300d550048010584841d100e4a14405002c40e0b01c030024010500310313101800400440c40820304030700031000c140e441502d0415081903161908000d100c51154859052080c040d100c0501500402040d2003c2d00020404904111f090030680724050a44403020f000b080120b241000886400c1c140e200e422500c0d004a18184080c140300f80100444c07a1955180070071203250304d20300e01c0010400c40c20500209404c0009400250300c0d131170324018400303800a10169550792044003040e04000b0100c005e2072001d842e110308204a80011000d1030103180904141c2e00140d68a0b034044403254161007148140350b000000401c001082e011129031000c24072682c1d2800e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 616363300 1250 616362050 616362053
    0x4060c0f06060602071a0301080607140d0501031b1d0406020c0f1912170103030f1421090a171b0703080a030b123d0e0d0f050a08040f 59
    0x781c801d03a83c011805a407020300309204a140b0484481460304080d0002410356250684241c0c0d92940903004c5001d220702c0007201d070949100c020840752040c80c060020b00c41569070389041074151001c00c0000d68040313003017000490b0ba451160350f02650383c03100c0868142c2c992540e486250082d07011642000040c421440840070303182d010300410710601003441d0360780c080088504081034040950a034031000c2001480907410900684420541500d8040c82c1c2009140c500b00f00c01e03501380d01d514400b004000c40100740301172000b032400c2c00d084098900316101102074480c0600145c1c2c03142040c81c0100030000c005814400800040c1c0030b0030304941c070344d04070440da00eaa41c12502e080c02d017181c05c203687c602c40c0001c00560050301800341a00c0c48400343c61030648901900062901d4584400d0780d4078a03546260111155150701141c40406240050004685c8450a58022000705140b0880c80600d00520340313005a0180140b4844400c192545c40d00391501c030b000d105c121203402c4000c10456210800030344c00c10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 616364550 1250 616363300 616363313
    0x10e060d2706020d1508120a03021b0a050c0f0a090902040605060307021018080304030f0306050405010b0a0801080102030106050306090a06032301180804091a18240604060c0f 77
    0x104107900903000140d80e0001054681e0549540040c1c1d20303801e40c0d03105d601704501c2c540001e2a10840fa510100303d5110400060300710081d208040b6451007a08203a413010f9403031304000c903602e0340b802c2c414001c8440e508204c0d01807060302c14100100c0c6910000c0b07084100071041040c0c00c200b01c9584002e00c001006a1500002001078000f6213042005910840000310f080c005841408145012800c00f558404480c0e07541c24004d1000034030080410000c5110310181ea4047e400401c0940f600600900c182c2d0f8440c1d03c0150799070080c98660002449210000424070010300c2164141d81041c1c1c0c03032501d507941c1c10f4140304c00d0107000742001f034450740e6881c0c000003c035035452908184480000b12440807070218444090941d280c65810080c0303030103a01031140009604000f100c04507070030084085a03d01d8044207041c900c00030000800d4024042d407180800c01d15030f50300d10764400c90100e401c0740c40c0c1d1188025038086810b610b02005410003000c21040c841da0340905044100c00e407044240070720f8404c46a5908 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 616365800 1250 616364550 616364621
    0xc1803031204230a020306041118010e0a060605131e1206060e06220506030f1005070206010e040305090409020a050d050703150e06150f03060c0414010e060d 69
    0x1503070700403c81a49403c0240541944a103207401c4140100060100c9400107070b21617902403c010000100084144a5512a10758400e00042c1d9400e190b2155a580c001002c0b11220444104075590303d407000c0450144e02401c1a00d000000c0810342e00c448a00b8450841c3c00080c0a11240300503514130500010425a24050f02d004c091051102085c203501c0c0000040341c901700540032500c1014044800400d02c015503141c1c505110300644c0100c1c00b5265440405d0405c0d51001002030207025108428117007115a40180b401010740794200c840d560383c1d03810714803900c5e00241e078003c0002d281007101d0002440c207a001400b041c0c0c002000342c00c1700c1d45d50340002984c0040f525812940c90304141c10800501001a40c810010040307083c06114858007000403a0719088000d0210040341c190480051854072800c0306480c142501900b11601e40c240303000c4920032500144039400350101d0160b850a8154071600e10788070f40c100c0140c100c0b4100641c0003482005450001e11010301c0d071a2a07180e5003500402c20b540c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 616366906 1106 616365800 616365803
    0x9090f0c0e210d170703090819021203090a03090501080106091a071b09050105060405090a0b01030b1906030b0603060a030f08090a06090810050c1803031204 69
    0x9500c0914180603442d030750b0311540640c0c072641130300001100c4e1102d01010400302e082d91003010840585280f200000e04400c428081c2858a103030f0600700741610715170350050300c0900e952010b201c40a5001140d0b01012980001004428541c014403040d02500080c600006291304141001d09181d40c10710034002e070300308070134100100c01410005036078860790310000c800f0303403084098004140407616020720450140b80c54000905481d00e5800c031801c9540292a48000b0b40d2000c0b0060014207000044170f050503243c400040c51070303417880c540f44c5400340c404021031541400c1000080c203d502c0004c54501907602003041c0b02845c3d44003101d4808403a8018a107401da02c01341e1030a6030080c00340401c51900402d21003800320700140c00103e0b076030550b1504c0045409031804101c42c0c0302950030a403840041034108201c1009001d180a115a116600180c1101c2c03400c4108050601d0b6000111030 = true := by decide +kernel

theorem cover : BRFrame.Cov 616187050 616366906 := by
  have h0 := BRFrame.cov_init 616187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 616187050 ≤ n) (h2 : n < 616366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
