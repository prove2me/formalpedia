-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4961
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:17:54.553528+00:00
-- url     : https://prove2.me/submissions/65031347-3650-4cf3-adae-b327a1959095

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 892086330 ≤ n < 892266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 892087580 1250 892086330 892086341
    0x3070b0114040506040c0e0409020a08071d0c04050307090209190f080f0a0b0f130b0a0204090605030d120c030b0d081e0703020d0c031b0b0a050702010b03030304112101 74
    0x70103680c00e108a42d141810801242c03c1002c10f4004103d9440300781c086d500e026444400720510080080301d2983d1180c14551030242d0f143c100c00280f0f10910091090070804541913680000c0303600700c0c0d502e41801e0101094032076125206103078a040d0003140d004030560344c10110b03544207460203180354055030b41d03401d0840803c00300d403040614034000d0030007281c0d22080118002e41c800750088010516070300d8080820881200040a08500d090f603071300d0381c0d400510012001e5000c1c00d0103413005a115800c01c0c070900b0407901030303134007281c4640d000d9000e00007a290000310081c01051850300000b101d44050400b80c02070149101c9007940588030900d80b804000b100c0020b0304c8101c0342c8510f0030b20b454115a810480034810801d025016038480a135141c40d80380314503418000310b4840d10b0110b080f030f0380006041480740c0b030212084a81200b40c0e800c0101000d402d10403281d000d402480240000380c26400401e803a48001b81c800b90074010b20400c0000300f0b0312142c1d01c0030710070003040701c4034905401000c0c001402000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 892088830 1250 892087580 892087619
    0x70305070306080f1f1104140a05010c03231605010f0e0c011e09181b02070b1c020415120605060909010b0a1106130308060907080106080903070b01 65
    0x2841c0842c04210f0140002e10780d20020038000c010700c10310441020381c0e501c005100000c0040c458035190280c4803e640c2c5c0c4054002050007000c80b15101c480e00e01008070a03105078100d131381040701d18540c400109a0084100c0d509038003480c50410704e510324250317081b003500c10255085010801c10158804100056001380601e81c1002c80801c000701c40e942d11540c0340ca084640309400500c2c0907031031748420000c6501c04044101142481c85146503600a00d030401c04000c1c40c0b903002c455541d00000344011080581d80101011440500744441c1080c5e070700070705401180a0b0104100d80186110a040c5090b81100c025068514400d150599802e100900f0448025403500d81181040c400140908000b400d40701f102100515a036140e0f804d20800000c11340080d11303400d04116030842c4010038040203000351401ba00307110113102c2c8010b000703050141006101800650050805004000c646948107102c1742c19104d8901e03000038a521800d510628500800a000d0103484900c0d00008040c110029101e1062 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 892090080 1250 892088830 892088837
    0x10c050118050f06270703020a1409100317090406080a0501060f090905030403120507140102042108090409140714090114090606030a0608240f22080f0307030507 71
    0x71086a542525039405807850402d0750145d0704d509010304101c010306a11000c1820880720a607517242c0008090b100f20350f100114a88180504140508210341c8480e44180c40900b0301c00300d5499039640419803c21030103645620100421184901c0d80d80345c01c090024901e9104807020384e09182005030082c1850b100300400c00210103c005005207150203440b0082e900000598109840c42d01d500b440d412003a00e0800800008211042c009000d440c01d0a104501c1080010b8813541003090303d01e0314500505c06900d51044402407840050300c04011034a072900140c03008203248441d40307081d03e40b08031480700d001030501031180049507041032000a035410f002c08841a001a90743d031a02984810103408800b5000018100000d4070b03410603038001c1d034000c6290040003c00e155507151050403c03072030001e0005c010802d20b62110300c081e00e050300b903a00054030900510107800c201000c40c08404101d443c0164580341c402c4080140011042074a0040c55402a8642d9a140c10600100101012075000020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 892091330 1250 892090080 892090093
    0x6040f0b150d14090703150b060313110d080d0c050f0d1401170a06240b1306170a0f0f060e040309080706050d09020f180106091203120506010c05011805 67
    0xf90318484200501408014000c1d154543c29601c5410060800e0801d540c01c00c2e032100400d0301103841d000015445000c0c3c1881c0c070102c5081e14508800c203807500e4581d651103a46190711990100d03000008445500e0404000007529480101c010b0390b403400341c3c031030000b41480c0104401110401c907400c81d1144115041a4164503a2a4000800000d04141d0400030b164400c1c04101e0000e142e540c001da0580c440c1c02c401c40259010140c440080e0003817900b0100d61440c021903000d1050b9901780140c4080c1c20f00c1d00302445503100e50081c5010309540109903e0405440b0083d2840d104a0380d4000c0e00703054071004050110b16140c51901011804c265002c078000340d04000001480354001c5820000d5800381d80d2100e1400300500c420704007a04190704140e80c0902c0c01d101169181d03403014441441205140012211b80d89008005014284240c0c08801400c0301240c80c00e00003940442144403585c2c20920001d600d4a4000040f1440c0100410090442d0b103010001c0c0114400e101210941c1440380040f07826 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 892092580 1250 892091330 892091351
    0xf0f0d0c110d0317160e0618030607021b0f150d11030f070e0906280e04050610150c0f1109190c05040311010c021503070f0e040504050606040f0b150d 66
    0x26905171132101d000014120208110035403416400400c0b903072030410254030f1042c654000080c00d10b4400d0304c032000940d020500300c40c00910034503081d240d141d90072500520342c01010300214801d07200d4154022025500020068008503003a4040070004100f40e0310683c0b6403510140851024000382c40c0d140c0401c210003030509481c50520003031441008003619803009803000850180141803c00c1c04016403109401d0301180c581003585805129600480082485082142d2080d40020407071f0010204028021915031403160800e110072036441d8031292030107101056041c503600c088075800d4019404001070f0103201500120f00002c0f4240c1e14101810410380955600c150b95521940c40028070120701c0540d500480d40c029821025800d001600c0000015240c3c045148550302c122007043c0411b110001c5030085c0f80d8400f1300c18071084401c3da0301704010b0500f600d03200d0b07a4442c01003c0501c502d4072101c000c941c810041d04003120809000d014202a40344490440c041500401e9036441e8217071801030540d8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 892093830 1250 892092580 892092601
    0x40e0a0c141602030f0a020405130305030411061b070906061b120203070c0927050606120304090606090e060a270216080c0f0f0d0c110d0317 62
    0x308081645a00c4070311400c500c08200980c00410040800d407254154840168030144107441004010401414009140d88100011503a01030720100c0e041e200c40d80c0010019400400b281e800030303004551500280c690000080ca50700c140d0180381000400303070310015100c0c000024070302c040d14076901c4140070042e260304040350500c010074100482d011100b207058011424004240080200d10720540b8544962500d840d221001036600424100d41e50b2240000b507003035205138400140e0f00d0200d0016000c0503e441c0c1586e181c1024001912500c03043d038000030b00803410000c0700c004040c0c04000b800300d00d03a20b01c8064100007941c032400d0b490400030400540140b821748010b00c29a089a0005050500c0c551405e107118260b2030306510005034200b28a900c0880345048000b045880b9200721a41c030403a080e81c5a0425203462520a074a5001440004100c10042480d003106100351134801201c04990130a8141c0f02d80d01010340d608012012203210916a106002c28504e8464107802c440382d855116000e03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 892095080 1250 892093830 892093841
    0x3080106030b030a030e190324110d0c110d11010f2307090e0f1807060e060906270a0b0702090f0901021c15050315061002160902040e0a 60
    0x16407507004204d5010009001d04001050300001800f12130050001240035644807089800569070784c000f030131440140c0100900d40314040c10b002e980501c401c0b04a020f000081d4020074559890309a1036080609020f0711030064a543c02a004040380e160b040d000c4009007200c640503102d0340d02075090034070200b030a0032030b8041c03001038810714440c01d0740c3c0c480726007001510904060300010400c01d80c00d81c00220044c880050078000c0c100313500e038100a4101a03990a451201401b100f1a2980100030b0030002c50750024a40c440030441581d80544d10702070383c80000c00314401c0b0b50f58400703003202e08000342504030000e54403074030740c0b200680e9003182064032401500514001c801c0009c1d031000c104000030308100a0340e08119084114680054206008134104428814000544002d201e07515000c40c10002920610040104020780140142195907481030740c0340c540003403009008071030304c828042c0414401c20403008840c250070b61100310942c41d010300700003a40c801d120710b11030141c1c42d43c085515022a84a074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 892096330 1250 892095080 892095101
    0x60c11070509010b0c0f100f140f16110318012309040c0e0d150510030b060d03050c0f16150e0d06020903070f090c020601080a0b04020a050d0303090308010603 70
    0x4468168a000c2c0305840650000c2c030240721703500a4203a14207072901d04200303802032030403640408a40329040403400e00442e402c40f400162000e00f08020320a40a049680d001d402c40511b01d4441e5055440e1101aa540101038110750504d100000e0035002c00813410910b40c210b00740903640c8003034800da08100204411510300070862a20000c100d4401c191501d503110004076500d0b828000302e246200000a11004044241503036000e40c0500103404480311072040c550301405001600f5242ca0441d1103002c40324100803c854000c00b0705015120074540188160344100030035404941d00c0300340c0c0700070494444180c20640c000f44452082c0c085a82203042100b0810240180e071461001c0001808001e10103c039000b0a65800703508204a4a10b0b0724140501c20160401e4090f10252920380400d00089a00c60042c400171034021000501803c10042110326949400503004d4009813524000505a01e031294805580150484000380801d50141c2240c011107000303441c1c81d0166030703840c08180c043d1280443c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 892097580 1250 892096330 892096339
    0x215070804091e0c02060a0f020a020706081e04030504090e0a0f1b1e0816261504030305090d021606140c01051509010605070201120509010b030a060c110705 69
    0x1040c050016507a101c8110f10780507061038031440d0700c060f4941c3c0c00c03121800982c50050b04180c08004010b481c5014080f421000404218900b60514400030b454070b0140c000e820400c5106000300e443d40f602c14200d4200e441041c81d4141d8181003928020f4001c5c2c1c070502c0f03044a180c0c18402c410040752400b06400c030005403c1250302581003034a54611128041660920f41c0362204244082298060201d44104000501c104280c440c1d061124151402000d90140304100c15a884103010300c46a160415800100d40d05580702410501c10307900f81494141c103174002158842404001c1450380c0340e00114014851002580c40c2021688000ca07100d0880c611810081c26011404111091044050086504424410500b00a9007000507070a451094408500b070101c000f14074035592404c000c02500418203410201d01c0c081c000d9002800208150450301071040d502d9000906948003904411401a0001d003694490849883c10b04010400d4104581c005901c100b141443c1d103000140f21400d880c4c0050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 892098830 1250 892097580 892097587
    0x240f10031101170702071805092125020111010c080705250c03052b0509120d030e0105010602010209010c060b0406120507080606010507021822050a02150708 69
    0x100c600c100d00400303840460400c035101e901c06800f00550394246000e03016650203801b000c2e180c86012061130004011a1480034a004144054004000b400300b060303030210f003280b402c400b41e03084001c00315001d80c5191004480c24444444172050032404d0403011075100745c0700d80040440c04d80c000c03400c84450380c0c00304010408007030103e000705004002402c0d201c501c0410206180c070030005400001c0180760700440f414100e140c0c0900c10000103000003d4218000100c0d08400d00194124901050401c1100b0062220018084c406c0d600c80706030300c841e5151070f4801c48140e081014001030003891205013004403175103000b0021031101e1040c000c460382ca0f04140c2d1341c1c05094030070340c88040043c00480c6615130700580c0d54070006038410b070b0001d40504003406a0090244149400c08680c00c00c00000c101c00d040100400c601c0c0016500e41d80040e070300c0081d09090010a40e62060354115941025104150b03088607035002c4000c000d0005103855040d4801d0328040c070060221103030040c06014025000302410005d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 892100080 1250 892098830 892098833
    0x6120f02010c23010228090b0c0a060c1805040c020c041503060615030c0305270c060f1c050f06090403032414030c03100c020708240f1003 61
    0x1e5000341c031118000c15801e401103440f2680f81c9580d035410300c2d00100507500450702d089070101c1040c4030300e0486c0c20810260b24018000304000c0100710b441c0141010040d01140e64001980100a45100c05611003c1004144150040900304020803884000d68414250000c101b0f401c00d80120305600c41b040d0002c0410724022420000981a1071604e01000c1c1c42a040010100f4901e003d454014082045942c00e0580c4103000101518018500c40741458104003c0c080d00d50403200101c2d411074944034000c40101c00503030b40e20f41094040310740e140d8041d20200d02481c90410050041010041c112024941c88400c000e0b42001d4071011a80c010040710620001a00390804000550703010b0301c00d140015150203040c42d481d07680d44200c0c0b031420810081c84000e00c14500c1ca014205c440744412030080002510040c0025524108242600c0b041900c511103180c540c0c0c02003181c0005001d80c001996150316034114104652001e8051080c0c41c035481c100407440312004000c10a020f0010f4100542c1d00d5800c1d03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 892101330 1250 892100080 892100087
    0x8060115051309150803120c18030141040303020903150a14090109200d080304060e120708040e0601091d070e010e1c0c0b0a080a06120f0201 62
    0x44100010920500300400b900b4031454401d4075000d4404050005034070010000c1d1103180481c42d410144c0c860340304205100c110f2440315200340d480b84444981d19610075078049541110540305158035019030a08228003000280c3c0e4182d40403018400c0d144036080e0711044030340c04076075240190031010072400da130101c1c020910940040c81d441502800f103698100c2040c00c0c0c03100b40401112625441d0f540d4101d103072408070304821081d4004000340c00a00010683e03840360606603040c181c0c01c29071600e900c81449429154190071001142d00440c00585034640340c1040d01c06070410b00180003142c02141d41b600025030121054464880d0040030050900e402d00070003020405000d09074506100714040c0008402c0001c040601d545000316a8002d51414114000703441a00d1181c10581441011000c0c100c6646072883c00502c124680300d2036030f89042050918810545a44d0880700707904000060f035004254003c903441d0b0040c0c030300f403c0030030030541d13a901d028203059440d001c01091080d5808200780958071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 892102580 1250 892101330 892101359
    0x1b02010315060201020703120b0f04150902180f04090c0e07030b0a0b070204050603190b1015081803070308040602030a06091a0f04090f022b06090b060a080601 70
    0x10604001403441ea1000310460580025031002005039000100c1108040c1c0c0b00340f80551000d00064107000c440507000004051400301021580202e07992403500403204c980415001c01041d01e031400f10f6445100714210700814200d40c202602512091010000d00e0810303104549070503800201200325a070038481356000d4030902030007003020142c4425285a044d581c40303200700002d150030014907030340303802c0d601c10310085c0c8500600c180d2280d082030301c010004240c1c3c0501c1c0e400f42c07640b10a00c805141c1d0307400807140300b5200360703040350030420800c03000960380b03c0d04450003a00988000d07070300b1f400c41003400750a103a50f4490144000c000071200004580014203e401031604284003040c0802c600d600c4400c040d04175903804416030000e18003081c116444e401c5c0300105980f903010a03501813207042e1494031413207450060060b0080c0580c200e020040301c501d0348681100900c3c0c500102d54101d040040c2440c10151480000c190703903070041c440c04524240303071540c149002c481081001c6c0855a00e407034819008140e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 892103830 1250 892102580 892102583
    0x501050d0b0414090114091e0a0623090109032c0d051b030a11061606020d050402010f05032a0d14180316170d020313031407031b 57
    0x1d49601c510403580d0703a140142c9003d05944104440185062403455095400c0204601820300045007407280c2120041001c0c0c4c6e030001da020645c07000c100c1c500d09440c81e0100c1c1184c00b5001628254450522107000400000e20f034039000b00385a00340e280c00c4000b908072910b100c07004000c902202c0101482000c00012251003980051541c0b00d181194008264074101c115004c03079007a0841e4100c400d400489008074406404141c0080210b040b0740d42d29549241d13044c0310b50a1203000c0c0860f103c0c42c1c0098035035a8019640d4881d000395201c1617260b03a0040a0b00044da0103d012981070b0034070521162150007604c1c8104014216408100c4400f000c58403040d592081981a86104001c800004801c41c0030380169511200700c58600c520704100f402d9000398110380b00c40303002d0f00100641c010180300e0b07402282c91141c1211080f41e404043c61000b00940c8203000300500014004001c0000c4100130800d55412103020780c54107243e842070188a032100c0d200740c0100078089010410b9880198041040d64030206 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 892105080 1250 892103830 892103857
    0x271504060806040b04021204020108101208181f08160c0f030905030a0b01030606080304080a082b090b062409040b0405010f03050c06070320160807031a0907050105 72
    0x3001c44d0300414103a82c80845130709050b804a005000840d603102848684c0904a1100c192100d1308084600d01d031802041d1f000381c41d4210124500110481e03164001e40d40080081451717804c150f600c44042410b1038400a840d020030340c3c401c00910104901c00d26818446501e907124040c021481d0394801005092034801e0b4200300b0040408512a2403c2005a000300c0c002c15000580c0d41c59490050241e84003034001c1a001c0d0000e00040000c1c070030014440900d40e0380549080e1f102d40b9144180031503c203100d03038154600d130207110303000308030948a40c41480300340c0c080c444582460b42d448060140d1000a864001e42442c221100301d1016000c0c24081d001c2d200c4000d00110701c00340418001401d8450030b0f00402d4448510307040810401504000c040a41d03201a42e1103810600a910003034000c0c841e900d8101c021070880011490195020b0240750240d8114603072028901e604c400b4843e54617a01800308440c042e6840004940031202c1007001031155800a00a0181034204070044a40b42c01190114480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 892106330 1250 892105080 892105091
    0x1e071b08180402030a0209040e0106080c011d03120a0206280e010b0d05030903100b130e1c030b03070f0e0103120c0b0a050a0c0c050a1e0827150406080604 68
    0x40b0380c2c542c001180245008080507864482ca1000c120440e040300766802c0c2030ba031502000f000b2074100858221200303042401e00c95020307011b21140c08130082900b85656498004c800c40184640b078803070003038103002c1d49c9a400c4560319a40e4500140b03c603540d2074060100f03030b081ca00072402c074070940d908248184105070b4000306803c022240400c0050070716136400c0740d103a040802c03491518241045412041c49024805002c08554140803d80411b0f805113100e01c113903101c1e001c54120740000c2014082c2c0b400c0660003540d03104080640100100781d200c01407482030080d10720008040c98000c02010680d030b000081c41816910f0341d6980d0105100244003507060010040c501d02c0401d20b82d89200780b03d42c5850f04045010b1418604400031181c000c0344640c10322648625500100c1d40001d00c4114466001500c11580900d5400c2441420300d4020028221880001d40c1021060081c417640c00d0303910300d0400700c0d072500100d6007044202c4070300d01c0c140f040343e0394248010012284030300b100d16003109000d480043c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 892107580 1250 892106330 892106377
    0x2303030f01060c02330301150e010f0c0213060503150a05100e1909050d030e01050a0203011508190c1809020c1b21060709090b061608040504051e071b08 67
    0x170b040e0002d900821420040d80c4c43c3c440210740101404501c2c10302480c060b91032282c000d00c090400d601051019008014840d080e140c0001c690388040b01415000341111b900300c480f410034003c02f240c1192075404003400c1c90082485640001002815108400b0000d83c042d620340c200c0360f542030001c2001c6008180c03110003d0001c20800d201c1800a01460743d0045107280c84c14904c0750948201400c6800110301c1040100301c050840b140540a461092800d04a10b40340d01c4156060b45e0f4003d085003010515011040804035000300b1200500071644020400300d03a03a0310543c200301d01401002d030b425030304016644200d0341a12051281064070081454000104100e40e004a80d0040500e5003500d038004014807540e02d4015017031707800412103074100b8050104441c1c04034019008486036080c8041460300c5000402c00c0d4030054401805029204001c0c81c40d0231a50464021a850129282000180081354620380301c8e00c0f9081e85030480290019048181c1d40e149030060344807440b50303003110840c04002c0d071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 892108830 1250 892107580 892107679
    0x201031a150316050a050f070c050406180b030a050a0b1f091d0a0c090b1c03030204030b0c21040201021501080715080907060c2303030f01060c02 64
    0x4041c03008003801501d91410900c2860403031020581c1106000040c40701e04401c5a1101c1101c3c0c481014811072515030300d07649070140c0c0a00d050f41180d035019051141c007184210800001701c003c0ea4040d5030520007440c08505064461134921006090307900300c07000c8580031401c2001c05a81264144400090008511002041d0340445404c00e42d5016140c0303208071280d481c120000ca400c0303105000904081c0216603255082c1499500c5100c070f9054542010901541d2449525100080458840303408a4074500d00140250305c1b5000072203c0350211804500c1c0110300609603594525124861b025107200d03c101d106000c030340180224118428440d05070820600049198002d21090b4018840b15080604100c1c9582001031103400700a45030007000001000050a103044800ca810302ca420841d280c04d00c01d004200c800045000d2141c07500e58001140d00001c0103501c100e864099040c05645c864004079014110a2006580205240f90b41f00c3c500c2d114980303000c5910302040e172211004141c0031090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 892110080 1250 892108830 892108849
    0x30619031a0a0c0f0f0e0607051903090b160221010c02011e110301170109051204030b0a050112032f07030b01060302030c16060204260f06130201031a 66
    0xc0141001100c10b100102da424003500c06590154188004240e50b401c000401c800d0940c01c000081215506032a006519640c0c21906015080420344003581502900c490004010746030440004100810004e02c9403850070940714400c030070b0a1000a014030343c1c2c081241002019034400c5061400c01c42c0b003034180b0380900c00c00c1d003181119000032400c0001c4440f40410b0001c0c3c0c9412800c243d080c02100c20f101c0d81c80100f120b064510301c00c0d50383c0580684500e03050040c44c100d200140300b440381741d010480f07006000000d0003c0340c0c1324218098840e92100b2048003070355002c2c03003000710003000e6000b10f500190080c50300c2421050303600140d81c0c80348101030309020011481248e01c40f40e9040848240148040c1d510000e000d480d61b41010361450401105281c0b640c418552110300154070a200300b0100903c0707030111030007442e003900c001c03001c810070144000094074800c0c04212544034821500c100c140c8089501c2c3c2c401c107005418041e101c0b8090b001980034002130310880510008203c640c200c0c1f540c1c0c2c11004e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 892111330 1250 892110080 892110113
    0x60123030129040b0402160b0c0708040e150a030c03061d03040b090f040e0a14070f090204090f0507020303150a0305030f03040b010609030804090c030b03060903090f040207020603061903 82
    0x16450711103866080c80119401c40113840c0c0114010021161700c0400049101071150340662a00c00d607070780e00010000e01e0f0103800030040005000007000136000710b03e140102c7c003550b01c210740e031010701c048a4104120300201e880f0003498203410143c1040070400c00d500000e21007110030f01c10499a11000142425540030740c20051101001050a0300c41d410311200300600000c00340c90800c48480c00c940070654807039421900901c0041e165040302e20210040c4406001000d06885450100b41c035941d40002030f4020740122600141360400300045c3d032209000303190090146030003841c5103884d145e40551644098241c041c0d0030418021000000aa0410080181410131241c0d141c50b030402d0320f44940c0400040c1d000c1801c100c004242400815015021102241c1e01c01100041420200070103070f001e00100045603600d030240204001c0daa040200c004c20303c07518111030b114130110410080008a00a503600a074101c041030000401070300701002e0300d150700c001c80da0141d0030f503039a01e54862501c1d810003403030b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 892112580 1250 892111330 892111391
    0xa0f052a0f0d0305010f0603022107170f01050f041a0415051314060907022a040c02250b0403020f040603020613050901060c03080403201e0c030601230301 68
    0x10031046c00d03060010806008546070075480c01c100d1071221804807611040100303041c8900030109100c140140e0b680107508000c101d00c6001843d04204080c01d8680c00d2240c107006160314100092a86454420040303507018403c1e0700200c40e6050000e000041140582469030740250301c40100381942ca4002c8100040d00810012581c00c240b080410104a8007a280034016121a400e015166401180c02e001c001c0c4800c1c0a10f141c0d1103110110b00155280100141e0028034280081d40355541c00301d641c14a084ea0f02400e15401c40f510b410b1400030000a11a111020f00180028030040c601080e10101055009102042041d200c0d00025a503920401c0c240c100580108070820072824052400d50040ca6542090005c41040d520003401108005100070108906980c504002e0100c403003d81000024032811104c0c0491082200c100d485858031102140c0c0c402c900808550745030024146068a100da0380ca4403481201120364800303124000c1c1200da140d500c44076030700315220840c3c1f00744900c00c55401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 892113830 1250 892112580 892112591
    0xc11010e0102091309030504180917090906060c0c010c06230114010201060303050a03020d0617010c0e030c2110020a0f180b0f0901091203050a0f052a0f0d03 69
    0x908025584902e40b1404001c05d00b82210320000c640c1200c2985d04449142d961190358004580404d0010802207800400d01e20b00159105541900000038107041181911182c109440b2001080381e01c0c001c0c16815800355000368180c030880e500c10861090164490400800c0710b806850303030949820040504a440302d407064004201035101002e04003030411080c00204801421038500400074450b11b00d0f002d0506400050400450540d60305c03030030081030b0440200003000400b844580c081c0c000e001c2441e0005c0c2207450784005500c0c011030070803074a1000a1015000325114841c0706030403140c1d404041100c3c028403030700c811101d040c7d00042056000d295038401d664213028001401080c0c0c2d000006d8682d4280c8181400300410290032190302c000c3c05183c550721080c0c0301004941c40941a00000c883c00c1c02c3d140d80c1003c254006001d01118500d03a00c0744141d00c148100d00b00d85a01030150116102c8420404428001d4003c58804d99115002016105042c80345221149019001000c09000907503a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 892115080 1250 892113830 892113847
    0xd1d03070e06011205010b040603052703090411180415170c100f0905040b0d1a010509010605120606030402010e0d15060b09060415020c0a0e090706170a0c11010e0102 73
    0x40113490800c9008002000554140240c2c0140c90003a8001e9006041d030302c4002c01c100310075090103820340c1816884400c0c07140d60810146502c0c3d070040d041c401c4c00b403810070b802005244040808e171004c5410000d881c4840c01c111404000181c11480091001038150010206800604140101105007440004d01c1000304850501ca25000401030131030402411311b01118a03150300004a04c21a5001c80e03010a188810b10005050314000060042c01111048008607106815101c0c0c07a040380e008039484401070f079840300290342c2440341140c05013a8000c22000550740d0b02e8000007854001c0c5c0103251104119154002007411824186c000b5601c820701302c180c040510440d80101c1c005000d8400da15030078410008041802401280107202c0301030481101c88a0305403080040c0000c0c044006e0504d00681c3d580c0d901c083c041581a998404e25000350070000c149e0a0181440940051081010102c1b80e80e41701148002851103400c204104142c0c800200f003010307024006c252807121000001130707560104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 892116330 1250 892115080 892115087
    0x6020d020c041815060f0905010f080303040b0408070f020904030c0c090c020705060c0c2e0f1d04090539091602010204080304060503270d1d03070e0601 67
    0x104114852410701d80122000c80070103d80305581e5070300920044400d29180c00700005814250414901a10901c0000030f448040d9044241242c4c050646800c40644401c102ca840748021034000c0c0c0815510000302e000901c0c04001000301902441e40100741c4040e6a000035891101617a0a0b00050614050003040c40f9031b40300454018190400b0400880c101c141010391100032911986104403400b14010180704800e1040c0011b142000340b00000b000108500100740129400b00da00e0700c5815003201c078917018004e035403450344c170005502e4900916645518111200c0b01c548555500a9207540144002030000c0010340a003d520244828180c000080000e205c06e5a82070100380314481411003202944400610680140202500d03c4a4203843c11050b4007910460b4000030051200240001d055036101d0003460041c590241010b0000c5400d807000110098811007900654121080021166004005070b01400101d10200e2183c5014480080c0c1490a02d92203100d40300501000c000d041c1d81e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 892117580 1250 892116330 892116343
    0xb130b22150314060310270507170d0203030604020a02010e0a080c1501050f0103051e0c04030c05010e0333010803030a110c0a0b13050a11040b2d0d0b0106020d02 71
    0xf0620f4a207150300e4860000b03692120071030f4800086903603030b412004000e0140c14001c281031107200a8a000302104d850810760310103080c400c844552002c815892000034010400311006401a40210708540390324003040002d5010a98000c2550f5a5543e1400c00d40e03418820540c07018020f401442c1c44041071480181008119107581d52900f0051005006594680d2902c41500f01d00f0300e80010542d840d101b52659400060840c09501b184200400c50700420305d01c02001600d20421703982040b107030380f6001960045c81d404000c5a05411202005000d00405085e81e96803085a810121b078014429008021000080c0c000c00300c00e820005c1004070880c25030040e01c6034542d00c0c0644624000d10004140e4032000741c144010708011700d40c004944859080c980174102a904001519034090042c0707010000f001501c9200ca02903804c10080e111f181c0b8182d580401da14224840e5010380160560018103000c8076003040d0b87e4040803c0c91003030013113030180600d80e010308000d8000b000003caa504003c2c0c500070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 892118830 1250 892117580 892117601
    0x1e0608031e091c050c0f01110c010804151d071e03150204181a10090603150906170c0a03111c021002160b130b221503 52
    0x344100101842001c41c039400d01c0c6011a018400d07516964110001200c640c008040180c00c0c00c908040c1800703003c000329611071400f070225182020401100010344040c401c1080f03902c881c0e041104000025401804641e500c41d1042104144000e4040c0c0402c084580d050300511510440300d41c01030401600b040008080c01036400d000400c8414010003031078012041c00000c01c05451629a005804140c0d0161405010505d0f4054441100092507800600b250030000305000d0182a08007a5810a80d00c03140310903400365944000c8030b060441c00e40c041c00c1c0c294103082488910700d800080c0706160344582000790910310031110300800c400748480e1401c0d0000075030034481c0460032400c0000803481c101c850160380c3c00760780c0300e600340d0710b00b00c0440d040842c3c01d80c001e50843c44140007a01300907404502e41c2030034030a4994030746006460300220b060501428500c44041c5041810a001d030b88404000381c5001020014850024014004c0c20040303403c2d258020009001000c65140c0781030713058012906100c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 892120080 1250 892118830 892118833
    0x270c070501140c190207080712060c0906050a05070519240b0d02040509031e0405040c020c0607170d020c07050f030d08070305060105070209010e01060201111e0a11011e0608 76
    0x1820072a842c10f000b4419201c2d60060500d034040764041c964001d00144004160340700075900c00e41d0f0b4688200b480300d00d00c84030481d6014908807960b12410300800492054480b070740e03612410305141d42019141c950060b00c06458078802d1043d2142c10ba46000340802d961440390010700d12000c10038407500d402d034103482c03c801e000c43d0800d9140d1140e6216181c0040344c0a070116000f144944074001c6848c1103104a4150001e440d041d44240c2c000900000e0080088032419242045560a01e41040b6103803420503040e04c0d44940104070400c042011042030f0200380310881202481c00c410f080c0c1c0c450803a440406840c61a07004602c0401c103d1820040748641140b06801070507000751902e60082440e007004040708203165039100883c1c001d03403140041c0d5403603e50181c0740c80c2c2156107079198401c0d540070074400c000040d0f0034442d0765154051000c00703881c0c00000b5402c1d401c0c0c89400d03001410a15403c00c098800070000c07041201c541e83c100900072b0080b1001080c2c5081102c002090148050300c510ba08600f289 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 892121330 1250 892120080 892120121
    0xd0501150617270f0115050f060412020604050910050117010602030a180504090302030c210717210618100605090a05040501060210150e0402270c070501 67
    0x1080c008042d4264041100200c1080d0305520041501910103614a407a92a2040f40b079103a0788001c055022800180503080500440c1d0342d14403c003c0c011640b46106900300744107000030040c1240c000742d820a014401401142400d1b1aa004518850011104460078050341c08007080301c3d58101c00694041050b80d00c07001270660600d8030180d56072240580010410007052081740b22080740544100c040e04006006214825060034029925000342891103018010403901403845090f44d1b0aa031600c03004005400d041c84519180d0141840098209102d0308404201e06400040c07002c1c011125040f1954482ca49401c109061000c0f004a0786035894200e41d241d4148408160300324600b80031280c0c40c0c036003079a45a0380031000c1a07161601d54001d5400600b01000850100d801044501c400c00307485800704220104003c41d600d8071242d80c0300798842401000e0200c1e016050401c5a182c0b0f6a91045090403500707000140034004143c101c44001c8203410100300002001001e0254180c50300d07204041400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 892122580 1250 892121330 892121357
    0x60e03070b0f0a06080d03091502130b0f04030b0a050a180309050409050703060912080709030f02011b0b090708100501080c0919061e05040504120813020d05011506 72
    0xc031080040d01000c0c1e014840341c0040c180b6103007504060090158031041c0d640d00c1e00c08000c0031340680b60303c00742103549c0982c4e020201444d4a6920954039030b20542a00c20901c945458508641d5900c8843c5441c51014104404408120700441e04d90062244040002c0c042c544407004030121020707602c14107c20512511701401007640400038a0950304100c0380010720f0b01d03151514518250840c0c5c001007040c0d052441e80002c0c000c009a0f032a60502d646e440c0e038007031a500c50304115848441d030300001b016407841c0f03988400594030030600c0d40001c003203072100700c408102e1584a1110307102c02202d0351649903000120900803402d05008184260a092034140079a5050460003611100015011801006064006204201130b1150340d10307100f070b14400c100142da48408152981110103003082e00192403050000409060a1040610454202d111480c21109551080300d0b0808080c0c051407010f540354900602580d210086070001f14410400082c4110729a004c490076106203500c503000f4407200c2c060701203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 892123830 1250 892122580 892122593
    0x40b16060c170f0612060a0207020f0105120114040e010e07150905031b0d1b0e0c0c15060307180204090e07080a141507020309090906010807171216060e0307 69
    0x40d0084030020000c0c2803540c1d01404504040c4450300d41d05d440c5c1c441ca00070303c00344c0f180c3ca81c000c14800d4001e4800e107601c200200d005450a00c40c000715101d1581d124401000080400148421110700051012549c640001d51090a4035800ea600b0354440d048040708001040144008080c00d2030f00b82043c0e040c1c03d00d40700010303031120885044c800c82400360750b40d82a07a69a5400c0019081e81d072080e80754072807071000c695060400c4054041d0340e40c1c0c980e41c80c0100301c0c40b054150070344008d00e40c0da40041161480e00b82e43c45003040310190103c1d40500c0380346000b050000180408455021044c1e000684452034031082a0031343d0707000d462a900a0b009103d05000e031140200d0394500080d040070305410220b5600720124079000f50741c90400c0440200c0d41c14403203600d5005c802442e40443c1145e1419640e140c0701c0d42d49031030740028030802c41903900140c000c0080c54050300c1c043c4c44003588017040ea8a41600ca070100300396940f20100e4900f6503907a450401c01040018410360307442c50003e600560400c010b555a52 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 892125080 1250 892123830 892123877
    0x1005060f1305091b0d060314030301080114040f1415070e0306010b120606131a0403230c01110102040801061205120306010203030c030604090203011b032a0c030203040b16060c 77
    0x515804c40000d44005602d02980240004690181e0103d040b007203214500350302c0360002e0281100c4c035400d0010049004200001c803500a5420040f0b0040b008031a41e500001d68041d4540c0c003e0500034100c000f80a100490184d41c40b40c041902c92003000d0742d41c04109810454160040e00548405000c52450382a8a40e01c0581c0a07034151860303581d07031840b011942d01003c03555004484a80f074002d100c046c100070b500c010f030040701d00c94180c90301c14002d184001014031603c061158000d500290903a034032907128071468400c40c82e03900c00040c9090349030785400e82551181e03048900d9444000c0200c8003000300810131060043d05141000f8114280240003d440e407001030040d00b0301d454040b000c500240e85542c08039400c0c030350003402003103081100010080c44140c0e4015400100c0e10308881c002108111550920030403804041503125003070303240030a0f61640301c01c05003502107120034000070814242480040520081c030100412200126142503010384042000d003104004246510000200307040312003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 892126330 1250 892125080 892125121
    0x90102040f08070f09050711030d060e060607122f0c0306010501090b03150612090a1502070f062310030b150609010e1906050304022407030302031005060f130509 71
    0x1140540387d1120407a001c6c03510341a004998000002e91418486060740400e044403018581c4d000b0343e6a80c101003100074011500042c2c641c4221044483c2d07a01e1254401c448001e0909290180c41d41502003180c00c0024080300142040d80007080c03001e0280340c10070145004201c00d1805032600c1d0306044e0810000d00024040d20740d210710a200f801102d56400c02500c040200116040035245001c6407801e0b41c0b52207a804c1500c3c00700310120848030b980600c0c02141c1081d0781103d0000d8070f81d0416540c2100605214441001c180340400581000303d40e140e00b01406041512510107a0a0445c103142c2d10392407020b0486560031281240c0b008150301c0320300c142e40d100306090802c0340c074070544038000c1000031600e001041e080e100c2005002c9440341d00b15010310b000768001d0b00c01c110000c07200c400c0000035a4080340d410b10314090500907000041d01c03d80080d5801038aa0800706466962000400d140b03801042d4005a0408003062a41161010568460040c40103c40b201068101200146910210440c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 892127580 1250 892126330 892126349
    0xf0201060b0f280c060e101b111605090402060f070b070807050909060d0c0b0d0c03150605072a0303080603210f07030e0a090207020a06050304030e04051509090102040f08070f 77
    0xb0005601b0140800c1410049000c8280190b6158a40004040c05400301d43c81c00b04001d0340806000c07020000b094008801c81c030030501c2420b81048200b02c16201e008200300c1c2c3c4484208001c11002d030b4140050419144942052030341800c02017005020b250f0300030710034010450180a00728042d5504110a40c215400780c2e018180c201142c1054401a04030740c011403021079001446188010843e40665480e02d00766900b00300007890080d00390700703000d250b00c5207000154041c4244070105a058050202c03d1400423201d00008000e086804240000b5500c20f5010440c039104200450074140420f1320081c4c88a02d800c0c080070003d00071818607004d5201c000c0c01c07043c808954802054003810b5421043c05009010b542500d41e00c0241d9800b9521085c0100d0149020703100015070700d0701940c1038074082c41e41038442d005480c02c1130081c4402014010084041115401c6094007a6111303018040d0007103003900005aa107504043c0c000b0940348080c0d00400b8a0790141a040100942c0a805e000a4ac0c84651 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 892128830 1250 892127580 892127591
    0x31b05030d020c03070c2d080d0807212304050714010e0315370f0b04140a0c14121f0f08010b060c0a030f0201060b0f280c06 55
    0x10003c9203140900c0e03c0041c800310540c1c6000c1420b025100e220002c82012010720317100204030182010a00c0c0b0745105010203588400c0000c0300703181c00ba680d03280c2e11071007526010048070101d540d0111039403010381c040041550f44101100d0381d04d402018041c47c2800c21000400c483c200f955880b9035941d55441402085c3e4607203c0e80e0701541c2c1c4640740081c40510014221500c01c1054151403030000015180c24000d5041d10b0a195400b00800c280d6400a400c42004041c08400d2502850090300f00b0810040c00c3e180c0e1418240016038540c49291400c0d001d9020f8000c09243c420a00c0046610010304c060611070240e14040c10b18001804460048100600801c0d070b9844046c0603691040c4484803003401c102d82008042140100007024400301e400d00c07c02800710008102c1480f1880c4200885400650440d40500307001c00d00801110518145610000034281d5481810040c44d4204801c09151140d0003e071030608501400810b048080e04030301e003101009103031000a89401c00d0701000621954440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 892130080 1250 892128830 892128847
    0x10807090f090209030c0109060807081914101a0d0e10020f0703030606090605091018060306060e0303040b040302090901060506030a050a2318030705030c0109031b05030d02 76
    0x40803010300030203500c8007044245072a440c1600180d041032030702c58007074841c41b094000c0c1e40d0701c194006800c6413010b03212134980c1d8030b80314407c4865280042480710100015480c1c20031001d01ca20078100d01d400100c610742d51604100d40080040036596104102c442c103101e4035109005003000481d4114801442c0004080001d03260b4a41042041c1d0803c2c46401c1c8082002c018080b0f44200406080d440790741d0810045440340e10503202d203260350154400144080c0f040d04c1c0c403410441c181011100036410800c2c684048001101c15000082d00444002500c9031010090503400084841e0a610b048011b181041d08008510850f805284406845004d400c1301051070301c0002c0d031210002c0c2c44040c01c0c503942c03440d2a4a4080240c18182e814207110b51404141d40400d409034604c00550041483c8000065110743c6400c0c100d0212864070002c682c0403c124110000e00304200074214020038400106100c0c6c00d1f41000341a20500003000350b006071282c1d81c103000244004c022211024041c5000580740e01c0e24 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 892131330 1250 892130080 892130087
    0x8100e0a060906060611030304050a02060c010219090801110c0d031e090609023f1e01090605060108250e06030916091a0904030221190e010509010807 66
    0x10000d0180c0381d20315140d850020b01c02160046420748030152503805140c454000e03515528402101c0250443d00301600880041c80e002c2c0090201820100c00941414200004035210b580444a1031000c10000c3c4000c108601082c050700174100c01c20398405062291291504c0e40314007150007084100756856440040c0740d4880c02c120350f007440900b00300700105070b600d180c1580205982c55050b842030300d03502454a040851a0b00070302040b403074148a124000542d07116850b640d0b010703540c88200d038014a2804480480040c03c0c02070018007610010980310b026050510407504082c20150401c98030034100406c61039249001070300d0011083d1039100046155900f01c0f9a0a5201c0c2c4551b80200000300740300b180380c00010315064003e0443c8040312900e98602c08581258500e001c85040ba20f1042080b4150703261a20780c0c2c60340680240162209002e05400c402c00600311001880e50041022a8012804a07016101c040d00e021a041111018001d440042c2030b5020ba007695604205050001940f914030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 892132580 1250 892131330 892131343
    0x105090718060c20060702040e010f020d2f0f0a0302041503021b240a09050604121106010e04080d0f0f020703140711060a18030c030203060a0608100e 66
    0x2420328888a190385802c8003c0260a04035800d4803071a54404803032201001110f01c40d10000801043c8914000072682880090895251b800160b55a075100407010202107000070320410103c420001423041998940780d0200c550000343c003240310320300f180c0c000c18481c80600706c0d452603103450440c0392201c104a1084000e07125903000f41017040301d41001506480c3c2c2503005040301da84c20950300b08409a80044243e40c41c0600016018008942000741040303060124aa50304035004002c081003800c000d0301c4503441d0141c25101102c0b40039107a00d80c040340303690081c2c3c013040d40c19480024005952400031000003074403018102410400002818120500c203036844a004905580014021415406d43e850001c3d088014190b020407184000b0280b51030506080f00c00140d4410002c440524242082c0091504520007070303001c0c0b00560000003010074200304480011407250001e46291400d40c8149401d02402424400201d8145001803003903c00100e01810700804001c00040c9128002214030319002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 892133830 1250 892132580 892132607
    0x920030a090c030b070807110c040905010f020f0903070b0306010c14160e010f0803090a0603090f1403090406060302070b07030b0f1909051810050c07080a020109140109030801050907 80
    0x440e101d074004104105920b03061710800c4a0388801e1507903a10b242c1c2c141c5483c2000e007080302658100e141540c22070311380350b40000c1c001405440009485520002d1a80403130f440003040071960807010a0284031807038108001e2000e40b004c05901da00f5420010006440d0703205000b802000c031884152020b0854100b00320461f404425031004580d4a40e60321b660100c1c1200038007a0440100380c4601c0410041400821140c0c0884050080202c651401000321700411907010308503094a8040701010210302d0541128410345680c00245a540007074008003c1142c015034001001d0600500ca640003080045907080c1c0d01540c54200411403002c0c400c002200181030121807903000440c0312440c094000d40340000800d50f451078000b007289840358a1210002c2814500140859019501004000b180358109640040f40e5400f800d080152642e501032254010101100050b903454032103a09105a0301c5159024543e03001c0200902000c1d40c41c001d10b1400140074582c001c0310000041480e0a2280c1c42c0000210b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 892135080 1250 892133830 892133843
    0xf070509040f08370c060207080c07080c1e06030610090816091a100e0a1502010507020d05090d0b0c07020301020c1b0105210a0627060920030a09 64
    0x14000d060301280709280f24030200f201010719515542e51074400c5003061968013615111682c106900703548000196200843c1104d69140c1408540e5244c04100403980140490341d02801d2850190003c0c8541d00c0244007407240200030b80001300c2c129480d800120b0307400210555030303040c03000580c038010399880702c10380c2c41741d5400c0c400c42c0303107400307080c410b018241c001d44d454244140085412100c6c080184400001603590000b1a8401180030038002c0c680c0d245540400303028208519540d58001c003488141c8400c00015035160401c0007112907050090000f00c07030440c00c6c0103041c0309031080480c240b01d6074188024401050000400c000c952a0700a840705981d00074006d560310b0354949032054680c8044004400d8114000c50107612035800b8405070b40d0100d00b03081601c14841082820200e52010107800a4201c40d51010b0103d103102d604c140400b03c03041c41a8554070a00c1d03030114400d0489289902000784c03985014041c40300c0a01914202c0d0105503540005900c3c3e0721001c400b0002000d0011006081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 892136330 1250 892135080 892135087
    0xe0418020a140415142b0804080f0703050d110a08130f0b03070806040b120f16090e120901120912030b03010903020a080a050c0304090501090e0f070509040f08 70
    0x1181d0940c580d02c2860109039010700401803441491110700e00d290003060200d001107128111103003403080e44005400440b05049105200c106d69000d2003d58140c0e0a03100c3d2000000c0c1800924020003034080752034130600050801c1403440d140c2d6a15280011840d6040104140c00c40b120400100000001c5c103030401c80c81076070340000581012210380e0501c22101051001d980003c0c0b88400c0d5070a0300d100f200592101002551058100001451101c0b410f07944541c032000591601300c420000d00088400140083c007035016005d040c003202d02c10310b45c081098903090040d2900c0a07000460103e0107c10300300421500d40d0205001600c424050f500746100c414901341c400000d01982003004200000e80b41c40420824460600341402d0320349850015000da440031130440c1c000f5144100505a00b001c0d441c0280c2044c85440d1902c0c1503a11983c0034040c40c0752604010f010b11403051080c90007220328200104901003050041c1c6031a51080e10032680b00701c4601000600f40101c5210000490b948212165038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 892137580 1250 892136330 892136339
    0x20f100f050f120a090605061801030f020d06020d06090506150403200d12030b01111506040e030d0e06011d0f13080a030c11030412021c0606030b0a0507030204060e0418020a 76
    0x20702c2c1101c025a0f0080c00d07c80402c0c42401c12002c180c0d00e58146044c4100f19a0868469120100d207400041342c1082d604803100c0c000c1202407004e00701031208190041001c41c03401322008143c03400075003694400c1011680c160b00d2076000e00700b140c0840e68030080b040c3ca01c0b8001040c4070742803000e00d0041c0b80c000041d010140704009003642407842d5500280c4041044040400044500d000344841c0b4600d1540a480d40e103042c255840c507001c0d0300c014000c0c0081190f150b01003000c1d0442c0c0200e142e0000b0540c0341c845421600c0e0090020a01400d0943c1015518501080d8041c1c80302602a01e40c01d9541c0941e07004c075800182090312920320703d402c1503500d580c40c0c000a00040040c0946220000040c0b0701180d07106a1440120803101103901201c0c0d044001c10351a003c00401d100c84090303040c200029814941c0000c0e01901640d4010750140a00c80114a001c0c01400f09488000344403008040c0b0400c4140142500041d608202c861f060700d00180c4032103048090f04030480c00f618060340c031a080e04400107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 892138830 1250 892137580 892137601
    0x60f0607080d0f110a0507050c0a0b130828080909100e0916050411040315020a1b02030d0806033d0203010b0a0c0c03140a020f100f050f12 61
    0x400c0c070415400c01c0250300d030700c50b00c0401121101c004813030400c5001c01075030f40f0442c4950701a045a034099015110516000b00c001803410040381d1141c9031071500030440361401c420404603a4000c001a001a00c807540c80350034950040a1010141c0c410601300243c50000d20042c0000c2d10314000d800b03480041c030341c10984071b1103c00038035901c5941800f41c1c9140018085000c00b00702000c07202d80248804200d103040204003c003902c0e845803041142c0505101c0000800c501b0000d000b0b1048000c040140e4404030840c1c01400e0005000303103121142a0000ea040043e02c000030b0704000804a0328007001c09441d101c000a040003411038100e04007d0302408040010074007280901c0c111100651240b40b5030485000e0703041640000d02c2210000b4000b404129925402552904500b40c4610081744480b5120303030380c0c40c0c200000c0008040032a840390010301d085007800090100d24403821100c0280703522031008018130001c03214140a080010203c0c401142c60001400e0b00d0b0218201c01d8107030f03c540303819403010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 892140080 1250 892138830 892138837
    0x111603120c0201020604031d0a03060501030302211207120f0c0807031a04091a0112110f1c020f04091103061f150909020703050c0d0201050903070b060f060708 70
    0x29190815046001035059004044241241e60306802400c03281c1d84580382a5007654440308040742448050310400940d0f95003603d00005140b2640c00000e0760350650a009103060f844455070300300148003681021000202c40180c50002c80007040542c201e0b40c400c0001c4891b064503440c80300308141031041200e03040d80a50401d628004450340da01410b6500e02504509a44003102c540404d5042728405d10128100740d0040e60703000d80a9084c041101e2038610883c50014000d9011224001d0840a00000c110035046501040c0000b105c003050040c0300d143c0005c1050032030300c044540e41040c004003401191108080740405100041040000e60b4283c1895020848001c003294400d0203a40d0005800210300d01a001c41c3d001c25003065008c160421200400d10640b0440c3e03c0c05106810304000f680002a000922130700d4401c0c1c0d0b03103035282c10841c03040510300900c00901c1c10540e4109000c10441000002c2074407050794124148440742c0d150000429190741070b881e40c081d00020300140003028002040000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 892141330 1250 892140080 892140083
    0x40c031e080c1c0806010512040f023003130603180b0126010501032406090f0b03193c06020918060f012f1b18010b0703111603 56
    0x1030344207643d8088680c401d00b101c0e02070209405101c4194003604102e40903500034400e100d8040340105070380005111000301082441902c01c940c00c0310014103e40420b011b24481c0020040d801e21408000c000003424482c02a602095a03444800d4003e00070204001c09070b54110314000e60300c3d6128180c0c4094240b91841100f02c2c041549000c8031080e50500c0385c41d040b00d411004001d2107403000055404014644a42c540100351280720100b8013105620640c840750b103452500041031100704050500308210000c00c00ca00d0403a4074210000300342c2e600810581c54072220060450401e165000c110203102038400320301819011021081008086d0b4014207a540045414000000469407036a40b0b19804551607070f0001003940a0241c02d501440443c0590711590708090f101c1541005c401c1c02510900743e031840168000b910810342c0c2c00181d00150190391003a2030b5603124101c0e12444000c4803106104040ba103850024207501854495400c5008042c2c030a401d0ba0401071030801c4040b001f4045000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 892142580 1250 892141330 892141363
    0x3020c011d031206131b120c0905090c07080304110a0b0414040504020d02090411040c03021e0a0212030a050412030c08310305190206040c031e080c 65
    0x7481d4225500d01200a210426410040d071a04400804044a0035000380c10141c10040000c2020440d40060081c0d805000d22100129808521004001c005100100d21720030b120b4941030b9441482070740642000141c6205039051031580d25900b003500301300e20800318050906100801400100304d0580c5410710954011900c4151294031040e0802881c461482500c1c555416a207140b00d40342480d030007086d8002c0c001071452801c0240b940108010303e5085500f00d403200002e40d0b0080c0380c0e02d400c0c4900b034101c2c3c40c2440d08506101c8600c043c22110b4050101181a649000c0707041294079208008aa412001c540880d0b07840703062210003400500810b0314204c840008000c460b18425103c0e00c5204034240389a51204490740f90281e00f051811030000080402114903405505404411484003810a2103039850940c2c80d00c4070b2000e1a18201ea8480a00031500050107100105490030500004d41e500240c0c0c0180c022002011900c6c5021403c10060072040c0c0444d04c084469404038a54003400d0b030080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 892143830 1250 892142580 892142591
    0xf060c0f07150527011b052416110307060e03040603060504020708040302221a01110c01020d14041e0510090609151403100501020f16151b0303020c01 66
    0x1042503c16005040c0881913501c0e0655690710542e02240d40851140c3c0d06041c0142c400e05d000107822000e0f01203a009884a5100b60203070040e80d295580108904001d0241c000a1410482080e0121410b078440c200200120341500d840d1460b028002c6544107039000d001001004500340c800c030b0320380c0c010384100004a40351000000b032034149802124109a84854035614060440d420407500e540c001c40c1c4002c030024494021004610103200f00d00700302d404c101c51078024030495000140010340c544103404c1c2c20f8000c0300e500c0f8903990700080c060341e44200904004d11840c10300d0300020701501865000809204d180300644128092a418480c10b894050b65090f034040c0d080307581038500c50140d01c1008002948034404000c2c2000a00a070442c0c000c062414540301494245861003039081034600240c04401d9040402c4651380400c00b000250040c900030b80740001c05500000500800307807260308540c141c01c1828040d054401c1000100790101e605035410401038508004009401000c0750088540c64030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 892145080 1250 892143830 892143869
    0x160614090114010b0307020f010606030b0f0f030a1202160e060a0b1614100603060b0307060f02031c0b090a050f1003110f0105250c15050304020f060c0f07 68
    0x40c0102c0880c0d030860803021403a030b4641001c021840d4801001c43c0114065141c1041a1180a005a00c01004655004146840702004205141040000262040119401c1c42c00140c9011640840160700100c1a0340d100c1002007085e030a140018100360070181010401048001407588020f014400580d10b04035025103403281426144607080040c494400c9094241c1700242c0060403841000004405480070742586185030001e4880310340003124610745410718100d40d41010044140102074034641145070381d4017540c02944a00c684000c4e55212002c6440b02488800d590300810406076000c1d00710603151800344d00c4000142403d64016400d01e904a0214110040480f001d8055036006000c0001b410f5504081000071900340c61940d0500c4000d0055944034250020301440003501240d02c00030242140c40c101400b6002900299100c0c008a1052500546d000c420b03294003507415141c00ea03001e15003200150343c60150342d02c4c8204038803640b043d0401000c4081681c108403007142d8091507030903d06 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 892146330 1250 892145080 892145083
    0x30109110a02150a06080106080a05010c0207270213060302090a061e05070501060506040312090504060303200f19021f0c1203090203100603031d210316061409 70
    0x10401d056005a201c00d450003000301c00d8040c12904151040800a0481c3c0e54109050135910241c3c4070301c40f190001440041403182c20f0040c1030750b00c013052000c0c000da0f50a10740440004c041c1c0080a941c00010719000d110403006650444002c40d1010041142d49070b51040d00501940c4410620340c040e500b0b4041c0002d401c0d00541001500301c0b404a10004e092261080448494221600031740e800d41d22081c0018542d01e03200d00070400b4601544200711190600f1380c0c05440d514071a80801e000711315110080020030383c009401d007078074080c028481116005240801d441c2074440b148050700740c0901126028000303211442d110550b44207460040900010300344500b403001c02175061074041040031116030001562440e562260341c0840c1000100c41c1e0407a00800c0c1b9207a5001e158614095681c0f07001d1091681190280d011107524480d0000c500e084100881e0441000558000b0001c0c0c240c0400b494070130081c0140c90030001010320001441d141d03428954041c11420b610514001030351404a40381580 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 892147580 1250 892146330 892146337
    0x1140d020f01030902010203071e0c0602070807050f0105130608150319030806180403030606080105060702150306030703140a0b010e100302101b1401050106111002090109031703010911 81
    0xc00800700084524048010341c00707800c0381c0100720304600041103244002271154035541700c1d25030210a40b0210400506e040340c103004154003c1c0c0306652008004000c401e000041090980310150341a4041c1100b00b00180c40d1030180010603084100700c07007408107086a02c4401d4a218203083c8806414031030000d014103448221800c6040990800747c0010030100e0300070714031142c01c4500640701d80c4e8001c40790391070102c0c612030030b941c114002620b50108022503a40808218003402c4c0855059203421000d41c006440f8004040752403000070b2000c400281d081e0b900740451001190000c8100b120f0303c5004011607100c20303100c403088403080e449800106030280e042c0c02c40c038454403810b200200307424110307000c205040d07556044140070814003060b89641086000d42e0300480c1841521594084108680507900b5600140c000804214990070100091a8002814107802c00504c10059445000f100101d0758a41c02d07030409010349050441080b81c0c14400703401103040319a0850200b20408031100704942511 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 892148830 1250 892147580 892147583
    0xc08070201061a09090c07020603130b010f2108090307081005010816031704120303050411010f0906050f0403050a150b062704140106180e0124030e0102030c0301140d 73
    0x40040c890405542000ca0701c0b940c01c60046c416841c24102958001182544115030040001220442d92001c100f07000720781710b01401843c445060000c1c10714540200e0f40e8003010410440080b01019001840043c0003120741491002e0141c601e01612000d0301a030b40c5885114240c0018503000000504400204900c18401c24222407039114500d1915500c1c00701500c0c003410182e0354010000040c05c1c0d100440070010040c406c3e10082454500341c2841031080304100c2c503990600c200b210010540300e6100300250142c80c880e042960300c3d80c2a901c0a94900d0103241c00050881c460b01c0040d03410701c80030444101c1800d803207150a100d00812601400700a002d1850942e000c0039183d074603d10311650080e404400c05102071f10000c0c182d402d181c003445909400ba40103202040710700404482802c03081c40200040d1002c40481c003031a525100006000300e8034032050060303071043d1132078054907280b00f60030201000d40b07004c00941d00c0341040c15402089600070321507419030f00c856100d64075060501551042c12513 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 892150080 1250 892148830 892148879
    0x50709060b161e030314070f08070c1103030706020309120705030f07060f1508010b01030b0625051605010e04092a08030d0b01031d120d0f0c0807020106 67
    0x220b0000605020210b140708032518490560f29000c18078a451054424074003030742e00070170560310209100c0482d82c0050035540c208107035080320b0744500ba00552140d410014030310309030300c14801504040c004001181003440d80360100040080a204007500a14061600302040d0f4000082ca904118507502c00c01c00000c1c0260001c4c440045200301c8000075010301801550003003208081c40120500b00c3d0b840399440c00c15484695001e0291140c00d2054160607030003800c0c00c006c60000300000070a940202c000004c14803c18418443d40d094806407810b5207030b0784c400b0444140e9406460301c0a0300b40d1b40d0307000e03240c000303028144600420301e41780c041c042089402140c0d400c1240071036080462145041c1c0d82000c90b2040300f41001900c1d8404200400002e4100180012204241000102990400b00030a1030300640100082c7c0d040c00d0128050000e4500c021520b9600c00c810610b440182c54030180c5081154505003d00729840e1300254040c1c0b041c030303455000300401600c4405101c1100301c1c042141000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 892151330 1250 892150080 892150087
    0xc0a05100e071a032203030c080105060702090c03060a1505090f06030106050315120a05010f111e09041401060e09090d0f120e0102220e040b0f06010c050106080a050709060b 76
    0x200300d807100554012017118030f5502c81351400e207101c0280500c5d0380790490010360b40d84000070420f58804609800340130b049508902e0308902d500001c1d45501d003c2c005190320040000842c0c1d0310f584288100000309030aa0503071200c078410520103806600304400d0140180007600c45404a4500481203074140e580e962030791821030305d803000004c490f0400c0200290b0081c480c40c4100031010010040303c0b81c00fa100300004154401030540c00403e0340c41e0080280d54442c010310000c008001d44540d0350680c49069000ca58441640d4000038015220451680d4071410781d017030010031400e5012035006100c1d4000d031420b405944603203007500d603035004120402c00050410046244054070a0001c85864000702c131002c070b01d4245c400501800caa000c26600c5040490200450000103042c00c95080207181140e90603140e8501621101c44100c2c000781400315000200001560380e0380114103200700350b80c00c13000801000b91034450581e41c44880b82010303a150710514400240544160244805540480038124103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 892152580 1250 892151330 892151369
    0x80d0b1c030c171c0f020702030a031b060212010305060601140d200d021909060c060207031803240221090f060c09130203100501080c0c0a05100e07 65
    0x101d0b041c40500c2280e98085a84543c80c440d400c2e0005081d034030340100200c003890144461800102d64115104110490040c0100c8000d61b9000c41d100302c4207905410030217a800403801190070703448100342c001483c4e04e03c0030480c5c20407030034000340302d40c1a01e200e881180c4040c0c65034001554222500008080000b108101c441ca650447e500100e03800c3c01182c0b80d406803500e066140f00c1041d00180300d100551640400d400a902c41c1c4135102c50b00f5041c240c00c0480155050007002441c10010200c06881c0c44c0d000a4400d04062007081c031442003002d0f45c420540d52940740c0ca4810b10000002a24007615000062500c0c0c1003110751088810f48074640303110108900d0380c00c0c1c00c03810130034006000610602400302c51610400d401c2c00003a10a1050205550703880010404000350020304083c50004140706004020300203a100c0c051400ba650242840a925510080d0f0b81b443c600c5941e101f10018000d210340c1c8403c0101c0010040c0f400f40001000b842807810194100d07580306070300d200d0104544440e82c400350 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 892153830 1250 892152580 892152587
    0x20109092a050702030102030a1a0a030327150e01090f050604150201090f1b0603050f0a0f0b060708041406121f2102010f02340e04080d0b1c03 63
    0x1010301d4600d0820310304080d41900000e08981048541c426081c0c1c4449141c041c0f406000c64a01c200e640494494018504540b001003214075415034a580740642030f64080380d5000c505184000410350014058007031014050f0007800c2c40c9070482420f02298070040042a00074100a0f00300c01c0d0ba2029144034200361a015a0039070f80009039200800b555a1201d590011414481d050700c0d40602450701c1d031030310741c3c040001c100c00ea01c5650701180400d490407007402b07070036550700d03800d180c020f50070100204100c0e4074031401034001e000640f0040c0e442140002c4807401c1000410180c8119220306c00b404600c0c510b440140700d054031a100e00141c811544a0001d1407040017080e007001c08110003400c500c112502e44480d50120748145013845403010f0a03180a004541e80075007096514503661014103404070440121003004400c2010000301d00301c025440c084010241106000103025070003071003869007010b080980d40f03603010708004000e584c00d04007407180c10700302040380a4442080c840c0d807001099082d1001c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 892155080 1250 892153830 892153901
    0x90513021504090908120f0609070c030e030708070e01050303070b01151803032f1b1212040513020403030509221416091404111b01020702010909 64
    0x200d200c06110119030403e941c4070b80c09030b0030b00c2160303400c0e610121707a0000c034107041006260b0543d071070703200c010040c0c15101c50185540214050600826a40f400e02d01071301c1da007905e08540c0d03405110700c40c00021418000184801128240360203c81283d80392801d05840c1d00c26214080c205584803c010800b088584c0307001032404040d407030700030b00c204201e0300311008180c00d9500030b0b00040c4564280c0710005070100c000210b40e050303021541c0e9100c072900141d50b80341d40626003121040c40100c103d424041d1504042c1500000188040e0b0740750b0500c00c6030300c0c3d80301c0d0443c5c0102801080740d03090b200309200403031007141c081d80d4054071151304061100c02040014414100030031803008494203801d811846074001c586e00390b000020205200e281200030322002d02100c00c004010401da104e42003114200c43c26941340418029540494001000c40c80c95415100d0704064030088005568110b20001065018241c40b920076654104955520a10082580d801203440c8134010b03110828242541c0f00d04094 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 892156330 1250 892155080 892155109
    0x1c0503040f111c0c14040203090a141006090e0706020304080c090408071b050f1504030b100e040317010e09031602270108070e190e0111071b09051302 66
    0x581c0b144403110020644414000d83c0c00c0b50359410081c800d00030201c4660301c03040c401c2c0054404506503e8402e250075520183c000c0081d00c0c1d80b1201d80143c50a840c14070a401d0140c40a603814001a5518444903009008030781e0b80c480030340941000413500c00c0c40801240d00301c40e0600300a01d1586143d404100c042b1a015000f1189420200090400194100029900405160300f44070185140205000317a81001100b400c0c45010008070300c803201038072941646c0a4982215550605503950980200c103101181c000e40d40324420312080100b01544000e48080880c00718110300c182d079982d01c1c00352142c010700755904201a04180001e00d008424000000d941c203000800700803c2800c2e14407041c4404056100f070f0071956090b00014007003804100400030040902010480b06458402c2280126088440403500015103411350f41e40100006d4224040300542c140c801d6641e101b6501e02500d5103544045604444d682507003000890400622415119101d841940c8800728116420481c3c110000c005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 892157580 1250 892156330 892156339
    0x8030306101b350c060703111c0f0e2a0a17120a03060807240804050705060a030b031509060c07030513120507090501320405091c0503040f11 62
    0x520811642410501010744202e40315031343c80e080d51846a0a101c0001c124900349800e00584034185032a03030049880e00c24040381024901c4842d401c041d0b01400b0b0100190107024205a04900c15000201341030641a10001000c1c6141e040c2e0681c0b014a800700c0c48189074403900c0c07000d04118110f420b0084011421540050310b4000344107807400102600101c200e680040c1d0750701c2045c4100d0000f00000005042406058101c1d6903004082e00b4102c40d2050055080000a00200d410000c080085d030300a014000c2000e911180b003410001d004241181d0254031910031504450f0203c00142d030320b980100c00410140c160365a88003400103660340075100c00c404103c2c04200860007203107081e5401010b0000081d5020010b2031a0800307030714203440342e0000d600c80b40c50003004100c2c44080003419071100c001d0f03040d0f41c111008414605054000414404c41d0040e0600003080815400880e0743c0301c0159604846020f04940d0380001c07201400104c4008006d2404801c4031400315404100602c000d800042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 892158830 1250 892157580 892157633
    0xb1e0607050a0b010f050402030423071502030307031b020a02060a0e0d0c08070b041211010c06022b1a0906031f090b0c0720030304090608030306101b 66
    0x988462824040c10b40a45215161200610040c3c034007109084c014082104c0540c00c5080a480c0c1c5050b494031412807075130070440c012550030103200600c0820010100c03201c044451075070300007010703490380c0c42122814006450050350320480c03400d43d0301d01d01d1248450f500600c0e11000583c2032241c2070740040750110510480015400e0b07142d0700c01c0528004540315a980c921950318040c90b00e4a405665048840980d805000500801f14800031404045401140c44a044440c460040c1c962102c52136010300300500004075526a01207440d11100500145440c106000321012804001c48034000000341c5041d1340c840781d040f83c1c0d00d450b80c455504984000d0995030a101102c01d00412420b18070500035045131a0070b0f812041c0400c2102869010302910300b114034240d07847d49c030700410030358401040b030040c0c00c0030444100c1518100140d5000c0c0c207414400f084829102d0000c00da403500201c548611078504200800f00441c8140c14410030454409040301307025042d0307034030700250955103041c0712113260441 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 892160080 1250 892158830 892158833
    0x11706191502070305060f1b030c04170102190504080a080702042309070f03150507020717030d050903040b1606020903011d011b2703051506090a0b1e0607 68
    0x9820681d0800039580081c00da0a1540ca0321909101d00140315182044a0780100032003010861000c2146007402c030200381c0e5a0340c442000c60210f01454100c00c000e030810780d0180b940701d00705500412401c2c1c440e0090310004100d282d422285441741d401100702c50f8020605140000304104d01500d14148000c0c004141c104120030458800d0340401a088105030345031090000300c0d1400e2240c94054018400e05058490654a66690003c81c428000c3c0c01d00b035540c40010040c91090250101804a002c000260301c1001c80e11190360b078001c40034019031989040049203107404000100d408592407004090306106195001116200741a101a21219004c0002031803582d02131040c1c040c8030b400511010b1202503a00134150848400840910404e61100d5000c1101c5401c440b01060b1200e003a049103003051031100c4a914800825031000782039120b000700c03902c8000c100900349841032a080e24009425a11b60458000345c1d10b101345c4203a08150128000700202d581d901050070a0307080078110a280540c170f07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 892161330 1250 892160080 892160099
    0xe01020f0a0e0109170601051224071d0f04090302150703060f05012d02070314060f0c19230c06100504090203150717070e03010b01170619 61
    0x1c4507140005000da0106110942c0c200350254043d140d0540034a40298010140e41d40d15201800b415118403110114140c102c0020081d00c04005c00500602d005040c1019120450300400e0300c0000118692064030500d06603180c64a60060000520010f2036074195410303c0300400300341c41d09404500a12440d403e400c1544141c0c00e004100690780010490700d0044c1c00000900240c200c1340c10001442d00d10b500b140c0380c0d8007a02c989440800c08090071041c180b01c05078907104c5030303503c01003218181910f01c1100c6800410b035942301e01c03840813507a203007a500e0f124514110320800c8180100c3d403041400c0340841c1762040000e00c00d080b08001d00034103051041004400707540c200396411000369010908200c2c0525021203020002c0c4002d89091001c65a03c0d80082d894102150f459810b0745d003010300003100c0c1c512400000ca02c0b45100041000c103070424810081805010a040d80e02030340c04c040c0307054440e511807086025210600d600602c2c490315100100409521041706600380c01a4520010030310500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 892162580 1250 892161330 892161337
    0x41e05090f1e0102120f10060e01020303070e0f0d2d0305040e0403090e04050a020f0105041805191d061003020915040b060d060501180f05220c03060302011b0c090e01020f 75
    0x1900302c1b64080500d440c10310300408203100c0d00325800304030301c2c41da045619903000000d0f81e40085241c1801c652400022000c11162384030152441d40c0518052801c2003440034001c8041c207000d183e000315212120f00c040c80300c01e01281002e0010300240f020482084460314411006400901ca4503040000e90b80d55401100e04070025076003550150044042c1c02c0c11860b00006100801d84282080d03802c06203801050b0a012100c5c000d280310454a400004050444200118040c0c01d01c0ca101000129203440c030701000c41081040c805541d214201c0480d0b03141d9100d200c0d40040701d44c01000403507160345100d443c00d1406c0722904241d41150b00d81e1b5071419160742d901c1c0508100000070b13000180d194a4400010100d80f1110103e200b4140341c0b480c03c4c4403c12020011000307444040c2c408000741d0008080c608c1c00c01000f011044200382c03504006644280e0f15410000c1124000d9031224a5001e000540080e41c0c240800c0041001c90440c0342041604080c0d00302006900301c0c840010b0a000702c3e071020303c100b0ba0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 892163830 1250 892162580 892162591
    0x50718020c0a0c06110105270c0301110c060f0103050606011215031514060a030f15060b03270a120c170c0601120c0b0702060702041e05090f1e010212 66
    0x409501c10300130550700c0808000c12500c0400288054140000320720070031605032101444a80f581100d41d034003e130003006484800000030300204030320301c40700481c1841a0815a0100b1540c0503201c0401c03c19002c112489050300c1d0803101a00403a00d82d03c005480200008001840c0c90342c6981043c640d85a007411540011401356560f01d402c906500140740c216140140469189180042444142d448000c00202600c0c0c0c86181c0e41ca5040560408150070340e640300315078400c1400d00d040410307000b0400c4051406a200e841e50350303018140381031117007182d086008140959980300001c010085003811945d030442c0a8681010070014071a0f40303900120503100c110007500e00744000355105005804110990050181d50300100d802c841c0b5540700c00002d9202c0c442c0808205001c20044255a2442c2c106c440c1d0a0740240708011114629041c1d500b0907003980000032102d4507040c001484081c010820001e50f9800c6000b510b034105180e10400c5030f0a0090480301c00541d400c1c072034407a03c210411b88071809032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 892165080 1250 892163830 892163843
    0x21507111c1e0302060604090b04140102042607060905090f2d062121130e04050105060a3f260403080a05071103012306030604050718020c0a 62
    0x14a181c103000e450301101406c1240100e03c2d00e50b2410100303118040041d00207030301040d00c65002d0503c6180314064095504040c01804080c400d1060000f1aa43c4941102c920b02003511207003070b521101655041100e102d115000a01200000c4850707004454240d8007544a513503c41101c0ca10407100c840850341307181600e45070320b03107041401002c0c60203c030600000b4044401c105000d108055100362140d4000070003603003113a0441c01e6a808031203558181c0d280c40c0400450010920ba0381c4480e480340c1e07201a01e064410394684004518941000300ca450700b80c552001c204049004114112004001311203150284820178072481c41d880e130106451250703018015000c50340781c10300042c44241e40c003141178034008d14004208400c03c00507004100b0303590001c0040c02c08549410b0301d0306008146028840300c607075141d46007402d082d101c1c107c4441c038501020400c091102c004c0d9100800c1c945d03102c00595002d0703c84e2340300d94010030a03680c18906200c2805001c0001506122601c0c002c1c51610941c088112800c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 892166330 1250 892165080 892165133
    0x180602030c0c10020c0a141213320f01050930010525180312110703050a06090f080c01061a03040209010e0a1e0504021507111c 56
    0x6240d0100724200f0080742d0040d0071440c214060031358958801c1c2c1400c00510400c0c01910036004007100740800b20003041c0405400340d84c1d904440d0754405a99040c069604403494502c2d004240c1541c00c2410021942e8890104500d55503d004200046284031100c03810424100a007140707039124104440000082c680e80d01103801a80b40645408002c5056541032030380c0b405080041c0411a8490070002c052031060103500c050300d0100890358580e24402000c00743c5000d08002081110000e403a0001d404c0a640c0c20720020307042801ca030307100c003210b200290080d84220718160204c0d900c0d500c02d080c80f45c4071318120102c15038580c5d00d500c1300f9044140050702c0d40e591150204181e0140e41108441181107046051540c40c003580080e0300c0840600035501c3d030440c034500244262545074040e07810781401640342d290b1030102889080c054407045504038000c00c840c90000b1401107001058070200c45c3d01a145003030030300854050102d0a08025402c08130303140000050f802040d14034802045818048040414 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 892167580 1250 892166330 892166347
    0x6070807080a060b16170a0e060a110d0216121a130f050607090e0124211d210f04030210180812040501030b041b021e01021c180602030c 60
    0x10386c04103014604c90b00b2040061016084d4021031310800c02c4000c03030303900392035285120301141e2003030300b08500b0000c5100c1d60511600c81600041c8082041d82a85221101d46465544000f810b620340c2500804180c4402c8484403488410305076540c0c00101070f55104290300068840394140030044c58150b0342034105206001456034825081c0018210903844102c0725450602444841005560382038085100c000d009440b42e44a8840003400c4c841346408410103014448c806802030002c18507084800010643e00a00d05401150401a003c211202044e003e060b002c01c2c480d160f03010b10081060b00030200404001661144140c0f800d4512540c1d40300c15030b050200b1003180310700341c907000b04546038000400349104403802012101520028038011858400440215000d4100014146901401c210181e40c11079070000b9005290382203070802003034211154010900303c0c4035441da41100003000c0b210b07083c0c4105ca80c1d00310382d21040c002c001c1d1404000071034985000304d0f001580da20440040c00254180c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 892168830 1250 892167580 892167593
    0xa0b19121b05130806130b090c1306050108090f0d1d090c0d0c0c0213020d0204030605040b0402010f0c0302060f040201110105010e010f1d040303091407030506070f0206070807080a060b16 82
    0x40980113500041c4014105940040501d6013035580003401c00501200050303240e54203000744001070a0151a800d1084110040c44001d0103c40c09654002428100002d868107000294011900113034070244c04c0c50707409844100e41d0703414002c034468000d50000301c00e07074059202c1d41d01e1588580f050b50142c5e034032115956060b10540d01c0074a0790500300b0100707446560260b034860a0054005046010041e52517107283c061038041e003e00d40c4080e1000d4a450708010900c8100348a6038800c62003643c90414018158000792000442c0c002e010b0010307481500050014004920203d070498014140420a0556502c1c020309560003600661090003018004011940542d18084080d000907e42820003803e00100200d425038000e102408060301d03000e8050a0083c0c1849003c030410140301618030441d140d0034020f680314810303110040020b44160314505110300c0440c189005401513500c6100580ba40b980407201101d0252201da103141d0389900000328020040c0c0280800c171114405e0040c050154140704 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 892170080 1250 892168830 892168867
    0xf061501031d07061808011a01170f040308040201050720030607020d14130b040303030204030c050d0f0f021c03090302280303050a0311030c07020a0b19121b05 70
    0x540c000c00440745024001440803400c00d0544d0010b18111081600309407030400c0018065200d40304551901100e20702c00300d00640320100e030190a80300c1f9040122030000700c1961150452390862007421080100b40040d01c11b8048541280c0140340183c10200c143d250064400342445100c181c441c0701c07440104403410b050181a5000e503507800a44044051050302a2001e608120b158074800000114000c9140751907101c200a047d55807807140c2c4454407445c000e802503025000c281d41c2446440320028040c5000010414a280e0028110000c018560349a103640d032850701c4100e90002800d118440d41c010001610355030180a542d0301d03a40685580180070354000403046100140c2c00c0c8442c41040d00510441440450b81c2c18540725540c0c440c0000120014061604400c15040000041c0300035868224017030841103000700c0d041d2210a035983d0302c0d10300900c11941014a09040302d0892082d10340120000700c0e00207250000072500380d0300b0061030303500c0304000a8104c002ca0008100c0054106400c000c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 892171330 1250 892170080 892170101
    0x30910030b18250f020106140a0308070f060f060513020717030403050706020f04061d090601030207060b040207051f09020f15120c27061603020f06150103 68
    0x20002400844042150070100401e141c442d02000008941c14020078041454041c11400002d52810616000240720004c000d40d40301c015800c0001c0400c00b0050030f01c2032001070b00c004181d00e91062840d51202119040a01c1c140c80d485200b00d041000715000d4010f030800c0780d8000500060350303801d000400c0302c2c00f08030600c0364000380d02c1404030800140c4051503400c581c43d84000b8658030b030354451608480e90b220310030b40240900e001042c0300d01d807000c000020f0000d40717000352a907000e80b00284044451102c1603c01c105d034040401d40206030f00d0b501a0340100240350180c40081540e2000c0c2000c2800d80e444400112881d50004408040030740d000a44428070007a845c5060010380c209130002039800783c0815103a40706032180c148110080075000101c6910750900801c3d10350a240251442010350001c01c10701000c404428101d500100380300201607040c0724002c0045052400318500d0600c0102041c00c02ca00350300c214003400456140801c010f52190410004000c00c8110040004041d50a070320709 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 892172580 1250 892171330 892171337
    0xc050a02240402010e1f08060f010810050603100801050103121103130e06060d0e0607031131031703191802090421050301030b010609080a11061308030910 68
    0xd00d850140034400c940c0341c12540901c3c05c00070070801c075400a945421205508003481810302480076440d90032008680c81900d00b203906048042c0000300642e000c000c1142d03c004070a01c10441840145041000f460704101580300289510340c03511801c50840d0700c01e070001d91741c000202840ca410640e12501007201d501c280030266041c5408440c80c00318140081c00f0b40c80c025280c2400281d4252145426103000040322942400741e010001c0000f41c48100030354030000024205803420980c0c0340c80c042180c020303c0040d004c14080c0d110a80321400100030900200d88013610750703000040440c14002400c0140100110304c0c0d903484c00d2142c1e012280c8500a00100c5019003030240d1410039681d187c600036206601500c0403c074985e6203280ca17100071310a181c81480210007160303229072019407000c0518140c83c40340b0b41050340c690300d03004265810800c5101d4401c0e43c4e406010950300040d980d4442264109003d0907150801094860728141803602e03420405140d4008180e200310362030108003900e61074800b0308 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 892173830 1250 892172580 892172623
    0x280f020c0f0729160b070e120a031413060f0e09310b070c0b012405180a090b0103050f040215070c09050a0213081515060d0c050a02 58
    0x403c299101d00f000400c9290141c050103540c00400010b0007114041080001e0241e00403030b103480c10481030001510b030703003000803422082c19601d82090040821041d8600c0300500003440d681d0350483e49400f49072032030981010144000749005030a880c005010b080561075103090a0190f000c0145030180801c0164441c0d1114420b00000343d011420704010301a100c10f0740b107022005244403404011104100504103d50072040110607503016043c4070303080d40302c0c0c00c400d070350b59a0301c030305403a021049803072502c1c0c0c0e010003114000702940c000e4006020300c955000c659900441040c0018028040356444040700b2038540d00040000e6a042c072a440e40010005000b001500f801d0b004030340202d40f00c1c186070303210580008101e41441030004241000340034500040c85246030446010000e07402c90329030312071804c0d0440004500325070081107114a44e804584030404541e11001c807010b20800700a5203d4224904001c00451b110440c0500b1000b00042c0c4c903043d07a5162040c000070715100740c2d540368004451182 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 892175080 1250 892173830 892173839
    0x41503140613110906010302070203160512011104270501080a14060f04200a090b0a060c030503060d2a06110102040302030c0603060a0b0d1e0209010206280f020c0f07 73
    0x100c003010250902991300d0342090f079071840145c00900c1340c541c0295140c030444060040741c400084030a0141c542c01d03540076803c0404950182d09035004000c0070100b01005110070700c000030900c0451042080b01c50304101841c666218044110381082e04000c140e030b0081208a020320520003407803685e40242d10020721062400703003031040700f014010304020302050100d81c0590480b407004207414110f030300040c2911511640d545022009000720f04001d8040c00c102c08000400d14042ca80e1130b0115509910380318038555541d41086410880454226401001c43c40c1200310b049428500030200d003600000440d4841c2040c1d4054400303644071511001d941e00411007440140c4011441d80441c460954010703440e0780740d000c00640343c00385540002081140101c2c1d1070052000a8000000e04039072a02614561004546c000003a0b10600030700d1805030340080301003100074034014003d034600c000040900c1a201c0d440c00c0e0520981d5400d06c1200f0b5010380116200c43d840400381703c0700c421028032600404c4e10600e032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 892176330 1250 892175080 892175093
    0x5030402031c02100204080c030124061404030c0305010c020606091605131a0a0f02010b0901030f0611030a022809030314040f03030c030f0804020f0f041503140613 72
    0x4500c881c4500500c1c00300100c0090007040890700050143c0b030199203481c0c8400700e861307945a9034803041c2d10030b4bc01c0101410500342140b20510710540000410000c490a0802c2076681032010300c20b00c454a01c04001c0080451084075422000d94814800410034940c1440001d24115000c1c10142c85001190306000e0b04556441403c600182141003680e12801a8011441900c100e0b034001545540484540c68806600000805a520141c0c541c400c0c0221300ca18103c1c02c03a10381d4240185c12000303987c014404a0b5038030284001c4a4070807600030800c1405040000030a400c2a10f41040c90b50b000304964080c08107030196099611160080d904044031401da00070040030f414803001d003d00600c0001c544c5500804001c40d03001d00340d403541ca03860156a0b071800600e0004010000d0b0300103000c0391030a00c28248254034a50046030000c000c503801d031144008001d002c0c00c40144403982b29540f00f00d240d00c1da5404a0501d0015401030650003051403461170014101103005008000b070005004002000824 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 892177580 1250 892176330 892176343
    0x9030b010b27101407020301051024090513240f052e020a0803040302030d0b040b0d0314121602010506100f0804020109120c060f050708040308280201090209070503040203 75
    0xa0743e00c1c101504d0550003c2c122003034890004040d40650810080204288043c01d20b42c0481d8204090480e500700d000c04601a540c001906520000d681e20504124601c1c1080c501d01241a00100000c0c0c0403044010060301120b06c401110343c1c0e02c9103c1020402442280a400001c040c1901c482001c5060f424102d85d60f02e440d07240c184400300c03003665140c290f00d1007000014400c0f03074002c810b680d50341007900f80a542c9401030104291110305111501445051138001c518903948050720102c07050045650a42d49910002c0c05d4078820f075000d1007002c00c0c0916140c2400e02420381c0a45c204010703009450004d003900d6006103900c0c042e416400755240031a07800744106901408514203140251120301c0104c5170341409038440c5034070385050407900781440710700203024080f1440d030303111400d0041e180c110903181d42c064201c000e040428148020408110a20010041120035000c2e0794100c01e41c07a0503038818601c5003805140181c1d51805043c086040c445401038003c4003505100303086280580c0081c1c0d1341d14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 892178830 1250 892177580 892177609
    0x4020307050d08030c07050a0b011d0a0c1209050f030d0b0411030c121b0d0f150b04030b0606090604030804060f0e100518040c0c0c051806090709030b010b27 69
    0x260008071b107410301600307003c0034060f00da101003038980315650354110901c0b03108112050010004a0130110700a14020700c10b80b01e56100944411a020380a008400002d0801c418146d0310307401060502039518806000402c58103206040c0010141511400d00c011108003da210740800000c00034842503003e0481079a42d802000520400ca0355956000091419409664600383d00c0d40440c010800e42002d4100c0c1105200b4402d0802c8040c00a40d181e02b54040e0300d1007000e0000c2020041880410750304401d8030740c07000c409081d03030380751220950100308507510940c01a10320303540c00300c0c081c84019400b1200d0b10b1120110300d8002c550480000004402c4130075440d040082c8031300042c40d0b4461040c05000c0490789440140100442c88480d40050480204044212031610b40500c000c80e2500e0010201c1084100c030400e8500155503001c148508204090071400c1403001ea84400000192140396a40c06040060145621070180000344a01c031030140402c2c20940d181101041c840b0384500c94442e0003003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 892180080 1250 892178830 892178851
    0x303070903170c06040309091401051c06090b0c071704140409050109020409050f011d060708060a030606180b06090906040218180106020c060a0f0f091d04020307050d0803 75
    0x280c09110b0301c200755205a10360300d6418007651007003106254010f2842002c980c20b80c003051251a181950f41400140c007400340c0c5520440c0101160406203c20200c0d4002ca44103110010780006e0383c1e250341110000440d00040116000500807007084400f000440722082d41c15801428541400110390403000c1d070010300d600481e07695000d18244102500a0b80c1801e4020708200301d404c9086c14569110081c03e2107038503c96003480c0d02c8501110b404607041d108024420003030003190f00e5969003104ca0b80c2d0044c0200d030f44170700c640501002080c01441079500405500d42030104a006868810047c0c56008285910800d800d02c80c03c0740584071910300302da00c6001210016a107420759549030113581d54601501390041e90210075091000d00c51030384603060b0b030504d800702c8080110403000c124040c841c51504400044000010034841c40c0114004070581f6060306000c80c206859800220f2071000300300030201c448040605000545c102445035801805003035500030750318089603da80400f84000348c0f440c40c02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 892181330 1250 892180080 892180103
    0xc050d08070303230411010809120304060e1e10060b030123150a02070509060d020310020702060d0c0c031404150503090a0c030c0e0c0712120e1603050105090303070903 74
    0x8480790944c003140c0e2210741007440901d4189030a10507070202c480c1c0d08a40c0829800d50202da001000011340660807400d071403840346141e6a40c2d0352400a011803001d5654180701e0791080410a0441700c0ba80132500e171200c0300504001180d40b4540042c0c0304690711501c0464003c03c010b01110a009046117240c003003120820800743e020401280c01ea4110704000800042c2c00f01d001d445250307001c141103003140c1e070481c0c03217010980712802000b0010102c2031009526502100d5403201c0b140d080e801600000e400241071a0030212102c84d59410380311001180400200031045c0c02d410182c0210100c1d01b24440000310328181810140300380c030319088101c14102030100101c0041e85040e02000088100703948000103081c083d81c1d03840e100307150000b2800307440410081c03032000403081003c0710305581d01560842a52a090303e000740713060352020124070000c0242516566440f10343d010801c00c9100e2007001d402c03800b035075500e075040807402c6580103801000c0c42d0b0020014481c3d4a90b0100480007030303a0b0400b031490700 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 892182580 1250 892181330 892181351
    0x209090a02092b0c05032808040f03140105070c020a170709020f1b12120a0b0301060e06030f0102130521070621051006110a08160c050d08070303 64
    0x240ea89110700150400c8031030855203110707452003102030070191088189809858940003015202c110600190074000c10701284407200040d01c0b5071f580c1e000e50140c0f204920b07150329034600d1142078406400a4810106035803040080d0002481200d50089483ca40350304084015400a0940d2546215480d550841c00f401108440e1013800040014400a41d0071542e4070722000840c4059001100760103c223041c04240e44065610200d080c444007030780403c0395807070b000c6601303810b82d42c1e46400307000354108030b50b00c8031500000d803000d1007a01e02404451070701c10b903585000c004242c40c00c8840e4403c0480340e401070014070501ca5000c903226050b500200d42c6489407104141d041241010040340340d16185c40350040001e0480d402920381268a4040083c4802485004012500303030780041da02a80400e44510040040d188030b4854040e041000d00c0c262040c050180d1695299900036202c81050200c80b01d4034601040002c0c55410000c06080d288646444284d4032940c450b0701480d02c1c007609140e104d03081c0e0f81 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 892183830 1250 892182580 892182589
    0xe090703060e10051002161e120b0f0c091302280c02031009230313060203030a050a0e100509030702180702012403031d0a18050105040209090a0209 65
    0x4018054035012110b003460320010314031aa02d0a4401c45029402c0c4a02c4440f40038808a0322100048604803038407411881d0005140c4054095a0403120032503410101103240e03113010002e5042240030745544503050800a469102c0b0640c0581713405415003080090484d980c0b41c000500100504030040142ca52078039800c1d2030700203042400300d4512411404142e807101c1d038008500d441014025011030fa500303651014202e04031440c00314050280710f40007a141c602000c0888000308032004220650b8201b40107050a41c0140d0099081203003da00040100545c4507030600c20581d004008020602441400c03203a869102d00c0d00e6010f010b1075640300d10015801d903404000311070380e02d0347c0500941c82c0f6070b40c0c06030f5110421000b078600c0c000550803c150f8400802c0ca2803036501289071140e0a40d0349070342c5180d030b040d00c03804036000d24003c560a203030700c50088136600c0d054000000c01004038541d40540124103800c0c21250142c2101e0310680c8180700306800d58483d0340c002980000400d000590755404640000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 892185080 1250 892183830 892183841
    0x70905090304032112021611030a05100212090a020108070c0813060302041503050121050109080c03030108150910050c07020d1110020c030a170412060c0813030e090703 74
    0x1400d43c01061808803c0d9000c42a0003013441e001650322071400980c02403092040e4410b50b01e41c50b9840e102038a00c100420b40700013110318014001801c94440305178a41d261424010002c9401d4645503000ca508290145030b0b0030480e41c81408480608540d461942c00600070031000340c0030b00c1c01c000c01e030040401080480030071242003c400070005142d040d5165002800380d4045d000e503000030780b080103842a03036500070b00845060381d000c456994085501140310b40228102c440040e41d00d99214010a800f05903800010f2819003129000f03144c1d6981400c040a14200c40807850078540040b91003040010301010490744a240914a404a400d03295511310680c41d002d14080603500070049207001003001000f42c1c0780700700d0400580f000e03802c5050801d02030740c0710007c500c91182c042e00030590000c0014481c0702e022607c584541c408604080d100d019129040d8000e0408603115035880c810142030075001251658090802951050301c000ca41e5001002400012241e40c014807058001c950703140d000f500314 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 892186330 1250 892185080 892185083
    0x60109050c04120602092e030203060409060e01050906090a150b061c0f06050a0302090a020c0106030507060e19050607242310080a150b0d06020310090209010207090509030403 77
    0x14180e04001c24101a0004c0d40950300c05441401d000d1f03001d204819004003e070540c1206031600c03080c1140100819006944010308a40d840350b0794480600c00a40d540c1700b0060240c03681d1000080c07500e0070141052403c50060080c004542c40f18001500194280a0080c03180000d09400300300c14690703c0205049000e611800b1180c0c82040d141c2400780c42c06030f07200807000c10000308107001c02c954403000d000d01c503681d43c08082c8d0440b0180b000288401065002041e400380441c1c00094441e649440b2181010708940095000840803074a0044500d00994180170541c0d0400700c07051814545000a0310b03a01c43c03420001c0022100207060600c1d90b44030100c0e03140e8907140030400d11800900e00b66105032540c00e41d4000078905112808940c10002e0a410142603a0740100101085100f40c1c41c0d14803e1442c082c032041d00242c403900621926100c030701c0244040e5220700c8000d0784a08000480807030310207840d0021045244140600e40607a0790004005046500d0141d0008040c0c96610359141103103d582c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 892187580 1250 892186330 892186349
    0xe13120905100e01090b090a03080304021206040308041101050a0c150f0c0e0301110301030c050105031504060e09010e06250210150e011203090b0f160b07020c030f060109050c04 78
    0xc8000e4140c0080f25104541c0e02680e560000c240ca51000c10b166004450010f03812040205081c000039070040015604140020940900c1001510300607142c59030403102200001c80c48001d2004201100001400c207507400d081c024100808440010100701d004100a00350a50710380000310a80841d41c080c2c0c2181b6101c11003800018820348001c0c00f060861039100d8020340c40e054210030f903420450203503030580340d003d220459100d1074400110707600e40002c0e000d01c10000c860000d03080a56510f01c1114001c1c1111100e82109160900005003180d07441140000f090300140c04001510301800705075100b04503206000d110000d0079000407490010000311200c00e19260103416410104401064400c849a100c00b81e00181e80341c0b00c0c030344600f00c003089008002c0783c81100b0a000e01e50b9984042c2400400309080641007092007040c00660498602c0181e995015010501c100c17030783d05211904a00c403087c0c00505400502852055549905100d110b102d42d07a602c01051200d19008221001482c4904 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 892188830 1250 892187580 892187599
    0x70305281814040c1e02100501050405090a2a0b040f3f0209070c0b0901060302012c06121f050d0308190213050a0e13120905 55
    0xe50841900c810030691004101181401c0d40019806a0118255100224041d080c220b541d000d010141c0020b5a007482440680051031061101402840c5501c10341903006004007901c648141d000c135641130f00308602030fa0030601080241c05e030000da42c00781c80341d0110100820100c5449410041e40003990b44006031000b000000030039481034405402962a0914407181e110740c1c030278003113060008441c10915043c2414a50600c5140821000e540c140c21201c0b0070700800400f5400160381c0403003240c0920205d2540201b2009003d0301c034001e50b5024186800800100e4111b4002910715002c0c1c1d01c0d8500100c20002c589100321282850301001500041c1502c0d031a0514480c010000030022651b614480390006c0d006d15030901a41550380454601034014a81c41c0c4680d101195070010080c400da40482e01c2e01481c2c0c083d9030340c51006102c03140c108551034084604210403c940c0000a07031180021074410014840504a40e220b052000c0d9401440429031403405801501c1081d04d130f50240e940550940b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 892190080 1250 892188830 892188877
    0x190f02030a0b010905011b02030102040314010c09060f0509040203061207080d11070308041205010e0d02032511130b040c170708010e0c1b0304080309010f0c080708070305 75
    0x2500994021004010144495481c1c14011680d04d0f10b0f61040d140040da00da002120303400c0c009200403031050b0002d030000d45855101e40343c1e6004866502020301240e95110b1410900c6603102c1242009000705140c40c401c0c5011004000f41140141241c03684166030000c0402c520b65600701140007160300f92400d54805590b02c0303079180d80311000f0965200c08181c458100c0583da003804103500301641d41c0030100c50f04050030440d039800d0003444040211144d41d070b41c0c074203400615010051282d04c840070358015a510f0300f2101030324881c00741c2c441c6e078070725a01c0c42000080001000252840e40e60300050701c18144480400c01c030440508441444942c2007868442106c040e95481180003880c09040e45005015440300f0100315030030302c003d2040c00c001d001040089484c0540784030040c082013402e890310f0440820306088080c2107034056403290500c0e138000240300b4101c1d40c004940041c60350399414080b004100381d884141140c410b074100140611b0300050308074105409002581c80400d0410503500e21003114 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 892191330 1250 892190080 892190111
    0xc1906120f050c13091808030408090a2718020d0503070602040e1803030403140901090f170c190506091c1104060b090a23060a230a0f0819 61
    0x105040e541e40300300104c00031604481e14001c460020b80b0a449441c0a404241c980e02403642000e007003240c0380316042240404c180c0d01d15841c08040d010b108506800b6400c1d0300a054071400d00c4007204c0b0307000b034107101c80d410f1050340c2c170150b06100580540c0e2030b40c0d00b902180382c0a42503200c0c880340103250354404030b40840e05509182c0d0180c030840d108040d10555a910f5a15546c0d07030300084030024001010035208000a000510180106c2c14060425400b0f550300c6428030360300d000c500d4200f440c607441c1a00354401c0b058010408d5030b508030000c3c1c0b940f000d1111441040b4554400e64006c443c0120310024044c4060703150355808580201000c05510300360703c403501e0f10304860014441c034248a503040179400301c2e03101807810859015500007402c54611601d010044000601c1445a4040c00300e645d402c040c8454403810002c003c005590b40c3c4403030004014a00b01e0140a1094080541c0706000740a0443d010342c02c101c04c44020310040c101080140d54440041039070301046207400f8041c07814021130b8800c5c40c21 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 892192580 1250 892191330 892191337
    0x706020c0607241505010504031e06180305071115040e07020304050d12020f0c0f04091a09071d060a1403101e060506091c030e0616050c1906120f050c 66
    0x100d064500d0313140d840c4c1c01151280901d00000e4036410445400e1041111000031503071105100704070208100c07a2122090f0500603415805402103200000d44404000340300e9403010782407008441c880c0c40f09010303c03046e4004d8000c40c05001c1da481c00380390215030018001c105440040000511580f408444d618043c0070707641d03a158030b0202521810903030945800001c60b01e03009020f40030704502e070803016070000c010103070002c020309030f070101840c020310000303000c82c3e44c0060b115200b814000d08045d85402c0a9070f0345410118000c03c808102070060201075520200043c04070f4031904000000e01070704070000f90610951509442d14a8540b101c0351341e40a126400b00d10b100d038200e034410409a42e440040c800d551081d0107060f580070306c00b0080b6444190031042c411417103070300074680304020900200101b41c0c3c96002c0311542480c0c0071041071000c01c10100b04003041c40700c0002d4411200300d20f05241040b0a034811409a182400002c0d201004258079a5000e00ea071910304c10803c0c440c4d4101046041070651 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 892193830 1250 892192580 892192601
    0x60e19030201050a060612020a21060e0a0b0303090d060b090907060219082506090c0f060f0f1b0507140907090e0f2e170706020c060724 60
    0x142000000350041003a84031701c03001c58002d40c80300240c01540c1c01444000b94000107501c07061005101001c1d41c800c40c1400390059103541200005403250070400d040e012580c0c01070201c2407041c10701404103100d890101c140c0b02d826005450348291200e8030b2801c0c6000d845e40ca4500342d0001c1d090713403c001110328000380c200c08440c6a6003e5500c00c5219151680c4034250160001e8020242041009281040b00804610080c17140a1040c402c81c0b442c2c0d6600240d178442001602c403070780b00c1601030002450101000d00100708500701008106081c660251070a900c0c120460309025030b1403c1c8103012103c40c1000a88943c1c44801c0e2201203071505010020304142e01030740740c0100ca640c000aa0315a000f440d52a043c1c40e803105041c0707429902d1083c010f20304a0005d05903200c008000d80c8036a50b2030f008400d032041001042c01d0080c2d51030700b0b1100034070b501c0e000042011090703407060008100041d0040f6075402c10342000c2d0764180e9508200e003002c000702da04446100b4810b6885014080b42989130350720203403003070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 892195080 1250 892193830 892193833
    0x26180406050a030b0402191e030b070305011d06012f0c09060d060b010509060d0e0d140d050a0b091e0906040b01050f040b06041202131109060304060e190302 69
    0x1030741c598003840409102c1e800020f1144c007003a804940586001404980c908030440ba40f030f07a84136154a0603c0703075000b440e400040d413404224000c5c07040000d601c40c0c050744003640d440c1c20072040d0714003c90705032519a00d0004920345a24240421400d074480c544036140c280592000000b0440c1c10f050324603001c007228003801c0882c011100709401a1038850091402507000800c079000020558807610010854038a40c14148102040ba03141a51194005443c5010040c1030000360301502601d101c0c241003102ca0b02d00b003008005000a117181e5406c90550b84210078101e0b0020380740c2d944480d86801450718031203446d44103162404004401c0d0200d001c40e8081004441030b00010340364444050f03a40c44040d50003c2c09092110014001410000d080b00c41820000f0404540211904041012a8400d42040c00c2c0d52501150020941c02d00e00c400b241c00c140d1880d8100b1901d4501d10341d040541c05901d01d4584183d034000082010300c85533030480a051784000741a241145a41d212807612644052000c4000d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 892196330 1250 892195080 892195091
    0x10c1101052a220608090105090a05102301030524041112150106020c031b1302070f1e060c05120c1e032403030703020a261804 56
    0xb0081c45a0600c008040702540545403640c48802500b003c0e0880201007000d52070715415070020039000703410000101040c0c3c071078607003a05020b5a000d0030340380c0003007210030741e0303070000f03000b100003860004999074510803101d0001a01d0400414100c1e02c00c05d41141004c820380320b03900100c14010046600b19a0300060180034602d000b43d0071075401e800c14221000342079890b036504807800c0c0b814540c00c013403031108900003524110718400101c1070a8800c01e0f0040001039200e1400e000f0b20b41010000802400311000a5684c018001c00c00140e00001c3c40d00b0b03411240e42c001c0360300c50400c03800240d45034030309500402d000c8000f001d000800c00a80d0403c0020785e545410810702c483d40c80c2c080c204403003200456034900c200643d00c8800b0606103600000107c0000c40100a840002c084213201031400344035074081203403410680080f800c260088040145110b41c02c204603a00020383c00156100120b079021a0340424005451951250994044101031042e440050840d182a50080b000c03640e01c00111000c000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 892197580 1250 892196330 892196341
    0x902040501170f0a020d02070f0c050415030551180a06090516090504020f1f0305072604140f03160c090c050d060b030c03040201050703020a0203010c110105 69
    0x500d5030169000680c01c10f192001c6004900c4a030001d20038a408004094680820f030781c1d0700c500f1003001c400191041207a00005104900d0b2a014002d030010090016208141c00c5454280c0c550080036080300a034031001015030b40381841c4418000c0311050074000c940114445040b050703e004e00340c15001c071201c501d440000d0050f06042c580c600d01c003075800c4000d03d04800542d44c0d0b08002c029040060b501482040ba01020303c084900001018010350400403c4034140742c810300030b2207250301440d64131450303042e6501c100046010003d040c4c40c4095190205850326004030588082d0780040240d081c0000c0c22040b5204070844030b00090180748a00880d0a446e801860419188ca80c0c0340c001e0f020740d030800c02c041d596149420f078044000d13501400100400b25500d00040d000c0318003d505040100d8001b0400c1d600c900c0c040c2c401c80e0700038120150172034134500d8181e0020909100080c4000e043c098042001014584204102405980d010b0020040001403200182c004862491165820340c01c2000160 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 892198830 1250 892197580 892197617
    0x3130f06020a151a19031103060606161e11120d050301140a0b0c0f0d020a0507050112090506190605030705030d11030c010615031b0c03080c130902040501 68
    0x386003907007080c80080f4400d41ca0710300b8409810000036850761010080d0390440c8560390503180420342a84803950401151035464012001501994201e01c00c0d0851810411551903140c21150b031022a1a000700780406503241007104116640e00c0000f035450032503050323810082c081130540c12006040b030b02c3c0ca03100f120900300c082d600d035111070790070001035004e03c010440c400001842210045000704002401c58880500103156040711002a6295000d000c20b03980360700c000c1c482121410241e01c0940031000036505c0d21581c800c200e02c074060400c030880b56460745000444d17015098240e8030500344d9616041550707160300281c0307905111f00210791a1040014051a0020b104011900050054203896110107025100650000310031032050004001c0100510400c0c89410054540c0c205c0f940c18448003690300a0885204140092a2041c4004407034100c581194040c40308540c18039001e1159501c00c02550b01c20b02130004100c501c5040d075080030540c800c168000d402500c1080c1d841b1224224500400c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 892200080 1250 892198830 892198843
    0x408010906091728032d110408070302011b02060c0109050c0102010608061603090212030406090e0f0a0905160305030c0f120d020a03092a0902030105030d0509030a0503130f0602 78
    0xc2d401d070035100400d41605130540c20f02c00c071040039040026484002c003099008010510941e14560341d628a00c0c903000c21101d1046000541c4c903000e80c00d05040c00d24842655603121400043e0500800c1841c03100d0203e9081090700901d43c0c00f4000f181c03507500e4450b003140601248901100e260040004104155205128000c111503c103030040ca66505c0c4d404e056501500c4042034081019220080c42001d40c07610ba41c0305041800040041d0350744e80c940b0303070001c15941d1981c12162810b0004428843c00d17003140ca00554020004000024000d9110702d892031a180c0302041d510041c02000e000001840008000b8010004140055480c42e0560300413582c3c54440703042c0f01c1c40c3c10036020b10240349078203425405001411114180041c000409403150321300c212180c0741148207c109408500141c0348608000c03001000422410340c2194100800241c84040d10040c500400501140003251a0f8041003903518040d0000c05491390fa002291800c1648a514021204100301d000c0c0c0000d995440004c0c0e9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 892201330 1250 892200080 892200097
    0x30c18060f1b070b130e0414071e0b040b25050709020d0b0909070e0c07060f0209040f0b090c222d030309052101050907141c120504080109060917 64
    0x21065046d050844044020001070016180c06203003030a410307210101004480c0c090b00e902c4d103505e90781c3c0603d40d9842c0800302503600321400d010004c0c801040124181d90580300c04884200d42e60714001040c5402c00b400e282d104001402034031036180300040310210341d4000d00b030880a405080c803a4001c034009100c0e00380b00c140c4140e4410303071250108014030311010f02e0241d00400e41d1582103180044a8a440d4144c0d00685400c13000c0c2c560004500d80b451909104801c070106035004244000840c0800181061100404416100e80001409183d50803c0c001200711160f200d842100c00c00e0320707a10b06901d40c003920281d08807183c1c1c003540700c562908010001001103d5056490103402800c0c2024018030059450101c0500340c6001b851145200c801c1c051280305030341e25802806c07c40c0c68014110b5185074a482d4030f501620f0500714211118110408440304140c021000358a45c83c5e401d14115201d01c0b8540c00100194601800741040281c55009141a507000310036200c0d00020094968800c1e1042045 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 892202580 1250 892201330 892201357
    0x11a070b1914060f041509020903030c0723010c110f0a03140a1e0506070e0429011e02030f090f03190506071d04090c0f0303050705060a02030c18060f1b070b 69
    0x80051f014143c00405001c00050240e0b820441c0b8001000d01e04a05600304003407040c0e0603d0340d21801e040791507030348060010900c1c1405048081d41c407855400c1500742d00682c09030082c80c0c6007a100b80c40340e46001006692280210000340a802445c946902010320700311600040424001e20b440000c8100b4040140c1003c09850703251140001070f0342014106113066002500ea04520040e5160751080e00c1c01d2411a001208039000503500040540b448445444403000f40c400b8840a200c4e0300000f600c400d0400f007800b0760394462442e03001461540010588940c14810199081c0321940b48202c800308040c0306104485864030343c20400d8502c000000c40480015a50740b40039106840c098101000380c3c0d00810144480d42c1e11144140c888254540003a0b000c22000035021082040c00c004103907000512042c21803c508012600c0c8010b40b080104c103180303161581d0b0a240e460b80c1c9420031038280f204080102643c84828407034842d4100c1000f11201c1e0a8000c0b581c2c0000c26100d10b00848003007005084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 892203830 1250 892202580 892202621
    0xb06090103111c060f1715040c0902070b09011118190b19140304020906130912020d0219030c0b100b1b0c09011a070807020301140906011a070b1914060f04 68
    0xd0802c0c0c21060010310981e1481844000012b10440c0352004042c2d031801240e0396201032520040e61801d58000e81600c4072002d004100c8120011b99030424042c0114046440c5208408030381c001c0181c41119420410fa0440009900740c10303038011030900751840045440c0d144002c07000800c04c1320356020498000e50001c0c228400100a8500a03003101d079501e2086800080300c1506444407c60740c001c18108001507441480386141c0c05804004003c20300c201407111700e45005640e40c0003440202d00c504001c01c40310540020501c0d48900007090b0700546101480721742c03214010004544031588600c02c24000e80900380c0c01b5101b5044c04a0305a05070703040c3e1500f0710720740340b4180e140a4440d07000c50b206661000080c00180016902800340700948010880d1246290800c2e044180c10410f040c2d10148910036010060f046076100765040d5401c850b0001d5540740d03243d44410342c5c81e56080380da00c0090340507841c1c4540d62035150601980c09000310410344024806031035a40034841140c1113400110301941401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 892205080 1250 892203830 892203853
    0x6010f020604080d020307020f0f01020901031104030f020103050403020a17120f24220501140603010e071d0d150e0102040609050f180f040302010b01030b06090103111c060f17 77
    0x10380046d80c000c4114412507103140d0340e907481c2c5428800d00d41112202c907500000d01e0192983c2c98054161000080c004d414906480e44da91200520100036009040c140c5800000d8103240c002d0141c259801e401015a1a440061001000c03e0381c0c44a000e03c1c0200c01034101203603000701541d00b9075102d400c0710010240c00085081351101000c0600801940c0034401a5001100d0602248800066502c040000c5000c0d414440d554503a0f40410490600030b40d81403004102542e020300003603810410314181a40c1d160214408482101500d5440ca50000350340c041d02420094100100c032001050400100030001c45074070010301742d100d1403141d10300181d60548140001c4c5801c3d0841e0480c1c610052401110000a6800302407030002114088040344642d0200814941c0a00503031118120920301006240e00c00800100c0c2409440ca890f030400d0780d14501701e6402e540600031620510510511b2111401c3d80c603c44c1005019103009251075951a428000303545000c5000107050412210040c10424a00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 892206330 1250 892205080 892205107
    0x1002030609040b04150f0204030212060601050a030b0406050a1d39160312050105152205040203090703020a0b0a02030a050d27120c211404060806010f02060408 70
    0x10b481a04d0380ba1481e05c001d090780002d072046030360b00742c01081c0161300d80d46103004101c2c200d800c07050a000ca03500003100300100c50b0b03070000407550002081d043c00a800d004000201c0d0080101d504190307048444400c0c0410000604040d404030302c1111040462180d039001c841c0d1504c010748802c11101051310910707002d07158005d800c4604100070940780560911004540c041d1042000c440154007050101c1064801c0440900819000d00415280301e40c049100890495052046141d2600804c031040320003200250004001401807100600c15500c0b81041003800362200f040b484124840c1c221a0400a540d000309420b60380c0d4400306801440c1000074407c0306840070340c00030121401e0311795601403403410032030940015800d07201c0616810b0401e2545203020010302050000060030300c0740446203040000d11103440326100504d100180c08803032040c007600307a520300d0f044903400600700710104000c6055030b40076100c0c9108030004d9880398070415108030244d0725400300b940c0290070704c0010084016103010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 892207580 1250 892206330 892206353
    0x1270c2001090b0705070209071b02010e01180329270a080a0215010608060a06050d0b041d070501080702030d18020402070309140604050109120614090609100203060904 74
    0x10680011030400c99698a414412904550103008660042194007d6044c2105225440040d900340401c5a4480c2c86a03006006240300009041088440340d21021f43d1040c0c0750b6000c20441d00d075544075035945920703002d070102200714810100100500812070b040d160812003503000d1089050203403c2c0490f410300304238140211000b0f0051078440e006070030b0005002c10000380124150740c0d0144c0005403154100d079210b034006a201d1410440e001c000e10010340e40300c10000c0101c51050419940d074000900402c4060700c01044015031041c075280c1c12400780c03a9245504a410840841038900c1517031600019148680141d5402005a0051005801c010b03510350000380130b0520f20f4061003001c901940010160b0740308503412400120502810414580d0fa248007003800f010840d40c0a0070305050030f0009040031018070030700004241d001c40c06c00c2480078940c03107030300b55894030914100ca40c64456040c640e242001c2e2a074000a2066140005d400700303140c403e032030086100500c041c5c500c0d2100d4a46861240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 892208830 1250 892207580 892207637
    0x7021b0a12020a180c020705040e0c04050a060b04120512070309030b040816050c03060105030601060f051b072408040b040221010507020d0e06031017120301270c 71
    0x42000c0401c110b1111000c00400d004e10f52804500c04c550210000c1c10600c407544070b54002c5040c001504114000840c440ca420001038034002040d95901d140d11002e840140d000d003c440c600040c02180d03480d88400042549406602280c40080c9109a208060302c10351201074009203044600b400020041c150480d0070a01801c0602d091003007490a4004000144900702c0f49544182e1410301e0504003488601c2c018101200580744039854410040c0c00501c00381c40c1d00701000400100d03520700c0e0b00e04c140f0f5581d415180c07404881105495110f2199001059484031034900808550745104910a45c60300344146d901c035500281070385644e82445207800b11a5900b60285881000c4585456024802d040c0f207601160700904034000640c40140004041043c0c082c005c403810810407844507940d40c0e69070126191800b01d00e4045d1910507049040001580c00b51200f82d100000001c0c00017003000304a60321116210079080032803211081001240d288001100114082c01c81401780034116178030fa101000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 892210080 1250 892208830 892208839
    0xf02070e010f05041b0503070c02190306020715020f0703030207150f1a030604020607110a0305030a021e010e060406050a0b030a0602041716360507021b0a1202 70
    0x351160800d200e440000d80110449440600041080d85003501508041e59003102080f00d0016181c5c10007041444000e252405102c203c807095001c41d2251411091014200628800c0da10749a01c0c00c0c20103503011950696004100d18000498040c19208403541c012480c200c1914010301580d0660181d0404142034886418111001c417a40801d4040c03580f2071200e407500011b155680e11603485c80710007086c1519000382e001404000040c1c1700d00044503500354000400059100c40306000420580720754100904501000c160940c816400003a04034080744441c18100410313058001460880d04036244001c0c4c554081000b0401040e41640700c990012160300000c90f0072042100400c1c5490901e1800f1182ea6a000a041150140400c1034034030106082c800347c03500c03103d5011701e64070110f914010300701051050700c800981020145011588103542c0010340a422041030403010040c1000c8a40c1000360003413881202e42c0c059400e0b984041c00c00d008221f80b030100c1c10b00c0c0389094503a01d0080100c4c2c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 892211330 1250 892210080 892210093
    0x5012909040611031513060308030c090607050d0f08130f060b0a05040903050d0605011803120c02101106160f050702030106380901080c070609060c05040f0b090f010f02 74
    0xd00c030400300131031154040d0801011000401802d01228500c0c20781c1030060903180c07050034800103417602d045a030040c9a1103034040d240d0165038000352081c07241200003030842c4241e1000070b03015508000040040d101c0380e1296102903440e01040c0c0c0610000c00401045118070349140c00010384103600135a43c490001e00743c018140d48940203e021a041e0707080c150003080010420420507070300d50040102402d42860404c030f08694680c100c000c01d10341404000c042d03500000c02813038202e100d014400461a001055030406003060000506a0154105500400d010741030000390703840340c005c0c084d2002013099650050800762008003100c4540068108a905548900340081d01601c20340603008000300180e1380011990481700c9d01d00d41e4180142e0400c11400f028031403403007a44c1c2c201d079055030301451102070a1b0780e550f11850702e9001842200301c020130300c03841c004044680e95409805001a5419128150140d0f0380703416000059020704600c6503801820329035060340d40d5104e801115003c2c009801110721 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 892212580 1250 892211330 892211351
    0x100e070e1c11060309011409160303050a0215010f0509070e3604060506010f23032203030e011a0a0b0a110106090218010809070306020310120b04050129090406 70
    0x3407a03000b80d0300c108080e0f44441c0b090075005e02e06482c7c0d94020342d400f4010042c820b00c030817031525044010320002d414841e001c42c1001c08140207112190300310510710855107503580c480c00300c1e6200c40240c1c0600740c011000ca20024800c1030080d410305082c0c18004111a94a015050440c080182020405400940b82400800c07400062282440c010342c86400040303075928001c0d00041113541083d101008200c0864250301d08148a03500304c45200c080810865501d90362100700e02d2440368101800c2144000c006004428076505074460108100000000c0c843d000485442c1c4070b41111a2032215844801c2400400800d8403450003407843c1c7c405410551440d81e00982098212031107a440002001e400150b001c4003e110445245070040090814030642d007480744031103503030380800c1c0801401294000089121842d201140c5002810800d6800751038554902d4081c3d04100c0c01c2e502220950309001e242400c2d500288000c0000780302d00fa04040c803100c00c55080005030303040908113030703207099039109000c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 892213830 1250 892212580 892212589
    0x40302030a0506070201110a091a1b0d0906110c0909010b0d120f050c06070c020402090324060405010302100f17040b060109081b060c010b0306100e070e1c11 69
    0x41c44940641e020b0811840c0051010b0300b555600341e819424000100604864140c00c0000b080030784540004034104840d809079600c56611880c4060907404100190905096100284c407081c440469a10409401d580e190305443c84180c40b00b00501941040e98044200c1c145018420b900c002c0c10b02c00840d41e003a1040c08941c900d000315005840103200c800c1520035040e042080051600d429140c80c40c030708000c2084c0c0640f60007015103034104102c0e00004600a5643e603405070ba210381c8001702078601d45c601c1300c25102e01c4c804008c150595651500c10000e50189880e10841d130490b031f005810b408810548180803100b1091074080f540034022601c100d00c0e484c0b107070481c086110701c4c8140c6041040341007501c005000000e00c3e501040559021020400101c548052160683d0006450541d00c450309500d4440c05000e801c80d08c660103201c0d050411680000080040b41100c12019001485480da083c044414000c02181d1540118106680d0b94030080e20501009002c3c0c0a2150030b066161802d0004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 892215080 1250 892213830 892213843
    0x90c0f0c0c0a03080c0f0c210703080a050a090506040501050316110a030905030c0409120e040e120301031a060607031202070b070e13150608271b0d02090606030c04030203 75
    0x2a0342041c0045145c5070321110800051105da030001c8000c041d0407042030b00081807401c1c50741c401085000c640142d049804010405200a1544071807100c3e00c4050f034040050480e00280300340d5000907507442000419013045d0080310143c2d103045e56000d02c2c43d500c0b8030040040300d006c8e0b109142001100030520354030b21405d025a180d102e11070380c1c40d50442031900042516000c140c03106180300340c0c607140080380010240b00301030360801c50500340000c0030079180000400510610b0102015402640030351011142010011410703240f0400d03002c1c50324281011040c00f800c000700c810582000c42000340c0c0b404640a48926100030202074809440c02c90207a8550303e011006580400104005200c068143c1c9002d200c146802d40b03440278200140b656449101000e541c0c5407103640140070f84040800d114070b0301b804400404007841c00e4145850101200d400e542d03401805032005401c04105078103c61450071070281c000d0340c0c1d0001d04494107a180c40c010440b09600142501d001e0b0b9004100000040c2c4050200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 892216330 1250 892215080 892215083
    0x60b0c152203021f15032901030b06030d020604080f16080a031d0f0a060504060216080c01150e0a27030305060405060a03030c084005090c0f0c0c0a03 66
    0x40c10300001095010001e18001c180e03852901c9080a005040001714441000102ea801580c1e40c608080c21504207010b14007205965003401e202c49002009001c0606515409020140d0031642d17080c5005004a8440d00c1c192401840e20108000101e480c000c001d02508a1164018014800480e650386400a581c018210100803d031140403c1840d90360030007072000d01e820f079072028141c4001c20ba4600c03600c03003820340d400505040d40c540106050146503810340b0001007448000c5050080b45044c10011600301065415840d8200244c561020003c0c0c0c1001046912290113034a1a8903104803003009082e81454144030710385698655170700340c5043c0d0400c107800f5000340c40000390383c02c0c90818001a07074002881d00340940c101480800c0040c1c0d000d003400e80707200e030400000341d1210342e0050344456100050360700b0304140f26078401c0340c09a108044006800300054450a6410300e56490a01421080881d90700440381001e00265102c42860b03002082c0342c105000a0f144641d02034000a41280e4442c1c10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 892217580 1250 892216330 892216333
    0xb151008090c03030a020a170903030c100c02010902181b0a050703030f0603080708031e042102070e0a0c03060902030907061206050619020a060c02010b04060b0c15220302 75
    0x1031049141c41071064140784242a000786140c02c0c945000655100c001c0f04009040018107c040e91034481043c043e40c801900007025030b60307a044840c6042e55030b8096001800c4140c1d14040341d40102a005100d6a07660941c090300d0352003040c517131800e100c1050030024214200300200d003043c1403d060f000c0c402000700080036103859441e000a41401800c460503920380e1002c142c40c224050000c1a40001924032459002005035623130b40c0c40102e0805144040076414482c081480f090204004142d8002c59100500b0040d0980d1880c0a1004076500e01682c41565044000303031020540e01500782c0c009a03034005003400c01080d403541d03500c1003104aa2080729000619040f40d034080c4440c40d4408401d44412040503c02c2c0841c60410b00007821502c1000b4000400c4001d40090755000341c0240300361441c4980110040215541d01080680a000c04c80f102e00c3c8107518120b40401c5030394002e07003500c000d150307031800030620080d0701c0081141ca44400b6001118010002c0103500b1180a040c40340d80e14540709a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 892218830 1250 892217580 892217597
    0x516050a0b010f0807290c0607050901080f060109050609031e060429012903040f021908030d0515030a0602040801050a0c170a0b130213060206040c030b1510 69
    0x4109020068130f0300141070680145e0fa040011700b21200c04110408032000103040d02c030f030304003c9440603031045424004aa001d1031080044064000006d4020b10038285c0b200045503441c604030f98800042111158003041040100740b01761704000010f410451006401c075030303500140140c515402e200f880d2140f45c01d50700507010002081804911a40700b00d030510441c55913080b03040c00840310b0080c1400703822559904500c582a1089004095030041460812510365070f04041c100852614a4144180d028005241058095007541d124000440320071002460508407085044000740c00702400f015500d2240c400c0d540015501404948503c2d03205200050fa80d91901000381e00717540000f41002070311444c1c02d4407081000e4110700002424010811202999030b02d082450008003420b04405400011081c2c1c00d80014800341d008000003150b400700311309080e5554800720303036802d4200c4004044000c1100c08100190040c3c2100303030400100d20000c1091a0104e01044400c0320720707170010f0005030017a07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 892220080 1250 892218830 892218839
    0x4020705011a010201200708191805030d0504030602070813060c05152e23041a06040e0403090e0c04030308060a030b22020310050108190b0402010516050a0b01 70
    0x4100700b03148040030700003800404146280d440400401407117000c003a80c0005640420000c2050444000386403024205032203000c05040101150b00c07002d4040720b2a00300e48030228140c43d0000d811000100c850303a81d030740351506680c0c1e001c010350000e20044800d03502c240400703451004d1408025028065982c0c41512108190070194500b0140c0448001c2c035030004030038840341c0200a5261b040001081c590000c4102004802c641c91306000d900c0204501c0c0186800c508840e401c02201104010850b01400455208080c110140310202035556105000300b02c100668800a003080c0c1c2e01a0103402c103240e469644d00400700c40031100b16401e641c4840c0005061082581252845401910aa40480e00e039800d40c2d69025a100014014407903066030300e101290351140c00201c03800c0069015060b01c1d03001b41030403201800303030000780240000d40c090b000e00c1d12103901d6003580301b40e013464104004070b50079116500155a01d60080f030b4114410542010a14003003541044001002403292008207400e6151 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 892221330 1250 892220080 892220111
    0x4180c1205010e01030b07020f01060605030610020f0703060c180b0318150718080f030301031101080403020a150b090906061002010c0915020c101e14270402070501 72
    0x828020440e254036100062005481241c0c800341901e900544081c1107480d07a0205900d00303a40303440027610301c3d0f0a02002007071642d0300c44040d45c0220380c16140c1c1840040c81c00000d036100d0a1150480c0c2c40d90380003103c02c001144540e0070144001c80d041c2040d2901d1100c0c3c10710070703c1c1a2195007003159510b100105115102c814902a40707a03680c6400302500b012045605038000025000d050401040b4046e498680810000b4003490018005030048604462403040038588079082480295007200b502d441020aa50040700311a129a5041d4082e2540003041c4c2d0341d110049062664030080140c1c1c030ae5110070551101100b15010b00c801030700030100f51400d00c00b004404107070180c0c1481164180a0301c01c201d113401c548280309407103890901006100b42510201d10300080e54004943c00200410312461041d00900c003102c01604400344a1100c650141080c2c0d1a924041030b54a10710401304950703000b20341c074552040010040010202401c120030400602039811a52040d80d40c1c0e5036441303803210f010700c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 892222580 1250 892221330 892221347
    0x10602070f0b030103030f0c0512071b120305032d040302152d040602092d0d170307020106030c060f02060f0f0106050708090301050103030e21030a030905010204180c 73
    0xb41101060720315811a50024101c410784158902440321195000e400c00005000d04816081580710954030341d909400c2800c040020103a807440f500c0300c0301e840800c0548035202800d4145030941c540318503540b9908800f850040203105400341c01e1948640034142c1c8002c42c180300340194047d60040070351040165800c0500da201625200c10055486031000300008008100a2400d041c55a000000e81c0c56003030800182c030542c5602684800340c141030303000801e102c00607840103444282e51402519102c44c1804806d90080360080e00e041404500d400440f00d200004690080d058400440d5959503640e40b03541c03045a9800180c0820070340924020b5180e81040119403000c82039080e0185070600307001500042c03006001c2d42c1e0070440c0000e016810320807030340304540c0f412a025008104135a0351707040007410848170311605880340f40706450707803a00c180600902401070b421072000b0310315125a0322400e4005000610003210555020310001591760006644110b0443c800b04002c2540550181c00501d80c41c07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 892223830 1250 892222580 892222589
    0x506130605160915051c09050706020615040b12060c0c1002041809020d08030112020907050901120c02191a10030312020a031e091b03020315041a010602070f 69
    0x1200402d050400a0307021800d201120041c2d5840500c60280b8442124070b4802c03050511855440c0701c104040e00040d9a0200c141d1a010704152410951202404c0340c46035810764030607030742c0501560160940e185c154803c1c10601c0000b40045202c00300c0d0b098050508104484200f01e0490102e4800a0114144011108803d01a00440c541401c050362000784005a1a01d51205a03444850200b1500c3d401410480260040030064883d0781d01c203186046811245000c078010aa80800f0544240c003882c152144004143c4900c2d02243d03a00840384020101036a841701103105415280c031804000304040788041d8050b908040d09900b245160b1070403a071024040c55240e40b00501d04002182d4400124001800b0340d01c0056070703074241102c00314060b21402c41d07103868039165407180402201c100e82c0b0071115a40310382641c1c0c0ea0754107070b4852120f00d0040c52001940503005140e080c155000c0c0103150aa000d44a12560441c0c00d88544001000020903003051000d80c2c00404207004120801c0302410050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 892225080 1250 892223830 892223851
    0x1b01030603150203040c0e090304080709060b070b15130e060105010c03050d05060406091404030f080c090603250c050616050a0e01020a050f1506030109030c0f0501090506130605 78
    0x1249190740c0e004052541440a612140e40400400c003041b00000064000341015054102039091086040c0c1d10307540030b0700c40c41001e4131502000042c040b005018810846426179400c50915000d5103030382c0c810b84001001c202000034003e000004031740c0e0b40c44080111110002d00003c04020303106c5083e28040042e0480d50500850602d2040003030740c040101c618400c0d00060100d20341d25041c010901500c15500054621130820581c8036500c0300d0084901e00c100d0103a6071f009022074074807500f030b90300c00402d90301244c5224040002200500b080c00055800500340113000560700052521190780e925400c580d100007402c607030150000d2000c01c1210b16000710f0480d400c0c01e010222190701a00703610070b01e0b890505000e0108200c5e01f060b1300074802c032400036400c0815250101c80040c0132a4482110320000b403c03c18207400410411b040c14820060425819190501c007070035039450300042540034020854403503403a041400c000a50074090b8130700502120003407070034442d03e41c60844140d0f00c00400f000300c203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 892226330 1250 892225080 892225091
    0x1a090114041d06061c081b01180305040501111905010212091605040e0a0c0306020306030115051302090d120203030f060609030c2205010b0c07050d050a02011218051b0103 75
    0x88001243d2940c0240f000c50b0360040304600c80c44158038001020102820655011460031801c01d605c266459480c8603900007000381812140e2001003003080c0044c0900006c909000a00582d40502c2e500310104c20b00350b044034503e14028540c103001c2d50441c401194076035008125400c6103072440c204d45030411903010145c0002003030341460a102c45d04a104880c031894646800481115041c03000b021460382000f99190902c2d12400d0042c007035801510210b0181d031030061000d40041e214522803017640d10080440ba1f02001001e07109000e908005c9105903c14404028400040d00100100f10720f40710640185440b8940981103001800006220718018403081008945554020600d9945003c04840c04d6203491604521115500581c1e03120001c4185400c00101d80c03901614050b028075032082080759866500c44062240d284c450641c001e0035a48210103500066009000910b4040f6410344000359030904440281480315011505480640080480d07030841451050004d034400c0c0c0a0a06014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 892227580 1250 892226330 892226381
    0x20c0709060b2d03150d02040e21090117060307080a030809060a020705100903021e0f0c04020a0f03242702090d0f1a010312030510060e01031a09011404 67
    0x8040c0b20040144506170759000030204181c4d100090040340c2900a8000c024070a000d4101d55070300c0c001c448924416410003104924168144d20031602c0c3c550041c2d4801842a110301d800480c2000054500b942c1801449408688400c1c01c0010021280c040da46030349103400e00c11516400c02d0300260900e00102c0c0100000404988000f07180d1004101010000441c40303001c1c02c04034244101d52040e0020038030b02c0c0803844610a4002140340300e01014006840c520024481004202c2c400c840034100401d080445800003580254011001030382d4100391500ca04101c1d0303a0301003072a0340036044140c0060500c40ca038810301c1002140c1e40624110540c00f103240411040020f80185a0100014a00001e00c0010300c200135a25130740f181754072845109110b103541c4030710f01030001404110000000a140500007200130b403600240030115526600c070700e60250341c07120044020f05440140180720301c25551309403100343c40303000f01c0da40200700926030007101111620400090740c0090406840d42085400300e8072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 892228830 1250 892227580 892227667
    0x19120309030b0f011a07020109050405100f15020a0b090c040212070216060905100e0d06091b05010c02060f1c0c0f020c03030a181505070303050603150a020c0709060b 73
    0x3c030221718120201e490f54441d200481c0c110040b500001d0308079041805004006914090300e41c10380c0d2003284080b1500382c8508a07125026404010000164030448101300402c800002203900024241d00382c0f80505101c101003420303030340980e048821104036501006602c5506001202050201007001c10642d450400020198040c0c0d00600784100b0401c010504000c1c00f1305c12500144402502d40c02a40300c15081001c0140a1040b0554650020f40b03102c98024074071015140980b40c050315400040c2215400b0300105030065400750009078001c22603882c0c0c07030100201c402d000800c036a0000c2140a80310340002d000d404818512410366201d41c944442c5554048140d50191f003e41c0341120078044414240030f591500c40c2d10040c2c2c40f4039100c50701c41e80c01e5030040090078454042d440038825500d4030020305503141c0e6148140302041904070045010200399400030400c40c0040d00031201280d45076032401044500a41c0300807245240098404850108000280341201e044141d4004100100107001d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 892230080 1250 892228830 892228859
    0x10609080619020a02010f110705070605071509081b0105040510021c02130513020301260a171909230630010e061f0e19120309030b0f01 60
    0xb610354000c03800d000703428800d510070958481c0c0e4203000d00008840c0030f1060081d901004058549010300b0b10045140b6000788129030304aa40700c102d290410030446012001818441c0341180c51040401484c10031021010100900396030020000802d03050a280207482c1c05400114541e10078014045203103a001111712518031640035071005030307844100c000b02502034440781d00810b0f4084a0b410700c0300c24240710342e400386051b070344100d030390b20b00000e071805025501a5186080c40c041740e0002c004200025026401c0060005030514414140711102d81030314100e18a0500040001d102102c0030402800c0c0c1100d80262042e0f84051550507150703000c04103030240b06246c00500080a00751085003000c544d000b12801100d2410103940342561140d00440c11a9402d85809201e062150895068220010f5031080422101d45074284095a01c0b0140404c01c0c400d10300c07034117040c1c60103100010060030400c652040e65200e07030382d05d22082d4114601400e03c0440030b82801881c925080041c0074405408505 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 892231330 1250 892230080 892230121
    0x15030a0c03181b0f030b1006090b09061602131a0604030b07140d02030f1f21240e1621111002010c1403060901030b1b0a080106090806 59
    0x505520000b1184240d8003048640d00001c520144403d00005200c4d504c0d440782e01034406002c7c80754185644030011a4690403500070800e003050104113400c01864420010200c000d43e0700180ca40b10034290300056403e050b003a002c0c070a00c80c2c9507035000181102c0c1113114411903604582c16414642591180350504500400b40c100380040b034040000b40940f0750b026211501c03440341c420f542c1e03031911810b104500da40c2954001014280400b20b0b150801c0d8071000c0c5c40a0314468114903030000d42c080d00a84400b4170342c0074191603640302c030015024078904010805146511880c00480c05440c0d080040e072401c4002002d000c4460030f0b10206202ca000d403101e074002c00c0c6181c2e000d03201d92000c103802d22440c0b05414548165012006d8112135001a0b01074200021503910758a8107050074089521103480c43c8170458000303a000305601d0050000803112401c89400003000092a04035051101c00450164800c603004004901454010070007180d20140142c082c000c40005001d580c2400c26840f48000000c144 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 892232580 1250 892231330 892231343
    0x30a02042a110a02040b1c291b130315050f0c390d08090d050a020606060d0905060103030302180a060e04050a180c09060618060807020c15030a0c0318 66
    0x42c0d00380340341e0300d07803144111f40d0500a40140d0240b21b640380104601c500008800d400079a5010711484442488402c18424a08400300780141c1c0020b0513407101940c00b1a070b1118411503a04800b0000c40e080c0380017408160400040010302e8140784490310724040009203030894401c01003107803058100c46c607080004c600300e824060b0162003100300351a02806141c400d86910520401e01c1104040c1d9209080f02d0085034010151480c1e1101c091080b590345c4503080503a000f503800340001c41e1850030014001c0450b00e12030500003600e01255600c00d81011801c1e031082c1c000903000300e24081100c0ca1007050245042c8103c480703455552030488050b2130100400c0c00c45101d9a0f940b00060110704c40f0f908042c80e10100f54081d100d103150146400c001194983c09196103452a0560114002d4080c003025904000c07104407805a1503e00807040340d04500050075402103004840c0315074181e840e0324480940d103001100c88a0746030300e010340c8a5402c4500c641a00c004150a0044401c01501e9803859003860395000034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 892233830 1250 892232580 892232591
    0xc0f150a14070b04080703081f0b070212010c1107060903030c03051b010519180b181002070609020f191a0c0f1c020f100b030a02042a110a0204 63
    0x290640311601880301d0161003c01c040301003108000001000302800c9103c0e407501d03001034a4014400a02c2000ba02c083c0c080c18050000a00a040c88040605a8203200500d0780d2991034050b03503010b0940351600c00300170204100c40d0b40d118036007400b4007004016081c0b0345843c41000307140d600c0082158109a50103002d00500148518501038440412100c400400009101909004000d03001410103125141d00c0b191070b00039a28002d002c0f0000d203c0f00c8a8211100c0946a02c3d0100034203641c101540303c40c8094030a2202010f0f504c2d580d40060b0035403078011400010012000d00602c2400c83c0b1103a030700c5210700c507200d45411a1025018030001541c017034007045020213020900704005845448680f00c3c4901c03403402820b401580008000c030001a2000031003508014007401666141c0c03114807110a9034226503d80451103129030302441c0d506c03600404561740c003d07003034000c40d0440f0b50120b103000700d003080480380510f2806000d5001d0001c1102d490825001c00340380c0b45582e21001741c040001e10440d12007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 892235080 1250 892233830 892233857
    0x5040b0319090309060905040204030203060f070216031203050a0209030a0303110c060c070c0506030f070c020117090609010c260403140c03130e09061f170c0f150a 72
    0x4648842100c584074008200d42a52410301904030341311440703200f00284441d00003284d241482d00a441c1100d5020b0018084d54070b9007070040c400403000503c00404c5100b24841d81800105083c41340e0011409183e10070912a802d00004094800091001001500400c60605c094400080360358140b6050310b8005420070149000020714403420000b02c01030300c20345050110100511004007802032041c0f1400148070388c2c43c000d025213404100d405001c01100344000075802c6000d242074075060f03441450003041d48074071080820700061003501c500c04d80364803000c1003041c282024425010011214109135402c20030001010a40300340f4610300304501003005012070105402800509000c5c0300c01104280c0391008109155641c0c0c100140124101024880002d07807003041c504400e001d02c0b0314001030005560303100d011440e035490498100a4500484000140314403140c42c6c0d0162201104c00901345550b021070070020082540348240b403080c032540304006108801c480c00c451400d0890b00f0310b4038000410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 892236330 1250 892235080 892235101
    0x1d0d1103040b12060a05040e1519020301090c020f06160309050c0603092404031416080316031103070503070f0c0210260103020913081909030309080102030705040b03 73
    0x15540070181c0b2940110700c1c008107094116a5030700c192000d50300d030140a95204100000c1d6042036016800300e8014503485030850030407030600c603442482000040100390420848004a9109a001818507a901c101001641c0d505111849502c4000e200501705400c04a18241c115801c440c03e007400c0c95601c40056081020500c040d5912002c000c20654076468001003d42d1903e000c1140d6141d0b8090f20340150320f0050b0341d04010350040c0c0e00350351355003072101c00c00304040c801d640490449a203a40c207041410001030036080083d40700d0740103c0c96140802011000150a6036107003201442c0c1d865084c02008001540001500d5102c00c8601d400381c40005051010360303000d030a40d00e002e50002110700c4159403031a0080908c08001f01c044403900c540c00d038601140e4242c00401c0c00002c1d44900060040303400030603030907101c44016015100c0d451030403d40030000b204001581c55610003088084000b0024160001e40b50001401500001d51561504c2c0c4401032080c441d900864211020210105511404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 892237580 1250 892236330 892236337
    0x50d0b09010602070303110f06070e0d061d0f0c0f27070f08060d0c030323030a140c25080d0e071514070b0403170106050a031d0d1103 59
    0x240600181030039611120700a413035071400d00069021440745201d41c200f4910004e41d40910351450405010192140c1c1e0707080b1151810042460f502c4400300f031425010840c030340b15600503001201055065138030f10b0000203061034800c00c0000959080010014810b4881944802181c41c04440a92203460340847e503601018014800211403038005082221242e0030000d41d0040c01a80d44440c42d542d81c0366820030241040c0458014028140900d081000070f016401181701458040c591203000e0642d01ca40d1416504110b4020f40c11a44805401303014820401203142c1102d810340c4600e203086844090350300303031009000b070100b02d00c420400d60405108605055070b140c045410002d1061045000c441581c2c0c00c134134001d6050f02c03a03c904101542c9402080240c992840c811a400d0038401c85072190610300034010310640034010051800c0404401c101c408a010700910344400e03841e21400c80008088800302c1c5040f40360f2000300c54500c030701d9220018807444031100500d0034400b49040803107064114003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 892238830 1250 892237580 892237601
    0x7060c02040f020f120a061a0a0f1b05031215010804110f060c1e1c050f07050106080619050c030105130e0105090d0e03031e0703030e0703110f1f050d 66
    0x40045a50140c2803102500c46018000c46c02e000c0c0130302901d6123030702c24112071800d00c018150803040080c05216802603200070080741503410603a059a03607117620030117250390a61080380c240d0000107030f41041121102c4e02541240c9648001d0340c9408007a00043c0c0124006440078019034101507429807581d40d0440d0003e1401400b0f800d2949a8040c016115550451030310345002c2074103460041c440c003a10001701511184003840840513507100400c03040d52950302800c0400da00716001c21282c4c01041e000d00404004140e40c000800c0185829034aa540d101c20450070040c030f66051030148404501e80308181c0341543c5c07088444110f41d00803444550005c2c200603040c41e18650914040000320000400e00d0b00c10403285898007175000ca006000c054a901c68603146031390f05200700038045610080c02e000390104a21034240088c50030a20f010340d61410341e81d613000701d0310f000303601c0c4e4882c65074100007090340f8141c00192540c820020800b0011941003900900b0f92080050100b031010000085400a1800c82e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 892240080 1250 892238830 892238857
    0x3040515090316080606030c030d230a080f070507031202030712050f15031501120c03150506040c03140408090406032108070504080a11120f06061207060c02040f02 72
    0xc0c0a5560008003c0300984140c1455005190021301c0500303000c82d2003403460350f0040c0901034442a0900640300007050026500312035040e0004180400360200042408040e1501c0c0c240c014902203205410b5804014004810804140301c20000650071000403140d40603106005030301ca5482000031607107071000710f42c2030390343c00d04017800e100c01110b031030260501424030940c00300032000782681815030f40e5000221041e4000f1071200100850380081d4070a5035264494901e048001d907807501c800c52500c02855070141c0c800c1c0da800500c0351900e460b10500000d07d050781810710a1000c41082c00c0c3d004980203002504040d800100302c0615074403603004002840e804900c048041107060111581640010f0205000c1400070303000c15840341c001e40c10f51b011a070f00c20004001e01c808a548000480880580c10354001300050050805900c0038011300b0741410b02d1100810151410a00f0490801401110f01e0840e8024050602010360f2029285080c0b64064801003408034030000210020f01c1441d5550501 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 892241330 1250 892240080 892240093
    0xc0909190b040605060d1805030a12050105100c0b0c04080706030605100810120204330f1a07020f0612010e012102010c050109060c050c060c0c030405150903 69
    0x21401a5200a4161660140800c014054071080c002101d00500403190301c01c1d8148070049038491160001c942020140c60701e0400d1000594800c1c0c40d40d006030389800c0100b18070005500e0504444c0c400c0130300401007118035441c1d403650140e000d0260000c030a0043c021142d81000140903200881c200c80040c800c090488606a0f5140c81c024002c0c640760081500c42c43c07803400802c86440c4a0a8070a025500c4552080c0c14107140013558144e000010f001260050344803038100b02966810781c4800d000b58000c4101e080c140384080c040001851b1250003100c5d1200c80002d003880200c896810760702040c0c140c5101c43d80e80350030a00000c2c0c0076540310001580c0c03101d00007071014220b07455012503c3c1217134140843d040c1244d072030384080040282c100100031b01c8000c0c6141e80c50301641c8104201c210450180e000003032a0080c940790482034400702c00040d000f0900020302882d0100c01005005c6d0711601c080011400c18400302d82c102c0e240c2c8100d10406220791450319961000200368401c8480489006089441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 892242580 1250 892241330 892241341
    0x18090705091305100c0504050d240209010f03090b062b05030c07060c020f150705010908031503011a06070231060e0403080f13080c01090c120c05090c0909 68
    0x1070700410b2600407605402405803004402549008445004070f807511454103150403c400c2c0115909903c6007035501702e600100c0100501e41150440a0b03640310840d0250395410705500241c40c0b0261056018100340c545192400802d0401c100c05030032039011a5004400da18020210103030540110341c40c140b0004e074100720010040000000e1407009a0382064550031a900e00080c2c0b06802004000794210f004e00020502920380420007070403940070852114104000d036142e0500311a201071086076113010000034010300640e04030f000c81020504030700034000b4001044882400d581d95560303003801540082034240440d0b44601c0328500c40041c04200e0004103424188490b4050417045146064034540300c00030070001e8800a101c0d1080c1c2e0103480f0515640c54000212504200003031000b40c0c0d40d200508d84c180003031001c000401700202840c0c0046002ea103a800c01c01d01c9102e1540c40b1044606007511110001a04412100102c440c2122603002550f283c0240e040a481400b442175071002c0103001300720 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 892243830 1250 892242580 892242601
    0x90903091503090d050319110d0e0105010305100b18090a20010e0d03051b070801020a020303040b150d0b06040902040c051908070c060b191d07030b1809070509 70
    0x51051001d80d00b04e9046060b07003c030990b582d00c02620b2621810580043c00148032055070042004401a6440d9134544100313880c80c0001c85003941c4901030720740d44540041051010401114450607418081004107190000001e18400240e080e40c00c6411005d20002e0440700c0c0521010340385641108507060903d5500e10380044170807640134441d000c55003581070b904550400c503419442c069072640360146482040801e400c03a07016510018110707846900d1001c149440c00380040c014500a54000716120305151030300485020004046440f580a05a4261941e40d269030300000f440740c0110000f42c00751500808200900003161b40079400a0401209020702548400109942c5948504001400c004070004441860044d10307820001094280c3c50b40204500303900690803121700500c1045102550901c800159106034000d030729a60301c960145815480440354a0307400200c514080180c40d80792400601903161110120680b1030803600010300c5210108400b0307020303003402021b6207400d00c1e0041007078 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 892245080 1250 892243830 892243837
    0x5090a0b062a0318120f120a0e031c18050306010e070e03210d061e0807080115060806241305010c0f060c02100926090d020909030915 59
    0x41c40300b6000d60414680c0038040300f61212601c0b82589408240708040c204903682041e2100c032200d600811900300c00000c003c00c504444442c0310100d00d92150240140a0304070745840103054001e81020290301d64149502d03000406040041c1023151000b2600b5200e11011100c40d041550944100c00010a4440c2c2c0442e9441c030a0b40c05e59181030380c0598100506441d446522004602a104805da030409000a08054164528070040c000f030304030303510f12601500400107841070341c080034080e000f844103010500601d0b0240528600a0003208200c250b4a1480c0303200d4451503040003902e801040d91507940c8030304280f010340709210555400399104101400d80d40180c0440d5a2360048100005003940114036055541b5000155545081700b1074803550081e0104000b1882140500c4200d404100c2803071150052440c0500300f40e0f0001400800a182d1207a550101420a480309018100b01540d13011446040c455042da006a80350f01c44040051860007043c0695502c1612001c0e4011060010000ba = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 892246330 1250 892245080 892245127
    0x3031f1508010939030f02071101080f07080609070c0b0a0b12011e0e1608060601020123040f080f04031a060406030b1f0b0301091b050309030405090a0b06 68
    0x300032126401d071080301c44480f6010719640c0b1441084400e40c05004002440f4582240740c217011031548201c0c103103c4100d0748800000c440500d110302c8207000c1b40d40c0c0031502650180c54200c0703800c1c960615442c050132081d03004200d5441800c080f40000d41161140c1100e40b0b50030b60040200d01d040c14082050f01c041d00201d00f5842c040c000310101200c842805008000c04c43d0214401c0c0052100d510402001408241142c0c84803131040800008440a072055028020000a00034100381c1c03d02c00002801e4900007001c695818081a04c120540101c5881160304181d12402600140ca558035150b42240244c0ea41c441c980d000c003003000014040d5210040d9001181e48031010050f81d940c40030001222814003002e800d880c030410020300041e00b10502c05082000f070303440443c040c9030740e5180b8545030360003600301c0c0c43e42a8131801c01c1408141c140c2512100c040c19402c155080d4504001a250350f0700175031269521601150020401896150740302140c0200017401140d52000086001d0020303140340d164 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 892247580 1250 892246330 892246349
    0xe06100e13060606030b040f33080d080103060c0302070c0e062404050312040806131721073e0d18090501061418090f0a060f0803031f150801 62
    0x180f2120300c410310b2007605140c80750000303501130031040e50b280c10b03228440020189c3d124035590040490384481c07c00201841c400c036075980618030741c110310f000e000381c0306040202c0080c03500601c29400082c111015146c180c2e550001410110b03902d030800901d002d00243c20ba00e404250300140d503404d44001c14010b1003070f20b00681c01c5070f40d0401c2608222280b44074a01ca041c0300d540004000c00d8000c042d5200007a44c10303028800b607034143c010301072140110703a0008040c5801d0381c18000442c2c03040360f04502e4075940304405007850543e2592019080349107c060310400350080b00c1050a90b840104c52062015110000204445501c0f103802d001400080110080b1101900d800c6000031311180180107403810399209030380740c01e140c100400f2070f0000e6400000400008001c841c1c0d4041ca01d407120303070f4081e210300504060800d150800c640c00204840042d000410302c1c2903120000d001d1007030000100e0b50030031005200300c2803035000700380e0000c038580307403500003840042c400f468040801780e225000c075040c0c4180c0034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 892248830 1250 892247580 892247591
    0x1f0e0d080f070c020a080d0c060605031507180306230117070b0904061e150203070f021e0303070c08100501060e010e1908060405010e06100e13060606030b04 69
    0x560503500d0540446180a41c8550140020030080c414050781040510241c42c0f0403040c0d85a90043e0306002c80c10300000005580c1825400c14403040780034040080c002640580b010100300c11509461b07130001041c5000344924052100f00800c1c0041185008541050081102e03900b0f0315040f003184440741003da010541110000b040031104481e0303201031400d14400400e9140d01e4940000500d410540d101d5070301a6640500007182485012141c070740ca80b000800c180e240d4205080008841b41c003400500440d40f05100030b03400250800e00d455855a0100c824848007240c0c00c419070300300007207082c50079098040811148204485a502007050b140003c0c280d0318030b440040000d404a81007403207090005001000c0428603540220812111140050000a50b0341a64069545980e41c158000710040c3e20640420080c803d0a1103004102c0310b034000541340d01d0906001d0b040c4462140c0c0222208100c0b1440030400764410304031010308955005506104c030582d03894019006020fa544840d0180c0e0400c1c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 892250080 1250 892248830 892248853
    0x30c140c0319091d0903070c14031c050f03101a0304060f050402010e0907110607090305120901051c0204080613050c0906060d0c12181a011a0703021f0e 67
    0x1080300ca000d546031410501c2e4038100500c941c120300f00c0003070049001750000f00040300c007045118000c0000f600380c5d1454240024002d100341450710001400400046c2400000303c083c807544a0100d800c100b04011805449860b43c1c040d041296049500c0030750308010300a0070100e1000f50344041c40c8640c0c0035503c04c21004000583c030f00d082d6082110002c0c001040d101c0d50843d203180141e40b2980000091412008116165030000d28042041c1c45032800314280c18410000c00c1010450002c2070850750b443e03d42061108000a0b0050203110451080864100c801c040d040d0544c0e41510024030846041710b01c80c0c10511078054200002c440700ba612030280b0000094141403150500380500809808030340350581c0b9400c800014a40c0c0b013500e800700b1941b01041640c440d5240241d10507854502c02c20302c0d445c000b6203407800200c0350130222150030325181401000208103501d18480c8814501d40640c0d80c9581c0784c90101c0c1000005e00b514000d2440080701d00b17002d480ea03540a01c544c80b2180d001c68100c0c5541 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 892251330 1250 892250080 892250087
    0x16020910050f041d01090302060619230111010606050d0f1806020a0215010f1706010305030403172b0b030307020a140102030f070506071b0f03030c140c0319 69
    0xa0701445402801402142240d800c284e4043d41800c040e0307081150004140441060945a090b482a07006078004000d114082ca4022090503442070345200700405145040030b4400030317203240104807421291400383d07083c1c0d42e40121510400c6140d442d000b000303d692100005400fa80200c81c2c41000103107030000c1541c1c0744283e8480c0004c940c110f000c128048a64564600c0c0c080d50007000b5120845c00303111a05052104c00b100140d003c0d004600c030b6283c0701800d101241ca44401c0202c00c4a10960040c401040800c03000300c00c071803c4d00d4002642d009001c44400c130441e07561041d40b540d10500940e42940b001c801c109030700d110020074100c413014402081800304060ba40d0040c1d96000e98400e030101c0007003102e14000c1059000700c00060055030b09000003010070714100c0d00540c00c10303140e5401110401011031340c880002c442c0c1109060060f0350380c3c8102c0e1907240324074100c00401410f255980045005c5940521408003021001c0d40280f035554a40345082504c0c0d412000107002c216820500c1d003a01c5c58007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 892252580 1250 892251330 892251361
    0x30c080105010c020d050709021b1516110106120807020405070e06040e060d06050403120e1912090302132025080c2e0c02071415160209 60
    0x70594500b0701850542c2c08000d0b8100c0701e164120f0b140e00c12260300103000301e001e0014080264000009004c0701442108907404c0c016600750b504581c42454040008480403400412014882031a1001030030b59004c4003980104515001000c03034404545100c0e00300b10381000141034192094406100c55211030809885103800f100965030b001c0700a00060054194211030b1a500640060808882c803101b074270b078103007103c106450580014074100c0944094440b40c0c080d0102e016840b1000305101160703195046500c06402800500a00c54405032030207861240302c00e0000fa580040003100c0002800da1700f00700428459403010744a060500050420404241c180d481d4001e412107610701c0202742203840c052604c4008000c9501d0141445403141414040010304105074272482c034000c4440c10b4000100030100c000080d400514200b00888203000c0d03010903080221100580b0f4901414407100000f042e01c0702030916001b01800100c5c170f917903002d5240064600741a00a81340a081500c80380b881031001d50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 892253830 1250 892252580 892252589
    0x51501051e0114161509051204050f04020304260309070807030f240905210a120b0f060309071505040602031207030e03181504230114030906010303030c0801 69
    0x1c0003000718000340c00701c00000700007001084280120124144d030302d511017a410501c00c28442596002410200007081000354400101031418600341858407000680d4000030310f4a903801b80d0780100215040060020491510002ca090f0b449001c896030b0101403442c2c0c00c111000030b4213125002000810280c0800c0302410b480e00058184c0035040181c840464070a048506114042c500300012100403031070f88100b0030321911400c043c0800c0304000300c0d03c401841040400740e0316000304109002d2225081000d100c1780ea0041003022554a69501c001444901c1c510744168002500004000d4806404a20354040c1d0784039000500d4224941b80040f03545004034018040543d000300700072aa00a9004500f91f4044484d20700440c03047c3d018040035040d50040050b0136007a440300c200040342842c1c0b029a42542d5007011505030304144c64503042200e210403140b03810381c160b2010b10300504264810401d1010342e01d050701440c6d80c0ea0804840d22981c07a03900348070a4000038501550249950301c6851750b94102d8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 892255080 1250 892253830 892253837
    0x1807060e060702121e01020c1606080a0f0e030a090305190c03030305060312270402031b072109060f021b0f0f090a0f0f11030115030207051501051e01 66
    0x2070490f824480603021026101e5480c0c0b01d0303e000c608000d10010400c4640d101070718000340c1c90300200802d551500c00324401c0b00306040c500c0e840500c809079100303d083e0350001c0200130210708511200300c918002c14030b4004081042c00300003a440d420342c1e0004501c00c11a489201107031402000d0003004280ca070803101004081c20000746080012a12a42040b80c06c15402003e8401c0054609503003060b90b8030500403a2207544070f500407400440d080c8401d030b1050220a0701c05610354944280704565600740d2a114000210b408602d40e4240030607042041900341c8100c1c5c400d990f075448480c02602211072031059074001401901280c0d1454400320700c504081c4c52400000303000350201e00c2000360444992402d681c001a84000000741d40e507403d0fa100307014040d42c2e03100040e148000e800040c1900d02c0c40b12440030045c109100440b4840d00101164111401c100800255004082c402c40103480344a4000d0701d40d1084800404007003040401181c100c0d0011116035103882758034410400b1a051391429203010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 892256330 1250 892255080 892255087
    0x209010e07052a060406140a1e0f1103010e04051212071407060f050114010203090603060105030601140a051b0c0108070e0301111b150906070309020409050102031807060e06 76
    0xc011890341c0c0c5443c1d0b508400c0948803070500f0310309400e1030540c00b101c00380c800302d4642c0070180c0310044c030003004c1360441d51454040c40f949610b03941410098408004140c040d90b91b687d61540301c100c156009900b8041082201552560f55030089900c2841c15601620603000720507205040a60280890f41c0300c05040301102004d50f07441c60113541e5504401e101c4040c01104003e12030004500c1d1040440c5004000400601941000000c2c416940c0200ca101d0555008002404455480000f92644004c013480d01503525a202c0c0300488040b115024401e280480110303041e5441c0341c1003806003980700c0c00401107903500501440e00e0340c2c1d80e4250605007808202090007042c0d04078859049044400d01c0600040f660b280400f410546036408120341e000944100304041c3c01c4110103121a0100178100341c0c2c03400c41030924121113501d0343e002400319070038141e5440b041d80031911103030040c0d103000790002d0086460f80781503a0b0200400da0001c2d01040d09029030b0030041074050141c0c04155030040080d003042d04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 892257580 1250 892256330 892256347
    0x1d070609060e06030c0f071202210f09040615030608010c0e1807020102160b06090901050702061906030212010f0b060f0f1c05130309060e15160209130209010e0705 72
    0x60990003e4841e110312242013201c449448542e500402c02c7c0340c42038500100c9040c4014001b800c1600d407423500032141d40d0b000d03032000c1c560402174251000c00c0c402d2141c2039514284580014014011a44118685a0f0311003004c0e01c2c0780c0d0581d0228080b40c01c1d031341c000e003d00340159004450300080705050b6580480c000120703664110150a40b5030b840800e60000500d460010304d1030480701d03216030400710b4000c00b13140104400d5090050315190017107820700003400f16041c48100a52102002015110194121541c01c481002c03190030030801160040e000b412003e0000f00160301900c1485400645c1074208a4245801c0c10700004a441710b480e0030a00600b0f08000034420000750713001c82c0e04c40c440410024214144c0e1103803031040302e01441e180301c220411011030b4940905515001d9201e4400e000d5242d0300074500e903c5c1e402c549401001d03408181507503180401010b144820004d9000380d08480f08000700000002c122140e6004a80201c0301d035000e42c2c2e640c03042c8604001d001c403100340010f0000d000b82003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 892258830 1250 892257580 892257589
    0x608060102070306020d0608010b091e040302030d0f0209010219050d120f050901021e091c03031d06060a090e0a020405090703060f050406050702151807091d070609060e 74
    0x16041581481901d034001d9882d04d8540c266040400d0501034961b9540040003c0e00d000d10640c5450300080d90514940e242080c0c88900080703560044032603100596001500f01031003031040b1a0305944803041000505035030440d400c029082880882c0c05071041c0d507280040f40541d21850310510f98000c0c0280840541c6c080102c0351407405120400d01d039500c500841e15003011900510340f2030442c40c1c000507110180c50880e001e403803541d07000110702000b04100000c243e41381e0451803216526111801000840c82e864120014100031801c08018681d019200d0f16000e00402d03903c1c0100c0d021907280200540761341039402180c07440c290740031550b8840480f1100500f05500029030140707a06083d260029500c0e2509000d0b2880c0940711010695110100020802c5c54031419401080030300c0146115107003107214844050000d488040400201504510044c1c400c202c8500030300b00140341448090b091022000095402014006441c0101c900126010303110349200800c89884d6a00c000000c41c01d1000d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 892260080 1250 892258830 892258847
    0x30b0a170d030c09090e0607030b09090a020d02120a0c0609080f1b01020c03190303060b030c09090a0612080903070902130329190506040b130b040b12160608070906 72
    0x743c180440c0074400107103190316101e61303416512040040d15a51400d441d00508807100d030910701d0710501b0400c0030f00c40c8150001444200310b56042d1588640c490f00c5000050008828a40c54402445600d501c1802c001e052a41c1c0412280c55894061040b61a04291a150360403021110a07550010800d225043d0516500441c100b2060059a80e044048000b103814000108982102d1041c171500c03100c101350381882060010b242c140011411400e12581c00b1903e81700e4121200d12883c0d07050b010640b211070b40d030311410042c00e0b800007400c2080c1c224600880c85030414041e591082c054100c0001e82c0429500840c0c940307220240c0030390141411270341c500942400069040c40c034540c0c1c1c0410407100104107101c8a004070010305443c004140800c0b195016a54020a81c2c2c4c007071070818421440e6503c5684802042e030307600708804115030201c0380205004107441d00c01d00e03504c002440081c0070010f00104800185d1038805101148241c0ca0700f00940e8400f005039010340004426000400c240c5102b903482 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 892261330 1250 892260080 892260101
    0x1106031303230c070806061017460e0705010503100f060c020f0a0e011a09060f090306090d050906070302100507030c030605190506070201091203030b0a170d03 70
    0x842c90126510100c001a508001d2420880790b00901c1d040c011000200552036001c40116901e80281c111040003c1c03403c1d00c0c2d40c01103850100c0742c001160100140c1030000401c00001504100b0a400c0b50380003440000c00d175805091250200810400707440b5182c01041d4141b02c58400502903d440c00303004455650004040c0e0130306070350349000407502e600c65101c2c481c0105125540c0fa000c00da128010000442e14106440f80b14054401d41001851004112641151104100500c03943c03000b940e03d40c00c81c802c250071a41e02000014091060403941400381240180aa0465074503540d002c0c00c0e6a81e5021007140c0d80c000c594244a000110314205004000c031620034410340f01c1c4070010010b40010703a030040c2c07100320110703032120b000000c0d00354144101070042c4411a0b24216402403400080d44021541c001e041c01202d0001d1451301b5a406902110010201250581070f25840c42c10028018820340745250721440360040d000400340d800c3c111001021198038050880726211400a50007070055204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 892262580 1250 892261330 892261367
    0x12091401110601060f0c0f03030c300c0e06040f030308010503030c1203070e0d0b0a1b080105120c0d0b0108060a0c0806300105160234030f050a1106031303 68
    0x1b4010005500ca000e2261601d120b620007160340080d01c0e0300a0007030206106c510320f90b41541c15070f8111505182e0b0000d1128018a0380000c2c0111100c40b040ba03054800c407071a150030240004001610144c40111042142d0080d0303a0400c099807100700705512803190748400111030340842e003410b0f2880311074001103400a105080151a01d1040c2021a0901c0c2d12800180d60740b0385100d013004030b030002a004820f00c3c003000800b06400c00c072110f02d0207454904180200743c090200854080c00c540404c00442242400040030301c1054141850503510210090140f203289000d0300c40407900340d200a009140c44140151070341c410907510f0300e0500c03081c514000c90400540340303100343c2c200c0103800c02079501d8410310b410f0b4004201d52420110550300c1a218030010340440d0b01c0351124845000388442103165100700e803014450116500c400994030051150400350403a01600c11000801000003400c0489a200315030361a24100c809017006403c2c0021a030758080c2c0d200317400302000000c7c402c0e0341d2210a41040d92 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 892263830 1250 892262580 892262597
    0x70206120c0717030a0b01050327010207050f10060b0a1d0a24081305120705010e0106060c1a06060d09080c030a0509011b0f06051312091401110601060f 67
    0xb1100600c009000d1103d02d90000000305000c00301d5524000e80740040d00038200359207142020101e0003880202e80c5c5910741200002802100c540400707404441388182c100c01140d09a40d0040202c60700d41d0350304622484580d151030400034000f1840307829640c1c00d42042e222200c1c182da80304a03141e6060030301242c15a0100e1001d001190a0702418150445000044e920400d0000d02d41c802801c0b60034090100421070398091515400243d000461180710350700740b6422502e401c41490314078054007401898038455401c15001141966000314540c94a5009590b100d010260507031041401c02419074031036409c24000c20904c009120903070400c40069200d550394601c0c042e10f02c030006007981c001d032031203c0000d43c0015410485691000840c068140c400072a090710741036030342d6144261081c1c510010089031b2a440020405010059801c48564215548543c1c4d5146890b008058011500031404400d601100c400c407954842d800c201c5a0204c04030003440b0690034028161044102481407108100c3d095 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 892265080 1250 892263830 892263833
    0x1c120b1305240402040503060406020705031b0607120219050f12010e1807081510273b1207060209033912010c170903070206120c07 58
    0x51144510844410524014180b6a4814080d9942c811000d052040d0f00501c01848159000320780150043d03440100141d03200f18918089055009011943d0607001c00c1c0d1a826040031008109035100f080c880d5a0860340f1503600d0000c801b02d0140240510300007021a20b4440014051802440e6a2980310040b0b07003040d005c0e51080c1d60b1250300760480300d004141182440200c102c2002504500000503000c0c103030311800e004105640e50070700401c8802c28a260401710341c0c00008011003101402d440301d1a450348410321841c2a0302c8114002e20029002e20300007401e0308580b4100000d004100c1220b24111041c1d59003540010554880d241651180c0200c0364240703d80c040c506c00400c040c920400d40541c807907051804150400100a000c0980100703c1514420300b1320080d510704480400391100002c50164442c04138074640707001c11203080d0030341ca059103141c8a10780108402da1414249610302d0840d96943c01341c50b459008162009402290512844078081c10641c6001c0e480400d10401c94101070b0507 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 892266187 1107 892265080 892265119
    0x2010c0c080702060714010509060714040b1c020318010e0c01050d0e07090509010914190305160203070f0e100f210f141c120b 56
    0x8001403060465580030b00345d81010350024000102c0002c40100b25008102c217a90380d0001c0d204090019040da44910480903000101191040c1414540a904802034201110b131001a1200c6001c13480801d040e4406140325424220360f0303042c030b4003089401070f00310b070040039030a00942c204000c8000683d030844100e511598100200040c210b166008a0b42008041c0e080f5a04250030a030a00c2004034054000d41c2405024440000780b0204210300c240c1d03100150410303120f00107050740c400c1c00030900030f60280c8034004502c00c00e00110415680000d0070582590445c85a180c280e00d0305001c110081c1e032000364402c2071040100481420940745a1240e8058440e0103d1001c021604800c0440c42c00b42c0c841120758098140c0e90041900c1c40c118041406460b503200d103500c1021000b482c4498801c0410102d070503152922080c1c401b211030b070080a0703c8030210240e00000c44540c0458020741c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 892086330 892266187 := by
  have h0 := BRFrame.cov_init 892086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 892086330 ≤ n) (h2 : n < 892266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
