-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4976
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:20:21.050614+00:00
-- url     : https://prove2.me/submissions/7185a988-e4ee-4482-80d5-108596b2d208

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 894784172 ≤ n < 894964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 894785422 1250 894784172 894784181
    0x2805061602033c0607030203060d06060b19050c1e0f101b0807080a0506060c070f03061401060504033809120a0c020f030c060d050603010c030903080a24090906 70
    0x804a43d0406989081e0303c407140c13501c60040c4503105059001c00801d4081c0c440103210740485900c03650400400d900e42542061641000034925014041200554003162041054035850741d140c80040c807413130000e9520140125042c68503aa079030b116400c01241c4110341001003085035003000400080325140325020452820030200c1001c103226030b03a02030140680e4424042d6a004468001c002003503165074000070910701c01d030608620a032251a81c0800d801000300031900c22240310b00c0701000f00d0004504080d00781036003449030801096092104001003903840c050002c0180200c10110120400001b00309619004a074400d881c0c0003070309042200e050410041b8a01c20803099450034202a10101e00414140c24504003d000e13602c14008811107403010040b103991000c00610058981c2000c0032400c008000c2212954030a43c00d1420048403c0d00034418800c00740d8040c2d0ba40031160766180c2e646000780c01c07054002c05010040000c004401d000350f0880398050409401d021400c094036013400300aaa = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 894786672 1250 894785422 894785503
    0x18090f050c0306091f080703110306010611060f060105071205070203102c0709290607170913180b150d020111010e0304030f02280506160203 62
    0x316010410f00103690b5a041c80c41d6072180c000100603e480a00066030058141517921030035072807003129404070411191291901c0d03288026400ca4180b603076109001c0b14048020010b00180b83c01540c04203201d0a849003040d54880c034181040c610b440c205a4a00d219140c003040d0040010320003041a000714a018450031070b444480300401e01440b20500c40d40300003d04040340120300c3c4003069110a030700600c18840b0303900400341134800300603220003044a5030344030303140c08440880b11904507160030092810000b82d0300c21940008130700d01042c44002100c9110f40c00081c41c1a03008040e170984071000d05983c0102003d03100c02c40c8003101d9240e020700d42001c013400e000c1e000003031a0086200b4142c082c3c0b0f6121030710003165024038000d0034111201d6146030040020240b84180303030000181c08030601100c4540000b0035882512880c1410246943c1c0b8070341c1012030403241d400d41c032810000300814a4844041d190940040040712422603140d800640780406041c0c40740a444120910f42051388481c55800000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 894787922 1250 894786672 894786691
    0x1030b0415052e020706020d09030c0e04141b0f03210702012319080f0a0c0e03100e0601050a0e1324060e01052e18090f05 54
    0x40c9254107036000c045030700b40034150003900ba541e0540c18071522561205007243c6500f43c07030600e14690010003034075510a4000ca0f80944148024004031520075030f602030490b0b402c00390784d500726401c5c102d031250803820203001a80c01c8240d00100000c1003105100010510104006580071901c859042c09800c03440250124481c0d0031505441d203208000000c1113480041d0240310f15a00d10031780c80144e88101e00195803c800307094071640c1c0060190104004d107854880c1031000300040d01c81050071034814030115204031311000d41c0408036000c041c0036004096517005a0901d50003040100021a160440841e40c2e000700503101c0d40c440009420a000c002d02411003516030700940c82c14800c2d03c2d0000c1d00094244c0b4102c0b0410241403040c4000034000403d503044207000050141c1041b0491400340816000700030000368081d000003503618101801c000e041d110602200c451024604e0042170407011001c240702031211030101e03000360164100140c009400400030000712046450b061000300c0c0c0c4014485e444 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 894789172 1250 894787922 894787931
    0x1050913051c020d170a181707061103160c02130c02060a0b010504031a10171b0102011505010c060b0411070c0e0606030a0203070e1201021e2a0f03040306090201030b04 74
    0x604c1021000403540403402d06d01c0454460050360380c103451103403150806070034141d9050b0b038855820448401048001e000740c006204010003016000e149100c2030790b10103185040c2400710841c040c050a400290f0500043c0004c43d280d404030101001d481060790f140d80180c229904002c0c24195030711541c01000e82c00c1c070f8400c2c05d007429540c03032503807040c11000c0c2c03880e40b90307c80d0002440700441c01030071202404504440c0050701d10171070310195441040d090054001e1900009001c00303548140b0440040000c500c0540e484145081d00544141044903019102e550b192010604141c44a0007a43c0c0340100e0244c40310f68420180c20010202c610a42108042001801c103115165481000780c81d000082c071600160b60b8cc48540060352050320410340141c0103e440302804101c540d040d40a03049031526840320845c25420764800072294800d03072040ea80d00c0c42030f480902900303052a80007104a22626000c94190f0f00260306654959042a1302c1155110b4840320320350304550b0b05010b504d01148042d1000d20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 894790422 1250 894789172 894789197
    0xd09090e071a041a0405130b010503072607211a011b0507030b01090606020f0a03031d060a05010617060109060f02011401030c03050c090c0301050913051c020d 70
    0x251501003a10034060741d8094910b029002907038107000c40f001040100c0130303a507203000000c0884c0716039001445017034800d260480c0074401d58001c85c0207030021510140e54840c5180c0c4d5000054414108100001c60175140c2d0307032408071400d100c015060f8000c24003a1500b5a03c48001c10741c1c80500c0354040c01c84030b00d150810340c4402c0f095409620202c1030410074213090300403c2c1c450cc030072444040300d05c0002d441c0e071140c0d20000007800b41d1025294103a40d80410700713004050300c843d07040c0d03654250440344030003036400b241c1180b02081c820783c40402104c1503001c0c80c02c54032121034401d51802c1c5080d20900315441c4e80714010010a030b00700d80c1004510034a08049081c3c0d141400000e0716031760f1584520390a00c01c101d600e01d403110b4404c1d4000041c468003c80140441e503100d08004292103110b000c1218544a8103003800c165141070310f0040d00c100c1056003400d1540c2e003460144140c012010b003403180890011440e080000e40c007802182802d0035001800007000118038070007460490000b40403024000e804038486c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 894791672 1250 894790422 894790451
    0x110a15050c070c03020907030920010e010e180c0403020d060b0a05010804120c03050c070320040902060d0e1e01020a0311030c2a01060b0406030b0915091806090d0909 73
    0x80212a01200c0380c420341d07987d890042c1d01902e04510300808040064840070150314100c007141807409801c3c0e89443e400740780d80c001903031080605005241d0010702c448140031584042c4001e10341c00002561680d08150780d0303502240c1080000c10341151400d403a10042d4150b0f04081070303820300400007440c00080904043d100c4030076044030f242c255030401c402401c003501418094004c9840b20855002180d86503540d908160071070f15403075007043c000c113848024404d01d0307440e1a0048100280d0000c08262505881ca1028002414a10303c20b1425000300c0c2c1516094040c6c000f01744240380c0e40030002503500e07a64084010116403a034100c00419007028402d01000c0c02da2882030315060204d900c178074001042040700c030042d003408080d1280381e5503082c4040880c07043e800b40f01800c210b400390b8506002c1413480c4001c00042e002c08544081c415102441001c1c02490000d284a40085040d0701c1c40013141031401d226420000102c40300c1415901c00c1a8049401d603101075148010b02d5280003c104061140201c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 894792922 1250 894791672 894791693
    0xa0b09040c290d0b010908160603060b03071b0309180501090c03141f1a0406120b060703030c05120a15081912050d0903170606070506040201050307110a15050c07 71
    0x10f0b0381895a40c08050b030075a4003400c142e030040d00900d400c945100301403a9050104810501456002a003014000281807907080190b0703001d0b0595445901e0805580e01c3d4640207000c00d00000d0303041080c10f01c4001481c4e102d02c8210360905103400c4011031950706118419041d0740c100300400c0c04052070040050442a805010260411104403401c0c103001c2c1e160000d804480c074140c00003a041700050b26250004000d2400a00032175009440324550406c028442c8402c4a01e58012036401c81810080540080d1295000e85030321078142c1801c50402d03e80c10407050b0b0003d021a003420001d565800e20f811824454100c4100a2420400030301e401c200f44c0076191003c04464600800403004040714400d01401403007964085c0e0506507081122a606082c000c2645203061100580519000d0120301603090140848400c1a0004018155078455500441e03507688003c0c08042000a41c040c01c440326901840745681c00c034000ca8451038a400c0c031850050483e00c0103865900c6030103081094a000a092188 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 894794172 1250 894792922 894792937
    0x714010c05060f0603070302060d14010509130210091502010e011b140a0e06070302071a0703080f0901020903030f04030b010b03040507140f0607050d02070501020f0c04050a0b09040c29 81
    0x1511010f8407100c0c00700e80746c12a207400080d0310200215021805003c42e031300180400714814200c00751030b66204144810600241c40486040d050602c658000d41004485001c00001c0c42c40d00b071980540c0c03058002481c0602100c24001030b51642d026201219090181c10006445a047c4d84254226240b01074560008a400c80601c407101041100c5800d0207408940c408038000f5000300d80c0c50b10b0920b4001c2d281c1c9013600450104c0d0700034070780286445030740c0c1d000e070303100d2661503101c641694884040f5014484d00041c002d1903699001c0121030f226440a2016011980801c3c0d1045d0700e4904501d04040c154a0580107104056010b00401020580003e440401c030303002a2514205071030308a007c51031103040424041d41180002410710104800010070310041c549076402e42d00d00c1c03500d0301d004903100c001240504403c1c2d400840700080381c0c5040d900180e04034822000001d13401981101080ea184402c48050324035104100f410031018403203008002c400e403400400031510710a44000184140500903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 894795422 1250 894794172 894794191
    0x150b010f031a27100308180d1e050f0c01020c0d0c0504050c0c100b01080622091109070302190c03111501061106040c0b07230714010c0506 61
    0x980310060325a02c10071104603214080c1c00090080e42103001c01c070507003850441c400d1803001e14000241e2806220802c900c02e80e54440f49031490041c00803c42c113250240c8107201035010303c68561003400120704001d40030740d00c602d080d505d100c440d9650801c03d0800c0740c1d0741c1000c1c601303800c041040843c0381e90100782600500c40440c0c1510450080c0d0511410b580b031250000c641083c0341c00c0510000300300300c03030162440d060000f044400040e20b10010509075004201130340d010420342e0b0302195151520041480c00081c0c6040b000425039060002c1009840ca03071740341a20030007041402d40201e401c0c041e080c545d0202d031900717042d881c0c00e0300b4202403065042c40080c41c8007001840c103502c03800c1602c10320318034080301000340490301c1e0303402d8000800f02031003401c4c0710740408100f0600c00e260260711701068144c851900f03d0303224030382107160201d0603010ba405084101c904802d90880900080500210b4145090514000b4107241d420400e4007009462850b8000d414052142d550f6000200001030140e480a80c22 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 894796672 1250 894795422 894795431
    0x20f0c06031b0a0302120108010b010914030102071506140303040f030305091c0605071d031b0f0901092f0339070b010e01060f0e0303090a080a150b010f03 68
    0x1c10301602c056030316010700d81c1c40307440011140c40c07003503054024100242c2c00000810039641da941c011400c8820b107581060104200a40030090501c01c604414007091000d00054a08046035440c0c8102d07003540c804c0034a10640d0b407c400c1c000521003558115841b01c00350010340c6410704007502071288140174403000342000400550a00592618080c40007445101402204400c00c149440c0000d40000c9448070000b501d0062840c4540b61600040c4021302006800360006a82d8204490010001c0000b06030b0420301030040e9404a480303005800d4024004028003f42c5603180e5200200380d0f59003a2880e4100c203800800d005441c9112004481d003201b01c0c01c10400d07507242d0075126160300308040d00720040341680804405a5449000c4000c10765140710360442080c1e80c2c0c0b6046203000100382805044001030507483c1d8084a180642a1040d40c03a40003421207041c07001d900001811191075400603480c542003c02d8190810818010400c4124150182441b810102c000001d2400310100960010036448 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 894797922 1250 894796672 894796681
    0x408060408071a0702010f0e010b060d0f060521060c180d02012102040602070b21070513090605010f030b0306130309030512070c0b1611031914010c020f0c0603 70
    0x220b00f403102520507490708071500d152102c0c020380201081d603802041e49081001d482e01c1c448040c4503116181c00000c0038103040012164a0100030b010f40701809800d690b868001094655420a222048101d440480f00ca50181d03180c00c80d050550103011154182c0f424002c200b0749003010800c00c000602c1c00d80c7c0030b4249003175500040300d0003540b1f00180e281c010300c48611040c2d2801c1d5034000b0010358072580c00302d40400d551066416114840c518a00000c15581003003210340041c0c00300380743c0c1c00442920746070b800c1255040c5641001116540320f1079205980703000c01c004c0c5513004003141c0d51003442414104407011400005ca0b84544000f4940300110081300d030150101030107000c80d00d010316040011070b0f5040d0030100d42c2c88000d5102080541c0c40e0344510b0f50014415040200302e40d04040700b04010500c61003150341c0c008168040c0800d46a03d4064400d040fa00c001d10208545841406a5014005111114922400c54503544800c0086400ca801c245000075000134081c2030b8460306403001755030ba03034a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 894799172 1250 894797922 894797933
    0x180302220507030209030c010c02181003050106140423010612090b151c0c0b0304060902060304030e12011a1302070b090a05060109050138070b011703040806040807 72
    0x40001440103603203081c06000a056143d030142c040d2040c181c003154280700c002c0005403040e0b4040b1000035444600179401c10161501c90a406400c103100e440280e14480e203d40d155420769030a5001092021503a20600680d0300c4c00d07004440070361304412103051410078030f80c00b24640c0f201e05024500a100c0107401d480205030095024028942c0c115014048504101055242c5a00c3c107450310b500ca489094101206007520b00c00710984640e0103440c2103601c40c03500510710203035013004000b40e40f030668231403140016803101401540b08a200b40d0303d0b01001c0d1290380030807174002d0f40420008016890700340740000d09200540c00d009480c000b00c074848103072841c0b0901c08010344a2030000034110908a000e00094250005400020b14070401c240c980903030b240c6003501c040701c0091040480303010b11117214040042004492866051400804584660031124040000c0d07100c0795084035650900b40041020010504280c541c6043c1070000d07500d4980350803402070b517440000c1c0c00601014000501c1300d04222 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 894800422 1250 894799172 894799219
    0x9031905100f060306060509060d0b0c0f0c030309060a3803070605030928030f09031202070302040f0e0303071107210201260c0a12060b07030f180302 66
    0x100711290501c00001d5484168015042600c0300b01d400e103003403140c04203461911200d0207220790400303403544000200c1034603110000003018122290800c0100711609496000d60000e18080403e1307001984d8904141c3c071b90078500311004002c1d1000300d25001030040038449143c9a640e100c90600308102d1030601e211628040510048200c40d41886840c0e4005043e540140165200b0a16101655140c0100c2034903801a01c6890840c10010950071a854000900400200d003840c0110700d000c6569549035550f000440941c60411005680b08c49420402c6140c00d008401c0342c1046e001050240c00c00203002da90381c074000580103000b8440c03103e6240413802000c001174402000200082110800c1c01c0e040d1780816901078805030700080c6c0c08908441100700c002c44900c8200380001444403503544440c1c40c0d04264210169001c00c003c0f06008040c401c442c28029280908150300079550396140c14036000d0040740c40c04084d14140010a10511244801c14030114100c0383c054808041c04180d035211400c250 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 894801672 1250 894800422 894800443
    0x1a180604080601180e0307032f071403240c1c050109230406050a090506041401050f01080601090b010504030b1f0602010b06030a091e080d1109031905 66
    0x190089400a403607400094154100d43e0004244004010150440c400707840b00b00d81094000d510030440c5000082c400c801d280407107681c0014000110201d201e203c01c0c00030a40244546650180d101400003407035003c192030f10401e00303e004220701c4100c040d81b001c00705609040f40c948400100c001420100803001100d4403510700c0d03941d1540d8403180418182c0100828040c0b40d00315490711003200c240c0b40c1c6c03401554912110507800c01c40d403a82d55540f507801800d40100b08011081d01d40030031348001203080029500683c840e0140c14a0290700805c0303103003162030091200d01c0c10005807004000106000c41d00318151000c60501180a030b035403074010382c0c452080c3d50005180c0580e0300d04214001c89100e41c140380c040d0050f00c3c003802c442d80d10b540072170a9400013445282e0116081022804e5a9950b6100d51003141c45400d161540e004014085005020820030580d510180085c044035840118440d8040c100c810761800b600b08051040401d5842c4040d103501c90001228002ca0803c1c0b1808002a1002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 894802922 1250 894801672 894801679
    0x307030c060f080a090809151909090c0f0c0f030201140901050703060b030c0f070609060c020a211b150213050307120b24040c080612071a18 62
    0x55079806000745000741e0040c0d039200081d54180820310203101c0b80079800004c1c0d0012041400d260f4600c04012800440300f1004100752001c0214402c61405081c10741090700160301c035131450500c1c01c0c44050030307114403003915002c00500380421110190000400980c25800608130380030303202903107410b0303004221803050158090f0000d13040005401054020610440b0196000c4c0034441d520b00100b181408260361681080c0b0b800e209400440703520b2000307414458040d02c800b0880c840c2e0341c1c41e100300f1190001100d40060300031003480c5042c0b01100380c2c2000040084154120002800400244604407006202c0408540c03031350800c1c00d0003010101c0c1a9030300c1c002c0d017085617910443c90040880386464403420340680100e8900055000e40004819103960f04000e80d00b0030303652242d5080c2c4440014002203081002c2c0640c2d50052238950384102d600da000701c1e4803805880d003018402c100406050001008280d8040841032084020052100000c10140f004054803003000c01c05011003403110361a210780 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 894804172 1250 894802922 894802943
    0xf2406040e07020f010504170d0f0912080c03130b0712050f09010e0102043c0b03040c080307030f0503060d021302072a03020607061d0703020108010b180f030703 71
    0x10308015004601e40903030050b030211500801e41d440070354240c0300100d4000d0030625000303c20110341d07400300005040ca03580c40400040c0f11034071805403504403040300905903450b030b88a01c00c10300c00c0d81d08004025041380d019200c43d811880e011303084245140301c543d4014642c084001c08565030600582c21002003a002071418041132401c403040100c550012500701103551b0030138603800651041072003298180e4481e008800e0002c0c007940f001d482c803485100700c62036042c1c90829014085025204020000e4254156810ba9a0505007050f2580b03480d40c2e0448800b41d001088500300107500800e42c841c0a10060414030748968900c40025442075290601a41110940c200305001d400640d00400d112072252112003540309040b03600c030700308840340f400b8404001d000d40c5060001d0314000c4017410040d44121008184d01400324088006034030b6440c1c240c03016600ca00d0042c400c542c0c1004c1064091b1004801c0780c2c0c1043e402c40300c0c00d100d20f10035842060040100e801c1070312a030703182881158095508803c82c0d11 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 894805422 1250 894804172 894804179
    0x30717070f0203010e0d0f0c03200312012c091f0b10080426030a0e1e150702060c12061507050d0f0203031015020124090b090f240604 59
    0x941baa254008a1000070301135246080e0070038007170044440c0f01a05a43c9601450000b00301d51803140c10b5030700d0400b0b1207201c00e2185c00090114007441ca80685181c1c0400800e40c00b5082410b42d207400c3d80e03040e40c2940f0244408225100d040001e54a0650348a010319144240302481c0c0b000003444502d080030380060400d0b035052011504104900d00440c03040705625418569006000a40b080408611038009010030101e0701c003007943d40100c00d4045801090f180740950112010301a490014508501c5412004403611140d503034004481c0e224055002800e030038a008140b640140c4921200c401ca98070411020450b03a840d507200c0c0580900d10400d9980c1e07102c0e05400c295aa807052030084100103000f50841801062020054a0203941c148850840c0c240c00c04980c41c41c00030000c00c80600b150350759948000054000d080800640c0b01d0314054401c02828070200009440500d0152070003402050203010500304a000003640c0302c040e01c2d944171300c000220b036180403411030488035032030340b180c070114021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 894806672 1250 894805422 894805451
    0x4021504080d18060806131401060807080703060e06010f090306021b160e04020103020304031b060c111c08040201140d0f0509010e0c040b0a0306020408011d030717070f020301 77
    0x4902c604058440425018107a1555000e24466000c1c250000760120089400b42c1000020765078221002c00001c55140c1c44480e003511a407100b64000c00c0020314243c140880c45030894106a0850001d01e414041d081c2814480400f0380c3d00175051078100031607881d10200992184a201b03000d075078803500a5550b203101400040240c810309151907424050400b800394000c8403a80441c04451581c0160301a683d1640c0043d8000d4100810a805100220307040500030b8000302000c40700b0034410a40051554481400141468511800c00846a0140140921704000c150900b4a036003198a40340300d5540c1c0f2440121500800100c0f410783d0450041a00043c02600741c0003180d4119030311104002c2c903a1051070789400c0e00ea01e5824001c080c0c020a400300918113142c0c110303550b072100c040e0011071620707902c0c0d40f40000c90b0b0040c0c3c8400a036940d1100840001104681040200041480218144405071301e0780c680483c09080303c42d01c410700004601e4200071082d80304160590300140200030303000360603910 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 894807922 1250 894806672 894806683
    0xf03150103060806090a15060b031602010c0e0d1209050303030109020a03050c041412030910080f2d060310061502060106050301080304050f0303091c1502040308120402150408 77
    0x14203011a050041c046080b12001400a10800c048401001400c0050326a28580310004444028440d16180e0106045000f080154010602101451800071180300c0003403c690706a403071103003000507582c02481c44d40d07205580802c4043d0003009003c80c503441e13008295009449a8400340c1c042c000480001681130440d8042e000c40d046c0d03a1401c4c421942c64048030301d4a48254010014000491031100195043c00900d8050411212046a10b419240c00004074103041c46410407002542610802480c4815591304542041c0052408003a0036070b5440501080c0102c8594120007140543c0040c1440e85c080054002f80c1128440410000343c81d07a800c1c003070a2501841407030141c49002c00015443e4411400c40e0304a40d4408051402d007402e101c100090b0000c07042c0500d62510062090036010f503100d40d03054811480c1020400440ea40b01d18240000101d943d80c0c41d22043d106000420119400b51f04403150705d2000011049550740fa4800031381c03102c000c85158000c2c014040740228002100049 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 894809172 1250 894807922 894807961
    0x10020d06031a0709080313060f0e03011d100e0d08070207031e110a0b040b0c030f0d050717040b040b0c0c0d0818010603021516050d050406112b0201020f03 68
    0x403070914841c1c54040da1981c1f840b84082c55501c01c180103204126913803040d2904040c1400a1514801d11014440040d080d00d4ac1208144040c1c280000c1c9011414020400c0b0743c0c200300c400300180000c80d402e01f41580c60701a0b00101e281030001c89800120b2162091050001031540261101c5c1303080421400f0200122007150b00b1070310030645241e800086d1801d03d50220480300480310702c61505081c064481820303040002450f80700d03c003c0c4410414008200d010f05144180e44000140510706150000e22420007080c2848110180d401480040740700b500d46a640140c20500000329a01c1b011508000c500c900c040040d21806080b0140c0c00c15a800140b050180c035001c002c0034001c22031000110308a49107803200030340c40703580d01d568180610302d440c028182c47c8a40081c50351003140152901c030300300064482c24100044000500b0300045030008200b140710041c07040109031030000b500da10464040c603469001001811040c4540165100b501104c1407401310900d599240d007025003807645140558003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 894810422 1250 894809172 894809177
    0x306011421160e0a17010212090a0201030501060c11090c120403020601050933030a20040c140a120f0606112b180e010b0703170910020d06031a07 64
    0x2144082c010710520342c3c11a4918010104101503190040803e04007001e0340c3c035418503540030f201328020022011440c504c00e84002d00a08000340340c610004040300d2050f0082c9003400061807100c40810803000b04041d441d0420780b1490425260030300c0440c424003c0006d03401103442d11104100c2055404941541280c030182d44520300c0d07881d52804541c90510102c1c03c190b011600e8032610b620030b00800c0c05441064405400e80341d6100c4a80c0383e045552038811184107900d08004110300c11740c10b040c451031401091b00d15004030700c141200c02200c132500c01d603410784d800c101c7d128203205104880e0b580f200130035510300da108021080d950400070705110380318500480385008451003d202c1011401d40148000d40708454412010060f0f001a294100001c000800140d0000000308039007850400946c060500c41804d941c4465040c0b400600b08144404140303d043d0f0070400740301d510178001481d844104510306000d43c81d00c4d1090b024200500103640080c1040c0401e221043d080381200d01180c0c01031540e40e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 894811672 1250 894810422 894810451
    0x3010605090a090608120702150412120302180103230a0b0310090804121b0e01140f030706200105010306061703030123120d02011d0609030306011421 66
    0x243c00d1242103482c42d216130030303854000035800a40450301030010040144002c04074a80d514012400e100c00e078104c0d800c244001100c0702d11400c00d010412034410481c0d481446c1c1980f4060722540407a000140c500301150526071500400980c01280c1d00d43d011608000502180a501c0d080c0c007040c01034078600c11851701a001c0c007210001107408602540c1100b40d0404001440c1901c0c081d651a83c0e01c1e21100d003034a1044503191039004105c00c0f00003500040010413402d54455040203e0b101c403500c5401201d03071188100349030044264401003140001c80c0c449082080300c026500407410100c40140f05040d06a5207010b0020003000000d6018100380e0b0049600c9204001122030080e50781d00c800c0c0501c1c160032002c08401900351a81900310008100701420b411900728032808a81d1501c9140c107050320150351103030007511608041146030f0010350500c0008111500740200455128400580381904100c110040e112184150300c0440300c041e50030318104010740d108940310f00c0384003100395085103105060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 894812922 1250 894811672 894811679
    0x10b100e090402061303061802120a210912050f0105010501110c060a0507020d0b04110103060b031807030b01060801030b061503160e120309030f060c03220803010605090a 75
    0x351590030801402900e10010703500e5503000c1114035040041d4a820100c0340301d8000c0005007041c040d01d03128000102c11a0f200e4007503031040001d0300c0e03078079412724900e0750001440da0040361000c44001c02d81c0300526080c00301e2041c03548085503948074540042040402024504007044000a0f00100102c00300d070082007240d13210f03001124403451541d000c15840d032005044081c40e26190740205002c480905040b407600f18940d01043c02000c1e00001942c000d860f070010041801501c3e44c025016000901c1c041040900b0a030340c115850101825004550345d0746001d0703030b041c4c81d002c02c8030b90041c580280c1c0c1c4072003640e0340b8040105869000d00040b01d1101846021070540d041c082d0700202c803005050883c5040d650703180528070032580c04480d1001042100b50f070140c0542c03641880303102ca1390564006036950b40085c4080c145459a140c0f65500d079540250104048000c6078015607421a6002c0d05c0c00c5a1308040d0110000000c1c1001e030050001d40c000000007441e59001401807482c10802c0e944c02d0700700d80c1d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 894814172 1250 894812922 894812927
    0x14070e010e06150a0f0e040501170f030a020d210203090f0d050a0f0305100b04081506030d02060612010f05072d080a020c070806070e12060903040501110c040509010b10 74
    0x100f99004041a14244286081d0902039000c0a001540c0ea02c2c001c1e80c0c40d40904002000c4d645d01703074000000808c41006110700c0c1d620602146410200700b8008600d098018140295a141104401c1041101039180b015208414260400e10020344280c29902d80c140000e0660310383c824041002c0d40741c40740d03407142c07142140108140c1d90369081585034003003d04c01c4180c0c00c2d405820010110000728078010710101c1d0014110300038101404c0b001009289070504800300000e128400340513603109174005842c014000d0f07400940c00390700460130346a012840c480007a00710701410074890040581e5040030304005900d1b81c07104100001e44642401c158550440d020002246400b0645e14400145440c000512400250700101800410301c1c3c2103850565940c18190300b0030708242c60010004055800c0010340b07241c042c3c0050000c5ca03580001d04542e0400580742c0340d80b4403482c03145c2814003403064803110410005022194003c1c8001d0010300c800c0c0f0382801e2490007854002c0e80640b00390303071141c0e030113118070b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 894815422 1250 894814172 894814189
    0xe040803060918060a0b062a070f0506040317070507061706010f0f05030603030c0102180406051009030f210c0309060905031f020717041a18010c14070e010e06 70
    0x40d030a0302404c0c10f6161000f81502070704000740142c1d0454010030084803005108448089100b0701405402907400743d550b24a410b0100c80d0b07100351003101e0004020311903650f4100441c3c088070340c801030300c0f84000c4e03201d41c1426041c01600740161040c000e24400040d81c50308510348100d2880415101c10031030756800019180342500240090000300c0d0090301500701d80c0584019608850010112401d14005d4050942640d00c04540384900c0b15021240ea80b0a003002d0041c1400b4003c103c40500040003c2d20004204840a2002070900003100f120300c0c0902c000c3c1811414050801458100700d048600340c00740c0701c0017216504800003045c2c40e100103100c501c501c51813025104002e01400441d0f007403645128194420164416109600300582000030307201c008182d004200c0f80803903d80781d0346014180010103d405c21078800c040003c00441c10700c0c128101c142c4c4142d201c00d003800c400720704445c00d00580d180010b5814034800d110300100030440862107200e1504a62401965980907030341c03001801000b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 894816672 1250 894815422 894815461
    0x406092a090b0403061505030d080c03130c090c020d2a05070b04181401050f0409050c04050901020d0b0d02061615060b12150f0f0a0e0408030609 64
    0x111018400c24400150980030250169464000c0c6915111044107590b9401a4000c0310b01603078549140340d0380b4408241c90402010220050325540030950005808808001c00601d840b07400000082c0b40c802c5134144104405030401d60401c5103588801d2814001c140d400070000251003481281c0440a1044140048402c180c03c01255078031040d881c9104101c000ca00b08803080d00540c4004290000c0b4400900700500c4143d07101c440520090519000322404004c62040013034100c4014001c0d5124562207441c1024185c1d000140d5619038100b650030300030031060165206040c6024420403031f105401a00a120303092104000001600003000001429004029044013041c40341c009071030390700901c4805541c042c0625810541945801401301c44854000f00d02500c0c003c030f10036807400d054200e05540a0105070b4540911650440010341200d0100025807041d940f03441c03554450744452001c44010401690444100d040074504280e55810071140d4600400c800070010381c50a1469103040b828 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 894817922 1250 894816672 894816701
    0x30115030809100309060f090c09022701021c09090e0703020a0308070516030c06140901090b0901210504290f07030b0303070b1b04061e021218040609 66
    0x2c014103142071100300780c42a2485420b141c0e0b42c1a140c0c01040d150b010301c0a000300c049000180d20101460070840315006070b000340c2e6804d807050080705030035142d03004d030310000c04690140c0fa04102e20100040740740902d1180302003600620f040c9030680d07083e00007038003105842030450180451004007500660b81d044510000e944849001810800310705a4401405564020400d80e21600e01255500d05d28102c25441150501007840c4100441a070144030b01d0003505a0300f52282c90310000f500020a00070160080c994070b000c1c0001c10207040d0703024428680b08018110190800010915180b50051030216000e56201400c05074551542e442c3c105a05a000700b48113410b00252208801903400f11030041800c400d05650340c0003035004c1c2d0f0702080a002e101d071060019400a280c19248224420382441070b10400640900050011176000392064100308020008a2420840c50790102d2900e904498200c02d06071000a50b5022080c54070303a0b1b044c82c0302d0f0954040c400d1550340c0190070100e510304200c2c41c42 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 894819172 1250 894817922 894817927
    0x8090a0309030b041703070e0f0402030f06090a02040f0b0403120e0907030e011d0a1103011a0d1b17061027060b22050306060d120302160803060301150308 68
    0x56043c80707801ea0001d0003682e240740c0d18401540180603a074800e480c2207011a1aa0710b20404a1501a10040011006540942c15810055078010068401074902e9100b1031b000000500c1030790456041d60010706d070b00c00c00d0011842c0e542c6601c00595210b4001500c045940341e0891002d64002c2e006003c800c1c0740640311210650742c610044000b01080a1003071a55500c0781c40040ca20000a600b9120301000781c40034145100b07443c40c00c1400c9440c03d04405000741d041440980803075407214440e00c410300c804c0d25030b240b40a00c50324013200d401420030b1844800c0300030800045044421009600c00340003e5604494580c3c480c0212079a8000c02480707002c1e003c01c1c2c4541d8508995858220884940110820119070140c8a07002c29103e40c0040e03800c142440c0b907940710740088401a0900794011f01080c1c014101d641400e4021444540a800002e801107025481c4001005d219030704858001d500d00c9041c0d082e144142c500509140d10a07215140309609240c86c244001a0310010300c070032698000d04151 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 894820422 1250 894819172 894819179
    0x715021e010b040c090e18030406260117060121060b01120c0e0406060302070b0609101d0106030501060201051e060a0308070b0105010f0c08031b2808090a0309 70
    0x2001200040c040d61019525100809410744560144c04207061075600c0301d0058078105107080301ca8601c010310750110004e801c00b010701c07600c0c004001c54041e50203900d40741d04800c13428964202c0301403441f03030403103c0c5031110300001440030700d090f000034465a03c140c2621983e9030b0340c40b1001c1ba101600541000058030381d00a100c00580750754042000c035031041c1003a14440c5800c22143c81210181c107072660226440c040ea441c01e5141c54801c18015000a0800314280f2100d91540702c0c107240c1c01803c65024030540c4004c84d0608a0001d9014011702e03020f80c00d0f095141500b00d40350b010310300a10400c00400d04041c00800c0040c018020b09200e20f8500b042c4d5801340801c500000e1b41000c000e40040d400000c007504c04000f19845000404000780104031100480d450480010301c1c0c0c81038203408104004480300104001032a90040341c1d04180d5044a411106400d40810240c40c45071104002942d20f41e40b1405440c00c1c03a01c04206001d025a40702c0b00c1c1203942e1a4600360b1107102e00710000300007881180062 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 894821672 1250 894820422 894820453
    0x16021605010534110607030903080706061a071b0b03040b0c1e071104150315140403031b0f050703080a0204030c2418030b0a1b11071502 60
    0x1012031001c03014452841c01c0d4040d290201c2c445242140214844041a100f800c0c0400d00c40e002d00904010b490b00741c81c042080e00c0c0200915064040101860b100107402400d220058015078060312a442c0c20000d083c0c11800c2c0c20007181c0c807510044540d0070f012030b04040e02d107074902d5840e412100d00d2039001c1d29640e00c036070fa2003a2010000b0166a1901d00600c03d0500c2c00d0140242021110881c11885503220b0550801100d14100008080d00c242d01b40408280414928080c0a08403680003181c807180511b01110076010308a1421303800b440c06030481c01c0005143c0d05d508102e07540c03800022203500104690600b1621101c18000c01e00c04514100100780010348503070b07141d40d400311900c0401030400b40c9035511b00d5260070566100c4d500645200c0840007507040d141d420091640107504001e100039034032840b0b041407002c4030710010f403040e0701c4680051901038040c2c0000703108291070703003294a224030641b0018101e04413681c1c102c0094401c118012480710358001005003105201d0300204a07aa4408203c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 894822922 1250 894821672 894821677
    0x90114040204150806090a1401060f0303120902030109060504021e06160f02060a030e0d0305101809150f0605010e030316032d0f0203070c05060306010e0315160216050105 75
    0x50046052207002503800001d2003803600861445003d04a07843e12070a0001310400c052303a0108060b41b500d40100441443d01060303a08990b85070800c024070100484090004000c48140a9015403d1001850810206600180c0f10300c0c42152009150300c0324401c5240181c41c402012034214004100103040c01031484864501e00e8495081c071480d261859001c61120b4011802c00000700b61070310400349400300107200c14404107440785010409440c2256a87c0985c0d41c0030311800c040000f01c1d914610089400b90000c01c080e582010044070030b100e205440c3d6000f4412185903654083c03900c10040341a46c440c506010704464000c000714140384000250010500d0150b00840034030600b203c2d0440c40700140c1c0e80c1c81d01ca42c0011500442040c200690240001e03a2400c5a801150810007202c00016110314421090b038506880098032070340c6110051b10405590803d450303040c85040741c04804c1d6214502c1ca640318000248410300399441c0244282c0c0d850880c00200619034201040600040d48200702 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 894824172 1250 894822922 894822941
    0x2070e10080304090209091e01030f06021209161d0c1b0a050109061404030503150105040503120309011109030601060c1b080d0915120209040207140303010e090114040204 75
    0x21240000d580764941032840d40950702c02944140c0101d050030040c9881c01c095030b0300c880701e07a01030042120f8008500c0b50b0341e0700501004105030070b00c00c0540d0a002d903a90507148801030105411140c0c1c204000403d0b0754070000c01c50544061080000440c140950340030501c0000d0360040009607a80f40e000c1a0100b40e00545094003000210681410010904101161040c1c0c00f90000045410103401d0460581e507009040d00d440505940a2000095000c1e044903400310200d045050300f8001100125650b21840c2e0000b40d0612500d049003540d484d41e2001075019002e907400030402c0310f81c601c032002c00501841c0000340c0d05401c41401042424029000c0c58000d500c51401d44003044518510000600081d8001c0c4400307900110303052001e00c1e000740000c0060101d10611804100f02690002c00c280100841d00d400e00340c001c40c403550940c1310303501902c805991081c0070313810121b4500241a90ba801c240329400131058408c010501888040c030403518880f07031802a944040e5120b80030f01002c2c204040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 894825422 1250 894824172 894824191
    0x3120e01180620040b0408060c040510030b040905100227010c12030b0616121d0d0203192a05030304030f21020714030115051c05010510050111060702070e 68
    0x10040f81000f40d8800400c0a0140384101540b00c43c180b58030103282c070000600c1011600710800003400595035042cae6030070360002c031454085114410300002c03a016056007040181184210f004504d0085065000752505000c8891000700d09210b802084035400123904030140411282d0722814041804008400507106c01400e0100f500810b881c0841ca131644001d0300003226400132843c04040000c56204c064002e8a540340510040000136034089640006040842c45500d48099040441d1400c2c81001220400c41c21146081100743c24040300344002030480c403142e1540c240c100380c0480010107014040c0c82000e8003d600705800c5035141941c4080c59001551009071050381001c8804003188088901c0c403035540602520b520700f801c0c0504948200b60341a110343d04003110206d25440003c08441191002c503840c107510fa480e14a1413a2110881300081c0c40c075400c11082103c40c2490b40281030440e542a6220b5801040f90540c10351500d4056455000582020604000098a46c0b0240d40c0080000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 894826672 1250 894825422 894825461
    0x3083703051b071a09011e0e071806060e091006200d020a03020705120a02090406020f07050c0f010801061b02010908250b0a090902030c0706060303120e011806 70
    0x600606819800a140882d1014008200b080350000c0035074801e030b0001c6020000344098011a101c7e0720002150120901040340d640607080c8503004c0c10091140207021060000d2103e4154170040c1d0041c0c8260300840001c40d825101c40011402c100e00454419850190000341701401e1001c2161086600c2842150302100e074502d031f0001c2c45040c000e81c0f034120389c55002010204000c1c07501a04048540d4015482010b8554100c401604041000c404c01681100c402c00c0030760702d52070906d0081c0500a01c011403810003091190401000103417000610f4021103d48190940c503800445d0740d08001d00031940041c0501400e11450080000d40002c4903105051845080f0703164804140b41c01e601005060f68015810500181200b82d030940c40c0240411345512071a0404990026005030058410504041d80c0000000e00d1203080000b0b940c50681d000343c09114095807402d008141600c0f5002d40074015107460403844031050144160280006c4050145c0744144882d2900c0d0300a08102c541c3c00520840c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 894827922 1250 894826672 894826711
    0x60c04080d270b03040b0702010b06040b07020d0c1205070e0403050d150308030901060609140306160c12030504030e0901271509051f06080f0405160308370305 70
    0x12a5590041c0c603d0342809626032629042854504002038100000d69140c0541501103896072421038080d5021583c00aa648802d4804a298000c03200c0d0042d0a030301d02140080b881d030012481c00400d0303d004004071103001d5240c03481c2004a50055800802080301080b50b4084210990001881200c0b604950700b449a560707100e50200c0d600031038005605941d80d103400e0244503040401c00f00a0b04070150700112403c5040040b9640b000702910074680c103028408040c1c802880358030103501d0141d200c01234140c1094a00d80240140c0000d98045001c82d07a10142d0308100c3c02c006900030704884c01c81503000708854080040c0340054008001c280e407240c0d03e590a415042101001140060140000c00112407524010030000c1d952648145840c1c011001010058940d0001d207064201720b10901c01c01c1c80d074660740340192a002c2d44003110064800351030400410300c152200a041b000307284a03a0184e40e0100c072000c3c404107800810070552401c1003c0400a0840e200c0d078007403a400000c0740740a0550264 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 894829172 1250 894827922 894827987
    0x1021c02041716090b030712050105070e0f09070f18030c050a08070303170705091207090605120a0b04030203070b010e0402010201110c0613020a05060a0e03060c04080d 74
    0x24595110480a400140070001c00321003411070400c28107000c010303002209002d40000700f481080d00c10820003588520700b04c007556038103008280051021000c0414004810f02d0018040e04080f90440d01081031007010310a10306003920b506010440c001c1c41202581c0e1204c0c0196546020180c400041158000202c0000c0c540e5492881c00355028000d83d07640ca910304402c1008100160b0001540e40e04403038001c200180d00120480441005241122241d5660030070440c0c4078012500301552000d801d80400840400116009007612841c4009100064480050165a810716040389031503038041c2c1072a20106010303002d841d411910a00c15249441d100341c881c182c0855084c0c01410b95400e200302408110740c1c0902c1407402040d0031090050621200c000700d10744a02000b8280c070b01005c00483c1c450210364035a445100941001450a5100c0c050018018404111000e1840c001e110300c401207104041c00c0c0707040d00e045420500c014a104904d40200321401c14035034406040d24408039102014001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 894830422 1250 894829172 894829207
    0xc1f06031203093306120f060506030307021305060906011e030902040906020a02060906061804030819020c0304050f06160813121a0a060e2e09202701020102 69
    0x2d1130040c2c0a8000d59046000030100c9540364003181d1441451101c002c0011510400c04a81c5600182c00080e0703540c680f40840e0861082c3c88000750302148240c0103140d10b11150b4441800b03884180c99410701ca681d14030042d641580300c0c0d44e003003a0006030301c1828001340340b00e030b0009801c9902c082c0c00420092041e644103000e0f038000361004030140e00075408000641e2030400080381d2100040300c090742c50702000048030765042c0700580094204801c0d034000403003d0104410381c0c0480d0700003041c1150b41d20a80d440550b01c1c1d800600606c1e01c40d0300c9043c110109450158150b486142281d41200e0f8980c089640d4100241e004010741c03800e904001e0302c002500e41c99040804c010b03a028040344003a0103100881d0012500c4024915643c251928106004d901008015681d02c485007134548003042d14007000701c1c1400701e51000d901c3c800307628410000c581904203030003001c0d07001b420010710181c000c01d03402170310b5890084040d866202c0c088019084042910b0b4114a028100b060000504e4800d18103407402086 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 894831672 1250 894830422 894830483
    0x30e10231e0306190e04080a03020c07031121070e0619120b0f040c0501030c05090904121701060503071206150e0a08030403080d090201140c1f0603120309 68
    0x8410402103007060101c0743d024900d180c850080c050300300b40c0c0b190f003070b010082c1007c3d00c003071004220980550b000394101c1e110303441c040c01240d40c100d54a2074900e00e1000301d0710a9500a00c80f011020181c8020307029800c0028000c44041c2401c01c0c02d003040c014030000002c0629601589044c0004d41044510404034050081100003007411900c13820b14406503107024090050918080c4208000716900500520543d9000d00e0041040d50480800f01c960f40101c48240364020083c4040c0410404888024582d0b548552034a0741e0311200f44185d40e200b03030001d10031200410410400175050901c50540740030090046031000400680310031b0b20b03160362007100c8048808504041070203620b07841c0c0b01d42c4c0c41d0001d0440c58011880c0c141150b40c0e54107207004122500401d29241e2800070216800b8803144c5601081e41580f40b80c4030120b1042c2c048c1d0310503101030726401707603c81e1101540a1042901910068a0304946200544c403030ba194120001e040614064943e401180c1c5102c08000d4152540c102c070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 894832922 1250 894831672 894831727
    0x327170a092103050d0f02130b0d1103100b030402061b0105070e09060d0f0609060207030512160f0507050708030a0e0102010f020a0804141018030e1023 67
    0x5140c10040c0e210561690100a02c400c0482d4070041070002c0d40c42030440380c03460108200410030082008540001e4040e21010800e440410403004c034504c4400406041412552101401140c060054420445c0b006840c0b140644d00b402c14180509030296000710b07009803010744150314000131114407402c40c20f00100420303810b9441d041407003180d03580178805210942040312070038070b107080420018400b0410080000d02192040d02804144003660780700e03641c40d0340c20071000e544e10340c885e140040140d4000e08400400e160003d020454100600c20141002d1007240c0724500c045111800694031a00540d1040319540714908001c03070121010f10207030807907160546a500f403454080740068203496580c419081c8961042c0b0109214550002c01203030081d80100b08020740d0300b0398008250402028a043c400a641040d509844a4441681d001201400303940d501c62100340c0e400c200308402c07401280540c0054030380020f00310003c80b2099105e503018038040f2200c1c5854002c4141c0d9904103460500c0560303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 894834172 1250 894832922 894832937
    0x1060e06030d02012a05120906010317031e090c042406111c11061306110c0a0b07020c1c11030304030510050703090b040507050406060327170a 63
    0xc090074200103400e0003152a000905c0388160306190395880c00050106120204914046845124001d2040340c100e41401e00c26090240f42030f090329507032002c00f1f1104840303403500c40c68000e500c0790168080c1c9020b56444085ca0751180d45403503041620400c00340200540c1c4c02440755800a0341e4031032040555440a807044407a20040e82ea401d220034140961040c0144040103031f900c44607203c00b05500717501518120ba0701e6000c85040004950781c1000420543d8a80316120901022551500108072958802c02c0c0c10700016058a884000e1402020303801c003139a50010390404001801c2040f901d0b40402c680c8111001c41d00e1240025441c01100d80e10b42882c0e9444a100c1024440c80314055854440141c004510305881c40d5580341c1e030790f99030395203036480d1568850210f00310b039100350010016240c00ca041c1413a036042c00d0528544840306446a94465450719000003212802401043c0803074902890901655804820a1080c4485880100c64aa03010840081c4002d54807000d41941d0341d40f540c5414 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 894835422 1250 894834172 894834181
    0xc0602010e0c0312160c060806030d0507262a070501030519020c031308010e0d141b1c020d080c0f0403080d06081c0810050a0302060f0c01060e 63
    0x30300712050401200e0a64000791a20940c90f24001184456040150306040d40c920a5010740d25001890103402080c400d03241400050031a4000a00341c0201021001c1e225181e21106003a14180300d4540014140132844490312020740044801c841400340e0202c14502d85601445046050603102e40c2c006924003080560580e000410008100a000203003020400d500301440a0b45150428100202c1c14a4001580220800382401a90615424084100c109503141c0250358060103211089100c107100c0e40c14121001c07486950145c548d842143d90131443d103080341005400c004010b071281c044a00c03414002d541e0380e01e843d103000614a82294080d226140200b60002c3c00c032500600401300c09002400100241c50b0702108850890341e11610300da0781c882c0da004212000d862164011452401810103441560b65030440741c4202e0102581d60046613a2f40800b121500c800a000e440d400c1780380c8103000c0c801400c01c40300030300091a0805c4850b0504e00074452140c04d450301e98001103c2050402d0073701 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 894836672 1250 894835422 894835427
    0x1110a08060f0105030115020f1605032b030e070b28050403050d08070e15040617040f020d08130807050103060b0715181415090d080109051806040c06 66
    0x1030700320008941100d0520702c00c0000074024081806182c40741014000c100f4401c81c000c10030411503d03600c030151a2000c8506882001c403007010302c6018003070f020b6146a071154075a24404003185090b0440500c02030a0340480880050640513094403c80c469140d002c50321130350703101c040e140031076160742c2001101c07014515078605400300d0b02c0810f046c003c0c1808140005140416609081c250520300030a26a80d45032048601c5640800704d00d800c1101c00002d1080b205101000344103035a9580c0324a8034800c42c800201424101c1180d014104c0d04000c00010014500000b00444281c001c3c0c0025091104544a00805502a034440d450316880000c2c10411342d60540154401411117051031420201c203a110301d40d035050141c1b8649440c503580c4100344440c0001101c0d41c4801a0000030800701824201440d541da00300b9642d031702200c1c405590019600340c0002500c290f8010065544403050391810342864081c2c5030140448591450030820317401103c0040020714840ca001c1c21690203071314640f1201 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 894837922 1250 894836672 894836687
    0x609050f150109060503190b040203240a061e0509120708100507170606041a3c0a030603080c0a12140901110c03061e060105120a0b0301060801110a 65
    0x9180c10703c605490200095604503080e213510841040741c0e140300d902017405540003040b401d014036600c02d00c04414004684580004030040d403440d0040907044a105001704039801c40d00d4030a010000e0b40003000d5a080410348180072241c1c1d8840c3c1080c0d81886c2070b8100045015400903040111540800410850000c042120b0100c18a006408026909018800401b2000341032400c410000c0c011002c12803c0e02c83c44221401450000c0100d41c4242021000446a900912480801c03004c444841d409a030a0001070600303070a0f1502400c00d485184183c0915140c000420f0071045c0b581d03c407000004503603004003d00c41c0400c0c40d000303094210b0103490000703065014070304904104000d4801c25201c48400ca0122241440d003420710128010300c0340c410b02c2ca8100c1e000d00141e054041c18050000800200c1455404001c03d01718032400b690702c5500440d0240102c803154120b1302503000c0468030030031455008071028072018001007012501e0b400000c1c20340319075080341220309000290005030301d41d0100c031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 894839172 1250 894837922 894837961
    0x90b0604022703160303350a1a0901060c021f02060403180b030a0c0f14090f2101090209180303160e0904080904150e0c03060d0b01060203042310050306040609050f 72
    0x4e91092110b030b445003010f01c125008012307544865079201c0c180c5951800c091140e000403130082c0540306640c0c40e400c0041000404c00001c0307011300501fa400041c1d0071011010740301c0f60f500300d80c002c20035544c0c2c80e1012191207882c8620000811850503001c0313641842540298424071442d04046244550050024442e0090300006010003221422408940c09014100c1e0401d000c2110600c800100c4a00041e14140054000d80c2500c00c0d4002d030305d02911019005071116900071506007a05c1d507a407040700408030070800e001c00f20b41c0d00200700141e40200c04e0320184c9101801c3d4586a5040d45d10440410a03400080d1030680d051040814000c00034540781c028001d5201600e51001c6a45241c40f860000680e0040c042c0d412004010000030039503201c901d00aa040da410a4192006581d0703608040d44070381c010f015081c4603081344200045100c400701260b00c01018040e01c440010a19032200f120a0307040509080e5015464403000204d243c02400303464016840c102e88103e10741400203040b40c51505d80e24 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 894840422 1250 894839172 894839237
    0x204111c0b1017040303020c01020c030d0c0206100f120804030b0403020a061d120c0c130c020c060c0a12120204030302061611060a020d0b090901090b0604022703160303 74
    0x81200458840040f03890350459490300740540c6640d03600280601a004461000100d0706c0f02084d0094444426081404035100940075100f40da03e5601503150140e101d4010301c6c0c1c880260081c204120a43e91081c010040e02800b2080d0030300d9103070760b26000201001d8506a0040e072010403a00144103051084810644a03640c01405420100f00d0342c64030380b0035075030f406680c0700c201140a4520442c00c0c00070100030f84004116012000c20704140c1401000f81c1188940180b190704492051402c2c1a803ca40e0480300d214014004060b41f176607484022000c420801e02040140040000c50031030074005400a907209401400d40e51070990030020011440c024500204000c040c0020020300c0c0200703c49800001c0a4005a5600d0700c201c518006040455a03840d00074844004000d403544043d0b0100584034450b140c60b8150703468000410050b40140d007201642100200707140c00c0302e981c0c001401d502b0040043d054400e282000b841c09a030020040d0720540115605042000800c44001c050400c0c0c0c00440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 894841672 1250 894840422 894840437
    0x15050916050d031805120618031e091909230610080907081b01020c010201060510210e060613181118010b0c150903070204111c0b10 58
    0x40001030700d9030312822028083c044c00c800c2c041ca10500d240c41c144060035014000910200803243c0b5250754501c1120b922504405902000c010080044100e4103003501c440e0714181c1c45c41400e284e01c51207a000c402095440840005241351400007031002500411f0202030026665030540c1030882c1400340002d90860b0340c00000e0810519a03966802400e800ea042d00c2c02c4100c03543c44ca003c1904d080b81c103030441c1d441c621070b4504150141e0680620007810707041c00e07400c0e18004020400160f098030030a0203410f9014a103503006c494694442c542103100c403180c1040407117002001d0101c0d8811610854914490754011800300312042c10102000d042440b0803100c01c000b403150f001c2d01c0300c410100700c1000519081c4440d880030b1981e0f840b00300700814051904c101440550b995030b0310316459480305241850303138041c8144d040710720790003124060321500c2c1c858082c51901a0b65820000101400c0d030f00380354509010301101c5c080d449401c00301424a40d1480000544030741c50001c100d924034500e401d080410148 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 894842922 1250 894841672 894841679
    0x2031204050f0c03280c0b0d06030c1d01090e0a0c0306090605221502071407140a2402030f040e010e160e010c0303180c1d0112030e0102070315050916 66
    0xc084407103500c80c5c0f0003101c500d111495460306c1440b4118940c0005454000841c43c0740d5642c4d01e80e40700038110391180318103401059940c080340c0c034404100c5252620210080c1c004000311840358010b4fe00c00d840b5501500d410080c951f56200b5108015042a10001d550300800010002c840c0714840d0810f54261900c0c0440113410b00b003a00c0390b040041700600c03110403829000d0070000603405035041550700500010302001020b0380340741c0d0303461f041c4190380d9540300449481110703041001c0d034441075401c0705400015180040081c41050b084015512045100c2002900c2d0329141d0000034102501c0c41030646581545005034011090300007500da040640c0c040c414207105260000550001c1410a080481505145040a07002014079040a00048023868566420045840c01d1001507402451128050b10700c0800e0001d1080c1d000d018a40c104d07428205040040b9000d80640d440d98901481107401e59500c81c0d491444003070b1502c070170800b0240c6030b00610444541c01e001650415000c0c030000c1030391614 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 894844172 1250 894842922 894842953
    0x908190503071205091c050c151b070b0304083016031401080106061106060d02280e0103030219030e0f03030409090b07080f070905010f02031204050f0c03 68
    0x1600300080c4965014038800041c03901030344c03e03103004c0c0c1c0005106d01030718081c58200800800d0311180480d01c074001e0031140c000328940488103072903087c8000c2e007840c10702c40c1803403400100540c008034450840c410010f0008071041d14000070342c0f01c0d80c81007482c00c0d290100c83c646140100d03100c02d2078030010020134a242030b1840003900d1055002c00940c142422202c0140000d4005020358440e141540661900114002c48150009401ca41496a0310120a00c4040150780c071405c06482255000340c55205210141c40c01000c40440031142060908c0403440c1504000c41c402040da002c600d00c0a041c800400915405010800325400c3c3d541c0382009403c080d582c02000ca000740c0030940c2c0b18010000f2440b0880d00c003001030b207015111082d401c1141580030b003000100100c0c00c44a02c40000d00c400d0014040b1009c10043c0323405111a0b880711426181403000640729201c2603101c400440c4401d03c102c1d2081c44403000158051ba0084010f0170344040d070035048509200f22640100d00951004000b07040b00744 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 894845422 1250 894844172 894844177
    0x715020703020940020a08010606091415031b04140a1e091a030a0501090606050d110114121f090c0503040609060603081224010806040b19060908190503 67
    0x181c1951002c4c400e011000e982500c42c010400382d000660b819000c0f40300da10551141d03090701c84035101c0c007200c150b44034142d41c005012084d11580010341040410005610000030b907401501064810010720750312402c5541e1900941d1100944017200c42216210b418000c00700d10203041501203c3c00003258482a082030002c00d445203098150344d1b0410405843d0b0b061042c818201720040a4541c1c500042c01c000f4043c142f0340005a8103280b60810029203891300c8000308001682c0020362100f210a100300640b60096a022117030b81d006010010400c849040301c105511809440182c4440f048107200280c403011810b801c910b07011881d026680300c1a82c4c00406070f80d03204d03900c40c1d0045103035030320b6107030400c080d0400350301c01014000c004c00c140c00307003504400c455480303401c1c80281005070b00600e00311f0300d607a10ba8003046180401c001030085615418281c002034140f04000d0906502c0b10765020551038403180c950b001c0e0340015000300d810700080e44103010b04812454101c40d08803010041d82c032141c0e200c1c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 894846672 1250 894845422 894845491
    0x602040906172a1003020306040f09030804060f0207150c121808090d1a07030c080c0d0e0a02090705070204150b040506030a0f0203100312141b07150207030209 70
    0x1042ca0041840c41c0301086074001c494600e001c0c003003c1306210b405502402030b400984d00c45200b5810086c0e5402061820f04c180100c1d0390300743c0d6848500340c0759900c650000344900c0f40d145890070380070050740001c04c01410600381003100d01c000000750414072800091050b0100a080d0000c1ca042100c042d04aa150b986500c4045170444000da03030303c20000d00001c2d4541c0c00a0001488201007203a10500d03107582d0100c0c1841002d4a8609100790086d00700215100c0d00201c8051080500134041600c0d424a030f80d00c100b000b020b002c0100c0b00580d680d0780008200b8182242d001001403400a90b6508500700f40c0a0a480200f5018410700518100042d01102c2d00603401954012800400010155000ca800512100c0b90301c450071941c0b81800b810704c1040032042d001c00d8500d000c22480e901c054900c40c5480000082e80c07008994206000540300c0c80b20f54071201481c60051040241c0416004500402d040484a10b60020007000d8594030500140040050541042450850442030303c02c017680c46c402d107103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 894847922 1250 894846672 894846703
    0x3051807050f0f0301060806040c08030309030d0c050c0f06060109080c032104030c0f060f050a08070302090307030b0f04020a150507030e0d08030420030c0102190c12060204090617 79
    0xa121040400c044030784a180c05940b646c2441d4002408080c081110b5010710301520103502c030151108109070356440300f9503002101d9841004405620300050b0301c40d03a4924034500d03180b407408940e40c0c80146001c0301e024580d03e80b600f05606000e501d6801c501c01000600c0c86601400001e901b140010b500c40c060128449104108440d11100281c4043c01301c80145900c103507800d100c41e0b103490441039050034600882d00890030384460440715900403819903480440c0307656261a99a00d4110440c0650000b194050309031040840120024100c1030480d403241c588102d02280b00e280c140108081303a160359200007054418110142500c0c1e6120301240c43e50ba41500300950303002d0f480400b2504500b400300c400f4200310000300910040029031508005840f00b020030205040030114100f40c1c8800c040441a80580d0215040c0e00545480d10100382609001720070f1501ca03165216590300c0003030b00c00d11048901941c0000c040c89021030070301c21980070340782c100c0f029148008920500e5503202d21905071a0203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 894849172 1250 894847922 894847939
    0x15020604080702011115190612021014180310020a17061807050310060206010f120c050307080f0f031206040509251706090d0f05070609120305180705 66
    0xa6901503005e910032206201d00322410903802c00009400305c0360076907005100c44850304100d41000728a00989003030740d4015603451503a03079a540c00c00c40100d9100702860b0902c5454600b51441c1040c08003c0c21202071900c440710400509401003604012500701840813280c418845034085541c05400d1410b43d40800c401d000507a01c6120004400c0a0014035049a41c894003040240c107661007000f941c0a15424501c0c035041c55111901613807200d000740502d0501d091003c004010544401c03c88040c050700407140d00c44c2190b02c0e000460f042a0041d00101480e80c003810100da01c41d441008100750210000f0003960901426010a1414040141046100b08c0e210408903410007014031523201c8c900e44174100c41904003801c0100c2d030029112481500c0d508031440404141c4c040f03022078114450881c10700074000e01d9404040503502d400b01c0c0c1401008016081c0b00c0c8000203012442540c02c0c09008040307480c080340400350005d0648500410040c41014485540400104001001403c0d994102e8500c2d0303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 894850422 1250 894849172 894849187
    0x2e0e0109050d1a070207080a0c06031d060a02071401050702071e060c03050c0c0a03031101060e010317250503120702010c0e01081b04031a0702030a080105190b19091502060408 77
    0x20301d072201b56004555103008194460003003241003a019400c4400585041c000c07031311400515204800c8280a021031600700030000703800c00c1999801000500e20809025400760500081c00e13085802c12111000540c0c041081480700046420b509602200c5c0078500724489401d0040c002e022540303140b0003d0a1040c00b040d1a1036914040c4403e00103810007400c0501c0450756801d005100c040d035156050071035460210080344014012001c5c5060382e80102e2032100c2060301300b0590700580e000000c0f08814803071a00c00e002c49203230708840411507240100010741e180c400708603200f1a4094003a111105580c584140440030541200d0301042c03415003400c000c110f56071842201188034100090180d20b00c1c80001c0c001c402c000052012002c207a0341c100d50f0324010741e50403d0070303a920710a0075170260206092034010481c4e4a040031200ea0100d116159001c40c00f43d440040c82107030f030001d01d42001100a0903100040c4203610070004070040548800d850400c458068001c2e480d0180a440038101c850000b8154 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 894851672 1250 894850422 894850427
    0x3040303020c03160201030c0e031207080c071716180f1b02010212010801290a03170703142b0603080c0f1510052e0e0109050d1a07 58
    0x6400203502c2809603590703070b030307105180304c2d0802c07003200040b0b000c01d1414651441c500d00c1401180303800c1c0c0000d002405550324003080300c5059001444200da0005041000c4800c10409205100060102412200368040c07400c4c10076092814118600406d840034032400c2080d07040010440c030403481c1c0d074080010301d01450214800034000d0071403070a0744442070741448820554154000c00403072907030b80b0003004203903200c4111070300380c075401041c030803103c5403484010100d490a04008000350310000c0000641c4d1b5981c0d40c1daa10b11840c403580c80943c9107001302d100004d15400c072040401d1288910f0b002880d00f040255200340205124446060401c0364091a03072410300d9a501c020301946d000803041e500c611140d0300c00f60747c030342003090740401c1801504815586a5080015680106003207451510181c0c02c181c1031201400345100205800130700d0790b117400c200c200304030000354503149295100c0650118000026101c0c294590005006103d50710102c80403514140142c00c5521040c07000302a00c0e100e01808 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 894852922 1250 894851672 894851677
    0x4030f0c061b1709062d071d0f0916021f1e0204050102070506031e0a050601030b090f0423010c03020a0e120c061c050411032a01050304030302 63
    0x340441e2822804001402622111600c0c280040d554415010603d180e4182d03001c60503909164550700c204045200aa0100031090100c0c51805a4045103003100300c4084084406440e5a00450030349581085220604403201154010956650608125840119000c0d0100425034000c43c180000d0b01d021080c400e12807008508400e2480f5800a140e5140540050170359800c0700b40c0580f42040310141028282c000c2d202100c0c816005002c180f0b00d01410703c05c495000400050610b40c0c0705800240085401e0001405031144090020b1149050000502124400a4694070a1041c4d004000d030a2107050a00c80c1d1281d84400440303e05a242c0c040700e602285400300c04401c41d401c0440c1c0d0b801107503141d4003800d00c1142c55500c140c90018400c4c2805007007034044401d040c070354118010446c0d20b81051002414040304c0c000400c1c10a55509240300101d84056408a61110307014a601095240c10052403d40d920f203204020307032013454000c00002126801a18034140040880001c040c18041e505 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 894854172 1250 894852922 894852947
    0x30c0a210c09020a02060601020a080703030203102105010c0203070b010b09010e18060a0e06131104050a09050a0b040e061302010c020d0b180615040b032514061204030f 74
    0x40c9803182d4071010b00801035081404040014421400003401d107620009801d4506030304030320b210b4a0410140c0701240a548000d04210f00348400c0c00c4001900504480034200005d40701c021401c4640c03840c505a4250784a42102400b194410300c1104040340f181d540450441d900f1842c010382e00c500010040e949070b1400304032164022450381e01c0d07a00000030900100e200c5c0070b00b180c0c0d810318aa10b55485c04064032080c1c405a805c03080000785010060b405900c0b0b800b103034104178292414030b070740e13100040c036088441e4028060262301c038414071031a031480e805100c0005100325030a10141c03e0001c0042c0d03540200170114088a000803c5980035039000f540c5031004160042e024500d42d00e0315040001c04070000399440811558221242c510900000c2601030041c03500327281a0754201d1031381c020070018200d60085140c1c540904400031034240c070310404046c40500568880d00303101b4038007507009003001e1021035140e0190300c0400c03900d07020b01034407151039510942c14104005020f28801c0100c0d0010071426 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 894855422 1250 894854172 894854183
    0xd021c09091503052b030c0e040507030e07082b0e060a0504051302040314060c18182a070b01030f06090c0b04090c0215070804031103030f04060605030c0a21 69
    0x40c0740e44081c0722580d028441d00d0805c585420300050b00c4401c808492038030f42440001500b000b0100c400349400e0704001c0d013000d2107240109030341e55910307042801c12080707520032502980a409038880500c000165550380d44100d188103180305682c13007005060400b4002c043d0784500e8001078443c4025005405039005048060803000075080401d2205001b58850300003510051128070782d2400c080c00010b071030b62042881004040c1040300d00d101c01d480c0e03040306443c0d81d6846900b1342201c050300082180c00c1751040200100742002010754241c13140001c0b8503c00d0f03514040341e00700304203000728428162960460f49c0c089115100c5102a00b0a08024641200001d000321501280000c0c00d1407220054000e90710721000800c00714100711401c0c0c2c0c2d0b5140c1c060707403541844903001c000341205000d0041c50742c1c41030003404c0010105940004860442c1d00c1140c0c80444d8070700741801d00052211900c22680600015001000c06110b40000100c0200252040c4c400c0040b00c4180f4030085a1720182070b140e89940705 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 894856672 1250 894855422 894855433
    0x4090e070f14010306050316030204150815061c0c0605130510080108190b040605060d0b0405150c0406050331050303040b06040c090311010512090d021c0909150305 72
    0x10382c0456902080454024006804c201000c00d03a440c0100368007035a20082020000518590750074800904100707407451401040c0410005100c0c0801d200140c0003608428018000b403130440100051840343c4003408241d5068401820000340b40b127500141036640c00d042040d21606e903c101c4070070742c2c1100e401080d0807402d0800f0450b10f8035003180c4042d06039882e0b54103442c0c012413401542000304044a10207081c24030080302246c00703e40c40e64401c41d0440c001414a84100e03115848860000c9001e8078105c1d5594001c1d84c506c82c11800041e9520b170420400340c0440c0c80c180c80c100c0300807e180805020746001d50421003007148270040046154044058089901d40c10741d0311411b103252a41c0040310161401b80302200080d5441c0707410302c00c0030044404d680702c0f1443d00307055460780c0120049840380d45040c0001040042d08044010040c0d92084010784014170012210050090501d2025803031440c2ca1051402003402d6260032a030900c0c10340c1d043c1500041e4100704c07041c2c0145034801c581d0018100d801103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 894857922 1250 894856672 894856679
    0x904081e04060816050307140705010908120103140c0a060f0908060907080f0a0309060c0303090203060f0a0b100e01141b03040f060908030a1d040e0f0d031104090e070f 74
    0x109064030508030130900d00014522420192840e201c21111400080c044855410110504002500c2c4c4c0380c2c0188000141c00b00702e80d0390b0340303a03030760020802109003050500104200f0508820a41802c0ca11307002902d00b41c40713800040b503103100c42070042c44c0034010080c086403015031003101510004c11720101199a54145801e0701c03502c1d6600c41c050701038907028121841184100006801404990658402581c24078040c41200c4408002804604140d181c804002c050390b000c221507801a5046082d80c0c0260a004110004030f03444a54860300402c1c228020402e03036038220841918541080c00c0001c400c000480d4130f00c000380700310406420158042100c008140000101920035648500b90100c946030325500300741d44101051040c0c4000da40208036900c1601c1c42000c031000700241d84064480c40072a61030028090701d071665078540450f8881e22040c014071900300000344807185c4605003002803002042d075000051065005480a140c0c6801c60020041c000304884402044ca92a03d1101341d0748 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 894859172 1250 894857922 894857927
    0x803091c020d02030a200a15050a09150203030708061c06020d0209040e0c01080c0408030a120f0e0a1b0602030304021005091e0109140f0f0a09060902070c080c0904081e0406 76
    0x5206110106c140e01c2405030341560708016030781109462a68080c8045c582d45894119007981c8480141070420101c00000030710314002e48140c03840715503a03070082e5132689880800107020102c0103120600c10303960326954003003420006d5000410035401c628090385d510700d81b0741404040c5c030501802d182c006242c9820303448860400f09891070110400d0361303290364686075204903008901642c020034000b5001009502d880c2e13801045d01c030103880d010070008100080f8495000742101e801001041c110b400050360002000015003042d01c0c40c180105c600e0382018180310009540b8080180020302820041c2642000503015005690b1064002000038100540700c0c00304411f054108518036002ca0001e0102140390303800c040742c176542144050003043e680d820071820010040452120740f60802040003001c22151241e014410203404451400350781d0b54170601d0030141c400c0544d0310a80710303900492448030712075840c0400e180c0c01030740268501c0d494010f4030347c03905015045a1030b05401d5080001d000141e454 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 894860422 1250 894859172 894859193
    0xa0c0b040804051302180105030402210c040606030b1201060609030639020c0301050103330609090515060307030b0a150303030c170702030301060c05070504051f0803091c020d02030a 80
    0x200d06c00460343c05001d401503400f4001a50000d60150100c0c201c400c40000d0310a5421326144444102c034481c00c0b480300450b044a2154210100098450f400c060321410503840070740c928041c01e0000c1003070920700720008002802600004142070348640940c140003e000003031746841044101000918288140074103070b048040c00240015001d0010711450034134040c811103040305e41040380c1c075520781d6038401c001101c80c03140c40341d110001480400e21240314140c0d02c65040035020b2180c2c00102c0b000c80d800c216180610084800c81c00c180000308100346a10085000c0d002c49502001d40c4400d40c4480c01d280340a0422550410b200d90071041000041c154560002d9003800e1a5490380c1c800520340d070010460049044032041e003d41d01c200b00400000d4400c0c0d088903641d50041007500d040c640c9940c0002c05442c010707a11124184648015400c01b51031600744280207101d031100461501003001c02056620701c811411200d22540b4078660429512170711440080ca0754010240c41c2c1c00310040c80e107a6040d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 894861672 1250 894860422 894860437
    0x30501020d14010f0b040e0601020a05060103060e1504080901030b03100507030c031a0d0803090304090e0607020706051602040c2109170f0d020703140f0706110a0c0b040804051302 79
    0x1c2e040d000000e6485a0342c0c0404066920f0700c2e0782d05141c1800c1c00900181510003406640c110310903007014002040d4240900ca02944c41103074082100070b01c1c600c5040c40c24520b8400c0208004059042c000000c4d008001c444507101e00f0708021401c44500030002c1c0c00c205840001c100403604003000c1046072075040d03000c1c1201d02e045407403c201040704c00d071230040440750940a0580003041440982e0205044002560740084500300301c1e481c040c4c40c0d80c2c42d9020340f080340040a0184c1c0c08003060181d10354050246501074030051501074203180d070080c50740c0080388040304080d004170b0795805aa03d60074400c500100701c088422168407184044580100014041140241d0b0804000140000740340c401004850700190145101420008080131200c02903105541c120140001072600741044141e103030103403566152070391080343c540c1211b05008003552441c4d440f981c6020000c100419010b9001240c0302c02040d08084104040c1c0d59600e4140840d1183d03400c41390380f1903003491114003048255001080d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 894862922 1250 894861672 894861701
    0x150e180a0b1b0909060f04020d020403050c0f04020702011707030906060b0a030b2403090309121c03050f1f0b040f0303030b1816020307170403020306070c0804060f0504030501020d 79
    0x144005100da02e080b0f030140d803554075404040700010407210b2a0500007602d076240d000700014604207208802c40c08980c82580100c82641040c50b07049138034035010380d0031255800c0c16101546032490a50009200c07540d03081c420007240742c3c82c0020542080c031a600c100030307141e4032510403c060782c2c0b12410000c45410103a80c1d5000242089000d400c0b90034091504d1120248511619154200180c21902a50001800b0340390902c014407801665542d405400e83e4480504005011504880907802380304454039003072142890b00b44018480b40030144004c1da50700442102e03103256445200305525900d0006940700901e90356021402040300081c640f4a1412a40320352420040340780b03481d00b40054980101700034820010440c00145003071400124041e800720b650310581f481c0560030794403038403084140e245040c190480031400740f00b142270070015240c02c4403072420800e15890840ea00d02c00503204500410040010003010940700034020b409075400b03103074058000c0d501c07000751135000001000c6030b0009246 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 894864172 1250 894862922 894862951
    0xa0b06030f0f0601141201090b180f030d1e0518100b0a09021c06030c050909060f0402010f11060406051f1805040f14060712150e180a0b 60
    0x16540002c0b2a080c80b42c515003e4041c6a19044c000440c110440100b0ba401045407111303401800c0003849814001c502c00c211001d03407410b001812a000c90b1030b001e52590281d000986103e6008800401c0d11107070605200701107400c2030ba0744248500ca000d08054228039a0400d028030a80e1804188940071102c41b81046404403c03200301c0d044162505160503c0e00000c400030140144031407030700107041c041d82e0080d0183c0d004443c0120a81240c48560040d69002c514401c14441c52405a00e1960001380b094000c010500344031500c101883c00c040c100a06010a62004011050241258410700c1203c64141d1b400d80c58242400c401608007140e400c549102c0d40c440040009400c01a8403003078400b2101e070100f0101c60794245000901c0003600c01c1c1c551032000510702c40007031440c505058012108001401503403d140c0c001603c81400c0b00f607200001800c1120480e801040c503080c0000b16001900031640301e80f11154200741400c035041c11a02107011302c81100d401d1140c03e07424640504411004142c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 894865422 1250 894864172 894864193
    0x260a03020d0f030b0a03080a170a090c0e07050a0e04111b07051219030e0607030302220b0f0708360f0a03200301020d0c02060c1207050313050a0b0603 66
    0xf0211020307420481e900801110051010410200150140e01c046041c24066030703002c020308040300c80301110f44038441600ca411360b504001180e40300e04020840b2580c2c00b200745c100610090460f0040c844103e0800041c0e000340c6107541d5868000e042041000a54159207940c00035503800f203520003015a04a6114a90b000035540c101418004401c08105c0c0192011451008000f4040c02c00c0200c250100f244540e08100541d45980050032542e119440042e6a40c40b400d42441920044c01001e5070b03078402c81601003080d00705843c06c17a811040c00500b1103954002602d0010000e0203800c01119945501a9101600382140c81020041000c401342c00c4011181a004218a0b000244d007103c0e0003101d02130b400c000040c06800c07140b00408080e00340440d1ba1014402180c01c90300615081d80c40d10362a0240c00340f4a9405010180c1c0140381d0b400301500c0c0c13000c201c1c00c00e8280c0a02400310b804002c4000005801620103500040c040d95002d02511103040c200c1c02c01654201e8142c400d64803a0107400740b2034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 894866672 1250 894865422 894865427
    0x60f09050f040308070c030e0301050c0702190503030d1116230c06160302010b030607050d0f0b15070201090b13050901050301090309031b08070f0807050d030207260a03020d0f 77
    0x350b110707941c10b603662411079469039404c45803250342e49821014130001d40c09500540e5000e00815214010089038180c07a81800c0c01044220380300001e032220b028043d06000d06c5147c802108580040c040da08002c071303010900d902d80204510a20307508214aa201b0070084003081041d5040311180b000790b041841b070130040d401d42c6075100d100c5890426030203102000b80140c82103114140491490090000041c0030381c820300440e0a011007101e42e41c000aa002804481c1000184101c1c0c840314000602013140101c05004140c11001211868206070404075501c821a0302c03981140004d090b5510029407100b11480040f05200302d03a000e41449404244000302d40ea00701407081c000301c0da8165a4200d07200d80395440c1c600d070011105074030ba00c0c04d508160780822040c40401c4080d0003040c5070710ba6158014a841042808d000303854110ba44030340700404221740400d82c00039408050701c2d45509102000c4a002558880d07400f00c06400386030314000e507030152050540102d0300109294050312020300326032060104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 894867922 1250 894866672 894866701
    0x61205071a031911181c031227060e010513030507020409080f1809060a0303050d05190c0f090e0606070303020c0a020d0507030c0f0b0901030203060a09060f0905 71
    0x440190000780b0010301003040ba45120407410584010004625140481c41c1080707900c80c0b85030880c81a940d0031081c05900300120004081181155101000f400582d40101401061403441000300c1c0c40e41d00420f4031501030340d92441d1040e0004120b04200150340b60200241c04144281d500d04e501e0a40000d02c41c9284c454200c042503856039078103141c44001d80c00c01000b407140110940b03080c0400e11800354500a0070000386480c2c0c02c9074114004801c2014204032000200401c454003840140d0000c00000c7d40220a0b240207029800000c60030740d540480c101001c1c840a031014a102c0e041c02802e240080c0c104c3d142940038650380d1f5806144a494a0301c0c8000c4950030b070b0781540c102e0000c00084000c04d102c0d60207070050788002d0f0242c409099450b00021542d03440360b1000d403002d4101c4c20041080080c810311420080807c1030154640b640392400d54050750207000580c030306064000001500c10795400c410000a480c1c070342020082943c0700c940c10004040d0341d0250b070003880d14100125210180a441 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 894869172 1250 894867922 894867959
    0x80f15012a080a1101061a16050109051905101517070e160816080a0b010e0307030b0114040b131e06060804120c030f080702030d06120507 61
    0x1100980301c003001c0021002000700111070080c150500d4180c20001d074032107000340144202650b0708928901e9000c181421601281d0000001406004048400e90907140a5070807070030f0300361354010849a150401e503025003804140240507000b50700080d0b90303005051030803940030307401002103a50607602035541e0360450b0008886001444a1200e08000f0242c3d001003401d1040040415904e01a68884070406c00100907a0150020100381a0318031040740c0c869016640440b41e41040d40c80704140100184c44d03100c0113003810320365907205c0031040e4060340118000c5040f102e02500b22041e07107a890074210550402030150f40c5104c01c210a0110862a00d4052154058001850040c0b000c110307038226030051601550700300c003121041d81d2a8480c3c0302c1c50300c540030040604d521008014605840c1081c0082d03101c4c20b02d0410301c04c6030070340f14020942c420080c1c14844920b00700b01010752138069050346140504025000954200200440c040c4c400c1008070051a100d802102d04403070715000c4000d0403041591 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 894870422 1250 894869172 894869177
    0x3030810090e0c1908032808150603070309050f0c1e011205061f03020306130e1f0b04090f140708210f0d0b131a150d0c080f1501 57
    0x191001103882c00b2104100c0c0d854420740a002c0d13555071103101c542150002d042e0300328050300303072664148480071150214603040444d213020328035440c02602c0344058054455141c0e005442c08800940c07918040c0d4030800029411500301c6104800400596076580e034004c503814001d80091000c101c0f000089003030408c04210585813540300a1480c807a48000300001400294448800201d0410003e488070394030702403a0071540e002d6a2458584103104003d024240490140d40c90150541030b90003010030035010229980030b1801e01034500700d40d48806040041d40840e4040c1ca070410201c104001c3e486045c07030a0340700340c40c18103c66001711205921941c0700d202c0d41c2c5070b540143c204004000c04840520488076100c004041c1043c8000380306204039040400401110b035601d171070208007441c01c00348082c2c504a91040c21f0182030040000040812808642c10380194a100482c00d07058143c0c0c01942c0c3c1c0d2003245c1c14100a50072415100810840084e00c101c400704c9518000300716207200140542c1d05031341068 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 894871672 1250 894870422 894870433
    0x7091a1f020a02040515100206040303110a05040e0718120605130506071b060614030f01090c05190b0a0f18050d08090d052d0c03062e03030810090e 65
    0x9800b40406424010301b8082c60041501b001d07030f95540c80c0400d400107000c56600800302c07413a0500d0041c04640d01c0144141c95400c084c40200a0641d001040310b058072180d00c00c1d51101d844440007503441c01125106c1c1c030b4030007410502c041514200c2001c842c3c1a680985803c0c000c64960485a294442000c0005480d41e007004000480d03039405040d0308111350214812030080040c1640b034280c1207603003a41142c06000080c00140e01549002c2019a201d000c448000b000107000300e5462542881e01403240c54017034074500705201044000303822040000c0556200d6180d4030300910a00400c000300c00581c03800880e01c0140030651130742c00000c0841c140c650180200c140c44c1e0994561034219000740f1060b03031f442401d0001003000a0010b00400d10b100d0400013001c5040c1008138050520740003420030400d0640c1c0041c9400071240d900140c9140c01c9400d09030034020400400e000c04401c603510101b2080100c200c000000101503008194921801074103120751081e44d108c10047c4241c0c2d10040b40c000866100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 894872922 1250 894871672 894871693
    0x9110301052505090904120212031e010b130e0a02070515010602011107050a021c021e010e240310150f03050a090305180a08160509090303011a09010207091a1f02 71
    0x7c00e8403031110000f540c0104d84209460b0f007076244490384111801d141070600c21111100f1040d913041594003403c05480c000303007800300380144a40340018a00c40c42c3e1988000d240400e00d402c200742e04454019800134155041824081212600c0090a2080600640c41c1c0901c0800300c0115009850704039a0202c0078148244581c0c08010040c6042c8404800d5801c0060750140141e070b0308026401004642a1781310980009640094040104016403e018028000c0340e025804500801021100d580c044000d0310790b00d8a2128150300942034200ea000c004244d41604110b81d009044405082020342e82130200d9607031141c03660142d0f501100c000300070071b40c103000424504406040301d00c00c500c0050704100c2e078659244001440e10914000040300102c881c0f50501c00c40c1003a03e021684001c69400071b61031945840d013803600143d81022013010681010910243d642e00c01d020440003080f040006115041c20742030202e82d01d2103203030407142c4100429000e411300070004c140b04500c148450340281c40308441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 894874172 1250 894872922 894872933
    0x10080f0d0f02010b040612060c1407021c061d062401050a2a0b0c0903071a0d050a0605010f090e1b070503040e07022a0409110301052505090904 63
    0x1e100c0810001d40d5214140701200342c40b680714180041400090608548091303003031034403c0305d400384840402c004407031020292041c000c00c00c8940b600e40c16181a40b05a075000302c0c8510f828080e18000b4080c07801c103030845407186484404c2c0c1c0d00c600d0256041d42c03615220a5042c81d001064200ea0000030000d460214a043d030041c0c0c044c0a84d10600e0070280c880029142000d019800c016014000341e0442d00881001d01020b2a191135100c003085028921f0701003501c0c00a591218a441042c0c90320040e2030003400b02070500c0c02554001e0101c0700c810700150402c16180405403c01e40143d600203a03100c4004034642e8400c4e00c0d0b8904850107c658501c5a85555010142d800c03203040d503c801d460410808000090700c00c00040005040c5a0080703a010301b04034030300a0822640741111400301c12084900200c07200f0b0070842c802c00f07606c215400035410b00ca038603044413103201380040f032541035103800100646040741864450b9042d8001c50503440724681848203a91501031a5005078000e228140020300060 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 894875422 1250 894874172 894874187
    0xf170d0827060702011811120a150504111905011101110f0702010809030715091103010513290a180b040813060306050306060103050a06150810080f0d 66
    0x304803084140c5212091041e501c1055080340924626600c580308200e1115820701c680d107141c4540510f0300c1007446c44c0e600d9003207401540586441c8640300c04403413464445010401414000c0e03010f940c1008524270810100c00404084500707840b60018415030100c50b241c0341104a50300402c507080e60440fa1305001c011512171395600f00424241d0750f01c52a134682000d012010f000b0141d40c05416a0761080350344001810440068001c00c034590086c0700000004400500c58445403014610000d82c51a407030070282d1407540d1142200ea015464101889a82401c10241c0da206078091520004004000c2c107285d03020314400e41c180071505429034007144110200da000696440140141040b0504058a0300c10742a54103907401c80d10a5400184000810214401240101620f00302000558075005c0440e4880030000c18950405a80b03100044190140c1e911401c0600b10503012815103008030507011300030200544101031040d4070030b0b01c00568905c001031040384080c3c010010788080c085d00b100c1920001e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 894876672 1250 894875422 894875431
    0x503071103030d0e060115050c03030a111c140f060f0d020406080d181a0d0203100b0a0215060f1012061e03020f03010506060412060e160f170d08 64
    0x502040003480c4010555000c1d216550b09044d01800c1c080d40360007480c504d5010154110000e014090140241d1860701000782c80c0d110091600101e1001c02000318248144903150000000c075107540c0c3c1a40d4012184c0e440381c003920904a024801c540c80d120044904400101d80300d070b40c405600c02c0c410034141810f04c0c442c1e06440c4094008501c0d5501c4028090074440d5891003800012a50300c088000c1c00410003011000303000d41c00c8400d4044064080040c02c82c0329141404a04540020105808d9030b4500000c10060100030302098451410b414000c0d12a0041800000c2c504540c10108007075141c00c1c54076420459008004503c40e0301e443c0d40c00d54214417500c402944640e40c0f0307032001980b851700c6034140000f0000079155110130381c01c501c1000f1504281c03208640c00303680f51404100c02034031524200d034103581e15010f01c02c0c0801b20614005005d403034100b941c0c441368080c1544458500d00300900b4041590342c1194070031006500c4803d0b40e450b01039078500007216036103c6074420354501c1c0150b0006400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 894877922 1250 894876672 894876679
    0x41e0c56210f010608090714120f03090414060307031415010303020607081e0601051e0d0219050f0904200316030e030c100e0a02150901020601050d05030711 69
    0x10310070801c8a401100340521070031811a6049410024580c001001c0c00380945030504004200341084800f00d0741c0c1d50224002c142c051900a000c110b081c0d076401030f41860664100c0304840e4040ca18000980c1c89400413007a841c007403410f019601011403000c0ca072942c8140300c05001024000d01c0c50304c4030340e0640040d501c120094041d80c510380f2006a00c8200c014040d41c0250010300480c201100002c207141c1700206035002e0810a5421220409120704d011a0080400d10b09681c0341c01021742100e8000510b030f0616100381d24005039523805001e01d0b4000e0070a0398000b100705003640d0b89a140c151a11b2160703d481c022010350421031003015207800e0b446407e908064000403140e2848014042c0c2141e8000e580f560b441040301c000c3c030420540e16004180c030018170b41c4091410403d001c22041c0d07507114690079241045880d1440c0c4c81a10000300034040350340c0e40003060054030404003041c84095134040c4c180c0b180140504000400c0074100f90340c03070100719580003000358900441521003006100c03550b818370b6070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 894879172 1250 894877922 894877927
    0x212070309050310090b0c030103120c03020721050c0a030b040303020325030e211605010f09030504090e16050409140f0c090f0f041e0c56 61
    0xc2c0d40d01c081160000d0759550000c001040301d4241001c9401800c010000004036008100500000740e2100703008440d011a406c051902400700e15090b0304104498100320301d804a4040c50f4141028008003002607d40100151070001d50000207001c040052404050038508800000c1400a0f200e54010b40d032018100768a20035503a4400107183c00400400644400a5100c21141442038014400c200800390010581500941b030340d00303c1d244034000e5580402c25402101e00c01428848290011181c14074011020400c1d8441c600c1d01400daa0001c1c01143c4045160540c55029824002561140d082c410030344186181e1030081000064841e2030030449801c08075944a14500c0030401181c51030302c55420140000014003000e03c100b00c00000e1034209844502400e2109001d0010940745d0020303000a0380b640810310280c40202d406070560f00040841f082d920000923441c900216040030f00d00400c2110b4680032200c4d04c82c00201c4654005450343e03110840300d502c48007000c0c02064400d00300d0114021f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 894880422 1250 894879172 894879179
    0x30c051002010b041e0e010603050c0103180b16110105070203042c070521061e0a0b0d1b0206151e0406030606050a060807080f1b0c0d02010b0301020a0212070309 71
    0x1c064401001c500b80101d41140c4045001001c1401001c040d022806c0080001c2d614503183e0541d00c442c20403400f810716a880c000e00d0300c3e1188548070061000e0b00b2008143c80303814444090342500c08244002d10000c1d00780950044420018042c2900a8540e41d00a50038541402c0006091400800c620845141e0000d10b0700d2151607454030144c0310300341c02d40302d031a120603c42509009801d0040007642541c20760704c0c03c011f91a030300c204200c0900441c2c0792070307440d612109034007150f4940181d810810b000c01d0082007c000e120500d8000c401031812a981580002028440503a03070b80d030041d0b4103c020460b039122200160305002040320300400020001030701110440011400321240c0b50010340f4280c0d242c480506c0b071801d100030014028082858000c409242c81d1900821000c07018080705110309450012070710041c0c11100d9517815440820020360340340c685080181e03071190140e038010095401e1205000003840c041c0b007a00c0e1242d4264015205180d04400750340866488444210140000203c021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 894881672 1250 894880422 894880429
    0x40b1017070f05060c070306020d06030503030f061003060503030a03110f04061701151b03020a021f0f08011a030603010608030f12061905040f09050f25030c051002010b 74
    0x10003144400c0c00141078801e0400c0c40010b0351825a0304401c1c00b41c901003102e030035482c00000768002183d801c04401030300c41c1820038042d0b0141000f0351000c2e000c2d10000c07051141103d0000b09035070003010219410010008003140940c103940b0607109060341a08140004500d590098100c40d03000394625184d2803a19540f070885007000c1c0c009400480014009074000d0100184070900d01c1c0c0540b800e1201001c155814a10007001c00c4d80c0d24107110071003000e080e4603004042c000c005181c01d0541c0207112402c66460541c004c20701c01415131043c80040d0707030b0b00b0078207503220b02601714a4161820400d440c400651442c1c0150700d1030340013800301c0384c1640d40c8041c00100300c5414030107480f54081010701155522005000743d6800540541081e01c43c40c11b034403141240d0b503500e0016000329081a40d0201c1e15100800704800101036508024005001c0c40400c091110404510502c20b42c2d02c2d400f410305041c048074603083c00d03c40617000c024802d484808061043c3e16040110751100d00d19803001268444180011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 894882922 1250 894881672 894881699
    0x4060302101107080c0d140c040603210f020316030e1c140601180f3c05061003110c070603050a0b1f05130e0903120f040308040b10 58
    0x140021115400c02d40c14040a200000003803000000404401080342d0008009041180c0001c00200801104c50000c00e01400003000c021401002001002d80d6400c000b120111004107107920000201181101c55001d5801150080c000381e00035800d12200381078420100a1b00340c2c041c0d06001d407142045810750364116121091070038829084810b1221864050505246d51000c100c2c03540206005209144518046040001c024640403070b01ca055000c103100149034101d20039011000c03034241541c1c0c0b4042e124074900007048580c1800d040c105a84083c0c01180c42c1560b40a03480a14115a03081591007a0042d4140c6400021040c2c9050078625072030385810040d03440a000710380c84e90108a110100ba11031402c2001d41591003024903c1c1c001c080000501c107178a04142400300120302180303841902c150440c09090b50303840c08902410101d0040b0b590b03806c030504110104a0600000305150001d422440c00f46600d80c5400c001a00c0d541e6034410103400041c031444800d102c40e800042c0b540d001a18 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 894884172 1250 894882922 894882949
    0x60301120204060512030f070309080604050f070503030406050306040b1507060f110906030a0f020903010c1e05040f14010212160201022e02070812071701080106060c0b0604060302 79
    0x88003500a105000644105038482c40c03003060211100f000c00b0f01c2c040112002140e007140021703501d01c070510f01980c80424030741081126106010400080140001c2c00e1405490010225581c3d40e540e00c04060343d900c603c0c01004000364050011034440d003416002407240e9200203003c1c400301c10f0189000030041c1c02c980b0003a02c0903034070380c07505541c8291240306150111992011480c40c00d183c0c940490114132014000b050050703503c5503500c01d00c01141d07054a418400080003841150079407040100703020105402c01c05401c070b00781060041381c0d0050b0100ca04407601040d4015545140c008241d08115000004038150300071040205860020302005082048020881f80700d40311260000901d0664100d034400d61100b0203c40490403194a440c0daa030030495060f0000d0b96a03900c0340344c031520b94001d94548c82c0401968805220140740c000d4801e01d1403180e00c41e400c0f10107a98840c1c80d9400d9900902c103072804560342403004004103615610080e803085028202090380340e80e03940032405080300a130 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 894885422 1250 894884172 894884189
    0xf14070b0d15091401031401050106080403080a110301090e06010b0c07051219082805090d17030c1c0c0c020603040602070b01031104150515160c09020a0908060907030b060f060301 79
    0x100510070820384090007d000c5803900001c02c1150b05182c0050400407000d000a01484881c00006182c070303e403500700782418080b0004084e120b580d140100c02c09450101c0750010b031409410008034840c040708041e2142c5925040041c28450300c1e000c1444004942d0342c2c80d01440c1d0150911180f510001200300c055010704c640c010301c1d0340d10214181c1c13034580c281c601e80080700c27540c8900050080382c0d80001510045801114403048035080745ca0180400445000300750101c072008002c021900300200003a1007080c1100390b4100c5d402c80400308440880b202d002455020400000001c405400c015001e1540280f04e010700620300551a00c03505039440c8260300c01c6600680188800c102810140540c104050404143c13024060070301d00016940030709100441d0481c2d501040c00e0b40c00c032421007546030605130810644400c1a45074903602000e90721a00b10040401c044243c005548540014194801c140d46405441920b0541c0e0314180100c00c080e084942c0500c400720b64001c2c3d81e480d00001c600034040107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 894886672 1250 894885422 894885461
    0x101505040609060f091a0702030604120f1419050c030d060603060f0807152105060a06081905060f04020f03010927140709090f14070b0d1509 62
    0x101c00188460032a410032802c01500101410344c8a4004132141c0c1030704d51071114400080c5214a104403540182c00700a5071500c6441c0500003441200c2610b4510740c00307070b5034501626680d019007da900f10700c18544948601c00801c50a03901c10618241402003d1081c030b002460810600031152540c0c000d001e003000304a9446104200b1641c06100c0c20005140c03d10484406603e04002c007511139080b8864103507044c00035460f07802c3c1548100550707c3c0945a00c040d0311300021040c11000300a0804851141c0202d2003201c01180c00d900542c20f5611a89036607a45150800240007480c010386805882582c00c500003c42c450719940c0c0d070380054143c903e865106161330750714110043c4161480565000c11001075404402004c0d00000c2007458003540001c003071b00d44044003070303011450a40160301503880c05241004020030803500ca00c001030018040c42104450b58440c4680c1910313001c183c8100314606400b00201400d40032590008403c0a01c2ca00e604403c0b01c0e61180801c0c140c806040c4507040c0015030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 894887922 1250 894886672 894886679
    0xf0519140c03120706020708090d050304170c06032e0839010804030509060d1406101b1a0112031e08180c0d200d150510150504 56
    0x10403203600d9008044008103190403d1a040c10040d200700072010349010f400144032414061504201d07070910724003a0018a642c0d0071030034881d480c2d8125000f41440c0c030400d8044041d003480d0010310b410321080010300e091724644483c0c00540a110594802e5204096146221150240720018090007014914080c2081d12511102c039011203445001d01801400ca0b0380c020448519403080d103240c00c880a08003082151923504044c0c4071030140c040c00c1a400715000610407521307016038001d00e803580c0c0c01102c0c001481c0c54190030000380c0d040c441d4002002030aa882130416002c440c2920302841c1307001e00d4224000311310a800e1400c80e02c000f40c0028800e11512012442010340c410701d00f946419580e40c1e541c900c144002c41c01400c10308003500d030740d00604000c412642c40b400c0c284280d150003600104908000d071f501d0314203000e851004c100d9407581002c0c0c00481d810b49040c001c070f00c0004e00e40e1103225010003400c0c4042c410000c0402609051007010401c0e404641000071810b90f40e02d048298580ca92210718 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 894889172 1250 894887922 894887963
    0x2180a0c05070b0a1d010c0c02150c0a061806020d0c080711120307050c0102070c050108061e09040615030507320d02121506030607020c0d0f0519 64
    0x4000c01403040000c10840000810310b0720b0400d1380c1010040a0100f440a034a020342c9544011140c42c1e40115441c0140040d4010381010600340000c3c0b09440607a03800000c0401005140114880c40c2055004481d1031000200c80790b2001c80107800620848081440c0d60302c0d8441260040c0070351102096071034188401c4641c0040745a507002c4403500d0064200000c000b01292601c0c081034900d21091004404144020300400540c1c00003101d0704000c5485140d141031281c1e208003d84200b40c080342101c00451100c0c204190312014200504a445055810010074041013150080066801c6551400440705400c89640c0340b00046000b1001052518200031040c0241c0c01c900c171107400105080200360700103034080c10f4802150001100c50807484060360021801149003204086d0403070144903000ca0104042c3c60010303001d400103078100c1d4619605c002059a07200b4480400b90342c080d09103a1544002a000107490600318480d00c152690b66604100361040d900308000107c4165070801d220194842 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 894890422 1250 894889172 894889181
    0x260702040e0a020307030b040c17010b0a05060c0304030b1503030a0f031a0d02010e04110f0d06080708030f0c01141e0906160f1b050106180204050906040e010902180a 73
    0x440c4900601114030b22580082c0c1e440d0b00900c002000f201081c0f0000d024807150480303641c002e184100d028507189000b00c40541c020410800000d100e02101c03800441c480c01c0c81400c2e13820200522004600e02425a11240401a002403608030a0041384400303c105c2d80307041c005814640c006407034901004125010160540c0d0b254007009a03d4400080c00345581e617034000303400c1045034081c20035849a0421002080181202c40d07141d00d03c40310001403100c000040080101b18070410207004020854a64405603101c4420348a00c1c03005038028403512a03064510070041003041003500000a17902d410122102e51083d08403000f0340d009203103140e4600014900e000e140d80c400c04200c003601d144e1030441003419070058030889040c100882c0a4400503803a01440c10340040140360b8031109103098861910b40e000c1c3c64203000f03081c4000c1d04c1c10030611546009009a400707941c1c0060055449650b0401440b00525020201d13421a41d2909000005604c0c2d0300c41100d07a86c0c408445003002407400e28034840c180e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 894891672 1250 894890422 894890441
    0x60905180603060103030e01030b031506150c070e1801111b0d080c0d02120c030402103204180b09070203070206030a0911060409091109150d26070204 66
    0x404520080100e160b50200b2041d054a606d400c000300c2c0c410351080101c00901c0c451100680511440d07076600710001130089214400c0c04100c8401c95407500e000d030703410760a002e0b03120800c40540c4510024400c0704485480130703074801c4131000d100380301c8030240764220700399186007600c14240c0c54006444e5404406595005c83c2094603a0002c002407007c0e02001424058005c0060702d440700f0200d044d0000400c0f617011101441003840341d008560800c1948521182d10640e0b017280302e4440c4502d5154003d00489403801589400c070061920b4a034804908041120030400f10000b9204c00c0202040c2c1c1105218011551702a0100c00039842a800341072020a62000c2c2000066610a000280c0143d5881003100c1e8413900220303020502c900c81c2c0c40d0841c15554007420b101d5001d40f02040200d5900c0050b441032448034000d400c92144582a0b03001d00000d64026150151001c03000e42c1e5a01c40e500302000314142191281009500401488111840714090b03958a02001200090f0500c01d51400b0b00650090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 894892922 1250 894891672 894891709
    0xd14070906060807080720011a0901150e130c02060411010201050108030d0b031c18090b0108010e07021219080a05070c12170c0403020913020105030109150f060905 72
    0x407a0800c44041c042100c02042c50080042101c0060030540c8102054640500c2803100382c420184a51703066406405540d4101c40221400345120f82c0500d00b540c0807a049801c40056030440d00c0d194401101c522201d501443e401000d03110211440256512170f6004429a80c0d0107042c1c2800c0610740981000f20f0324507440d0443e810702e001409948400b2044803140310300c1c40701c0010462070101c00320703050000404500340e903d059242c46415241c0c11030942d042124103602070506681c0c85062070310880e00d211105034000b42c130000046c0010309410300c541d60031400343e0040300d000300c490010405c05035009069511088d0300c01c0c030003514502d800c01040c98103c01401b90900141c90050801000d500c0031a4000c0c10090880d0070170540c1d2401000d050702e081c10200c00310720052410144149641d03005220072400f600401c0e00060510702c0542c1c074064035541c16559186035034640788841c0302821210780020704142c2d401d034000801006440d11300300103000d02c0e1113103500c682c500010040c2c0490050300910340c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 894894172 1250 894892922 894892931
    0x602090a12230d0e0d060c030c09080105041e02032a0123030c2206030504170304020f040b041119080919060c0509040f0e0f0a0309230d140709 63
    0x1034146011411401c100082e1a00500600007000010700601740f9071406030440d458074203603804040c0d05170010442e0080540310304c00a9507641c8250341c201d4104a40141104040528002c40d42c040c140c4848001d5000a04442d0000807200480001c002c001139450449040c0d03a1003041c16580245040000c40305101315000101c1100035800b44500c002004d000002000040c0d1220040f8030070804480e02040e11400083c2c1a291000a070003002c0903a0151000b1a254a91032103001c0d8503001c4030301c039a42c00f03841d41103c180700605101c0070784104845550700a440b4008400c01c1d07076490000e402c50b08100e10480c110b01a04200141c0300c800040c001d49601d42211222031055070801c2524403110307a001800040355862818110b4440c0030300c0c00c8841d4411b0403c541c0f01d0036101c0c1900100e0103e81c1840030ba55211403418546580da0031030090007804544c450300200703c0b09220200c4211500c03d04001c240b4900805400604648485007044580c0030081c0100303080d48808000300406400b40910800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 894895422 1250 894894172 894894233
    0x30b1005090f071412071d06090f221505040902091306110309010b03250b030c090d0f031701030b04060b011101060f0515120c070602090a12 62
    0x2824440024446100c0d120601c1c04142c3c881d00c204100c05403c03045440d0310382c81e43c45405041101d1041035550b200000c2902c00280701c0c240107258602110040148860700c1c08012038280070320765281200095003c105a45000c1ca814101291183c2440401000145604d41080c00e10020030064001e41c0c0114500a003200041c1c8031034004036045090302c80b10400d0744660707142c00c00140022000c0b00c036400b040441405440101500414000d2008805603106d0580002c0c90410303c100381000b110760700e04000d10811566960300011900000007880c40d40c81d01c0b0041000c11100d6091140446002031001104401d06a0006c0700021401c00e8030b03126400d41d451500c0340e10f0030141c060310185c9034030380d28500076400b03a000310568036500300c4000c02408911b07990100303201611851710650b4084d44004000500e0ba01c0418120303034910703c5c01c5112030140c4d100c1002d6003034150044c48080307805590801154101d640c800048034020500e50b2030003540041e4034640715040c1c01e600070002c0c00340c0030380c0c4090340d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 894896672 1250 894895422 894895429
    0x1f03060f0e100b031f0f1716050411130e01051206040312050601020c150309010c02030306150c1011250201021b0307170705011112090114070615030b1005 68
    0x100444807000072054417070b1075548620102075610f2103448101c444002c40083c1482d40354001004a81100c0030161103090f90540c1c0a49484c052806420180d00b42c00c41440580760541c031007503285041e1807005040601008a00c00b404481e500b101100c00d040d04010801840d21a141c1c26002d541b041c080e14071800d15680103032a00118114201d8403a85800020714164030801000303821140061180aa00741040040c5845a0055424101ca5400e08002d941410b00020850b1300480d4050000d100d038030000080d10381c04e0b8003c0c8a0381000f90141569441d20900301d8040c0341c0d13120000342113050ba90742300d18034210040e13840554540640e405d1003201a0150b038010900301e8021295011003007140156130300107400c00010340c00410405c00140041860b82c6800180d5005440088c1c0b111401d034044a80c503640d83e00380c00440201058810132040100303522131901e6001c0c5495041e409810302d10950f8500060f600100000d800c00c41001800700140082c400c410350f001720315088405007150602020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 894897922 1250 894896672 894896701
    0x30c12050d0309240903020d0207030503030609040606050316050f010305041a060406180905012004031401020708070f0501060605160f05150708150103020a1209021f03060f0e 77
    0x11a401c2c50366901c194810b001a10020400070340703554002d610b50b00d00b00c62035a80104180041a001841485090719544c0d000044407425681c01ca0001c60451703403000d0410600410040084a089840c2c41c0001015101003100d040305254141c003160702d42c1d04103010300400461448041c0e04041c101014480851a61140315105040c0003d0015040d80c40350085000f400c60381e03002291420550302c0302044086680c0c070400ca03480c03207500284000c900640310b0b4518900e008401d1851300300c00b040100005007402c0140020314101000150800a40c1d848400c1c964014000543e1410b5400d240c1000300582031041c10060b040b46d05007641410000c81c00314a1071680701d50700402000c0f54204030f4080c000100110014200f9034074041e07080e468411402071000c0da0503030b181c103034584400d42c0c410410740c041d0003507842c2080c072652031080329400050b1250240540001c2039800c03140305080f100701d510424000b50049110340c4c80110302c1e6440d0503585e611019460b4007260140c4080030601c003c00680f10394 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 894899172 1250 894897922 894897943
    0x190e130c020f1207050c04020901050f0d0608070303080f16141c050c210705030f06010c1a100501050906031f0f1202010f03180312020d15030c1205 65
    0x1203048082409a107450b4070344410b03403014880c82145032a00e4203210001e1100f1072140c0300782d42001c1d40c502d01340026401440c5030240852002d001880c2c82e801c0420103099107000c0340310085801d40c1d035245a80e060407503540082e40001c401604011aa140d11240e2580006120303800540503910910000c0118a505090714404000010040fa1444a880140070000c900e00030401103405e0000c003440302d5070b00c2400034081d1030204010504905801d990b0591085040307480300703484e5569400e078100d00352500400690600064810001c041b80e540c004201c0b5501c0401107003c1507060100308192104a254005410081e00f0132016907241c584000341c941210710700302016400e0407820900c000983c3d00b90001c00850115142c00607090300d02c0c0320401420350007a02d03001725008642400302c042d80d04c20b0a182d0748100230109400002845034a044941358891440107041c0408407400005441c11201e680d0134403c00c004052060011803c0d041e80248182c01d1a00c1c80381c00990703611502c0b001c4481 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 894900422 1250 894899172 894899209
    0x50f16020c1809210904050708041e022808010b0a0513050907180207020a050a1202010e06270f040504050613020d08030712050c2d0c01050408190e 65
    0x100890180641040780c0c418281c4951140340d0041c2001d40000a1508045d00e1507100d1424440844c04d0795004800c114013998000301207a00c2911490045a40d00c050084202e0300817000d80d1a5841c0d110042c00c44208201c450601005030b107280003082c0c0e0a483d1051070301442906080003c01c1150341d50000045c400d5440726010800f903840c5642c0740d041186551102c0c82d40b0550300c0410581c080141d000300540d92084a035281c0c490740f1401404008240341c0181e4460f01c3ca4441c0030009503014040310407138001d000f0460742c030340000340e040300d4048851103541034181312440d044110a03251080341440e038007105a4042000d0f01c2d040e107445076580c00c0a071090200510340003d0300159111003041200c0f05820600075540c4e030404d803c0041400000920000080c3c1c40c00740819642440300d02110102141a0190624208064070842c021840100e96001c150400c105204030f8071028011030748668012440203444480000144c0705080b107071080301c41080718a040640003540c86103d111030f440c03e0107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 894901672 1250 894900422 894900469
    0x504020711090702030c034e0109090210052b0903110a0503040509100308190216150e13060f03031d0a030305160510050702070b0906030109020715050f16020c 70
    0xf10850030b410b1311000180348203030700c7e00c0071904201e808000201003010b8503230280c001d040e81d894150f0400c030b030b8400600960000b41003128039232903846903000e440c1c180300c0c50820080d010000301841072041800090340300c0081c0c5842e10070301419013000d510000790b40000040c104155585c0d4440e80c49204902916102c1c054001c003082003440c040c0340c0781001c0d40e44154401c0daa205800441004807207008113000043c469980c209401c0d00d40844584c044a0744d030501d2003401314520005440c0201ca001c1c500341c008500700c0801d045c030707072460045200602c500782c41c0407500c600390b05000b44400c0428260103001038081c1e09035240c80e15081142c1b0112600b515240b40c60721803088501c129124940340140084c45200b2001191101b941e00082c02000329800b100d4091360f0b01c0c00d407100d00340601403a8942c400014001000a103a4940003018404c4c40b56007903204610f4400c0300442290000da0714170080985020400149900e4954201c02450003400146a040034140008130006807080e0041c4508100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 894902922 1250 894901672 894901717
    0xf04030210020a080d021201050d050d210f020903010518060123060a021f09080301180e2a0405040f0f0804091a04142e0504020711090702030c03 64
    0x3d01040308055401448203554011501402c00a500444500d80b90a44600300002c0d0714a010b00340e01003000d0340000640340b029440c07442a070310400c800d0070358002a00540d02c002c001120b04c2c440d0b004000e0600c5401600c0d1607500e41030600b12400144000b80701d012000e404580e44400107038890460740b0307500040b42039405d800b1000c0300620340c60307620035001310001c0f0340111010740100c0c5101600750000e10750310070700d100301c0c0452064502081c0080d01881082005005480e80b050324041c09182085010806641d9140340c0c40c503041000c3c00d9441c19040f0802c1e811034018016420844003001241d040c001e50a160700c69010203800900018038441c00c50074a0f2080004c42e006513030081032240d0b801c03c0486200740c00e0050b5550754400c850710a078a48040468000082c00109008608011b000030386400203c20b0702443c02044a50b40c07115800700000001c06036142d00086c811750384924031071511031079018148100381c02c001e00001d013590001d10032022b8040000040d90801c20f110ba41d03c0740141003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 894904172 1250 894902922 894902927
    0xb04330b131e05040207080a1d010c0b0603120c060906161b0201140a020d020f030a0822060f060501170103080901140d050103050f190506010506031528050103020f04030210 76
    0x49aa110f2038000340086004e50a00140201030200c990440e00c403005941c600e082014001e802c00110307540071520040300d000c04903200c0100d0691080000d07041f55081c80c2e1060101099070000f00310002290300c070000700405c400090200c1600000704509010034884914005000c1c44014801049460442c1c40c6910075a03104407002200f556200c609690b96000b2102c0094840c0d2004030700c08050300c24804d120410440000c125105084103543c0c141c003607200c510090943c585180121640e0640140b24a070104225105007200440b4517000040d0081c43e0100151104103000071002c0a4400e8000410105428400f150580c03c0b0918040c0c4400e440d00007600018094021542007007858080040100000098001100c0444000b1116412a44452651140000c0b0002042034000d030300100030700c1c1001c030003841d000b134405490030380022030010105410807020552019002c030061501a20300b003000712010f024120a203400c1d031402081410704003540c455484000e01924204c00345001c0c091 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 894905422 1250 894904172 894904229
    0x3170c1011070f11030c01080f060103020304140f2d071505040e13031413060e0d120f030c1b111807050c1002030f0a0b04330b13 57
    0x9070f000110807082c01c118101149050350540d0418041e00c15004480029070052000500c80c0035503510074a50703551020011006034101600881c1d041d07445503102650004180300d0103150541c2000180b144030410507000d2519180c9002d02080098501c0720302c0b0607460003155403400d90700030310303900031143c0c020b21300c00c8490b03114039800414400e03441c505000c0e13910780145110302e00034041d07514a1000d9a80201102d00351107a0240d050912800b49010800c0310b01454403408043c00c02010b0134100c0130580c84240c60500540f26060018500d1660203c020b03405101d4005528494603112504002010642e040708541c0400a0482c55906000c02e65039a40c09615902d801ca50200060050800301d002070003540104452241500600d260b4410003406482a03900c0b40d2001401001151a101c0c56800204001c0c000942c1058640c4450080041c40449030213200d224583c1013000306041d00d080c80340c0110203401100303881608001c9514035a00b01c13007a003010380d041c0e1901e0020904544cc006581c40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 894906672 1250 894905422 894905437
    0x71a060616060209040b1002060a0f090b0c3f0a0905030f0309010b090f01060e0a050619082214070f15080703111602010c05150103170c1011 62
    0x71060360340710200061500500100c50b026507051205803080c0082007022001c00400a00581c422000a001c4001c00d401c0350380c02c3c0c94207031000030300d100350360315030003080c1400f02c034468505800001e02d144003014511a80300e2803c00010203148110b41c0052075a110508480300d403a405c1c4c2c1650126030944241d82c0a01c0c4066884000c482d43da02020503009004c4d082250b80d40f4281d468050703281c08905003541054031506403000b914030640c0c00d059081d9120440c085081d0f070891121940480d00742c484100920184604040d41035000f000207070001d01c0c1100040a610b400c03105d1041840c01c80544107415003895a0040c0000398422070308090700d103008031550225107510500440018040b065480c110402c1d000c5545802d034603074505c04140c0c21303581d42894a410f0144100f10194540603459061420244149000840520283c4645203032002400c1d13104007071610701c001001040000c44500064160390020a800e08454004207900c0700b2108003a201000c0e03e520280222194003012900d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 894907922 1250 894906672 894906697
    0x3020f060109060513050c041502010b0901140a05060702182a030f01080309010804140f0102031e1605030c090103061701050f0615070807020604030213090209060105071a0606 77
    0x100d40e0b50328403032006080310740318280c0950340d0041042e103104814056540b04803d081c0c002882c061814a20300e2a00760f03003a0410045540e00c403850100c3c1d96400c10310078000d000f030b1460364603000c0c910070070840000381c564000d40c481c0c4ac0c100615001603e441d003a1064122548410090381d5862604120404055a1301c98280d03200150100c1410b0003100050341c010204000e01403d41c0e81c0b5039070503035602e10607111950b0104140d02e000400007103501c0c8a5140b00007112041c0c0d9442c0004400c0030782660810380e04800014120398000b4402540b9180b00c0d6407000112000243c0108001c06c042e01d00e20000d05015030141c00000e8581c580e9000c0d0700840300030640c2c030700d0b46a00403204201d1540203010550702d0040d48807500f004116903103852101c5100d5041a0b00c0181e142010590320f40e902903102c4441281c101c0000d100000144e81c401c6500351140300c803044041200040c91040090000300104618144982482a40c002c201d0444217029074404401c1c00c01880c0c0c89280004038240503200e90001c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 894909172 1250 894907922 894907933
    0x20306070306080d110618100608031903050708040b09011e02070b481603020c03030301060507240c09050102060f06090708190f1b03050903041203020f 67
    0x24159072561000b030844a40800391040e12038072407000c940c5c2d000d81003040e00c4554852008a8060b4070783c84010407411020804450451201035032000036104194440303010340d08082030320b0883c84100002c003035582c0f1040c5001c100c1442d142001904d1060007401c050110f01c112800105903000945c403001c1072031811032907410f40c05440101000650f004150407141c8400c0d000108060404120703e000b0402c207401d040341007101074001c2440c00c075030b08944000304000740d0762030299003450000010400705090600c0c40e54800143d040103803a008400070818001d074003c200411159038441c064440d1280e100d8030b80c100c1d80c0003002c008441001e01c20403050308a464142d4a081442d0001045800c44000303800303503200c0c1d42c0e40745100003113a00c0440380300c0e402c42001d10004800740d220b0402036510211908150100000ca1040582212107039804161a1607450650fa032400d40101e0440c1000e501e20b19007031017945420142c0c1a228041e038030807000344040000c440c1e003c050080c0200140d290711712003280d5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 894910422 1250 894909172 894909181
    0x1120305070609082d040611071703090a08030c0307020103020d0f060e010f0509040503090108060a1d011d070f0f2618030a022e050a0f0b060a120513020306 69
    0x2090740140d03081702002c0540000c1034001801d120b0360315840149024034600f801d01d06482503581e0b483d5155402c400d0300a0f41c2c4045002c03881840100500044003004544814a081c1400540c01c05504403000365070003440f00302c101c440004200c41c1c800307a081ca07015031140d04e4581030b40064010002d41d03008103402c24801242000051004504070782c05c1c0401214840c0da5801071048994041d6005001c2da042001250800cad4010345150341c025801501d0b01501c04d07511164103200302c4095100900c0c460781100104000c6e18510401c10040c2003544001003503080012000e804001d40340403810503c0906201860381d6401101c88842202c0100b49840d04011800c006175071240003151508004650842101c80e03510000082d10080380d5940c00402c031102150404000515500e4404056410301450010403113085000300c03802003110740008641d80414848050544030750f1502d8a0084500b0f00a41c001154030054002443e01c00c007031f00081300c0e00c0352129202410484c440c080d400d03100f10350a00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 894911672 1250 894910422 894910433
    0x190f0908100e0705120615182818031116030c030b0112170c030405040c05030907080d090303051e0a08070e0405010b070303021602030d0e09010f060801120305070609 73
    0x405541d51000d007a6843d9075103034000c202c0b000000b1011185554000000190404681c14404c0528000200382c240f40c000e110981410450701100c0342030442c00554449404200584401c1802c08141e0406101400728084501c2c00c030b80b40084003904000d01070070b00c1041e550062101d203c0c040d007401c9100488584a04000000078941d00c011281020308200003e078591200d600c503118503501c1142440c11032a0100c95410542090b400c20400c0d000400c4006943e0355540b107802c22144240d00c4a41c0c90340390881d40182040030743e60001030030b500000340707906041d03070b10981803c2901c0e49402c05644451819031200ca00b030451070203e0550101c0001c8081e9450b8020b00075034890400c9a0b00d11007428500e0f01480140c0e81c00388148483c000c0140240f40010b8007079005003000000024030003206a0344d54000030302d04003210703016001181407008098081e0804640c042c0c09842202d090610540c0760400003032805005200e501c440020440900341014441d200b203a900c150442c8090040d00d101d81843e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 894912922 1250 894911672 894911681
    0xb12100801060b090a1d0402190b16150c05030c07030311030f040519031d030c04090c061106090c010e1f1218020112051e0f0601080c190f090810 64
    0x40c900c00d940907080007a10ba520900751241b08800d0121180441e2900d40c240441c41040e401088600d0b800040045101d041c04000340890003036001481d20101860300301012002500100d181a86003840d42c0400b00503001401c5075001120210203e5481006d400d080703004024105a1845044000040c080e01e540c0c1d8001081c00f030350162040d10144546070400011454948a0081c0840e040041d13500048001107951008214050140d4400344605400102240c6400030203c4542c0d1007120305010349544000c1e40c080c0254544024141030a041c50100d654500c280446810070003800040c0c0841d0320ba400030040c00c6401070b501e840c00340c0e800c2240034000c09810701005046038078109049480c5d09003044451429038042c0c449260074458a8440e00103030600901a03800069160f0302d043c402c01c952040c882c81100103e4650b0003505105000410220b0060141d1140c0c00040c081c80c003c5941c1101410000800b50408000c4000c5842096504c21410350018895000f41464003807602401c3c0c22 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 894914172 1250 894912922 894912937
    0xe0a080d0c1106010e07050415030c020c010207260307021804031b08121b0d060f0f05030d1d040f2f0f0c01061703220b12100801060b 59
    0x1000e000d400e9407000100d40142d446115444540d0005004104c940d0450150300d030401c6036441d00305e180c01d45900c80f1040036480441d10800003940d440c0e05084240d418440c07164411030902c0905041460300c0b90038415440010042c40710003141d162040c121803c108110740d401e80c0c2c0901541404000b0052030f5009600480c0d090b00464020360401c2d081d00301d4800d030a03d0140c0d00041c1241082c0443c07030b04031803005c4000c3c5001c01e03214840d4051209101140302401e03da0000c04004110181441612610312000f6844005140481c0505020940e00801c4000b000b582900c0c0c14052400404442004000c1c8105c081d0340240c03a048440140c0d924681100341c1e413024006156685600303a6554240707c6019001441d001c40e41030003c1070403802818002c01c40100e0250000c10700d961648400c0b0b100f1076819102141507440041c0450300120702c035030380700461840e02c40c12213482031420300d541030f5071300c1062031441085d0004400618110000c0d0064000340a004008001c05038a0b21700c076071410b601402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 894915422 1250 894914172 894914197
    0x6110c0609070308220b220512030a08071814090f040b13030903210f301b022109030a0f0314030f062b0201080a0e0a08 53
    0x103001600104002416034201e9a00c075003140d01e089901c0c480c4206942c503001950b1000d121380c82002070046000006402044c414610140b07a0003a42079447e481007607d40d00550280c00c00075080c240d00c0401109603581c81e44a03080407212a03881c1d0400b203a400b03901910b60a01022140008135800300603031003072781c0201016900c42c455610f4041d4a0b06500c042118010050034207480003413200c11807a0122910b07144641031400f4800c3c0c0302d9039101400d43e98850006070b104483c096011000c0e0740b113190084000c4050800701120342200384460036080034000341c2e402441c041702000d50201d44991100801d001d180c803501080100a42009440e40c0404606520782c800150131080c003641c8040031242c044400034018aa0350fa459502c039034221362980300c1a4184014500202e20007070150300114820702000484003031a1409608000d80c440ca50729810030034804521341480e503181d2030340d10740034001c0d0242011841c0c0c0d070703e5900c1c00c0040d0280c01c0c140502c500500350b04008001c41e03603010309880d00806 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 894916672 1250 894915422 894915433
    0x70c0e040312053301031d0a1208040b01090b0109030f1407060306050310201b120403080315030f0703050a020901090b0112020702040b040c0512010605030601050703031806110c 78
    0x3c0c404c00d1040705400d00c4a1644801010703681c03209a003442030031400001c040c18041503212120200840a41c3c5c03c1e80900304a800c1800f002e01088403210101207481500d09081d00d00703042c551598000c84a05010b206410741d40c1e509580c005a0188005500440e802105807160309043d280064241ca0364084038081c500c108000421481d00901079101916006001000240850f10855018011801343c85107050280c980be0192102c50a0080c071000c0d110314190b08079000c807030001e13601c2d020903598602c0f1f01031820b00c002e1001545004c01c07640c00240401e02d032501103400c140007d003440743c1103102041e0b902c6410800010081c0101d0514021070007140e1400840c1c1e60b82034480c069503002441c46000409914107041c08803010b501901010340060000560410f414010808a56041e0654004200003082c00c0a40360b2411549501618807072038903608500381400082c2c1a40142030008080c503031180d03445031491281060040080da0005418040206000c404a41c2c9074425101c0003054040e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 894917922 1250 894916672 894916681
    0x2b050609010501052209020a0e04031e1e021c090e0c04120206030a1803110d1805060c03130e1014100e030c1201020d0b040b090408070c0e04031205 65
    0x10311810f4101ca20281013040041e03084101451082160100c40300081e59401c01c0002517100c0004c50301c0035219a529104181c1800d040c003400001e2440c00c140010515641d0981070641e12421354011400c443d404a040c2c000c030403000340d0801d60041b00102d02c50840c030044100c00c59000040308100c406a0701200c040ba11141c0c00142c0601c01c03030080210f00f46001c403100c2e0040c2092801550f01031040400000e0002d0382450b01102c55510030750a40003c1ca050030064040b0310244000319260030681803105010124071401c0c10305503114402d26110703841c0490010307080344041c4221240403500d03a0020000d40c1d1222800402e9a1007501c5c8070728210389503d408070303403204018100c03402e200e4003c010310209100d42500700d400b4200304a8403900b501420952104640303c40b0030013407412030414000341e00c0380901202a802c5420101e80c6510560901e22010643e480314850316070416003203004c540d036800d003c1c00c0941540c40582c6c04218010907680c100030505600c03410110411b5442d42c1d0501c0036403503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 894919172 1250 894917922 894917941
    0x609061202060a110709090812070305100902030c0d05010801060e0f1b03270106180c0c110303070b10050123191809050411091b092b0506 61
    0x300010025003269080000b0100700d409868041e200e094003c0854403001c0e120341190050310311540c41101c50181c040303121170441888101e03096100724603181c20045498804d080384000c6d0740c903210346002250300002103401c0500040c1110204070350304005122550b91800080c2c020705a80c4900c9804941800114585602c440c5107280212005a41440c1c680c03242a015403243d4005014440301c0a40c4c0c0c408042c50b8205401011100d0f03100c40e000080c4103107064240009100c85100200a4919200564403c182c110b4500990503802c0004850014645804030b40365108044024000a640d00c04000f00603c0d000d42810a44100303a0340d850f02d046e03049241d80810300c14a40d040c2a00c0c1030900c84807000c10200860600040480d2a152a0041003082000d01325034080d0060101c0c503445504110501211104032041d151040d03601d0200c61600c41c01c161911200d80c1c14424156034001601046a0b8549501c1c503804003102048502d03003181c038181d41150600d002c2c000c07101806410005400e468 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 894920422 1250 894919172 894919199
    0x6030c120604140703020d050f010632040605030304030f0302121e030712180204060b030105030c150903120c010b040e0606060f16050102132702090301140a060906 72
    0x346640101035546443d07461070754015030030309032040b60721900c0710000240c6d0300d01400c450120b02079000f030a40c10268403a56800d580c115080a09208003250540d80500e40c000300a51142941c0b00e00032030000c48901c0014090001a4841a4144000305021060124403005822803902c2070f001c4500d030601c2d1410200702d80c01010608140300400e030100d01d0392103440d2001140e010045d07182070191180003038200d4045076010000709442540044c1a2011400d02c1c3c8580d0004d0400461201d08562408000a58901e01100e00e9400b4000e04415040380f003440c1c505031088039100800361030554045883c55001030700400c0384d031401c07507003072a003090b405007800d226840c600001039024001541c0c610b1309011392a03200c0499164150f008103c1005000c409540c1c10354003038890710001d6603400c00750032000307107000c0c032034101810086901e1060300e8420807075500ea9203100212000540c0320075101c40001c0c010446a0922110209520104105219541d00240170395140c80303000c00c2880d071200305000604 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 894921672 1250 894920422 894920449
    0x506070f0c12140d09060618020f0409150b160204111303020f0303090301150e0c0a1b290901061406033103090f0e04030c0308040c0902040e06030c 65
    0x140c2c400034901c950310501050164500c004000c40c43c10305503200c0d2108603410208291052a034604c018005038891070024039003290404800c1d4281025600c0301411071149115800c0c413655590102e4024081d0485068003c0c410b003525551038294241010a428070000ac049101c4c0d4a030030101d505103000d2000b40d440041c141001444194210f9003404548420040c0050717140c80244041e0b211075809018818501100031861543d01740740c00140e607681d85016084c600e0014003481000d0105521101035855400c02e1445820483d5240c02d0105800400c7d190050400c550310300c88651041d030104080d402083e020000304080c598070405100f003c0e8620703c50701d41c0318508002003488403080c000100b00381c1b20821003002051030034100b0540c580d0302440e800c0780811241e4100700007002000d1b1310f2a005103861948001c0610f40b40d500203100302e2050000030244a069000309040c00b451000381005442d0b08036007107550f01d1301d62210f1144114211496807080c0705010034515503061414100c44c64 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 894922922 1250 894921672 894921683
    0x1080c0f060a0503040f06150f080c0d24110c0a123b042c0c060d051f0f18020906030103080a030f140108010515011d0a0902070506070f0c 61
    0x21074403290384000b1450300d0060301fa40d80644824070214a0415241c41c80e0081101030004a2200e103009241c41c01d2042c007036041489842c4401c0080040b40710740c03001c521400c02110702c0c1007108000703216420007400500c100007250b40002ca4203a00c1420001105148240100c200e40003403d494001100e180f101240b2071000c0d541070f4092020b00d903801b401c110728408072101c03007172410301e0120001c181103613038400c210030b81000251b640c4000030b400b201544c2d54030400040905600e840100109010384120340d021442591f0719000904210340c1499940315060090300b041034500e94413441410f00d200bd03800b55105a044540e104005044184219682c0388000360049046030702c1c5485102a68002020000525854407644081105244684c884841200b000c50003d54108548582110402400c4412103d0300c51307103041050303030484038464008100041407030b5a130f8441d0001c0740401c003450f803000c4c090034008241c2100b000b001081880c0300d81910340d18015002a0350500300e80c1080147d03030180a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 894924172 1250 894922922 894922927
    0x80609090105090d051c0c030204030b010b0306010f050309160f08070801050f010b070203160b030a0c030203090a0b13020303070c06020111040612091a1801060801020a050d1a0901080c0f060a05 85
    0x1075014801030404224942040d90282c6d00399490304064403894245580080e50010b014000c100c2504076650152440b6250103056207021000a041c5894140c0c3d943c0500c4004800164110000c1000ca44080b40480c400c0c1e41060b80c403514209000a1030140a071980140130011a04090520505200701d0b01d5a62100310341c0d28220791100154486001030707030980610180c80c016800c00310001301c0142500c402c0a6528504032810b074044801450f100002c160041090214490001a0080100c0d400c9941800c1a896048408008c0050f40e80020b4250101085000078417904040c1c0408542c0240c009015556003d001c3c44407621903401840c011690064a0001c054100d911a143c00c0b88070399043c00003190140c010010303040341116a900007042c01310600c026040d00380200402004800700a600701600c01c0406441030017040c000032788003561180c01b0500c1000c002d1488058000c05000c50125586951703500f900c1c0d00500310084d00568880c1c51402103030500c071045030703c071101d60750f10b050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 894925422 1250 894924172 894924193
    0xc090d0b0c190f0e0f10030e0f07060c110a03150504051207050c040b060a14070c031202340e0a1b020304050102100603020609061b030a08060909010509 67
    0xa445000740031604803220074094640040c40040940a6010540e00d450030402c1d88240010000701140080c24003800451118002c02c1d21502d818880e44c0c6075a082c0890031482444056280c491482c600d2066031140e19000506690089404c4c8002030296012205002c5008240703c92071840784001007001a180c0341c4803006204c258802c1c0d030418450f205a4401820f0900210916040701406981d01c1d0070104000007140b80902c12090040b4081c2c0d60a400e1001e100409000840305415800021100207440744c05c111841d1403890140d94001d20054417600e46400017035443c8400c100e082d800301d9080540c03201e02c80c000f02c0200405c1c0490140b9550300360604030504090140506410122512900050440c032803208246084115940c002d40d00c03035161100091030101084079035180b181c0b40c01c00510140c1c0b680c808440e4040c0040c0d1703110b9035605640160140030f201c030008600c098000420070f0700d01745600001c014010201103c4890040e25004410341c200e0b44291071682840d0711200000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 894926672 1250 894925422 894925433
    0x9090204050306071202070f0c1e08100f110f031017030d0903030b030d02160501030908040b09060d180218090a060513020a140114130b030411060a11060c090d 70
    0x46550017014403015060800943c0d48800c0c4a4011500b15801c08510f2802e00c007e10060300802081a1441002d00c041840e04c014544c42d00c20506144880a88034070000030240c0b4160071a540182c400c00c1c826035503401d0a1340d1008181c10640f0141085100d00000042c10708001102048103030360782016604c0d048140090000508451508500349600c68641020b2a9002e0107e0140016250054006040c02504064034440c1941000381494a00003160010403284001c4c0d43c10346080d105820703905c0b9982400034105006542680c00954203000c44244848180751100c030a1038401d80740701d144c05640b08146080300794112981d03400ba80c0035007034010104010303400075500144076003201c1024103655004a501c24031300d0b411100c0640c0001d144440c3c1075038080014201c4001646001c3d06080d50741000681000d403900c591a035101000c0081070502c091040c01c0460030310001d0106a8440454002506e070010485241000b400343c00005040041040102c2e0905003005041c0d00d100102c66954 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 894927922 1250 894926672 894926687
    0x180b1c0b010618091b11161a040803030705090907030c1b0804090e0f06101d06010e0d0f050607110c0d060f050906090c191203120218010909020405030607 68
    0x109150f400b0b0f04002200900c13442004940051104507080c0300b00710b14009441d01b0404065450182c2c40174162402a110941550007075810214014031003a0400d0100100c07401160014280c41c000081808001ca400400401c5281c00039070f120502039880c03a4058045880c5031410502081c0c69600d090034896401c4c01100580c0c0c4103a080300d0406458500384000c03907650300404030482e440000f41070003207c010880b80d42c1c0302592000300101c2030300b421104844000e112a25461010b4006e02188940c2c2c040c1140240c0c040c0d010b007110844a103503080100b8a8414104256001d00942011418040c890704007078051b00d56202c000c1120380030080c00d114900c103000744141d0f0000d95500031000c021415008460044880034002d04080c24080145800c0c1800303010340034440c03085820405120b450b080c1225048500d50851902e0312049420181c13000c00c07540f202c024005200007421001e840522241c0c0a9408080e03961100d030381c0c0c403100c100049101754010140e0540c030520024040610800d84c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 894929172 1250 894927922 894927947
    0x1a010c030e01121d15041208070201060e0a02030739110411070302060a0207020a06030c020322081603080405060306120106031a06010c0b06010e0307180b1c0b0106 72
    0x4080120003c000c940c5800c4441d44481443c11030114101c2210307400f03003002000070385040545204620300b41587c440d40e03103e603c0801082800b91a0000034042c500039809040180b420140c0e400641c903103400d1140003507000300d6180001c01c6850000042c4940e1f40c010200ca45640200074600c25900306115040f0010340075000c40d40f01c11500312140058549010b82400e400c001c124003500c030304451601034140b0b40b0080c01000c0d80c1d031040c406000541d0311102e000040751030600b000201000b60b81012815441343c0c10101c269101c03046101c2c07420040c006106000c0b41c51403400c1d540340500c5d480b89680031070064031014054035000c2c04140814907004008540008004010840100410070540d0a45a1543c0140c501000f401c005402c014504601c1903400301d824a4103411340ca00d41d54441a4100f0050609410060001040010b50f1820000b800281000e5084180d03c84000e0f12078078003400b901c05586005012096a0541c00741c00b01c0201070042e940f000400c42242e00304842290035524045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 894930422 1250 894929172 894929177
    0x21c0309320a0503070b070c08030604050c16050c1005040803041a1e0309060a0e060a0b040b040f06080d0216171603201009030305030a090c17011a010c030e01 70
    0xc0241d048001c0c00c10442d8803162040f400b46840798140d0414500d61440100b104c01400384500b035280014030403c04481e44071004581c001016150340d540e034681d9010314170003a102089484054018400700180750070020008851568081c4e80041e4111410300442c400c000c00d0390f00a0009200f444440840e10024601d0034818500740012070261500070500d40780c010854a0000081c00700029090102d01d41c8255407400a2000c030041804007070340c1740001041e00b504c0c10f981e010280e00c183c4c2c59810504000b9401441848800300840000b00207100da40300ba03003001d205c1d110001801398004154020070807081481e04c100b00386040c24078884041c2c0c03c0c000203407601031038241840130042c1310b00030b1b03000d5030180c01030a6028000d101e11032000b1440a80383c600c142100141c12492550110950047d1f035450310b040d075201d0700d40e03000135400fa00f2003e1004000c4d1030303840b00100781050714004021082601300000d1021025080c1001f0070080301d0800540011240e640d28000f19008405441e03403101c061 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 894931672 1250 894930422 894930503
    0xe1f05030c01051806040b0304030909020a0e010806013608010b01020304060c05030d06140415030804090b0d060603060209010206070315060c230105160306140d02120a03021c0309 79
    0x600008003d07906c03640001c881100088140014154812202d40180900304021490200b0200c40036140001030303500c50341001001c80000b085030748550030030100e400160b8900a040c101100b107a4090864544540c000131000c501c001520680500903004500b50603009989024103141c1d01712030401c1040f0090311148401c00a2040c075400c1c0d132003108010000444103581004141042200b502c0c00f030440f003038030480340210500c04200340b40110340441d007248400148000d0400040b660885084c80041c00451900700c0c004248411034000700003030726090f800d0b0f4009940c4c0d80c1c02501201d981d0090f04451003038120042c09030500895000750600c0c05108080750040081584a160074000b40810890703075180e2041c00036500072590801c80c40320080c101070190034103180c401c500005620100c0384c410130603404107105540b50f07080358046178504d5030203903100a080ba040207036503081095a01c804809003030340c0340700203107200f407050320710450b400004071101e840c1800380c107840c101c0768001003041e00c3c090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 894932922 1250 894931672 894931717
    0x30503030709060e0324060103090510150e19020901030e010207110f0604060806060906091806090a020a0f0807050412140105010602060c03010b0a090e010e1f05030c0105 75
    0x800195100c1c080e6a036400391414100100200761003200b039040b60080c0d00244044494444029204001c54100d8043c2d6000b6965480102e01034410100d001c0d00501425400c1c60041459400a003250a8840d6924810640d210002801c07040b044404044c84a0100080030055103181c000b000c002d0320500d000b2038100d1001016608a031310945040f948808401c0e20851141881203001040850840f840f030b00f003628002e406402c00c0c1008020354820840001c901c94198ac0306800d0341e81500c0d0180071080002c40c031426a44d0040f00582c0c40a12a440f28000603410000034002c840943e01e507030b6a008408281c070300c403da5020f003024201e401401004d00001c00e40c050450710306a509030140001c05040280c2d1440b4508540040c0c22100c21034200c1410808105410304c122070459040741241380d0748034050041114010800c0e0440c00d00070f500ca100005018000c2c10940b405007082442c2d090a0305841c0e00000312500840c0b14103605500140021912036000d4009010412409040340980680 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 894934172 1250 894932922 894932933
    0x60908040e19020c030d051e010f060801120f020603041a1306110a0e011209051005150a060207290a030905150108031611030d0201061d010e1303050403 67
    0x10a40241e1034040e00c01c0200020054001c516280d44010107004520f0943c0211489480c0e00c94400d0800803140c0360008900300c001103000c0700f000d03074440510f50000c2d0350312401c0024403401240300343d5001600d56000422001400e4240e030b9046941300c1483c10403003005a0920172640c1004105407001028058949441c04800018038070445056405003a509003501e4074904403040c400c0d000605580038081c0d00045a000ba8081000c01e400b406c1c14889443c0c84a08140a0040c0880c02803041c0154032440150100540015020303860300e00c02e9400c2840c05105100c21310103a44524030043c3e0010808006007811160640060000030864403113043c8c004610000769031160124a0002f030340c0311a14020301030144400711685648605513609540b51068441d502d02884003420b6031141000c400b881048800180308040ca0b4000c3c042c3c1e503105046c500c01034000c0440d0701ca208018004440d904143c1c030302040000d07060303a01c8844180c00c5a100c501883c9100c00b00c494048060200c1040044042a07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 894935422 1250 894934172 894934177
    0x70e030106060302041a0306030706051c0e0a030809010207051011070c080a02190b03160c0609030c02091b04170a0203100b1507050c090405011803080f0f0403020a0609060908 77
    0x2c11078a016a44914080d55003016506000a2652031542441400305559000c01d1035400ca481034500180c494500c0c0001031080c2030f0b06081740030402d1410001410327000700403801003110341c000d444500b05680d8940480e8244c1c03003100b5009086421054540d42001c06c03650016a250301030b03009640c2070401503640c1158038480c80e00001902d130300200b082c07001c41c64501d041c20441c01000107604040d900d044218603581c0005000804402844024540c2c1903101d48044601030760040003d03c6040c6103801c000e0304134050040e0a80c0558031050008030b141003807100a00c50814040d0000d494149080b003102280145480c0248aa0060300d02d035502694003040300b03c1c101d6489241c000f6003d86003808019005c800004450401c1200f03101d4000414800300c1c840c000000c0c252442003842ea564900f40b0300418040e5188031182c0301d802110814558449242d0740300340c06e028124841e03525904d04446010408460060059000810440019000d5004000030701e200c3c00011032100c907940d59640f8283c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 894936672 1250 894935422 894935429
    0xc050709020a18062309010314250809071403010f11040603060801152c130b010e13030c15060b0903100b0a050d140a03090303020d0503070c0b070e030106 68
    0x1032040c90700b04103080c6490141c0c001015207092042d1402c1c5d50910707903141c04035070041052005c680170441c030056901a4001c0107203212854000c6010745040c40030080d000340140c884007406694003604550150140100ba4000c089103801080396600e03004000400c1142c41012642554136900181c10100c1680601c070292038034841d603680c455081c1800242110143d42c80a1940d0b81004401d1030200c00324070003e410361320803040c250b01941d8500c1403019603d02030207038a50351074810020014248400d00d0030360714403841086481d1040c1da84511105100c001942d001881009100e40c920019014041c4000000c1c07095031110f10800b00d0000f9802150240e903c05418140b0000d085021454103100e512200c450482c8204101191103020450680203405280c0c001c01154580b107040c4a0001c1307100300b080c0310740c40490721864210f00e4001c0048140b40300860141c440c0700241c2e0110b60155007640d10a08041d550140d0320801034030740441642c0301030300755000d01050400d140340c551003e0180c3c0026 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 894937922 1250 894936672 894936677
    0x32a0c010b030d08070e10051b03090112150b03040510150e0c190e0307030219090528020706061d071e09030f080412060b1813030c050709020a 63
    0x14581c10304141030400c1d06003880681008804010050384030f4006800c40c4100000341c501410140440100b030f119442032503000c98242c03100b00b00313081100c400003005000800c02a0380761403040c007964209005541c400e100040341254901010b12200e030040e4003071680a4011740403903c060022450f2101115042850070340741c0ca003011810302c004500700513016040414840717014508850010110301e11401103e61401308044a100c003040ca541c00c000c0d130405944c0003005900780052846100c0c030a443d0038820340c425281040c0000d070310f07a2030041011140d0f9007080a038520100030b5503110002588080c03801c030703082d41c0d0304e80e8049003041e840301c04210118041d2200030514109620013610000d501c030740c03146800503500603107040304d80c3c403204c04d5049981c044415182c010300c0389004c00c2035018617009150008030070780c1ca10051060b1600711158400041c0c60300c2341c111907000c00c048800e007412a110a00c5120044140b800a4072030850480124018000d450030207440701d0b000c030180e90006014000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 894939172 1250 894937922 894937931
    0x140103150308040911270a0801110c0f06010303091208040306050106030b0a15122f0a090911090f150310030c0e04030f050a05160303050702010c03090503032a0c01 72
    0x3440d42c1c18450403101340300f00d03615181446400381c120f01811041d24400324942c06107946001141e07c2c1d0000e001d0140c06050300074400710342c4c0780c01c043c01c02e5081405035818520419101489020020130f1540c1a01e80550385e41652500b00746134280d01d105841c1c8212682c40080200202080c0d0300d01c00c15010f400b039a500803030756028020403c031010290b6003044241c20888100581d000382c02024a520071281d140c008207004240c4644000007060540d049020280c800c40f610b00800c03030280c002c0c83c100500d40c49504459443c0c512280407140c2c82541d481e0100002c00c1601903600d422400e1101006000b0f01e016815408d600240040c0e8009035000303207103050240401d100700720200480c14040d01211560040514140e10014980150340d0409010b01000007510915140306101310fa150180500c01c2600c510800d2030b0040080c00110741480040d4a02588c07048914881c0c01400b81d05600032008606644504d224003902c42c0703078095031641c070349420420800c044101c0b00140c401c02254100018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 894940422 1250 894939172 894939179
    0x1030308060f03030d0b060403050708030a091401020a0f020418151a061602150703120b1e061c060906091d1507050c0318040e0a0c14010315030804 65
    0x804840010700200e120395040060318405460000645082074004680410450303a0200403810701c1c031480e0809041c07400390301c0001c111983d0010091402e690160743d48401ca564902c1170b80441510441d401d030040e04803091900c0803945000880c1d81050004000040164400c1901c109031141070a041b583d6103510602c500c500809481507541071203400518100901c443d40c002112031040e2040d40009224050302c0009648400000480007801e0075107855556485041c0600b00e01d0303010030560700340d6081080040c0d00341045030764400700da9150400105081c031517404015941d0022505511101c400c0312544010040a0094800400c1c80817070008820f410b000b0a2029aa0358491108103801c40b036024030200540010300303101c0c3c240824080c00f4039895401d02141d8500c500c0d00005587e11003c180035003c159034414908041c0740882e82080350460a0341441d4072030503a840090150741c89444104164a031200000000e420145000984900d00c018154106500f42c0c0050f40c0090380030800b071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 894941672 1250 894940422 894940427
    0xd050f060a060f09030813050d0506160c2103020904150302040b0603010605120a02070b090d03060806061003050c070c0e160815060c0a08310b030105010c15050f010303 74
    0x10010300b90518001a0402904901400c0e101442c80010013400c000907215005a0089500c400030300300c014400d02d600074131802c09940d00c6205580c40540d01100b040f040c00b20360f00a8900a141d90380c07004025803400d08109004184045031120b607010302d40c0030030140743e082d0344a128482c14805c125070480c00c11030850043c8400c8aa0140034030340240c00401c01406115000000d0381c0c2e0b10f290309041455142d8400507014080e01400f00c0007000c0c00040401c2c401c2847c0f000c1040280401c050394102b00460b07075103429640d102019102150000345200c82044654401d400455100001c130121500d44101c03030b278444080f456540d112070043c04101c400c0c04220340d0041142d90780580f1a10341000681030200c1c04e4004810b265200f02c2c41801c002491001480003401508115500021302c561070f002150140e0a20702e0480081c2c500858482a4110480c0141071100050300d200c1c1039402d0a60b8200f1005450700fa04100c01550b011248000c0781c11640701c00d000b05481002440600c001e1949185401b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 894942922 1250 894941672 894941689
    0x807022b030f020322030302040308040609140108191503050604051e011a0f0414040501050a060902120601180b0712200d0e010905130e0c092404020d050f06 69
    0xd84000b0750041051006811501ca1031480400c0740e440f03000082c1c51540390940c001d101c1c035840182114000b040c001b9903550048902401c5900880d003a03074038074064000451b044101200c40400400c9950076070000300c1c1c0c55a10041c504032100044035081501c3e030700d400d45000d20440d000c441c2c44e03005c00b11580c00c42c00d40c1c0300700040c004065402402600210208600d014008803800e500030224030340442c400e5603c0703420803408038110001d07056050a0a0070400c0c0a00307002c442d03010559003000400a01c852042c400c5800c0840801050003190300d6420044a01c12030803507c0e10f10030300300d217840401c003604044010076000340702c0e1103068030f0301c0c0c0020b402034810407104204c100c52000d00001d42c2c0001c1e00c04a252180c4262030310f04ad5406042560050300c0802c01504500c0d00301c03606840280c001081d51384a121180c8113081150750070001c0200300304c013500d000c58002c803490a601000982d03002201c9000d4074081c070300600260a02c00414400c3d41111001c4603100340c02070440051044a0501850 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 894944172 1250 894942922 894942941
    0xf0212070207050a0f05040c0306050d060c090b040b0f0a170703020703030b2d010228020f0418030815090f04020909010c090515120c030a05060a0509070807022b03 72
    0x1504c881c224540402051555001c1c03180602075030319036821100143c032036400b00010342402405001701440318244000104800122440880c90284001c40c1054000051321700321495007141514015034866000416005480c44206000e8801403c0114000201c405403044505540040e202c03241070a004040d661080005d074004c0800904c6810011168406000f40b0368131896038551800f0300c10300403407038010148582c1e03241ca016201d002c200c106040300c0940109000710745034401000448200001c95106007030060b2a20f05920300c000c00030740512030041d030041080f00407184a0495000ac00c0e10102c00b1990b401d1044905030030032007180b401e8805107400c100354500030480e9012403840070340410064024a8410520100c10b1744025035503200b00c6d0402e0a15000340142c070300f0000003d1059030410350310b4281142c10540016861305021a4100883e540281042c41540360030000746c5407403801400b82e90442c044c0f40001d07001d0141540c043e4401254035084c5002e00c840742036004dc2220280b91 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 894945422 1250 894944172 894944179
    0x703210501030f060203100e27010506100f0e060706020c0105161b210509030d0f0207060503070c0b040507081203130b09151f05030313180f021207020705 68
    0x400500100fa00608030340141948002c006a9907191480741a04288580e0b02c180304500184082000c12030041d070401e90800d000c2d0300312405621152403214240d03082203030520740240680b00c6641743d0500c01d034054000d100042c18001404070013000030801c0c542c0034803002c1d99040d80015610005450912420381d103d001311499640582c4152002000500c03100f44080c41c80f840c500020060081d001d050782c4441120034090012800500005010313500320541040c404c0c01440b640901e650b000b003103040741000c034503406407003204d090410945580c0c2020748500200031020fa03401000070302000e00140154001c200030400740303182c800d00616180710341c03541c80c0c01c0d40c0090040c0f04800d400c8924100083c1da2220090316680d0f00c0215891402d8407160407803103a0750494041c841900820502c0040480c00300221302407207915030701413603503a118000744403e903154080305c1008200103642c803400706980140004a110202d081d5a035050b60004540d449140149005000d10b00e601002040020081034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 894946672 1250 894945422 894945431
    0x1204081e07030c060218091602060c07030801180207060f0506090717061c020910080606121b150f090a12080304060b040f060e1821090d0602070321 65
    0x9a400510301d40d83c84600402c100e070049001a00c441c900075901c128404082c4c040304140c904841e24802c110824000e04000d400340034042998007007031004585107903805484034001c59107080d64841041000707200b5815025420302156002400701d01451210000110002c18103041030410000248409049502400000c4058008550051404680c84042200c2d08445030300c40a0140c0402110b00e100203620440780400c10251451400001d0165070900c0c003142c44995600342807115008010701540243d0703101e41202216140b05002204800130040c00c0850300740d02d403c40c404003603004003002142030980800c4408460500c0b00e0260300600a000b00745100d0081512131920b144806000507100c2ca0303c07184e49402c16100c2c0d4000302480c0c0c2c8241d0f810841c05a90f5460755440300c0b0195017058450021281c00307440c1400000341c14400250500f4080c0d070380d5290035104030f0198051911940c0000e102c8c0114404100301e4809000642c1c06a250785400c0f6240c0311139000d103546818100c5400c079242 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 894947922 1250 894946672 894946687
    0x20211e0301080a0816080f1e03070c1101090803030907080613120807090308040306091401050105031b011107141203070312050903090405330d0201141204081e 70
    0x840f150b200350021240c41d81d40d04103544c114040601d00c0f030041d0210f0070000e040401c000c080c03001000600d9040080e03c10304800d05100044a12003610200000380140e150a070105201c4880c5a00100050403c1000260b0b6210b07091f046030411a515171040e0001c01e801c0000440c10300c00f40c0c1d03111006400d184070750909940d030b5500d5100100c00b0320041102c84000501054010702204024582003001d6540308d41d5039290800113000e0b500c0c4102c490301c1070389800103008001406000d044ea85d00401410418411007119065980c040c45841e040005520100c20700388001d0144c031028110301c11000c03c1c0f04001c00240860441c1d06041b020301684104103007004a54003289540c041402d00c100800d00b0748501403050f144cc040c00344482da01c24a00b0b0141b0001000041481040560303c0c11081c0b05401500802503850001c2d03106250040880324004d00150310420440a21805400845041c142da078541c4811502044a00301e6440c5000603807078030840e81134048880c910f0b03804c101c1c2c149003800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 894949172 1250 894947922 894947939
    0x21e1c030222030804091a03070e0712020c1c08071b1a09152d0c0c0a0305090a1a370819090320211e0301 47
    0x418120082540c00310784155003076000a0440001d600c00c020842c0c036543c072424500b00310351044c41104001850080002c924400e1808842040003004014050b110710308401000d110710001d0a5400f0002c41c1899001490b103148054490000c1600013005080240510603500383e50202e41982400350031003c011216500c02c00201b003c00c2407130560b10090b00035282c07194116210f0681404900140e034208000c0040000384045400c3c556851500310751601c1c03216001400350a4883d150300141c40e8182d0781e850801a001ca40c000103060101d038a011020740c2194107001c150901140050000074628805191003803400015201c41c44c44000c0d4461007840c201110b218642d40c0c428149205002e582801084040d0035041c040b81c010b890f01c5408400c10004c20501048941821a8800c04c40941c083d9034a881000c45103541921241a0b1500c140504d81601070300344201c1c1d84910a00a1706031203805002801c01c050062400840d4440c3d4052107440840f80800300300e102c0f500b034103000404c03100b403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 894950422 1250 894949172 894949213
    0x10605091f02120307020c2e0302070809060c030a1101020909040b0403210903020708120f0313060c0f020d1103090d1b0605090307080d0c080a051603021e 68
    0x1010062080840e80c215009038281000c49860b403d88031400300401c40b809402081444000c10121109140d40704585008078040c0441c04000c140350314038201950034140694010901c19000d2040182003803441c20001c0ca0740e600903212a41503400100700d001006030400d02907100e82180000079410726140602044410400602c050700413850308000c1024580222130b004401c0e51f40034541b800001b0341407104c401034501400c0450040c420548006581c61000c1501c1c4481075010840d140340ca80192804122a000038150350b201034503078078080000403d00d2085e5140c50034541c48004401c0c4040300064104540903800e0824806070741000448104080115040c1213000c6075180403098ac203040031412404410101d4681c9120900301181c6580c1050203018041011001c80b0603481d190500340f07446564240d070766000708402040f03020004030741c0d4019040c5140d80380380c000c2c03c0582c00d00b08140d201070500303802c1d00540c10034035402040107800c803202074181c0080d2004010b0041080d0015002c2c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 894951672 1250 894950422 894950449
    0x2100c23030a050d020c0708070f05010c150903050417010f06170d1d030a0f0219211e0318151e0e031606120b031902032a0901060509 59
    0x1000c000781e29071201103181c0c1669008100c1b00200c4992945540d082943d51211b401000c1c4110412800001c503981b154021220169012060030403000c0c15400345009060390b8001101402000e01011404c081180b0038582042c2c811000820010b2058410600700c4002e0b800c580403500d1541c0d40d1019100c800100b6002a58841c46c041d00030303a1490303901402940d4202c0c11a5403500400d07a60741c1c00d1210381d245001380980210f401c0207034104070701004081001a40304800800415841114503078280320720903d01c060085c080c58103285060800c0e9245030500c803500300c021035015140c11480c19140b80640001d485000c1d044c3d00da80c600ca6002615040c0241d1800000315060400c1c0203034a849100000c070f4240010342164143d420700702d0305d07189036182401890000340d0094040035080a007400742841003039020327025009887c100c4200c4004040441c0c3c040e0380511030140309201a400b5803c00c0440014807032030003581d41c000c0320100050403030182d02000400809100c00081e40d40c1d10000403452 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 894952922 1250 894951672 894951677
    0xf0105011403190e030f04170c0a0611101d0d08060604030609050a0501021c14010506070b04052d07051008130f02030307030c1b0b030a020a02070302100c23030a 71
    0x1024003c201a000e003810f60120020b900003c0f641c0e100b01104078003c2e20030343d0311054800c14010203001c40f0703d079a44100e00400340e0092001504100c110b0054204610040e8040161203030b00c0d00701d000f00380c2512040050409103507031a1941c0046080c3c24412640e5840d20747c5031156481c01c1500000f82c213401140000f50640f0341d03400ca242c0030131008216034a10660f0040095445074040f5059142c410074107c5584000c07410180c50308aa016103000d100c1c1039600060080342000569241c2410300d00004000311414803d0b14030340c082030780e813200d80c0390b04124103004441d00e51030b600441a401c0440541c0f1040c042d1071144900c281c01504860569400b5098070708007081000203091510901c00f101c0000b1b90507020015003134042c1944008903035181c034015002c1d800303051128803494252142c0d0f8841c129040f00244085200800c1c1034000300420565481107448480d20390700020420641e108180d00402e50010800040141d05101c01c0c001031040345102c1904c06080b10b0850302d920428416504 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 894954172 1250 894952922 894952951
    0xf0102121c020913050f10030213020706020904140601181202010f05430b0f0a15090f05070503010b07060c09170105010e0901091a06030c1002060f0105011403 70
    0x146541e2650580d022003000034070302c039019041d140c0c42100410303054070240e4492411400040343c880001110004480c1d01070131070580081642c044000035040300b401251600c0d0200101c2000d03070713030f41c0c080c0506c0f00101354a00e82503030821000241c05054a1200c4054203800c04030308100d461092840a0042c0f60203082c05070861551480880b410312583c0c94201407202c0500c222400f1040c00040340d2034051540113481500700b07040190244041c04003100a180342070030000607249040031581c1c69001a601240072134000800e000882444810783c004164007995101b0030445c407601800f61a82080741802e11605d10f5043c036229290910032240b014204688034036814060601c51543c500040c010a0510b0310142d0352505d007a400780c1400e100d41c6030100c03007200201c1c5090b20107201d02100b2562040c0090301c004141154001103500040c50b4903403502400d40b42c052140c50b03614040201c0607655001d0310051034100d030f41400816040e04000e04020303549655214107001101140e0300300c20105100a03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 894955422 1250 894954172 894954217
    0x10602010e01090209060d140f030408071a0319020c01180605061002030d090804150f08061c110f09091e03040f060315091b02060f0618040503270f010212 68
    0x29008c007890403c1c07022807103603440e4000c0d20840840176205441c00e0710180d895980d5500e40307854148802c0008583d0414082010500c0c2000909a00501521001f00941050420981039085038415400740445016851a88007002164403030030340d00c00c1c02200d008000040c81c1c2d10003076907800341c00102c1c4019599540b80c00d00b8401140266030042c181034048170980000314100609880e0310054410206514201040461500751041c400941c01e40600303900c0c44500b502c8600056018010803034008004140442c0035481c0c80150521400c600001003000304a0160746d6145036114200d60f06880d0001c0c0814040500010002c1c01110100e01d8003154a100c1c0c000d1419450419602807400d4078070307100c8a0303404200341c030010b0441c1c5030f82c0d90255052661006208070041c2c0d0122a16580558040c03c0e20366018000500590428000d0041760b0400d071300300e0b00c0050074001800301100200782080c01c1e01d0b483c0c5490112290080804c0c07001d004000c0d5a0041092207024000e00c0f030301041e000031260b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 894956672 1250 894955422 894955433
    0x306010513270f0c0203090f04020d090309030507230607060e10061419122402030604051608070f020f0a150612030909020f040e070305010602010e01090209060d 71
    0x50306440340e101c866201c00b0310000044880403001809054104940850380c944180701da0300b8020559000746103001405410402c801c04040362499000f0f03402d100543c00310361107102d854650340c032a440340000300b8118186185072618a03808203822205082c2440400c0c44026119058002c00f0b0350440d03160061407a00b00041c0040a2034841c4507ca0000c3c079003041c60a641040088070048044203c0314000c10303040c4006c10021403104031001d10084d01c00c00c0035540010040444034041d0f031030030011419109010807060100c13040b008555402105201e19442c0501c60b40d50403004042090514603120300001e800780c50700030a102d05001034a03049a44080c003e11101c80454829020b03600144214070f08811a8810b0b0b0b40010340403490a00045462490031306004415509602d841204600e04101c20011b9440004119400342090000048900c002d01d28507004403000c1d103010031258105000242111880c100303d6410342c0c144695117000d41c491660746508480d0a6513140d08510160030a03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 894957922 1250 894956672 894956707
    0x1510030609020f1c020418030c14012705010f0513020906010e03010c02010501170321131505072d0309060b06070c0e0705070305121302100203090f031203060105 71
    0x20140c22101343c072851345138448484986018507108603800c0207203001d60007500005843c19000100401c006015002c0400c0011b800031000351401000850150481512541013103205041c40142c40c040c3c808007410041e080c082d88910080152040107140740c0010004505a030901c0040c0c050001c00700410f03541e9110302c2c4006016079018000b804000c103440d030000c0c0286030034072034241030000c11440800701c180d0101c100c51f0b6040742e25043c642c210764460344454680034003030074411109001c40c0700e070030000348204c2d642c0007003140309400003500b440c0c0020081c10040c80c001c0840309004030818821455120030700c0304802c904041c90000b4010500e803a0001c000c140340d0403540e41c0b001c0041440c804200001c44441e0580e4130130803010445440341241910940640035000f00404d80512188035040a00c1c05103c0d440301244d040c1880d000015000f04048131000301c13a0100580000481e00d5076130030710841c0b139845144190f008103640c0c65007000803c0300b4000070304690b041042c005584550b10451250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 894959172 1250 894957922 894957949
    0xf0d140405100c0501060b13050f1503090a0b04081b060c0a0311120c070309090c0e040b062b0e0f0601030b06150a0207030303050619030b0a021c020705151003060902 73
    0xc1203400d440d4441c450554111048c1744540b101032000129150402d002c1c0300200140160140c0b11400818400c80119040105418424801c070740080740420b19894489010704d00800015503030340c2d00f05042922104038100c070507e084c1d000b8401c0c807880070410412281940001c1c5000103140035140204055071040380241501c8182000621285550341c0c002042d035580b00f5241c0300380140da1400c204068501002d85c42001c140b07060055451820960049400b01c880208010b19020340350b400014409104c40d03c10382c2c54a0540c405640c0c508041c810b05002180c01c070024002c0e4061012107580d183c0d014040100034190140c0401d415803030384d00040d9801c6218801040e00e030074602000960703810083c403060f40024105408120a400c10003207103121080c100700109822407d60300d0b0301c4085400602036801069007008109031055038128407204800c1484005a40d50358541031a618100d00e51741d034800c10110a01c00c0c40401d0b00784040d12412244c0c0301801060401d000c0c000102814520301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 894960422 1250 894959172 894959183
    0x160f080c0d09120201050601170c072103060503070b090307150203040f12031701320d200402040806070f020309060403060519180318170f0d140405100c 67
    0xb400802042401507440039011000d5000308101c1e5070f218011548117280c58100b170700f018405070214203c01d104d40c0040a400303010b4080e40e0802c1c6d501c4003151550300c0169070920000303980c400080c0080e250610542c0001c01c0c1d208092800c007000d0f00002030b00c80c5540d201384428020b50048a5002a000b4021b0b18010031800c103900702120350b14131003003c2a24040d201103000540e01e20b843c40d80700c910650628103031003046480f41c9003802c15904050162010060b9605440540740042d00e0503907074007046100b042e101d0201c48a050025098905c8101a12001280710303a005001c288070105000491991000b45450101071800c0c84a4040e800d61080300302c202e4010000180100a00c030032500828090359a03034034a9038078200d840c7c00d03039000c851301620400000c1002185a2020034481c05002403002c0200703200c520400d9490f042c2680038020080d40c003506030000c10101410300400d20103e04440218145029410601d411020442c4a2401480d104414654480c4601031084018882107540030703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 894961672 1250 894960422 894960431
    0x30b0f0907120c05030705161a1311030105070f140705011401230a1511010e0109030f020610052112031902040506090409020d05030a17160f080c0d 65
    0x1060081c582100b0300d1010340b02a040140c00c0081600c6801100c0c82180701d40e581d00d00f40720b07004002036140314094100307507040c0410110450b0500c4c4480800c030302801c080f2034400380d0b0031018640310008001c14280740d442a49010100040e180c0c0084030800c045c8501d21313004000003a5144109c80c0b500601c1800f40c0b50303618000b1054101600c4040d0207058819000742c43e89000c462202c61400c091300d60b6626500840142d10400c2041c03031114440d2019140c0d41040541081d07001082801c503800b440c1888080e0791030300800000e2541140c00082d4190b5144050041d0340703849240c401070060781d4071905000340c20f41c0e600f561031400c0002c90302440c0d40c8640180c8101c051a10014a1550010b541924441c5c2d001030441048055510841c1d00301c5030003070012810301901d44108001005a07150a9070404100307255100050010300081607040801e4685107240300c4400312083c401d401c0100181c00b040581000020b420fa0010384001e032401040c54662203907501c4042030600c07406007240d000c0706036041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 894962922 1250 894961672 894961681
    0x70612060f6c1e02060c010912051e0304060207060207050706090801060819061e060e130f170903070803120703060b041203021c03050a060f05030d030b0f09 69
    0x100c076592081c501e4482c0700300d09800864103603142002010849105200e240c01c04040000d0701d400a115040c2540c0341420507502031903004079405500c0240e01000c02e035510b81501c000c111100d1950042544540380c8103081c00249501d02100103040d1407824000700021001500304901a01114491540004150340b100c0071454034982d54104c41c059240800c1c884a030100f40c0c042c0502c11003007240c0003600201f03080c059042d4803650042590900351012920b0750780d554003100b003010014410a4007244002583c91900310783c610907a101425005d100d4005004810100b034410ba0600c60058022032140d0003003003071201c41d10b540d01c06c0d51000e03905400785100c009071030031020014000d849100c5140350103c3d6981e007001c0302141c81d540544100d002003400180000c485002c81002524482c0c011646009592101c0e20f054150030a000800291600200000c0700518003035080140a00020560740c0360402c000070391200ea034143c504040542c3c855107080b441d581c0d5080d0081c0e0000262582a89040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 894964028 1106 894962922 894963029
    0x13020d08041e140102030a050f2109010605010e04020c0a0312151202010f02010504030e040b0411030711250603020c0c0909070612060f 60
    0x4080c0300c007044050750340800ba840e4080302d01284a000386400e460a103540400e82000c1c0c110b400070300000003003580010550b1006151511000e44401ba000003005038000c108840c0780001c411320f01480420030040d4840301c1603030000e80c1c0d103036010480c60b0107010691189014841484c0e0001c00006c011034851903902103805040700c0c01140e0402c0d2a405074620f0100c07500000782e81088055020215a08440000d03002c3e07403103000038003444c6070946014000407200068039004540381c64100300c0555407544010503442d031041c2015100e0500306e000501303100070503c82e8840f03171140c1d2034000e280710340d04440c2920782d24403816420b8a050502c801103010b5041005031031140e1040c50740e262525620700002510070540880146007180c984a001800024500340c0180814035000040c001030b56100c040200f5981e81c0c4502164a00d214010200c00c060108404500c200010130600207010303 = true := by decide +kernel

theorem cover : BRFrame.Cov 894784172 894964028 := by
  have h0 := BRFrame.cov_init 894784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 894784172 ≤ n) (h2 : n < 894964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
