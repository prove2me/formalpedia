-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3132
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:45:22.229252+00:00
-- url     : https://prove2.me/submissions/3b5a6117-c441-43fb-9ca9-985452109b85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 563129496 ≤ n < 563309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 563130746 1250 563129496 563129507
    0x3190e030418150803180105091008100b040b0706090614040605100b03130204090c0b0a05130f0b18030a0206030a06090615020c01080c0c0a030305011701060503100c050d0c02030901 80
    0xc00310f05400c404071035440d02c894140c0324840c4d801a00c0340c058140107a0364040e0701640030740342003180c090190070407240030f0310000d00403003416079141c032201d101e00b1400203900b900d07007044805580714600954101002561010044c02075494200e543c030f0780750036518400b81d007000d10080c0b081c2e000d00808122030920303603082c501640154100207180341c002c00c100584450f02801c19140c559058034001030485044c18126030760f42c2d203900b02c1898003a0020f8943c804c03540c81800f80204880501c0c12581c00e076642c04540352510040d200b60151100140451807082c052540d0f840400c14010b03082d0bc200c000154009100783d8005c0326907448159640005200600342442414050302610010108401041401941e071303499050081c3e04210560700015540c0484d5400d035040c18400300700b16154001c092401401801090080d409484204983c0c010b08000501420040b601e000d80500003568144201c60080c090340844441405000c0006c1c6841145605c104901e801c0c1c0d9602440e110590354000401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 563131996 1250 563130746 563130761
    0x204152a02030c1c05030a0e1c030e01031a0312041a04031703040c0e0702012007020d170c030f18120d030207062703090f0b03190e030418 61
    0x20301808030303010100180c41c0060369440c1800e0444103049031400b90000d50300d402c0b0488400500714000401c620416580040c150292207008445070f00ea0a41c051042400c10185620050005500c50b11401c45d554006e034054070780c201d0040c40d00405150804007182c03910920501403414440d002408102d00783c4a01418003c010b5660a0704d45013500c2e5464501c201203000740644156240000402c0401082ca90088001c0525030844062840c111201a000b0b00610100308804140580c1040c5d10a040c541200d03401c680c0206901c0c034440071071311492640a00704000140101c4208030f0310b4140b8508102921901035480703a2607075180d18040301c04103403d01e01ca04460040c40040720071043c0e8a000b14625401003082d250051b00c42440d401d0141c05802000100e03494030810b80c0080000e0641e4812056005019032100c40ca03548ea124001c0c00300050500c40c0440340e003014004a2440040120100b000d500c0000c1c0203c1c95503024500b650566120b640f02c605458203445841c04184480d004445 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 563133246 1250 563131996 563132057
    0x18140d02030a050f130509010b0304061d1e010b1206191107060e0a0c080f0c030f03070201030b0d0203010516020111040b07080d0f020c0f010f02130e070201020415 72
    0x1400d148040d00043c00902803040350440382da00106030317101070055603100800107281c01090b903000d5503915410343c0300942c020360f4156103442c1000703040032004030403240c43c001580c2c40c00006e01204400c1c50203a0201010710300120840d5498080b010055944e007211490321610075000760400d4146030900d003600c040318101000085052040e540d0440c49031405542500b074010700086000800c00c003807941041d0708003c00400b2551801404507078490000358000885440300f0440c3d000000d00e00425035111030040320704410340d00801c204001035100c1c0d041101010b01c0513000c100032280701e6000a0035190221000702041d01404040c19055509000d00101810566045c510342414821090031038861a80301505084000802c401e1222040c0d00214400260b404219141c00021500a40303071002054010a03d600f0903200c400c00149510850300401407102882d07842500d800c1c114020618002c0007034040d95820b22000410a100c45910300e03450007031399207029540005601c0c90402c0703e100d10341d52 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 563134496 1250 563133246 563133253
    0x91810050f040201050a2703150b150d022a060c03010303080f060d050a0c060f0503010e0612030705030406020d080127050a0207020a1d13030206040b060418140d02 72
    0x1000007014184800d401a80a00e41541d0f01c80000e841590100c20021307080c200c610ba044150141104001c0302c80003900c5c418500590030040c014998004c0d18101c51595034443c403141039020b1300c4001800140351700c0c880a1405030030b0502030258943e81503c061018103507046410703841000000d007404000c3e03200340c0d03032a0080c0c219410340c1c8006050f903c2c02042c1201942c18000031942554504852204196116080340e0268407145016000050f40384510f0020603d8000020040da0290064034180c840346943c0086944c0c613002044075540301031404005da8042007104801048040c03004001500c025001802074a074080c0004010580591000310402099021820412650f41c3c2103080c01c1141039000c1681e40758143c1c000c000380704040000307500c4000c14a0010380d00003030324401c400c402c00030740350401165142400700d040810080002401030b04228002000210a40c0701c03030760844009400020300781e40038034207801000940362042d912290100b085600c0c2c0001081f00d413000d007010f40302a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 563135746 1250 563134496 563134501
    0x23060106020f0a120311031014010212070f08040b03090102070b33030c032d0f030301060c0f020d060f150503150a0e1507020d020a0c050103090c030209181005 70
    0x115a11000e56880007409443d48030340114144d03110390403440360110f03c0020250b032400d000c0c040d180400c3c154400c8404184812410400c2d56001040c0b41459070303e0701d03010501d0600d40d076494000110510b88201c40c01042404003040190f8a04061403268030124001a030f070704001d040c07440e44100c00404494903404010aa9606400c80f06500641d0002ca00744000c110340054000906013540d5204140c0c06201d0810305004541e82124034007441002c07500307640a00412060100d4848200d080348040607402040104a80d51040d0000581c10780240d08039505241c503035000a0380940070040070344041341c0b9600002c5011300f01d445060185515540b0900c0e4407494000803030740b20609000f48241c402c070954000740040a694000c2c1d02400c000c0410390b00c070620b181c91010b464090a0300d15400500c901e1002c0d103803135400010903104085e0807000c258111032038400114041e0800c91000c9034840c0c5840300010040c0c030344000c0b0ba0300900c40300e04501880050b0454980c9043c007203201041c80b030750401c0700703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 563136996 1250 563135746 563135773
    0x191217130f051c11040b06191b081902120706050109182f03030703030501062606100c051515150703030b19080703060e0102090a212306010602 63
    0x40321a0390000300c140c2408415000a0018882a56000d802c1f12001070340383c070b0711307005190201d03421030540e19880b088039040c0c40080300480101d00000c0c546141080015400c0c00400702503107094820b44115064080c5144000d0203a0b049824210390fa01e40341c000511008100e40280543c101205050700170b20300c410b85517a50001640000c8003100d445100c44070102c01140d071a2104c1445000e011a81d40d01d2a0349401002880f00b48102c100141071721521500d00b02c9101e009400442c90094200040c1d2140030801c84010280c180d024203000c0305007a07002c00604184041a00340c080b00d00c880d01c940c40c000304400440d40040907500c0c400c082140301c0e030300141c0c410310980c1d15268262034001550090300001c03a540c0203010034141c1a020030480001695107002070070078107982c851754050103030310b03110704180d0300303034001c1c01032017540a052102d040c050210308103400600840804401e10080b002529404502ca2840346d207214559828140c014900b0303010040c41e401440319100a10340880c40c0030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 563138246 1250 563136996 563137039
    0x2030322030210020309010609060f170a08090108060f09040c060906050403080708161e051504051506060417030405030115031709030a02060406030c080105191217130f05 75
    0x502d40c030000c1340d000c0082154114250302c054080c15191004201c40ba48a454132112880d142c41002080381c11500c9030901c801001c40d080032020f0348076018500300300a0780015100c5820090805402084204808407a80d0721604041e0159000f060680050350034104c4c000c0589030103801070010702804020400020743e034074040314004d64110074416200c40386200301c1c0404034103117040900aa20840b0b070458141d101440607441c942d120f031003180c00343d032000e03c4c030b401d071030b080866010b04150000000e8000e540c00c80002e45a20800c020505443c0584520070b015101a00c6600c100d1998030206090025040034450f0f041a85594042d0703052582c030355074948891048040c125950f04001140b0340300541c50410220302d501d60300400e41602c0744d85501d0010001c01303c42c4540e00000e40d0b81000003442e07007801d9455803d12640d05420100c8541044d075508035416007410121031845070000f59403141304006018004558111155441c09450000c81100090307aa8012600c51a21400e801002c0c90160 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 563139496 1250 563138246 563138263
    0x1050403031d10090f0504060506040303030209032a030f01050f070c1b030312050a0603020105091005090a033002030313020f0307090f0e070e04110d05030406020303220302 76
    0x1032410309110401c50000c402c40200c40b15810360010f0300340854070100394010b00d0800039103201d10001503407156500300300030aa0350f4600c9078030b41218080009102080c4650010310749080b014046442c22260600c20030198407181c010640b0f810005510780100b8134040c0148a12059a00000e10081c2041a180034001801600030420302035070f003120404210301442c60000d120125514070262550701d0602400020742509507130b900c00c1c82e11002841d0701c1e030144200b500340c94040e5105402d1104e000240039400e00c80789608002d003d8244510030340740c3d84449050300554495400b40c0800e400480d00c2c181ea80b030181f115241040508a006000282c0c0081540d61080c01c003c0c21040209880c00443c40c0d030300e420540c40d50180900030000c0342c103610b0780e000080c2c0e146140710100308466500c05501d4503000e10340a00c400003c403d40101d40418076040b06480012402001442104203684e5482d04e1940151f0040c400f47c0c201008001d403046014145610380d80c0100c1c81c4100d148026a0000e4071500341 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 563140746 1250 563139496 563139503
    0x10b030f0625090e1e1f03080f09030a0809100813150e0613031e091403011d1515060306090a020d0f02040807060207031a0601020c150a03140601050403 67
    0x456204181c0c1c51240a0b01c40007481c80150b91852070a03c1400d1100152088158a24216030f0402040256a103082e990220300b861ba00889850350640d41e03022840d50001110f8206503200744400004c1c2e58042c44021041d42c46280d01c155035101d1001481080c0344074a007034105218480003080135011882c00410b40c07042e4480a40502c55080c41d00403401010402c00d1408075100f5502007014554407001e200b80c00e03034043e80311031000c064540030041c030403a0841da0810000d1403a181c00c1056220a1402444c0140010008a1203181e1048584202d00d1100b1b0120480d0f0b1182d2030741d07803210007848455034112607500308000729188c41c2404907101d4400900204d000d1224400001c00c0d55a865040d40c022285104c1e00744000300c04c1e845d0080103500280038220250203400390003c0c10034000240c0c0d000701ca510040c07103601c2640248a070b2075255001448541540503240d045815035a610300601400c120501d402a140c00c08990014100e504000c220a0405295400d01070380d030380c02909a03001c0b80d52 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 563141996 1250 563140746 563140801
    0x1b010612080316120c0804020a150212030a23010303081b0304031101060503060c1c06050d17070b070909050601360503060403020703140120030a1508010b030f06 71
    0x100c01c0f0003241c00381681d0100b072001918110070741070300c80da01806240c022070003211852880350310b030072103d403211034150500c00250340512101b008501c0001c1c01b640c1e0080e020b5400068034032890000a00399030402c040d00c52540620001801015007000130360b40c0102481c01402e8854050604112a03840042d002400380300617416840400c2400f500950054040503003079480314101154103105580025108128058107120300312465a828801c800489200a101d0b088011a540300c0d06010007520860140c000800c100c1500806c8801d40c0e100c0c0141040d540c2c481009191025100803148040d190904012280d070b1196900c1003600c0b07160468000c00348100300400c40001904002d0a0b80ba8005501801400108030130300d0780100c1e050701180d0080d600121032003020b14425003228400d40c8401185440e00200a40d242214806140e219a44040010709010303104204034a00c5079541c4160740c1c0369140e03017515003181024400070342c00902c40c0c0c008142a0600030b00c1c6044008003003c54121020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 563143246 1250 563141996 563142031
    0x11a1206040902130c030f1a0a0605030613060f1a07030f08130b0405010b0901050a18021c090f050c060f0304060e070312052502030607110f031b0106120803 69
    0x6a6000703031030400394024101004801c4405c030002c0d0281580703501d4019254034148080b11110702c44031081c11103a0300204607441d4107051590a603100c0d04040c04113a0030104101c20480007500502c540f1024003100341c004491140707807094100003140c0c00a0314014054050192000182c0c2082d1b100c03c0d03060440c24400340300d03501c051040c9032075518014060300615900c0e052106024040d4030009040c041036641c036510781c1e264000d21803984030900c21458103002c10110700301911502d84c0581141c02c0403d41041000200c0c240c0f1a0544e0070181064800c0d014682d0b0f1a003c00000700101e20700800d00b0303a8841c1c1030542c1c44070500c24a00004001030441d81c0c4810880c5218942406040044c6510034404d15a4186415005010342c004104558104401d560340700f43c9450150119450554000d0040c83d017903958290403030b44c2440072980003a282c4a03006003200c9040c000d1000e004101c1094040700e2103e00d20640c0715003903403d65805100106081c088840114002108680d0b1010b0002082e60224 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 563144496 1250 563143246 563143249
    0xa0311010807030e160326030403120b18100e061c0f05060c12130206071b0f06052701020d050f0d0617010e2a0303040503010207030206011a1206040902 67
    0x20240302c2c03150070340ca001e400c0302e05d1001d080c4041480c05032401001d60310000e03402038440740444012072070b01b2090050103000003000244206176003400070401d00b0b4040741d41c00a2001180750b00b03091805c07142070400c0503020440d2a0440030103807402016090140d0000781000e0001c100e011542c0354446071076046195410041c401c0b1036a242035840c0e4042e084421504c3c10905020703544e000000d0400400040b4000f007034103840464900c03403000307400038007180c5004a280c4d140c00e603004d9092045050328410010029084a141c00325400500c4651200c2d1f60310580a220040289070000f4640304415a00c41c02c1041668009204510400b050a05030b68885080c04034552a01602015035980b605210021409010f640a0349c111207002000901440c03c14009842c1c81c0c0c0c2241da20140360700b200740040607007240c00218800003e50040c00b901e103055100c10101342aa848101c06802607480340004001c0824910340448c0440040d440302030400c0c80d41d40040300d5408001c1d25842c46682c440c40d428003903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 563145746 1250 563144496 563144501
    0xd06051f0816020717030712020109080904090f061a030d090312050307050d020c07031202012d0e0a0503031806011a0a05040b0a080403020105060a05090f0a0b060d0e06060a031101080703 82
    0x5041c034045c104a820042d42c800c2e83d540d9001500460b40e980f010708101041600500031214802d03886030380641400800d40c240310003003085c042c056544854203e10070000c68410310034210400701d45110900c40300c0c90388050510b0310340344004000c100003003c0d0041020810303083e070042a10095260040e0780c1c9d01c8441e02100c86d8020502454202840041d0b09400d03000006103007800c880c030a00b050920f40a240d4002e030708072424406040c0b020002d00f14420800c0e401d45440048400004c00002140240180ea0601c2c0c00852002218568000828000440340c040c0f040403811040700000c00480d81000004160320403131400304000c0d0079000c07400b020414064401c1e1030191003107000180d00c0c0c00440c003004002d00b01c00d46098000d5480d1030b01194203410042c6095054400107090389886482d403455203101c004000740211403440d6500324a80c1e507175542c1c0c1c0c010951040c1c00000803e250103620703202030a00b000504107620820b181c0104000242c807035000c140d01c082003401c0030566592184d006802 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 563146996 1250 563145746 563145749
    0x60204030c0623030c0a0c020316030c0503060a0c020d031a09040605070906030623031e0d0906030510030b09070806010801021314031f0f020d06051f08160207 70
    0x3070401d56020400c0d0b41d1090040d001000e1009181c0c0c0540b00c01c0b801c01100303200c107603000e58448070300b04191810036003d01d80c0c6058151010f011074002115203550b110518959030011210540c07001c10800ca14507041001503004046800d04008565001802079500d1b04a00122000d040c0c86061011800300340e140c00c07030542d01000c0d140e203507940f929240850003400212184808039a0254021459502c40d10a041c2660070785010030b4040c00901d42c0e05461410700902c582c1d4103104806400400c2a0440b8111041c40c0c807050051410b400b000c5005080002a6081502010701e400304100300b03016003814000449802030782d010450f454150fa034074100000b0340c020b5102480b40c3d0000050f800340550003404a91240894800162b03107801c05010303141000c0e41403a5040d48800c5520000c0441e907030440c0401d17912114001070500c14040c004003640c00c4440824603003541d4600c1000641860138141113036000c00c086521f6810003422002d40900409002920a04d02c0503410004c100c0c020030000f070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 563148246 1250 563146996 563147003
    0xa12050c13020d05180601060309082502030709110f2a0d030c1704080307090306090309030b0a0b03070e06030f06010f0602070e0115050f160615050f0a0306020706020403 75
    0x500c0e0208841c000301075031100059001e00c6181c01c0010303081e0b15890710107403070700708a01d0003a1401d81d107840c104402801480400391100300c0100709400b80003c2c04454200700109100068184c0d0f4042d004250034040d243e880390b075107a41006040b00301c500b451001c072101c07050a610b100c1e440d00000b03042c40340c21140c03491350380d08201c201401400c401c0c1c80001e00305401c0d400c156003d00c0805203d0700c048441c030260041c1c0d2001d2520000101d00001e8101014651110240c54a0246a580c13074a4500507102c0420301640071804044c0284180f1008100c0e03142d015070060024000d826510b0042559400d861007917005060003100403400c5540c0500c50300140d00304074401c850300c9585422072125910000d00c55030700035200c0c030303003002034855601d8060303e040b07412040300d020814041c2d050599140d8005401010243c4003003050b0b4400c41c0100c00c1e40340e4070b80d01488001401010051914116200a80100c0d1041141d49400c103c0c56581c082d4031010340750b106c50056207900389840d004010740105d81004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 563149496 1250 563148246 563148259
    0xb0f1e010b07080409152103021b01022e110c030711040b1e04180305040e191a030c061603050711040e0a031d0a03020105071434050a12050c 62
    0xb901b0741c4031180555041e03d0001d0000c1503201c544e0038618841f40800b40c0001c0c09a00302242c00120760404a05203001c042d4180103a030320503000b80340502d500d50303112800604212808502c80304c6c0c00005201d120300d5094801d00042c5414409075210780d4031f005aa030000c02050007013243c580103490344e400c0501201c001600d403c001042c100000003140c007003909003a011300d140c503403204a41c0c050401340c949203c0d010f03140d4916040c201000e010070f0b180f000f0482c4011029040a460122020b0f100d0390045982007094138040c2c6d8101020141090a850089403140d40305008904140c4c0b65100105d04903a4103041c4550b0382ca200b032500d81000a808050640c0c8285000980c682d81d806c046501c00081e03119035035405082c0c0c5401c41801c1d164505041054006803d84410301c0154080c40c024005a0300645503440846802e148292411082c1c0b824034660307a0803910400c000c0042c0b803212201c0400d1000c44c801c1d9a03030901000c5103a2a4041c401c1268412904d200c01e001d100c018007003c1082c84014001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 563150746 1250 563149496 563149511
    0x60a03020904060b0306130302011125052103041a1009020903100c081b0c0a030305091e0f0d0207030b0a051815010e060306040c05100e0a030b0f1e010b07080409 71
    0x151f509040340c040c415030140d402c18899900c03950060085400280d04c13488070091000c07078803241d035280d0741c50000704503014480d1524071150b01002d8040c14082c0d200300100707256070307160610b0010200b00300c05841e400480c0c00780e400d11108400b603c281c4020390303070891130068036000c1410000380703072003000e00422201c00d141444100015901c61446403060801c600c2d10300780101c412043d00700510411055a07029002400d021000a2090300001d07004014001111455138241200c401c2d03001300040f040c2001c0c2d11901c1c01c0c60846c0c0c41030040010441c4140040d182661035901c03141c410001c002c0240c92040e5940780001c41803908c41142c0710180c0785500c00c44000d074800440f05001c12100780280c29a2088050004030309150000c0d150344956031210091000910b41f0050094803020b4201c3c007018440e1030000e424403501e410003030f0b00c015401141d408540e070504032802e21030500060186c00b007852100300c98807603c141c01c126442c11500c0c0b1340e200c1640d40440d803e15a105005607001000c86900740101c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 563151996 1250 563150746 563150761
    0x11040c140928080607020a03120908091807090b071104090c080706090509010b09010c060c0509060c151303081803040b03011806050f01090506400608060a03020904060b0306 76
    0x2e01c002e44590500322402c1e85c80d8120240d03036076002000700034001015200c000205800e941c0010b4400ca100310701184c1030680c40c20000c0c250b0100c8940d100300089600081080c41a44061000010306401c1d4545141c070640f5180c3d0382c001c03420800d845004a48039003408041040c0e13081040003d00e2204140e500580d1945070040101d105803045900c201480ea002007030032142481180e00701c4c00143c40b0040030f044645c0d955805055130f0301c0080c2c144801070003403400d030b07803510001861a420508003408030703025801152001200007070519008000921884800260400c0c3c815401407204d070405021021803021162072740c45076800c01c0652650201c0002001801450101116030790804c0078460140c8500520002c100c1c0c810801e4000758440c2e00801050800304002c00d0702101e0904a4034074900c001640e803100c110b0644140c407031500c88200080382c1c001c070000000e0141c2444e28003681107042030f1001507a0380b0114000a482190300d4400300302044a80e0f4410045580050240d500c9854030700d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 563153246 1250 563151996 563152069
    0x1e0405070b28050415080a1e0204050a0e010b09060313050a03030902100c11220203010b0a1715120f0a0506010810061206021c020f030411040c1409 65
    0x44040c01054002c140c2c2e0070340c180a0000e44042c0c41c8405072907900070031a101c0c12100744101924003056643d4170300c518141003444c42485414040e09100140e81c80385410280510440e840d0300c422407600681005008103883d8008490250204946d583c0c2c5a4440359032000601e00b07803a000034141d20a0018880415800d40c10400740e25000315100d1410415030340d4240c3c5e03400e02035140201071110701030307803c034091a0000404040d01c034000c0c0c80f050302642c080915422030313100380c0140600202c0462950030150b07002102c003079080c0304154004124241040c1c40480b0940d104201032040a14111150002804004064404694600b1501203503102d051443d2200400c2c014104c1d280103a2820900d070b00080d000350401c850b8590a40440b800d00398481e18001d400004641d045664506d02e5615074200b18005040d0900350f900c107896a0341458036005a401446024481c0070754208034a20750004c2e000b0000b650919902c040e084e695003016000100c100c100b209910042c401d120400001901c220f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 563154496 1250 563153246 563153287
    0x60c03160f021c030e150d050903090307050a0b12040f02041e051e011202010c12050d0f0509100e011e09020f010309051f0f0e0a1a1e0405070b 63
    0x703445060400c004500c800c9828203d958028012491103040060346081c02c8418081d407030010542c40c3e04104102c01c0304800e855027900c1200260303101181c4103c45242c14001c06e801018129191321510b8a030034070202c018011503407004041840d18000a0500c0b4203d181d100d001d55005004000c00600c2c04031200b4400b2150003440113491900c030020700400c0f09031100b018800101000104160718001088044850740d1008904000308440b0000000344541402d544c00c1000342c03642920341040c031008601702c1302c0d07040074001c00d80d080205200d0141c0c8040b8000c1813001c180d080125400c0000320b002409131107407005100031054903a025000b0400d0551050446034421141c0440c20066100114103480b5a0136016006400c40e2001d05000116800007584440846401183c00141840710a044a429450500740c981040544804000700301c4007048590b000721600ca1054104130b80340c4da040200c404c1420305009845c2c0301141c04d02c01e041141c8030040502c5410244d485001c281502e5421015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 563155746 1250 563154496 563154499
    0xe0402120703110310120203030d020310080f0a0b010e090705060313020a0e09030a0518030601030c05030d030c1b021f0e0310020304110402030703150b0a1209050c060c03160f02 78
    0x80c44403c800c800440d00840740602203a40b80d10100f42d080180e0005800001101280c1c07510042001e010120f0359400654030481018030340915a17484d0428042c200148041d0071080358122007030a1000401d00c407841410344402058101d150782d1102401480e0201c10f03002980d024001204000c100c00c0c42210000c40b0300d100703032282c14607180d8500102a54500c20b985c42d51080c0c1003400041c1856205201502900078502690701404607102c01190601d18203070810b8800b44a0020240854101000703e91600101c614040142011542008040c10b20031601c0c0c0905c0f01e4681c1d0760105540e901500d0001d1070710b04811181c05414200c401602480003c1e586900900680c0103803201d0714124400c3e6032145412180e46100b883d250b500700b100950005101070185030f649d6144044403900541100050300005600f5036841000d0640a01000352280426244078100064140010350100c0e503001004c0c000e449442c4c0798540c0400050450149110014554105400c80b5003441100605820b84a00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 563156996 1250 563155746 563155751
    0x3080711070e270a06020a09030b01060c060c0c02090c1c0f0f06060203030702031c060e090c0a080d0e060703110f010903170105011b050f1209040c0206060915010e0402120703 77
    0x800f41040401150760074120320980c00814001000c200c440d00100f12a5015240148919890b580d4020b00d2110a80210000a02020711032040009a02c01c590404495042810600086600050724040000c1480c0c1d4844070200d203c140b040d1080c080640e680c4002da800303004203440e0191000080c4402c1d9038407001e8908203800010028004002c0724010242503000c0d5191140010302c94070051300404e0100b549a03070358070000451040300254035004130000400340445401440070005141003e410805150f0400d07101e813000747c1e421081045201c0c40c20342e142516200c440c02c0690340f03441d07003e00d6606d035070107480e281016149040d40004041442600e41c0d88208044400c0101c114109018050210b0085824295010000a0001c40e400d110324100d0b2582001d050b20641000d001d8107511034401000301d10801e45142034018038462070882c0c4024556445d0007400105100c030051303c0702d281e1100325aa09a2640d100d00c00031400c5200c043c200307540d15403495210340c610740001c0b039260380041c3c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 563158246 1250 563156996 563157031
    0x90a030b0906130c090b060f030c0702010908030a020c0f060706090302070e1e01121b1d091203060d110306130302060a060b09010e030c15091c0b0403080711070e 71
    0xd0400c418070f4036040010f075201203040c00703440300c0200440500180d1140d4184803144072040010b0045205100c01d03092162602c40c0d610000d0003610312900700a00e50b404c284000788059500050300f000c1120300f141c5001100400074040341091040240140c4101e06020282c0103240d00001c007041191107030031712041590780d0003080039514519807004402110801c001008400071b4850700640142c01703000700004c50044010300c03904081c0c8903400700e00d64441743d40c0d04004241005600650181804018240ca514000101201440001d10542c81904841d110205000d101040b282a0307a2024088441a042c400e01d0700e10010000d4070b088006210720705c002081d550300e6000e00760403210820740e1346061400d00d8005407006600800c085800d03100e20480700700c49586011a42c144e102c811110980d440381c181003405490014250007042c041001042c890019240b4901e040c2e02540601e806181e43d21146000c80f15440142e0700e244a61081d60f4010a442050100141c020701c0d00030707200e20311503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 563159496 1250 563158246 563158261
    0xc080307050306360601051b060106110a080301030807080c010203070305193e182404090c050d090606080607170a0f33121115090a030b0906 62
    0x14131056482c0f00714503050040d41038010000b0419150405414140036042c051003e000c14401c07118014a01016031118004002d40c1350401d00260b02c85110f140582914a4640c881001610040c03000074a50400080c14400340721403402038801404405c8002e650f6400c080000a020303001c00d86034001d1103050984a0b407004c01c407038031070030443c0c40e0b005840d5039400300d640b03a00b105103007251644081c1005d280c0d03050f080c420b41100010481301100c8a03458605803040420302c00c0b0510010440c401c4801c00b0804541500920760583d012119a0b4901268140703090344221a1400b5240c01d005040d800e010000701080ba281e00244c007580c0003c001c03900d030344d520510100c81c512002207280c60210660004640d4400d074503040307001003405448000c0b41e04086841030549540c0400981801142c034001141e02e0f10b42ca00d43c0d02c02c01803200c0031720024644a07a440b40d2403403071000040113100b0136601241900f5041050309440840c0001092041030329660b0804440c11302c1c003104c1d421aa03004d04070004400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 563160746 1250 563159496 563159539
    0x1b1e1308011415030a060b01120e03070b1b1b07150305090d03020a0e042a050d05010b040501140a0c0c152a0f080d060b0c0f0f0d030c0c080307050306 66
    0x145080180180701085c1a07458000003007010f540c2c41c9040242110751f403e45c05000f405000b0030781588600960380c54590341000b403107410024001c22880b1881041400307480d0002030039a22002e9003102c202c5009102000740074030741902c580c459001143e00080c071651003034240d885a4840c01b442c00a031401c642ea0075404508034403500c070948012504000c80c000260820342d000140c442000107000910b209940040f80c2000c0b040006100060320028905070500400d000c1d450042078401c04c82d40c20300c1c0c20709001916010302c40b5410140c4441c0454405940c42c030922004541f1070300b1009050350340c0d488046aa40c08010030b41c007500800c4080048004404118141d07158218103003568500c503034010f9681030801602100142c1e003020b8103000e6225080c4440c0b00e04c200506c442c28446031340360541000141411500b17030380350025400510800c021050042110400c3c044e8924000403640481042961081100d80020b40042c1002c000c02019580000045015038411621411401c4501580109 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 563161996 1250 563160746 563160781
    0xd0c020f0907050436052406040303032c0304080106060806130902030f010c0306051806011d061b07140603010b04050d0f06050405070e1b1e13080114 66
    0x44040008020411800c2116010090b026041d8442400d441c0540c942c3c5e840c42202c0c895099942d98140f12001041210b01c00700400d0724003200700d416a440d070000d440c6010314030000d0185038035000d1070b00d10311a01809045a07203807907190100081c4c2c04903001075602d81080c0a0148650f20700800030513618040c1074000d01c650002046582c0201d55000031b43d01401f41804100d0f0148070f000c0e10741442c8442801100810310729581d0004d1607038034240c00c00038564400909074400e41740d48002d210090740c0c01405c185411201135241c000c402e0103500480d00d20311070002d2146110184411404040300d003c2a217000b104c1c005136030210000904410480a031000f8451034142d01d0702084200040d0500c07010722814980071b140e80c4241d407a4aa22910b0940384110350888482d00b01000900c80c81d81c00c00c140b990022070715400b41400044000201c800c034810344d095691240c0c01c0c1600d100c41403904908503101c1c000914005220701e41e640d44070328040c10f0401440c480402c00b110005031705080801c2d03c0d02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 563163246 1250 563161996 563162011
    0x6090a05122a031917010e040201020319140c070f06090b070f03020304030605090a0c06020d0203090d0c24020d0302120f0a111306020f010e060c030901020403050d0c020f09 76
    0x4014202c00480c0c14982c0c40003201d25001c2d000c10310036111800c55812124002c030200f41c55100001030003240340b07600060705030405281c14030050b05000242c0da001003924034650030407801890311000340c50240c40074420780030304007001800003c00008040d00411210304490307940544041a41c0c071000d0513240b0000c0f6008102103e9000d02c1400082582180c0205046000c5d0065030702d000d4885d00e0783c2c01901c500302da0350401d5034001c01e2000b0401400310130283c01401c091000e002c501003007540003034036446189003651103103041044180920152100100040512054082c0d113441e407400c0c221280c141d0040e0b02000340c05415500a040c90190080340e4581300141c55410281d583c0c540307010081d14001d0207480742c103640d40c41746400c20448c001c01894540807610440c00600d181090003132030f041c0b0040c0d0b418002c0c0d042101c40b013030984001031410742041301181c50365280d9940454a500900842e400504248940c40d4101c01054000c0100700403180250350a0708540902e01c1130000030f4405640f0034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 563164496 1250 563163246 563163277
    0x30705160e0420090112030f0f0504090e01110a0801050907080103050d0809160305030d0b0609090a110705100507080106170f07030b150a170106020604170c06090a0512 74
    0x1a00207464100303c2c0305522409810f07400e01c0d0034003802103200c40009030080d40b0482c0704a11060709042d040303078841121a6051402e400e8100036041c00a04502541c42048103050312980c09084c11202034011685010f5100502d0fa01c4800700701700100009002c0c821140590b107181e0105074150700c0340c1c6189040e41d07003040050400c0001440102c0f00c0c030710700401c1c5007041d00865042c00e03001c05542d00580015070041e0300550725222a022410101e81c842608180300d000c0801c10350302c1507143d510402d54004040d00c0002900c0c4442d86401d43c040c42040300042007409041481920f00c207007540300301c1c007960050707940214587c1c880100b5518a9001c0384201c240c1030030000010600300ca00d10350301d581b000c103900d401708200103040d02003404590021000b1611030b1001c41e100014035800441c4070380c1d061b4a907500d685030754944400a500c0d41e00162000d4564004c1c05d01c884103e440041c101d0303003c400854100e6005242c40c0300d64a032600c190804c11120ba026003048100020900c0050301d801c141419683c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 563165746 1250 563164496 563164501
    0xf0f010c150902100f050f16080a09030605060d0c030602070204020f040e07031808090d0809131a03070303080123060301060503060f1f20010e0d0e0406060e12150702030705160e 78
    0x1f10613450f044207580301d024101007002d00700022681406802c0c414002d8446501c0c072400c500d40718003680d40c0284850f001d11041100307180800c00b814116130840390011001a5030f541c503400400c019101d1408400d280940006000412840e00144903201d89041c1d0b030204800170103524810900c20705580090a82032050108100070f141490f1304c2984588245400b078a012407400100c1c1803c4a03110040082c00d658664042030204003880708041031200704c028002841c11a580940741d054180110aa413801603012860f5008402c0c007091f595043c002c065544940e9908001016503100b1034885001c3e40c031403c0c03104580e0a044c0c1c105101880c49000c0c46111b030413842421070341e04a0116510280d40401c10250703068507030070b100e40d0132001600070140c1049902058058207400c0d1081c10180101e02d0301c1810001d080c0d000c8400903040508445400041d41000701040c98140d04118030803003c800c40e024409190340000082c14024803800c2501c238042a850030b55125403c10348103094807540318200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 563166996 1250 563165746 563165767
    0x504020d021309120201020705120a2f071202030c0f1e040f14061002060c0a0f0507020901090c09050406080304050409020d050a030216080c0f0f010c150902100f05 72
    0x41441032254201c0d000280741516032118040025130b640b03180b0140c1d60002d018018400c042c0a10320300a43c2000c0701d02e01d40400311030001c1915421000c070003001c0b050a5a090301154001e11807807980d41c24001103418084d214000c0a0b0988603510040b88644220501244142000312090601c41d0b002001d94804e030940c1585070108826031300b200b1390300c04d50b1000d038505070105900c1410302c25030178840c001071039290207420300c550f03c0c2401c00e95600703640c010b80422103140d03003400888003200c40c14a0009420010304909a80074010045c0003980158103000120340c4041303603030108240f81d120b0b54460301c40d582d680050100319030050140004070b800410040c4000d050542145103c03501c06002c3c04401c2c1000e48501e41440780c209011001a0460312440f103a000c0103912440c007078400c0d40040c0c00d40591500c002029100c02c148014011011900b80c45034681c091441000002c0d04040003640031160900c0c0704d03004000040c41203200700b107551100e040852042511071041c41e000e46503180380c8030320a0f1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 563168246 1250 563166996 563167009
    0x90e0a02010513031401021e03043809060907090905120a11100209030607030e150606040810090c0b0901050406111c0e01020708060c0702010c051002030702031201090504020d02 78
    0x19112040079200f010002c00105290740141819400000060701c8400a03030700500200c850007603024114000340284008151003061200c200340c18203e139488030410305d41651040e40c4c000314901001340345040801401c6203021603000e2042d0171182c01d6800c0540c17107409080440e2900c1101034000d50003403000c112030312140001001c03c1101030608000740d10000701d07140d01d800e8450b9000e01c0002d8003c20b910f5460f0808000581c0c1001d5503040600402c9100c00105698041c0c44496001100d0f0700b034042a00e913243d03a03007114003908a410030303641c8244501e01100054440400c088078400c201401c000f60081c14141555014a01655080d01d840e140c001e044440203023035296070003280100d00c40d084d14105880d40c1c0f4800b090860f01c6451903408503100181c00c00d0580d40c42203400c0d40100341001040403a060843c1c000ca60309081180c011541820018035040b454114601144c1c400410b100410b50000041c0c440c801c429540301103142c2c1c0325940c0d181950000c1da002034104400100c0c0c0c41c010318010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 563169496 1250 563168246 563168257
    0x90703080d0605041506260a1a060c010b0f03010e060601050a090f0315141b0a020f0a0b040b0c04150302090409060507030e0c03070510081f1e090e0a020105 69
    0x410707001c00c425840f440094110b801c3c0d2096040c00c610f40240403c8007a8214005003100c561000741c0f81c01c5002011703085d20100c68000c1c152140e00380e845010041d10b80c0c05d07104c5814003100180c0401d441d600c01c00c01050090880c0c1c4280c500c141c9040850b11100c0c03030705000b000c07000301010380a003906496800054907280c000c49002018052101008a250140302070782d40004d501444000d03414a020070030ba02c046070070440d100d08242c802e0504020628002c62825510400d405209550b504181e1f0412818180c84061602e82c5000d04614a000e00c80d030a208240a6406108441440d450309030310f0701800d100d284120300c8090031540b451b81c1c08038040c0d40a4000c401d405003020842d61070640d01c440450f80112f6241c40402d654480c40f20703d180b81080119524003003580101509402c1c0b0000648103051148507130200300a400000306c8400c10000318000b0442a42403107107141e600c50940c1c1d2000e0010f0004642040d14500001810540301c0c02500c009907424030180159121a400441d01ea030b020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 563170746 1250 563169496 563169517
    0xf0c0f0f09091e021203180a060e01021f02040302040504143d0908190f0203070b150a05030a05030702040b1e12010e10140901050105060d05040f1a06090c0309070308 73
    0x1100c10b174840d0030f10050248000d041510700511200004020404a01c0c1d000a410090709003031482890740c0000e5000f000010200f4410113100060845101030303c255040203401034205002d100400c0758004105e4003000d00c90b41a204190a44106500e00210000c41003500c80102e00c41211580307980009122640c2c2101d60200d0b0a01d440e0716008182c0d8003000e070f00b010503401204450003280e84464038180c2c1c45403610186180c00101d8440341d401140160034080c506a03404800c01103569030441210040801505884201c1e069060a60312504004001c3e030286007000c8400a07186488804424102c00d450309080102d184001841484511100d200c5c00b40e45d80c1d21a10354050782c08120000743c0080303090011130160040040c029107820041c0c400d4030568141401409141d0300d52050700c05c0103a21501c0002c80750b9403070070552074880c618103018000001c084000076920502d003285034413800f015112644103440340c40c01c1684074801183c1d01e0206400402c01400000c010f02d0090500800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 563171996 1250 563170746 563170759
    0x30303020a0c0c06170c040602101a1504090f05040b071101090c0b09041b0206041403041d01082406011124091902030c0103090f0c0f0f09091e02 64
    0xd0a90325a40a403c20380c104001080d01c580d00c0400780000c814005600080580c0c0c501e0429103082d40181d9520810219010b8880c2c41d4040c030880c1c0e01480603030407601140240166806444800c00340c00303d52042c02070510260805944000070341c40c46c000c00380216801070b071b40350480da203400c0101c41c0c1144c0500c00240c503548030a000d001041b0b04100c2400038000080b600b41d694105181003204484c0301c04029401d04010380901d0b14241d4000c154070794070542100c401e20105500784485130a5115a80008281501040c226410036200c01d8a41c2d05803410134041310b4440c06c2c1341c010600344036aa041c4041d100503032040083d0545d44201115981b80d50950104d500700b044081d240d1548001100b0b8442004a0031002c001d90010208140044080c41140e0401c040f64503401103521000206484c605064480d45c5445c01c0100d5400080341254000528195098586420340c180074054801d013504440305a502041041c0544203016000d40e11480321008080640310907141800c1703194069a0054 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 563173246 1250 563171996 563172017
    0x6150603070f0302191e0c0b0601141b0a1101020309033403050c2119080d1d010b060f18060c0604080403021e090f0a24051810030303020a 61
    0x1511410031700c540301c42e64a5a40c0284c0c081000e41100001e00c904000c1041445051035010a0020214640025080c60101402c03402000e01c00e0052080c1444440c074840340403216094040003107260500e040c072541c40b1031103c1d007042004a99902460450b503a040c2c12410b01092807168001044c0a00241a4a042400e0518004822140c1c038660300c1620f540d009180c01c0310720742c03400100d860000300e40c07503502c800b41140f1100001d075585040b44064070415001038004040c070000c2001d680340b00101c124240301c1e03640300701e0401d10030001e0003501e04111340c03c044601c2458502142510064001083e0030350400c0e84941c1c100300c00003d81d040c5a03400000400c18080026020702c08288902c3c0140e196a580d246544144078403001080000c10340111041d01d07503000c554940c024030ba00490740f4000c1e20102d071030798240303031009010414050401a1000c1c0b01d5a00c940c1020410b08101d503c2200e111490001c0284980c001000403151807006130340410007070001034001d43c051302a043c024170f0107443d0780 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 563174496 1250 563173246 563173267
    0x306180d111c171b0403080d06121112030406050706020f07230c0f060a1211040f09050f0103020607030f050f07081803010b0901051c02030303070f0206150603070f0302 74
    0x40d00c15800038000582c0d800a0381500d0075030f4000d001e820002c060140c010078000b10300341e60603901071408020644c1d03130001046100c840503a0415005000004030f5030183c46494036010968203540300400d40603140a92510b0030048010041c0c4003164a1038540f41d1412101d0303070720140294416031b0310b600d41440c14082e01c0c0108800062540c02d240240803e00c00c0716950500d031a01d09400c00303402c0e5100c2e400d0803040c121345031108000e039070302c20040b4100850038000308010000500240c01d01c014a41801240c00a0b4403500040000d084a40300701741080b030385d00c1d901d5648500307140901010350016410001140083c0c810881540c0d200703007520745141401c202408210181d8002e04c803c0e1510300b00820441c0741d5140520315200080000ca00810680d51402c0c08202c1e484014481d061003010905004d00c1c500c646048074218845e4001d050300d95030714008034041c0c1200c3c0c6070f80c1c20b100180720b600d0005020900102a4800c0180000c00c0c09003580c0c0c990030100d07280140c1d41d0110b001c00d07409001c2440103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 563175746 1250 563174496 563174533
    0x50f07060e060c120c03041701050103020a05040e030d0f020a030e0105040b0708040c0f091406031605130f110703080c0a0c0602030703020d020a090513090b01030b1305060112020306180d11 83
    0x2441e030780c030007865585150182600303011503c8e01180d613190b490000108016502c07070b11180216001074402041107a18036262508502844001c840710b070b401c00717182100803400c0d54000d140c5d00130640c904120100482e000182201c20403200100248440c4011810aa0040440503400b910881c0b00c1c0d20400c0c1c40ba01143c01c0100d2592140903419100c102d1200021400d0031a90760045065005102c03100003030b405004012028032401e8042c403c2210040302c403100700c0e00181c641c001100404d002a8800803422070711a800500c0540015001001241034603c0c0304044459400c40380e5a030300390406042d281d041c0290300141c2040181076081210282046084c000f40104401c00d031a06d03080c162600042c803505003c192000f0381c1c0c0c80d19000c1a8400910900c00443c19617801c145138403421b03503038000812090490303e41c0c00340070b52184500015a40d600c011188070f200e0300c26000c0d6005074880b680d110f0501150801d0154441d0040503c4413412440b580c405024410004101d5884650781c10500c02e6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 563176996 1250 563175746 563175757
    0x909140613060302180103060f0203090a060b010201020f13090c05070b0f07170106030f110c121312050610090b21150703020405010306050a031a072a050f07060e060c12 74
    0x180c02507405e0042080c0005441080c0c0e03500d180100952a600d0700c5001503032035100001000340030790f07522281000e03c0c0c2d00c00d5041c2c1c0ca0300071089113469612040035400350001107691041c8003400c1d08080041c40c0084c401c03001e881145511483d0801796440d2000d0f0100b4942c0300801000800c038004000d0302d40e0703d5449003218000c06541e14000345002c080882c0c1d10a0b0b9410101da04213500040004850f1b90a00107102c0c46140c5104156984504003500352044000700c5a000c1c9a04000030751411090060203e4468042e40d0002009410544e44442e542e0540388000e801c81d6002c0b003c01c1200c40c2401c52041e44148034492071040e205e0760307a01c01246c070380c001e4015155080080d41c0800d00b4845542c061040e030028141c125100010780d1304e03640d641980c8450507036004d4035403c03118000c40c5569004a80c1400030034007c3c6080e124107002000744451011120400303803064842c0c124a50790420002c12008240c50180e51180d10520002e000d01400394014444851a0302c42d2003941195000c14401602 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 563178246 1250 563176996 563177029
    0x620151b0f0f09130c020c06131701061806030c0302100c02130b1207030203060103080f07080a02011a0f030601050126010806011e0b0a140d0509010506010909140613060302 76
    0x2500d0b103005030b050000c0e8282c03001e03004d1002890140302d600344540000e800c00c2124400c59400b69035250340100b15200328115445020007a4010445052804040d0048025a048482800f884102e0b0700040c5080d02c4842c400580048040380c4240003500b06031190490101280c2001203504456901080c1002eaa41c00c1c100781d4240d641050840358035001400ea8030310004040146045419070300003903118078040c44018200b8400082c521a018074800550b500785410031079940d21401c002401a01920790100038580d1284034400801c8245005886c0100c2c48001500410582c1e080100650780441c003400c3c5e95500541000c14030340c51300341c101c141c50701900c07502d005000154500030180035600800900d2031040a4100c009000780c503952015243c6441c400c0c50107201d0a820150701250301d01c151a0918211414041046080401500620b004040a0380c0350074600d030b62415036404035403c0740104a0355107101e40c041165032801b040c4510f89580500000184c260b0341c2d9002910302c104052699 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 563179496 1250 563178246 563178277
    0x204090204060e1f0b040e13020d15091518150f0905010905010608030309030a0f0e0d06020309060721020706060e0f0403080c04300b010620151b0f 65
    0x641002c0e0394020100c004001c0145c070f00d0304081c204400c1c070f10f40090081000e016814030031042d6080d50b45101810001503000000d03600c0c03154034030038503402418600368250340401642454019030bc0380341c400c031218001c01544413041d1020540d0b031100700080d4480c02140b07103911200c21104c0c0302030074400e0300c0c441e502c550000154601b03603151103400e4030f550341c0c80341e8904e402c103000300880070343e0100807500240d11520340300c55907688a00050b50070004920b9060742200b91703c007011040207899801540038101034411a20103555051040354290358510f8010650303034041d40904e0919a031500600015441aa00802c01c41e864000d206440c1808654900440c041b550a0105040d0046c0c0300503006807041c803803035140504007031101401405440320b40100e500210958034440c40c4c9a5103605840e94494142c05e800e50b5680d500600c045201743d80000c880c41c10000503850f0503000500005000403c040c481043d40d1980c82051140224140c2d2a840d0101000780342d5482c01d01400400c0d00c840c945419 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 563180746 1250 563179496 563179531
    0x1d091008190212030307091802070b0c0d150b180d050109050c2103090f1309031107091b0315030f0302060f0c070b060907110a140f190204090204060e 66
    0x1000a2501d4403103002203ea0001c0051181c0e1543c401040025034a2180c6240c400300c1e201413408000303106034030000d8038400d4964180b19004800c08010000d0350b840031000d00000034100c000380c480d0007061141c0101000200052250101c41000103a2400c000078600b075002481603d400d402c0d200b58103070450717017a00300720940c81c02442c0039619100411070a1021444a11280301c0079952841002c142038425800c4424000013030396001540c03000000c1203441030113112036515000e071208442d00b030108110b0146840120f186402c501c40c540c40000e9039556940380210704c1409800602c4424140c0d4144020310b6400b101145425100c00f03030b402e1107075008242925001020400200000e0b001609030781003005888003180300c0291080c0c01c54000c0710011a1074441b0401a50404001c001e098601d0290103040e1041c800c011980e559411880b0701a90304403e241800e1a4036200300c0840381340c81140c0b4849000c050f0030181c3c0b15411341840600000f48903600c4200480c2d64180450324800006500c025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 563181996 1250 563180746 563180749
    0x10806150d1b020604030507030e210a02270a050702030f0c0303090105010b0f030708060f150306090f04030c1506090204080307060e061b1608070305070c05011d0910081902 76
    0x2c0e0074030300800b6071020301034030b00f025980180984680e0f03c025040100c0c2e000c00050310760303c104409071041d503041d10b080001c00e602c0c0300b215181c0c5601101a48609258141603030400301302070220442071441916102160b80c0c2c071000c4001040094050800c5220a0040d103000300e5002e4010200b0003480030055499290807198142510b80507040045842c4051005413225220300781a02d0b000202e034280740361303240d484c4004030b910031009a4840381e006400645c600c641807a01c1740150300405043c0c072a1003090f518103201e101304401c10348008000800e941604004606220000c8405844c441008941079580d0381004040ea006504400b08035040001d120341002428400e031a00c01041e04060304051404008141d00e00030403100005010302c001907005003c210060310400c5581d840f241c80d5403140100c0c28000c109800221080761401c50700200881c1642c050314001c029410a01803e080302da0a030020320460001c00f81075003590a0b6103003004940000c0510803041c89500c0c0d0b420fa40440d41c120300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 563183246 1250 563181996 563182031
    0x42601020313050f030915180a06030b0f1207060f030e0601141f05091002101103101205210903070b0901020d03050c0d0915050123030c010e010806150d 67
    0x74045026500c200001e10142c3c0b20301f01e260360720300c0e4510b800c01c0e100d000000400b00c034020024602a84030225120100380710b90940d1200038200f605607802501090102c0600034a400203098504c0154841601040070341d2140312100380700b244500c0e011070800394a001c02c61800c0d1080c1c011400381448043e102c40d8070308060004107012a00c0c010701c80028190108040c0407449030303005242c021603400140f59905802002007001160a8903001c10203030803502d1040a0a81081d0744401c46512050400a20340351107040c3e51000d66080406403100c1d130860599046102c0001b40030300441e510a218000148d5001c3c06141c0041c2020355242d0b5131a501c04000a00b0810301e40400c00505243c042400035086802040d64840510510001500941030909508103881991480d03c45814080046052503405480d03c2410349141011a0440c03281d0341056103c0301443c450a000a03061740c0e100500b503204000042d0007603806400d55000c44003440010406920061540c403800752240c40e0449140c080c0e1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 563184496 1250 563183246 563183263
    0x306090818010e090a2403390b0a0e03100c021603051507140c030901030f06120209100b2209050105090106050d110301061101051b04260102031305 65
    0x91030f089680740100e038000785101034040c11010b43c09660706110000f250301c803400f001d070200c1e01d50313840c0c1c01c416940c0c500381d002c60032030b501c10b03c6c0008600a0045195051040c2c00522407100904a4107010304240c4080403d40041c1031031010060050070108090310103101003c101c00c45100f020031f2444d400c02020307150601c410340301114600020b2081010a0f00802c00540542e540903815599480c0c0c1a422561008000c1c1c11202030940011407201c0c16100000505a9a0f001c0e2814407100d41c008680000311402840740e5841c07962032140c0980103117020854658810549562001c0254072070250041c6a0011445501241c0e1408402a03803c80d0180d0030314002c10300c6000601007907040c60041881c4070030621624040c0140031840000c401101d410000228140503426600e0750381d10781d070040031034000d104c0381c401c42c0d46060040360003610310303929140203180311410040c40d00f4641401c4041503d00024281c186950761b440350a000f0b4820300042d0f010394040003090a13500c1e00c42c10b000c3c2c10000c55 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 563185746 1250 563184496 563184499
    0xd0803060f1e01120219081801060b03010b0c070306060609051309050319020102070f0b16030608060c0a02070b030a0525140a03150303090611030903031905040306090818 75
    0x2101d404640854422062050310030b004e180440441c0d148503000b070040e001b10b000742000c0b500d4111404800320340c040781031442000820545041e080302d0000706400c130350160040c50940c3d4400c0005025907101c0900420084581c201215030071582ca80301c1d001240d2007a040000058400d40c0100420301d8a40501c0e00c842c4800142000444555601c0e03030b41d41d01c24400c40e80c04511014552181d820b000b98195015250407d401144501c5c0516104860040c116041c00464107503c0c070178580a886481088203031681c2c1c00080410b5160309103c40d0090304041c074000c0c110301c200700c030100e14011307141d01442c02504102e5000c1020b0411030b1485906210070313012031a140603812406d20688da48a050401c00c1405c46400703682c4c1d540d0b042400c5000d03140d8203150070000d0848040001c00c15600038182d2084913090b9581c0c403200c19801d20480d807a03200b0761002580c90391041c002c2c400c0f0320304500101402940e03241440d6281c41d590b41e032014141c40200009581c1484042680c0c3c40008184000070f900300320 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 563186996 1250 563185746 563185759
    0x309092401030e1510090203270c010f050903010f02040801020702042301051c0b0f0601030501090603080712090807031a0115051e0409110c0c09010303050d0e0c0d0803060f 76
    0x4841d0f56a503549007100c1041005400700e004144074468034035403400600b20400003951f40749842424018501785540a11700e1110440c841141c00b444042080441140140c2d1184040005160b0843e400d4104109559055580b1354880000b40c0c40351004000400444002503144c060b0b070b00422045030104030402c02c0f09002071030398800c02405400040c0c1952001c480302d01024428032642e59100c0310344d050042103102110b05101c07000c9140c00503240700c0c410903a030900171030380c0399480002034441034403000708415020b1040b040000c84400c2f4031003142e0b62510f41a94100e42e1011000d1130a4520752066850301c10191480341d1440c2c07026181c601410141d0320b034400c5090a01c1005010388148105482100a41c0352040c1c506154541214000c02e09c0880c24008040f641c030511030150302456035031149100d80c036441c0c034460400a107440e04803a0940c45441c10640c44814050140c06c040700c0c880346034001d205000d4001e44e50b2251303580c00e0b03e000f141000d4880ca003560521603800d00c11100703c0e10440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 563188246 1250 563186996 563187011
    0x903030603050705101b06090602160b0105060a170a0f181415062e1107080d08180712060c020d020601080706230d0e070b0f0703030e030909240103 65
    0x6400c03d8075101b00d04806900740802000e141003c1c0d000b8070380160018031032400003400c41c3c0e14050150005822600a4860b2035403640d840c01009500d1080c1400c0034042408035070094002c10360070960a502001410380480c440c1e52054106046910428031000c5501100c05100c09004644410101740804500104212245007000c10501c5200400c0700f440b41040c00019509040086a54400024104103054081c1d803182c2c40503100c1d5180d0b0803070121903c1440700001d01d00c1d0340026281c2aa89540c5c0303410201c1c1d10b540c0c0c40207004400d48111503000384110f85002541d604c03c2e1590031a0107014140c00140c409030010b009040c1007041c6511401c543c8014010310044c0f10210390042103440c14245800c80b40405032444081000003102110102c10105900800049541202540d65080c00544506941b0b400c9201294041c4080c0ea00f20103005002c02ca00081c004e80c08501201405822242080c030140b000400050701181d2a5420008a011203070b04910780c01030001e07542c402400c4c01d02825 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 563189496 1250 563188246 563188279
    0xf030f1a0411090402031c020606030c030c0d03140f0a03020a0807080912030907050d14120711040209010c0b041a07090b270d060e0c090613050703020d0903030603050705 75
    0x202c100c24541803090540b0000304085540420080e04d004070603100703000c0b001c94103d0019448600071681c050103030003000000c042c60720303001c10000d400d99001811001c2d080d045840841c7c09584080c03d0600c0744108214910380e51455030040d00c0010016a00581e507031401c90300040c240302c8050001c5040c001ca10317060011000f0040342c250030140c1d425442a4484d5101c8038182c1c03038007009074000c60f00902100d242000f800442201c901c07a4920010031158000540c0d21600c070180314060002d0030084824401190350300d090340080003240b00c1450305000c80b58168a4076106071806590481d4800c038952080ca11100301c0003c4103a01282c10b0408500c49440c00c4001c41c2c00e449491a202030105040380c004813803600a000701d0044502c0a400b0070801c070801d24025009081e1102019024890300002048034540032924038031070039000c1d1181e05820170302131648002c0d01c40034140006254007480b0f0b170a0708405a20802900c980a5075000c00c207a0f245007045070400c1c0d155040303e030141c450190045400f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 563190746 1250 563189496 563189513
    0x60f1103010e1f05190302040c0e03101e060b0304140304060c03030f0e070b070506090c0a290c01090b130f030f0c050a0303020405100f090614040f030f1a04 69
    0x14403005814500d030f118691044a04a82e94002c1c0b54445194000c0980c00003003c4002c80503207100b65000c00c102282d080c400d4601b115240304a0b5416800302500e14185225904600105440b10410b04e4400b05003100e004156041078100024403a400300800041c0300c082c4e40701122041d6031354041c510380760800000800040c543e507070260515840d800240151040c0d644401649001c41003039884d01d684401c00050b155100204c1943c09224401c04100300782400301da03240d180c0f0402002400d01905c1c0036052080d0029401c2212000341d1405a8140200c450b03000600303030f58040034000203c81c0440d02e01400400f001800c0104854803400900300060413040b0304112464043c241000070001070681100c2207815400010403d0003144d080c0c40c10141c264029009072081140c10717084203540e00008682c220162850701300080c2d400201040454000d4100740c540c4a10401940c0c500b0782c03075000051402c986984100d400b40314400e002400c0c0541c812102c154004402440107107403d15071070340b500d0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 563191996 1250 563190746 563190751
    0xd03153605190c0c02240c0105040302030a020d080105220b0a0f0f0902070b18070b070c030605010b1204080c0c06040e07080f162a06051005010201020c06010909060612060f1103010e 80
    0x90000c03181b486100e11000b58010f5800d484030482c0203111510301407400948907088010601c02603c50326101d034070042c0c09034039030a060303810190582c81484202d48582010034804100e958102d680c50790900701540f261690314019182c3c500100aa140c60f24101406182040d4010901e40c3d00c103015041c002410400c1c1030381c20580201c0310700d4441360748465960515407180d00682507940000740807010070050750740145c1101c0c01000100280e07a40ca49101455206402009800000d10400100002d66203030280c20703024011030071540b0528084000c1030240d03005401c148903580c000d02c02c00442d103900044e80c0da03112100740644083c03801c04450748c0c0c0040718000d500310184800000744500141c0d8030b16090700c20b0b10440e501c4c092112001d0615500500c4180d804440d0400d28800105e650350050003124000ba03001c2000b884160301e0503a62100401e9000801c80700c080c0c03503050010724850103079500342c0d0b03c41c043d810000d050f1101712a000c00308c6417403207032100d034112080c03004000d49000e142525a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 563193246 1250 563191996 563192029
    0x61e05090402070c150c06050a05040b06240a0201050f0601180306020f0706050a0b0f221d01050c130f0303050304030e010908010e0d03153605190c0c02 67
    0x10b8a60b165440c1c164029443d1741c020340300052a01100c0101c0590004140c0c9a060241804120f40d4840d02c00d41d0042d07603012200a01100015000315030542040c04400024580c5101586400a00c08504401c2580102e02d0600140e4580d03041c1b01c40580b0841c030464000509080c14004070701500103069400b00140701c007030031659020039402026100481183c0d0f0f025803000c400c122500e4241c2c140401043d4400e001c034040c855100c000c030070909110352800d1140540e40350b07040c5502e0454810802a01451200942c50403030011038410468003400384034060300b0064101500c0d00c6281880f030201000c141e01500700f52522200400c042900501144d40040e014680700c62015883d1005907000400780d03000e26035561130691540160b8202094201c03a40e981c6075800d0086400c840070001001c0c030315000b20040c401d4054215002441980109034072040b001d062400c500403d4402102290422100f0307256422040304204120f102c00c2c8500405262142803c046c07079510703034000c03903101940f005c0c204 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 563194496 1250 563193246 563193251
    0x320030c120c100306090623010e090a0c0c0b070c140604020901140d150b0406060513050108040311010f0501030309120302070512010213031101170103201315061e050904 75
    0x30f940610a81000b8064400d403481845010b030340e4404400e04403000018140030b0100104005150361081206a2030032100602c90001502d9201d90500140300058907a400c0c81810141c0800281c40d008050744100c1544d1600f600b052024240200c0c2100e0b407501d00c10301d50700503000b01300c0107907200c920b0141902c000e41c54201286090a012a08040107205c019240440302402440d581000ba000203807c0f43c030988062151540e01c402c00d443d43d0007a00f44a2151240254040c000c40d4442e250046d0b029019160006446804405441c00c480e41208c168280c0754031080180241904952018000c10185051960109140c1c80080d211042800340342c2c800d42d0048406a10382c8001d405594072101940b054031140b40e234070718050840070000d6200c00d0110313000101c5c01e03d8030440840a1812070f908003513080138111030a1903040b84a140c030001d81c0da0010701c6d00100b100050040c4150950032202003030309a4010b007804005004e14544a2414281c1d566203416032603029881020744100301c0301690302 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 563195746 1250 563194496 563194519
    0xf101217030a1d011b031509180206040e07020106060f0f1d0a08100f06080a060f020f0705060420030c19270c020303011203180320030c120c 62
    0x880001d000f600c0c103948003200d100c43c20b01c04011410340c4900e8000c81c6205240e01c000c2d038200c405406544607648980148003441c070080006845580043d00300414441521102082582c00078a054000c0d401034030080c2c051408201d1030503024800c50740900414100a0054400782d00c004040c814903882c00c8040049142000104440040500542102c01131501800640f10410599610170001c001240c450402a90f007603025028814030040d52240740c05401030782d0700d03500c0b020042c10824502044aaa08100344072019529502600115101d4400f400b03c1d407c140c00c0c80b90042131307041c00d5904880c000d103821031080e82d0300085405c010202541c818643d0b0b1603c2207000690a0035a201844c0b10300c0c18107440074070a401072248140004050300801443c801c00e40103d035240424003a03000d0034051103151a0210340108040c040c40901800031034220303a100d5842c0c19600d03090741c28245c0d0f4580c2020191017280b80038800b0340d81c170b44000d032440c410003290a225140d90f40026880c40303000d00024140c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 563196996 1250 563195746 563195761
    0x20d020406230a05060a0504360e0115140409080f0a110708070b0409020c01021303030f200c01050a1707121b0206041203020408060f10121703 63
    0x400200601c03007000348180c2d5000700c092001500880c400d8420941d02030041440d18040060358051100c66413160b00301030a02c0d20781c1202001d042e88840000c80500c0d184e036070290403401c056140d1003031104040340070b5540d070070b1803803d541e020301d81c60303641041402003400a0881d2100404404e042201d0101d0710072400c0c01c140300c0c1445240c0c803003030360180300144880d18035800c80d8414054008590440e010035558488868980060703000304074100c3c104000400501d14135030082e0190711080400185462001000440e0080700da0b40110f0100e981169080c8840d0340229a08031811117000e8041c503c1000003401d2600c400c25042180e046c072002050604002d03100b4880c6c01d030020b12880a1511508041030050324940c0b140070311442480c2803a0707900c0d446030000c907000c010011003034000f068281c0b00c030f558030900d2001030800a800c156083c0400111040b0800a50b4041e0700c1c1da088140321814070881541d044c6509812892004c10b10740c07c00320001d49021070090744a400241001e4a07925820b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 563198246 1250 563196996 563197001
    0x112110904050c031e33040c030b100504052d03030c010b090601030b01080708070513060305090d0516082208060a05010e070e1201020f040312020f19020d0204 70
    0x2103000c0d40040c904030810024044000c0210b0107806482c0c041051844100f01160400303004030b60300700c14415003040d01e000c02603c0a020700c102680001c1009034012040000c901254901205140043e444c0c0380070f59403500f4500c1500790030925900c0d10520700b6003000c020400c3c5018801034202c0100b820070305001d500c0d0984942038901c4400505072a82d6070307441c900f51400f0389000c0003514800c9440e0804030f8529070081c4112100e880040e1929001c0da03131985800d681e80e0303000400010510070204154400c80c1107083d0800d01400254900251300d0902031125860f18803091060814405c0800040b504020b0300281d10480e41d900900c0c00350741d0b6003124405541c0180350480c2c4428060801c002161500f00800e00900c903904004080100d03a98500c01006605000e4440b1000f080c0d903560024120708000c500210464a604000b610b000036090000c3c51a9010764030960f91000d04494441c3e140fa41404115941c401c0340c0000e02800ca183d041002c0032543d0850001c1c8103d050440d500110b44603034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 563199496 1250 563198246 563198257
    0x120f1b160204090311010510030f0f02031203131a010e06060a0512010f030201030b04360507080a020a060206190b030f0601030606050a0b0408062e06030c110c011211 73
    0x141c42405400b0f003510b006410252500716000f44c42d402c00c0000b4100c42500305d2060304807900a10310101440e03030b9440380000031041d40c0c003c0c1d030140511075540303d00842c0c6034001e40c000d5071801004007a0300c3e824100300760f070010070007111108100300390010040c1c481541c121a804c480220341300d941d5140092010380721440740740c24090b0404069000042c4000a000244080303900030b80301441411981000c01045a100607034182d40080d9091116440030341c0c4684040d1446821440700d09051010346034240b51100b1030340f0003c1503600c42c1040d8011410440f59800c0105800e0004281c1030034018405814000c000d40700b40741c50b0765144541c1c00e01c0e42e01001601440404501950348958407400c00c0310282c065030040038004c0c844a240050440901800c0310100c034002d030b000d00801e4460210f04d01e0a006040d180140900e9a100300d07045d18102d81d4640b8005065949000030708241c0c8140142150004499800864001c00c035040368a98001194101070806058001030030381c2c0d017070311240541c00341 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 563200746 1250 563199496 563199499
    0x1110a06051005090603010b01140921030a11070303080601080709090c020c191a0c1f020c1605030606131b020703200d080c03070215120f1b1602 64
    0x6001c00d0140140c07200100c081070b903405460320181656088149420782d000780c02c41c60f00060010103c40c20701c0592101138846414010710010580302c80d00900d00bc8400021804610742c1c01c0055000c8a40d50055400c030304610005000d07181c3c0c1840c5440242a0480081003541802004400504003030700c20301c0c0f150f01800f00c18200300400100c000009643e82407611304030740100802101c0b0348007891402c51543c00c90707294460380d910103001480c07003121a0f08080035500d1188103c0310484c0b08401c50240c40c08120003810001a111011038000c17030700c0c0003001c000325144200c0c944d82c01d01c02d60700c021502036441001541d0030010f6001d501910b4001304a0080340880047c42204401c01d12540400c101c001c4a0051140c11001c43c0a12035121400009007020395105850074403050000d5041da002c0c00341c1078280c0301528101280b0b60042074401c14151415103d2203800a00c4000c40c04a00500c01d8201c5411488508a0300d00702010f18030300070f8181c082c0c40d040c06002c221304000c2c216480300400c2140c0d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 563201996 1250 563200746 563200751
    0x30607030908131e0e0114010c0f02090f07080a11030c0a09030c0f050a09050c190e09010e010e090606100e030a1a0f01170c0906031e0616021b01110a06 67
    0x1561340c4079901d129135201464410700c0380369038005030010900f50042d0503907000e054040b0700c003440744006440000d030654080341c14108410010026950b2514024442c0c0313070031210454a4a8400001006800c0003081e01062a1070300710083e030b00c111014196540101c22030611561950b0550302901d100d0388562008115441c0030758040741030804c001c680f4040300c4050300c20f403c4054403008440c0585804413418103007008240511145640c48900315008010710741825100122060085080c2c0e5009800004904a0003801046544e00c402c0d2001da001030844054034240c1850000160240c5841c40e4880c2007061009812000d80d50500003d04e5180c0e02003c0c4400541402d00f942440d204112035038100d0340401000000c3c0c46640c102d00200342440300001d01000141031341040701212015008980501c02c91200540320f280105040e0b51402010300104800c0c40d00420703030300e1210420100b034021900301c01e04142101c11504104044680c007400c015a401c4030750400300349414a00240034202a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 563203246 1250 563201996 563201999
    0x60606050903010b180721050a1b110c01180801061404200f211003060e030909060d05010902090f040218010b0a0f0201020405031209100801030203060703090813 71
    0xd410100038280c10100340c0003480303051150300801000c1e1200505402030b0803040c0b000035401600c030743c807000c0501c403007001f41d03401100140d00d48204a990403501100141e540c3c100c145418030003442d034048000011300c0c1510588000226141c3c0b64549004094180020340c007164203a400c0a4140301d002d420800d00030072215542c0c0d030b80e900e41c10f030781c50781000e001e1480c014035810640090f42c4650700d00540220250b2402110f903030f1b102e85582c0482c80c0002d030410340410b9094000c0d07907607031818045e01101300440342480c2507041400407100e140c0c50810722a40104140f05440c3c603410700b039913404541110b10085da10811300303003203024202c2440001d501528500c00c1060026400c0c0f00c403030180e03000f0b484401200c1800c91801e058507200380241100040148113070080b961103640611a20a103d200142c14076645a0201e031030170540407258083c1c0000860440005e09100c07001c601071700a45d1410025952450300480e4692a02030700c10b004040d101c83d148000e000c06038003192840021740c00f40c4c040c4035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 563204496 1250 563203246 563203259
    0x20c01020705100501080c0d0f1115030717070f11010b0402071b0b181c050f07080105060a06171003020d0605010e15210f03040e0f090109050304030303090f0606 71
    0x221210f6245000c0c443c6800d0001c52520000100c05251040141c80f1551985260300c42c001426804602116450401c035038151460320392400800700c0c5591510300d1526820982c0002c2c2c480444002c1d41403010b49030300d0800510580c8660402c129a103a414401072103910030020501403c4550406500540000344103400c102c0010144080c0c1c0c0c8800c032403590065106c540071200340c4034a103400024240903001012080ca46070803030b0000280c03100d031041d28505032a901c4505107000d07400c010000782c11810040110800038014170b644880d048403804091400d200010340010380450301103008891403030000c1c400040d5000781c02d0242d41c0040409484500c140340c2000605824020b1f0b028102450000c01e5506160940c50914590010300460603e20900542c103908039440440d94640c1c0300341481501c189a00780001e1014068a4441d05464640f402c1c1400d10094043d02040c00e6031314100540001c60404025982643d51619010807070303240d5030030403518000001e48041d0010b881d103000003500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 563205746 1250 563204496 563204503
    0x2d010507060e0a021507080406032c16141c14060c070233090303091e010e01110a03050d1e0603061808070b0a09051603021305040503120a020c01020705 67
    0x6084c401c9661713041d501090a2000c03540c0c0550280100078200910040c802c10340a60001050201209501d800614011070050f26040307400c40c100c9103640008850100324044a1035090282c00ea4003401c040c0c240e000c0c40031426030031524000c81b501800084012040180041255600c850660221403103030070840368000241e442400c040f07201d010b00c0600741d0101c001a040c840f88540c0344036084156400040316030a5664010001d09915000402010b075055481d010070258480042103601c0320740340190000b404400400c03404505109403010410140320307002030b80d01c100c9a803601e0311940b6140b0f50001c18001e4603241d400340e01c103a008000d400e40301c61070342e40c0200200c82c020807084c45a0801817803442c81110f0405006058040c0c100a80c60200328030080c2c0540014864400040110140d111b0301e04041d01c0c040c40d88103102200c2002c10952070806010603803848911410000c5050680e94144d0300d2054100c60040e5180f10800540300080580c140e81caa020010000e669504462801a44 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 563206996 1250 563205746 563205763
    0x60c130816081b01080403140c1b18090a030e030c0d1b170d0e030c0a15090605090109050933011202070308060105030406020c0a0305182d010507060e 66
    0x603c900814008000406000c5140421042c0c4403025140c42d00c3d1821034a5a01404c80e55820f20002c11003030345581402c10040020000000701100442580c030104403103042841501c441c01181502404881c91001c0f4800584982c1402c03d07022491013040801d09200304c071010183e00c0481c60070070b2300500000d07000150701a010b9107120300f825a00d4171580240807001d40501841c030303131002c1d01a03428640500300004070300c04000c0460300c489041000040400744117404c19800312600d421a402d00e160400f18890240005091860a1400c3d203000202082010300c10540b0600186010406680c03504001c0701c03003107100040d8107406212115880d40d014003095581800181c414107102c0c46022180300342d0b100c2540c507a850961540b1048011140c80e000a801643e4180c0d0070015290154000c21801c40d2140c801e842d699154407002a07441810240062010700072000c2400c441402c00700d03500d0ba0303000a48400000c48241e004da0004076030900541c80002c108900c1c0809140c01c03003200144084 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 563208246 1250 563206996 563207009
    0xa1202010f0507020715090e07020a021509090a110d0516091406030f10080a0501270b0703020c0312011706070f09090b0d062d02070203060c130816 65
    0x80d2560040032040b940121044030068100000600c050821644c00d4922042507241903030807542c843e00381c0c2825000903075078140581c8c00028540210706005c2041d00125090052107424000c002c0041445c3d090024140c0c03a42c036a50310b44d4094201d0981040d101000e24440c010411840c1010314102e84905100284001c5200c84500059140c5001e44420750000041d06003411a250f990075801850006056261100381d808008a2100420051010710601810011891821204250b0401c40082420640e103123014105d90000c070f0300450225070880700514005943e80d102c181000c0c00c601034901002c8130081c030940001a82d02d600000c039400ba98904003078480170b4562000549013052005c1240d0082000b0510400001d80582c0c0325400c907074409461205100c1e55036070b07084110f413400b01d160010f40070070b06225058018000742000110146170300c1145452800e4000aaa540c80113068088601c0000f60030504906044000d8006040480403507481c0d024001c0c2d603000c210b0031400740b003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 563209496 1250 563208246 563208251
    0x60a17190e0a1a0a1e02190f0c02131e020c0d03050f15060405040c05180a08120d090803100305010b010512010608040318061224120c05030a120201 65
    0x60814620204030405800e078400702032040514034074485051080f0082400154540e907240300b00d0b64004160022a217a4040100183da0308031108481c1851181004c8103410088007000c5809803a810006802c0c04039011601c00800201c10700120b4050a2411160b10900ba08600365241d80c400a40180c109803814a00342d510aa0354840300310f0445d0300c1103620340452200c290104094032840501d9910450002d0004d6203003944400105080e1070748034050b000043d9001036100e49403032082980a07180c4104540351040315103000300703242d03a0f86c510703c64a5110740b01c0010840c45103844c40c0d21150600354843d117550b0701d0b40382c401030400b40c90303070588000d40301035013480004a00c0d98420001c50355115510452180240d0030090201c812000082c011400e00190540f50360801000001c003500404840e590280440c420203c0f90081c2c3e000c4c0c1410662480d03000c8500d112000c6680d680c50305030307440321030740c100901c14038102029010741c91b0340915014010f005d01c820034403105030105801c20250760000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 563210746 1250 563209496 563209511
    0x93a05131a0d050a09020123040815060f1002060c0f21061014030a050403020c09040b01060908070311220501080109030305060f090609071205090703230606060a1719 73
    0x4c000a4130380c0034000a000407880701c0c81150180c0020458840030b6410310b42c55081985403814246001c101d1400004081031010800c203440c03034842c0c809920711005031480130a14100c0b20380a56a4513001d00b1900b074041000c100008954018002d4800d8021040200e42c016180c1d12801d030b2180400f0b40301c5500136450000084102c4c0e0003881e0880d070662801c0005843c1d950340558403001840060400c4085006402c0c82441507554160040e0165019009111140d45003110240c80c0c69a507900081c0c0ba90031080082020070305000c4081040741094620113121110180c0c10741600110120890005103080d0021802e0301e0705600c9003651900c2a101007003180c0301c00c81041030043c0010910741c0c0c04030b003000016031103040660040350812642d080030f101ca01001900101914011a10301c00305500c111820418090000141c0180c24241d1240200200c035070100b03d030b100c1e240148910b01405001a0000301d0703071b00c60030400c050302600103540c003601e050094601c1c540485149141c6100c41c1007a51 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 563211996 1250 563210746 563210761
    0x219110117040b0108070b0f04050f01300605010c0309090b0f03030a0201020307020c1816180e0405010f020a140a0203040f090207110402160609020f0306093a05131a0d05 75
    0x210b4103586045852305050501d024100b10080b0180380c501030400c4074142c2400c00e00240c42c0310301131508107058036400b00c00c00000c1200b000c82d4102d92113036040000011400300820342040240c3e098403d50070380490668481c02c0444c4a0910011200d60035100003d45a03071400e5042d8051400780e140ca50039514159031140070415600070f8110441d22503203001d00803800d040c040d4040520544490308004400310201c02003507002060f075034044c4c3c02e0001c11008100402c20300780300c1c138404070400c1035085003081030002c030045c28441440484900d03801c0004031808024000c0040d6401050203541c0060303080d8a0f600e00744081e401c1100e0840382525581440c0300549024002c0d200303003600010020a4025a6441c3d134005080c1500040e600b01e080c074480130605031403d01101d449141400010441e803400c1c501c800c1c1185030ba1100303082040e80175001d90b4031100b03c1c1c01000000c01100386020380e00ca074410350070509201401d42c442001c5559045149984041e01d5000c1c165144520303c0c03c0140ea92580d5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 563213246 1250 563211996 563212019
    0x915030308070513090c0203040602060109020412080309030c010f060e070815041d010204060201330e0702151f0605132922060219110117040b010807 66
    0x38007098200001a00e09440760025204081344a035440e90781070380e135850a10842e00c0c0d2240f0000181c000080600c4861340400045004001ca40401c42c5000e1501310225a240b909110003043d86d0740c004040340c0d00c0e8108001f41c0f07a03d5040c178002080501c50f8101d0050081101c1d10810b03c100c00d100c4000b414160141410303d110350340d03070001c6400440c480c008100003030121001c01d100c03410001d580029501800d02c040c10150143d500001034032801c00203403581d0b040000c00c0540301c242d22080c8080050302c01601c170030100c5070b420038443d4140c5c0740c1446c00c0c2e082072010003e10350034032060020000300e0031224a016040d00c2c039179914200507680b2100c040f155449983c42c04c0e10010300d070030010400a117000c103c0550050900c0d01e02d804d40d219014410f00c441e84034001903601c0b07056505019000b03892a04450700141154001080d8184014528141c1c07050094009840402480c0f00c56443d6400b4440b40005160880c04414061802c0d2274012081381017802040411705ca01034001c202e010700034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 563214496 1250 563213246 563213249
    0x52404060e2406031905030d0509070b0a051308030313031209050c0904061104080304080706050403021011010b0d0b160f05032a0c0a02120303010f0509150312040915 73
    0x844a40780842c0448412070031480c007404840c0c0520500d40043e100110304464040501d1194010310b5840b8a0a07030f4550a407007010f0485521900700340410000307814a20121200f079031083c10700b41d441d050006550300c00322500e58055038040c000002041880d480b40c8641c550501d201c0e444480c1c02400f41c0c07403a6812103135454401003440c0e002d010145050729044a409a000c0e02c0780c000803480c02c1d1151314030001c41d0400c1c1e10244090784003040900c130030328007407060801409151522a0615156400050310b45030341d101c1d00000d10a003c44680f84160003908100e0030715001618030712140c900381c036002d6850300c02110f59242000030000da00708a284207407861462803110369540c07030540c0c64641c2e844001500200388240b0203515904803200d100000d20141040d8118000580401481401030101da0b40c4030028120640e0810001400742e000e071000c001c03040e114252404241c030b40d240035254000396131a20060b5494800d8000d600d00b10140c01c1c0042c000c2d00c811020900c4010300070192124040701070f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 563215746 1250 563214496 563214523
    0x90106080121080918010609080a0b06040c030603021507020112200a170c0307020105150915120714120d0509060304020d0f05062a16052404060e 64
    0x60301d032000b20181500642c1106034002c5980034508454203000601c1c0040c3d406140b408114401c0c010090319403c1008000103044442c040e258070105540d90820718100188403500c80d907510351644d1107040c07190b030103c0040d6a010b0b0461942c880144d80e160341302e4000b020124001388040c010042501210f002d080c40c10020031128a500c2c4100c04034000c51508004400d608005e188922040b9500c2c02c550481c0c012000b02c42d20305d64030f040603003000b400d54000414000d0840c001030280240c0351a10155903a004444000442442c018000080e03100c2c948074207415202d01c941000400d00f1601c2c403100e00ca10321030880d1411101e44039550344985a60403900902c0201c0c4080c440e441542c20108000d6500c03500c01403181100180c69a038000381543da041007030300d291703114004000c0394005c2083c2c40b4000c20800320b0401c501112503c0718030a070740304014441c4581000121180108007041217004007041e5420341d01140303418800300803211090119800e541550811840400055011039600c114840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 563216996 1250 563215746 563215769
    0x307050309060f0d0908040510081506031003140d17010806240909010507030606020a050303040f05031b100b010503071b031202070507030c0501091518090c0e0901060801 75
    0x10900c10882160403c0c01c41d0211444104144680402e9510907184881d100f401c1040c0c840b82050140409018000c1030402440320707110030302041d8002d003500d41d02d4286040703071465501d55418400c0d208514a82e44001d128000005180c42d0640000c99101e0480b10190381e004010020441d000720421070030300c900c0059400003002b0800c50b11007400514981d4103080540c2040301c1c3c40002061a000c01211480200d07507542040c0507000e41d1601407480140990b2005028200054447c0c0da16844060f04c020081001c00158904000d0107009440c01220021071144881100900c2c03662039407040e03c940789140740781c611042c0c1158040c10a0b01d01820396a0f230780451400b21004864130341c40c1d4041040d82071103a45900940c0c0881580002d01c2c4076481070f000380c000a4038500d002c280c1e039549500040d06002c0300341ca041c41000d01c00707405400d12038810715202c0028900602ca135200345c0140d41240f0941c600300134a11170415008002103820304020b0705c03500a6a82e0302c00080300c140c1c2082c080c0d03030342560 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 563218246 1250 563216996 563217007
    0x1f06050d0203060316060c031409010905040b040603020418061b0504090b01111209210303160c020a0621090c060f030f0e150a0b030d0804230c030705010203070503 72
    0xa01a07018542c00600501203c0e422407512242c004032001650050002403002480b180816502512129100c514000000c2c184602080043c1011800340140c2d40200d83e11540402a43da46400860003903070040d104102c501c030350340340c950203c509034601a60082e0510000b4401c0884407900d54442001d15640d142c202420310360144050700744c00815504026030071649880d0400140326000601b01140282650380320b20030140216480308800b508241c0c3c04802e425500820040100c030b51000b48040c0f03881080101c0502981e04a0850314013135006001c10b880403070031903000240400403042080b0050840c003120700b030b5402541c403481d200406a84414404020303e0b030203140313910b80520460a001c260308204001c440b007181c4171b2448104241d4008602c0d544994074000c600c41c1c020003600ba060149280c1c040201c0e640740c180441e04820441181d0010b8107000320a4a0f4400d01c1c94500002d00b991b511041d520b85d81c1d5090700000c1c0d803090045040005e403e6000004482481d58424051414603 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 563219496 1250 563218246 563218267
    0xb0a08010618150e0d05010606050a0e0414182b20070501050a02011e02040906052403040c09020703080a05070c051c030b0303040e010f0902070b06090a02090a0e1f0605 74
    0x2514420b500c0c5c0c21070916194000014420700603400a44255503406840c2c1c1b15040c0001e1012244000071401240341542c1142000c1503550141e41c041d00b00e6400060203000080014a0141c1c21031105804803402a0f080d031045203c0d080071000c6800c10303130740e0340b1900301c0b00c50041c2401c24640b03c2c058500e134051001000310b07500a1f400b43c81c0e032560074000007a120309098440c42c101419182500c03140703a0b00140c14810011140301d14005010169400602d41c545500c000b04000301d0813a003184800b4000c800507042000b1045410050300340101c083d51100301e00d00e00940300102c15201d0082d82410000000c002d2b074070a0f00e00c2c06450360040000d0801d4a944004281c107040e20300315880826440e0040c5131000c1e18100000c0009001003c43c003d40c1c1d40c94001801c000744030a801c240d605c68010404200454a50400c0b150404800c540c07882e495162056800b009110390701805411103001500000d400001e00340a0384200142005c10040300904101548103092078010340c400f0448c00d01078117140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 563220746 1250 563219496 563219507
    0x12090606090f06031b03190312050901020f0d020d0f060306050405210f070606030b250503190e0705090a0c090e0c1603050c070b1902121804060b0a0801061815 70
    0x782c8001b074143c0e0146201042c0c0c00320508980d50050300843d0220700e070401000000c1c801c484d03001c0d400300d0086081c544a103a0f601d03581d00c10a2a00c0d06c00c07a0300480c10310701d40300440d1f1000da806120380c10100700300381d520b20f09200900b0302280c09032070350700400c00280840d2540305200029403c10314440c601d025010701c1030442d075400041003901c15981d20070307010002524810295009408950b00703d1218042d0384024103404181d21222420003509005008003455407140c154401022030301c001c80d07100f030000306240c5480c010794004c5610128103410301c0b900031490703800314002c02d04d40d07035444048644403002c01d081060305850840c2d0b0ba84003000380a801c40d9822440c480414842d180c654078000381d50305000d152400c26040160002c074001441951000240855206c0403214001b61448a2156001490074020f40035140300e40d0841088021442c2d4513944402c0103401c4140c1800e44406503090014100d59007401440007060075a00001c521103489101d2100700c50684805812101070108111070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 563221996 1250 563220746 563220793
    0x2010215160c0f02130b090702010603050703060c120f020915030c0f031348060e12010e0a050606011b080a26090c010903051b0612090606090f0603 65
    0x3e1184549000303d0060341c907443e4070322203902c081c0701c049990784084040240040015010406680c5040c00410004e400410364000b02c070b810100008400744c40003810380700e0380340d03a2003401001c52034802500e240b00d040384c2c05081c0b03100099512103007003400400703140c213644030940780142804824880344001c0403d0b0801154801203042901c0d40310302d00381e034421241c5043c002034850858110628801e0213140040f000302c0740c011030520803030b065101e04200100c441440c080c00702041016107210319a5101c44003071030b40c1e40c0c50340030080013800100f070071681e03e81580d40c908440030301983d00460354030740c45401108041043c0c0e4000c02115074140c1c2d2401c0d500d0380b0082a0b1002c0c040b80401801104c0d07051861010100c1607810b48141074034001074810b08180002102a05000b005503052011620008841004500740a40c419a40c0106d03000503000380280050710562440e200f08210152b14081041402030034103442c0b0b04130a0301c1e050620f20088104460035601940040c80b012020b40003503001c1c11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 563223246 1250 563221996 563222003
    0xc030304090b060702030a0f1502070b0403030c030e07030c090506011107060327050109050f030307050d090c03020316060e0d15050403030b1041031810060302010215160c 75
    0x40c13400707044e070340031a09094404c0003c0c0e8000c5520039081e0f0038480700c04074074402ca6444c100c0440c034254075a60b0343d005c0542c01600c040d04144d960640c4440c4640139901141044140000301d9034425680d1914007440540d600070401200e0074100420340c194042c1071920702202d6a9030242c240319081103412002040003821340da41e881c200380500c80140d0142020b0032051400f0b84008190403841e42400c62804581400c20b60a82d881001048602e950081c29205a0b0b0007190000c21050311034104103040d180981c002950502031b568075030401e04d44164200e406c46e040d645442a010307035200b0400001d0b98070000040c22000440c509240704180560002e03038054840d06000940704217043c04074404100750000140440d0441c0541d01c603506d000028150881c2c1c100e0740081c5001c07042100ea4507103080001c013002c504280440498005a1044008590b1909038000c50300407060440b5204041c0c4001d01c0180d000d8000d61220410001a080e0340922903085007861451006883d0f008076060044c40d0003c0d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 563224496 1250 563223246 563223259
    0x6090b0f09150406080f06060318010f05161d010c081605010f0e2b0309050a0f0f1403070302060c0d02070203030d06090b09012702071b0609080c030304090b 69
    0x18a82e52292100d0000101d0406015152402c0503000340c0b0a64003c1c140c94800b040001c200b0065589102c03c40341e00821210038031071030b10070841d4044d000d006941c441d119964140000c000034018241e83c603061800c110354a036060003402d605110400d4008110071070005020741380c004045400751000b010010581004154914640d40b550707400c43e4565408030300601e4070b9018403000b90508002c645110541034400314620401c0d100c0000c40c00011020745424140c4030b4280b14103210080c01030001c690b402040d0010322800c1c80ca0042c402c03040041e801c41d81e2900c841c00308441d96070000192500c466150b0010051034079019a00b240c25000040030341e94440d003c1000000507281480a018a03c2240c03002103502414003040c07009072604011181e01640c2c15400400c0507030700784004154410451042056411040071144010748500d05021b00b6404188034500803850309503860798200d45035a80ea54403680e03101d0f40080d407222f903112180da0380365005000a000490159001f685045002020b1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 563225746 1250 563224496 563224507
    0xa03030b011e0c0b0121021903020a0b04050a06050c060a05090717030c0d170703050a1103090607020607030e0a030e03030c01110301080c090709090509011e0915050106090b0f 77
    0x110003003032203070b000c0c8000182c101207003004116034501c50502400504040c24124a42c072035140c450031480590280c45550070480300780d0745405409603040616005005008110388400056215521500c0717a10302880d508680007403480e100e2030a803407a144021001d410107403194203140d405400c002d030294000340100e20700040c1050362138000f1054400804050341c0c540c43c00b070f11814146100321700ca10090150100d8882503003002e61980c60380c841050300300001c0944a4203014802007182da108905018000418028100000a100740c4104016400c80c0d4040d6104002101a135103a40c4410481d944903020707400009024900310b4104140250859080480d070411480c00c1da007200406000315180080180304055062282d0020b0040c2541c1100542c00d201b80c000f4003c0c011846000001c3d40d4820114104000a400071400340c032806841c03000d030b900307000010f000074003058401f210701010030200c80070b0002d642e009003070483d00d150300c5170410345290401080301030b80f102c0010f0400c01000c005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 563226996 1250 563225746 563225777
    0x2060a031e061a2110090c052a0d03090203190c0e07030615030504051e0c040f1404020409021206010b03010303271701060b21070507050a03030b01 65
    0x100c9014580011404a801c0d031600c0b10b41030000001e241c01c18003041c402c000c407008101c03051094002e00c0c10322098210103a507500c0b01088500881d6000b400c0700c1420a1487d109241c2d1203000740c1986400c206100009000119000150b000f0036651003d0715008810500306841c0250300c0707008824005019284a404c1c0700078040c2030010425012900004000c00500c07071030310100f42856000b480c0b4101040404c0c14420010b031503110080d40d801c100754035240020708102081c00000c1340046462241002030010503407a03504c80304501030300d502580c40c0c00300070582d9036094081d0329800384030100c2040682c0c4640d001c3c4009071480350070590304204021054074100c84104851402495009a825201d5055107001444003030880c030095a1011a1217941c1c1711030a001c510b002c2100c0e070512542c0d0680e00d40301c00340e9024101d5944000e03150342010525110342050103901d0640c200c0c0c14080c21682e0b45e40d140e07040d6000d00801c50003410941c000144000001e0090384001c00c5040141001040b0801d03114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 563228246 1250 563226996 563227031
    0x4020c01112811030301140f10030e24130c030c140f01080108150723180102070602060c030408040902030717070305011802070c050a0f0e0c030106090302060a03 71
    0x400d074402c02520440280c80d070814060303070007420701103250500405010380040c139034900060040b00748101080c502c41004d95108000e550140102401c1401018501c10f800381c0181481c1142400310300070303005d1001b000c41e40f6a0010511005d1044880030395201c80c544100b00310f440c2d8200b00c0710700e80300035004400700e01d03883d50758001822602c0c1181c0c001c9840c2420700c0304101c0c010f0740040c148031115006200210003c1540d1120203040b508003000ca644490040707404490100e04d2003030a02d00b01c0800203242c150300b40184030388007508994400001854004903641c050600ca0030005810090126551328110b50056030050b005003003682c1041d44a82c1600120707882035a10340c010405019403000701d000c600c10415071241c2107040802c05585000110403240c1b044801400b06603a000607000c082120000007000600b41c080c140d04192901d5900d001070642c0c02d0f01445506d00c04c04000628a0419207003124162941592074915861850382846140c0e080395402009240e02d03412120004a10783d07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 563229496 1250 563228246 563228257
    0x3050f0105060c4201092d0513020901150e030a080307080c09040c0f080604090506010b09190b07200a0303050d0f151503110703110f060406051006021b04020c0111 72
    0x4d03209542c00303526000001003205c80303030400d048000048502140c06140c100d000814480c1c05868081801e40c3c031510503010920655000030b511512030700022a1020781309050311a121000e0700d6a1541c0e03c2d000c410140d50322001340000b0210102000083c80044c032170314000c0c4d00103491201c1581068200700c0020140d82005100ca000281c000710b940e801d056201043c2600724105640c2000281600d48400b52560814001d03000c0c2600300054000c0c4d030b529501900105000c2d2880382c424001e171a0f03401202c05510090084d10362001070400800388029015242c0c03092400140740750041441d40d501610103800542a031702105548480c0c603605a580ca010b40f00c00c07800c520101180160826440c03a2000f00c1070b4103503e040516050a40d0740f04040354080358405601801c2c2481000710301850756141041440c1c000039140921402e020400407aa0091402910b01800b000803d0b512150102d84c1c0d00aa000c0c10714440c5c1030703020407420b81d0810368020b182414841001040d1184c421800c440d080d40030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 563230746 1250 563229496 563229613
    0x122a020f0a030b0108160909020906010315030524090d0e10120f05090d020109020a121e031d1203070b10081905010b061c0b04091203050f0105060c 65
    0x2a448007803a05828444002c040c00a41c0f60808c103100d91070b004a2011440180754506050303440b24003e240d6842c0b003502e50015039010301240c0f4188030f04a140150014411015400c00030400017142c0030342c0c00411204401085a0303902500752038050100130185c1101411042030040b61068400220480c1c040c061024814041c04255810103006140c80c082401220f801164500002040181d4a100c2c090044a0303007002031113034000250800204001150034110b1007030b40310450240c10140c02c0701d204002c0d40404074000301309504000600c040d800d6140d030b030b9464580080000d1000903545010440e000281c00c41c1d02d0044a84418050b0300e003031719903002c203048031b24000880c1c4200b0800740910110220103132422130800300d420035840061142d031282e824a580e01c51780c1000150f1500d62100001d00d4115181c0301c1c0b0302140500c0a402070070f0542d134001081484600104881c00c2c070328101d414146003c40200b9281d2141c10181d101800c602c80c84802d5a803201903ca25600300c49a0608c504095 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 563231996 1250 563230746 563230753
    0x33016140c011e020c010c06020c01060806011a0412120903141006090605010e0d06090206280804170a0c02030f0102030717070e100516122a020f0a030b0108 69
    0x701c0400141c00d0203a40200d10090400303150340040d101c4e6000c521031807455021b090500710321714a85400c801034000e8031103844143d0300c0c016000030300780400921103041b568a4024081c2104034041900340501c110301540045a04000492000503c4414000d00c01221494088200b5440359240c58121810b0800c1d100b0641c4140c80c228030207841c030b1244030000c01c44400c04001306450b020002e4984010401d8591050303903001202c400f400a150808101203900500380d07070f9501505550541c980000e10301c0200d00c49005d042542101e80509611802641c2124a184418448404042681d4008201c1c01c0070810261507a5005807000c020031a4264108400562a45070105000301003001004282d00300c1c403141400c0c4060303a6041a08901086401d4070303012042055890261140d209a020340702c03120f030070660004103000030a001c8416113101c0d076440001e400550700b0140c100d4505d05031003d2007242030701d0b2813100601c0e280400266089018116182c05035607900c0d05500024268072812280d007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 563233246 1250 563231996 563232013
    0xc02121006080d02010501120f231b031614120f0c091006170c0405060d0c021c0503060603071e0c03030b0109031a0603030418060503301614 62
    0x45007840f60f020003c415100800c03996140c0b050103000342c101c961014080c0c0c0c144c02e101200703000031205507111004585114071201e00c80b50346121ba4800780680c181341c032154480d400c45101c3c5804030b110b00c85540f1400d02c1201c03036400e040780308070701072090720381d459210b080d000285104080500500c10010203980103891303002441000d020000c8402056131380551340c060000d1040e43d82001158402d0015030034082844e43c0ca40c00c10745514400c9401c400c3d0301903004070f000070030b4820a0b0007400701090154250f544121400c0c018900581c0c00d00c0380d0101054041c40040c0042c20141c001e0360780b281a501d0084003519100131aa8016409550320030b000a4040c01c00c0e605054240c055260450000e29005456030b21b5a00c07851440ca03291100c1c05000c2d90900089032284d9010010384015000002600031603000301e0322124000c02d5940704032402400f50488586103805a45248101c075a00c080307802e910081104040f41e81c07581304101d42504280941120004660814942a5a1040f1200905070302 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 563234496 1250 563233246 563233259
    0x30503220911070c09022703030904090b060a0e010f06180b0a18050109030209070815100f0e09090c0108070c0818010e040b100f051204030e010f0516030c02121006 72
    0x5144c40e08102403030b0f4010401e240303502d03c1e5560b4401c003c1d0040b0807d0700c1c0d40341101000034150b124003110b055001e81020340d61000d015146d030404c0c0c09500d0440d000c078a01036451040c00c0380043c0901c42c100c1c0000c81c80d00b0802c80725009209192a8940ca41c001e0011981c9414483c4003980003110750800049008003041c1d0f0b0320148000c540090642400c1014140389954001035046800904220811851401107101c1489030440f00d5500c9038010001c801d0740350f0140000b40001e08801c044800600c400c100101281405086a03004910400241a203018214015942ea84010344000f040008840d10000814000030250440b410310110703d658291070a4001024040ca43c04070034400c52a1451191440d03403030f503460030030701c1140c0e00b000d84850f50341c001d00303030703464010b42c2c14030030310008003408010130113501442c244107455090300c2d00b01e003440100008480900503c000a41954052400d10022078040c203140c400651000300321100e0035921004240c1800c0c0c801940d40c00c580c0d1a000d050060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 563235746 1250 563234496 563234513
    0x307050309120705120c030c0f0f15150d170304150501062606130912110307171812100518031c0908040f1e03050322091107 55
    0x80182c0c0d6110b0070a0b1050311400d031207903032504120580080029518000e07120a1084da0328450341e45007950300850b81188040e888000030394080308280220130129011082221019008085034458041c20b850020148000c00d4040b1034151030407041007000c88044900d06000350f02c124070940000b40d11080e000401c40a80b00706170400006d000b80c130380c0c51420000888050780c031008142541240349403a10400320709141100d201340c80416003001004014003c00800c0310f43c4002d641d6481800d00643c07030760516103d0284180090114100500006c0e4503004039019200f000c40c1e009038402a224004009a0929240815040c460f04458940540001217100b0715134440c41c9450b84403d00a161520140c40e441a505001011500700071b00300123030581c507400030000c3d0340d000c0005603072203480d12156154044180300300d0303001c18030242c3d50740702c0c0341c0a01048604480e4460010350600030152203608484c103200414503096500751070f00040039030041c01414043d883c10000c0d103654a01ca41000c1e0725 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 563236996 1250 563235746 563235763
    0x20c07031407030b07030e030a0c0204020c0109031106070201051311040b0d06052502070504050c0d06031a010b1305010c030c02130c090503010c080f04030903060504110108061002071202030a06020307050309 91
    0x3458604000050307c0c00700801160309069291411041d405258070010707009006054083c0080c2d8a043c010b0820140c00c42d140580c0100810126a80b42c0c3d40d4010890a9800480d0f442c01074100342000840001c00c55284503030f01a600410220307510b000c030750205003402102003080d0741440d2240184034158600240407904030b6000e400f02019001401406551071529208040c040ca44e036100042950000d00706441c070703002e810355040c030099590742440303c60922100044241441d081000140010b401c60840312402c04030f90790000418139103401515068250071040d4180148080307801b005030b407100c1088103c0b540a40b00040e950380780103c0100030f6075058001c1c0740030340c5c03404510205d400d8009540310741c0b11082c2d03012000aa0b945182c1103a10910617440207010ba82000c00744003c06c0b440c00c05e8403540700003c1c1e842003d80e070354510170080f00e0030429590b2400342c0c01c800020b014a510b410208400240042e044440d50f02c165651041207034022a01000001d034040f040c0407208100340b2107540f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 563238246 1250 563236996 563237011
    0x1707110405040b06100e030d020309100206040b040609050c09090106140901050307150225090c0c0c1511060a090b0f1e07030e01020d0b041d060406020c07031407030b 73
    0x200324a46981c40e0b1070f0b2200040c0045120303021404020354101d1042510407400c0802500340d9815001c0c1d5a00650b80741c001d040c0c0350744980c00303d0007603e6440d4400111103229a811914040e455142d586030b03c401003480fa03105030303518000c01c0d040298589603861003900900b41800001800361030304400c0804c803c07030b4490841c0300b0a015401000165030000d07601c001c0c0c80600c00c1d407000c03000320401d003649441e24039610585110344182c1341040a0b01240712000844e510028180501c0c02c80c2d14040b1854103100800910100e1503910a20891100085c40414040c0134100100a065500206440c2c10401c6410f4221207854421807010004071118094100251615000c0c05040005214914030048095540150a50400a52001d02ca500001c0861001e078000315a0b801c031031080c000207807003250041805281000030554144401150300e909020300320000c4e250984543e03980174065806440c3c0c440180c81030103030100204c1c8540c0140c07503185144000500c0e080380345282c5040791450003001c20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 563239496 1250 563238246 563238251
    0x1b080607030b030c0603100e0a0911010306121103030f07060203010524070f03050d0c030b041a010509150c060709090e0105040c050d1b0b07060b03011a130917071104 73
    0x502d5541c600260b0301e0128641124110380303076550704d01da001c00004103900907151600c0395000d00808901d19404400d4840c0a00c55500c004d1501100540540c1c10500ca842a001c008014840225503094100080c0c00c80080c281d074540880756407000e6568012800c01e03600340364000010032151920540282980c1c2c00442103a000346c2c180706815296003c5e403400078100c0d01d11401d07200c08244c41402110742c102a00f290412083d08400c50040003424040c003a603006502d0020641d031000c84036010940407280580d40e0f1071400c045281481403d88015041e804958400c1c0100c91144d842404418410169a510700180b10310b080045400e4840b0050300d21074691525041c400890754055505050b140305898140d101c41403403070010b032488140d1141c5c076a50b0b03c480d400807a540c0c480340000c04800303000d4842072101268500c20503080f5400c03810700403d0440c0c040000c0c0b0850500c09070241e05050000030000310030506403900300e001703c807880c40c1c0042d241d000a02d480400444462740f0010310307003e9a08 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 563240746 1250 563239496 563239511
    0x9070501091e0308030708180a12030213050402070f05070b0f0714150403081e01080709180f05010c090905070e13060306110903010608030c0c15071b08060703 70
    0x1030190101801690581241c265a007080e80b81d0701002e040c002d503804118950b807480c0080005020020070b40744482284038a0b46500c1d1701042c0003c8640e0582c4d0400341d601c29035103a20314107070001d501a4031048a051142c0c0e4000039035656900c050104c0b203000b1104a107400781070f13142c130350704100043d0001580f204081c054040c0c0301d880c0e00241c800690f80b180105528043c0900a80e141820101c0704524551035482008201a80983c51600802000d4490b48000010020000c1d100c102402002110b5020707803c1000381600b241c1100c04901881082502c6020180d1541100c0315900c0c0001d03211691a50040442c3e558066141001070401c42d408001c1400c1c442c00c000e04c18a00d401600b841581c11111103001109241c0c070140045502071010410340c0d00c140e5182807160803444001c1e00c00d500c4d0400010b011a8048202c1e8030b41200390f809480949480000c12500c0f915118014200c50700070f2201c100094141d0b443c01070385801c0c00c2501c42841d0b2030480c2d1070b480d2484c010020f20425050940 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 563241996 1250 563240746 563240749
    0x203040c060801030503070b06041806061505070b06150c0609160603090816060209031b090c070b010b130e0c07050d0201060602030703030b040230060a0f03120e060f040905090705 79
    0x5440b00345c8d031320010b4200d46444140004000e0403248080c6d40b1910610302020003040000e6100307008680d88510740c0c0c0e40b41c503603c00b425146070044c5080a4880c100000002d2180d1034400a10010b402e00c01000301d05010481c64104d240c10307411a81002154043c561490744203000d0400900242101e2406104c1081ca694548820307016078001551441d480c842580b08204c00e41e0142d503071a0002038121104108074030100180b503414000c0f0140101d1004e8045650001ca42080b942070f107400145211982e423814030481d03640d500030039034401d15440c0c4a4001c680040307500c0f0802c0c0680804d00b14140c940d2500d041050504c414006004203581c58580104001a000710558829075054240044c04c0045c5202103406441048215030031841001d01401c10b003040041854002c10441c40d8044090760b0b400c0a110200c20680074264041d44004c40410000b40011010098a42a45060a07000802101003134071a046100003413002080803400384001016441601e40c010101001404602c4c82c040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 563243246 1250 563241996 563242003
    0xd080f28030e0a080f0c0c12150618060111030f040e04030e1f050f071406010611010501030302060402060a030b090903220b0315030a20131b081008030309010203040c0608010305 78
    0x303c500086417030100b031140110301e050200c01d041d00700103000b1800e100144c160142c1c07920f8802c1da9203900c0f00c4c6100301040c03143c00d0000b10310400b41050030034030703c840d210200152002503000064854600c4100b141c00500303213542024000030800441d0290541c241498094032a54000d19603502821200401100c05102400d5084d1440880d0030100d66800c42039080000724850130201520038a005844000d2a0788005807943c107c520700e96920300c0c441c4451086034260b0717100b888046d00503403102011501501c1d02c6801071540b500c41d030a000070340303c840c8ad001c1001610101e484004607040440c40941a44e220f401c85221001303c0c141c25064a820440999498080600106d8003981d0421814541e038600b04030182516030821210341590b050400c581040342c10b44050740b40624072110348180700120301d0044100c1c8480200c480000608486411100008020720058141c0710b034060006085505200442c040d003402000541c0e2441e03e405c101c501d10328194820001c20140900400200e0300c0407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 563244496 1250 563243246 563243257
    0x40b03010e0705150f040305031209031c050c0c0a060902030c010e030a1b030b0a090303180f0f0606150c0b060f0108010909080f0a18050405060d080f28030e0a08 71
    0xb1103e10200745140b24084c081c5004001c4013107050030f0005004400d008000000e0410000d03068268940c0369203a0140750b2712402419111510f41c0c001d0031400000401c941c00050b07002030001d0b846414011480e0362107182182001c1c0c281d80e160307a40d00b0500c040d0700b0705021420303210360700b800e040038800f020074046999601a4038015005442034004441481920031640000b07581200c4680c0c0c090601b0070002000745200a4120701007407510001e6504540042c9080c402c154010a01c0e01140302152101c0528409000c01100d03007559610300030881e0900403401100c0b07458640d4840141c0300140c5004640707488050300c4648603000500ca800303e02c3c0e90109041d07043d2401d05c900440c020005141c158464019074503034a001504c0403e1a568150780865904111409850340346c00090351101400b048820a85140c4d4110300d01680b103202161412000345584140360404a00c0c0c40201200c4050600b004040244007820100a00d810254107008500c01d8a21500182a003440709a8801c855407060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 563245746 1250 563244496 563244499
    0x606030225050c030319080a090812040c0b0a03291c06204302060904050c0304021002010203010b190c050f03031603050108070509130f0b06040b03010e0705 69
    0x1c0505010010b050020801c0c54802408494680c0e02442c85074000700610395129000900e000c00107801c40c03a29000721980c507a000548031340382a00c201c01c0298040002131045d5003188959000042009002004045100c5d0366500051030850416101d801d40360110010f020000f0803040c2404207a68124020450103810411103582010b246083c001400003030b1000201d040035048207140e0f44410400401c90300009840e540c0b61010001124040c011a0b000f00291012550103540700840c5041118419a40000c160300d08058403c0c1c002415100102c8402005002c00b00a0000310300748040312401070072040c0002e40c255810904501c1c2c0038041d0080000c0c80d0301e09903110394540c60044619002c41074000d010350701e00144440e410765890b4416240114000080200c00032018801e00c61107059403500c03006498460300c0c0c01d041201409019014031012a6110240300000301d01c14582d824580c45449003448514117003081200319071214160318002e07410800b40242600001c1040c000b620300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 563246996 1250 563245746 563245807
    0x90106091b27080601090b04140f06061b012004030503070b0613090609150606080105131506030c08071b060c030209060a030515060403030c0b090c0d03050d06060302 73
    0x10780d500100900401000724a488408581000c40c0c00301004c035a103410307241084000e1121200480c10700c001c68101c9040349000303900d22404644051201c0c9030403500071074020b04450415110010a0041511151003040c042e03643e48c0464241c0c1c04000341c5d480060700c180c9100c7c1e00f0680345071102368403480340401c020f0030101003c1c00540a9903c2c00e40d0b000d0102c09418040051454600e0318100401c0c030700e241503030060204c0301120ba050b412409600291001687c2d46196a442e090a0020741c10112440c194041d86070103100399204100507a803801840d50f65004030f203076104504090300d2150058008010040c125a0000e03205180004c0143e00300e52101c0000742070101068124001d018917142194402000140e070b201003680f40d04054041d908007035501050080310410000c1d60310607072100801040e01945103601288040b143c966002038000e0030384060b12126000a20041c0c107070713802180861404103010104d000a0301c20003000d84540e0804500e403100f900c680f04540c203000d82e4000c880300c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 563248246 1250 563246996 563247017
    0x506150102010603060f1d06010803040302130b040c02101b1d0111031305090a0903020a1203090f03031e05010f09020c190c060f02150403080606070c06020105090106091b 75
    0x9200350301010042d50030140401041d44541e0401005d8000310700c060b451030304420f03110001d01c4004923910b0b04840343c1da0700840c5894619030900c02e48065000300c01404941c1d40c4d261180544540c0102c6007992050b41c080d00d40290181d071080121080c2114a030b00e455210012100141c2c1c1003400c0103020410f02e0141301210120b900101c84012005500e889540800300e01c0b507281d03c4003a81e1450555904503008012640e8001e26601201d440e03500c068016031051803508041000154200c07204026850040390002d0640c45801c00c50102c0c00088001030796920040e00902462a23005468084186040c02035500d060803442c01040f031800780c44500382d8009040d05214000f0490a442c0d580850343e00101c2845504120510720003920600f808612140052201c0c6480410024110490be18240a268481343c81c00c442401000300b080d900302c1c2041028030003041555081d240105078a50002c11a4035004000360309448a80e44902c00d018140311070b040e030103584405001c0380381c84c2c02c0c07412400d80e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 563249496 1250 563248246 563248249
    0x1802040518180f010b0a0b1809060a080607020c0109120f02330405010e180c132106110c1f110d0c0e0909030304030c0335010b07050615 60
    0x2c0718003204410301d880381222a885041064002c0844000e0445555103040e0742c03400303d064280300c1d01a440b074006402e0903c0c00b8585c540398440ca500144041c040c002e203940c0303542c01c0e02d140c0340c019070303001c0003503800005014102c2d80e0000d040340180650401c041131101e1a0707a50b0602c000c00002d0024803490752001d15003407070300084504c3e40d2082c0e12100000710030000202d40c030281c4e42c4203014041c0040c584041c00e1005050a50540210861001388032400d69109950718a86030070000c16803011034040000060446c0c50254007141402c046020354405070a01c4c5032140448070503108080c5000d80a01207011551004100003854904900300b0380c0301800b2070021034004000a80340711084c4d07003001c01c441c480003120343c1c000101c010282e101c0c88485c12040041051a00c82112040c1d00d56008100080010b442402043c0310540319041c0056080c1c0c5c03002c0403840480301e2521031006103492610803550740c1c0701c0c06801e600401510400624045c00e41e115161640001452401005102d180c0c1d007116 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 563250746 1250 563249496 563249521
    0xb060d030e01031d0703080d0e0106060504090b0418110a2c060f0a080a031d0618040b2d060a02060402211c08070f0e0103090f0203060106091802040518 67
    0x1d404c511420381d078a031a220300e41902e59410490419480c1841c21074009105103051061200b41ca01980300c1c1c0b802c0a1410300c00b6800351403164034681d0000e444002051140504243c0c042c11030748a1050108600c114030244a41c01c0751540c00b65005c0d8110a00c0040181c1000140c201c0b03034099000140d40382e0342c44002007071403050343c4c09540340c100b084400000340300d070310120390010318078402d5031120800685000302880210944240d2580303d1020030000045407007003102c1d001c20003c05400814680b0f5a00002075a507000c0070b280200b1001d0700458036050000d80d500f4200300b0141120756034144510040029661400140024003520360034819070400781003044903651480035841202c0840c1205803000403841c40b031001d000c0c0801e400c40d001c40d4085009040080b88aa12a035821881040303400044001d44880031060382c104a8042140d00543c40a100b264007a08154032a51a4030f850325500c500c1c022404284521000e105001c240001d64032220080d00071161010b0a86498940801d481c0702c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 563251996 1250 563250746 563250791
    0x512191701050d051c1718070501030507110a0305090a050301020f0702040b01050f1801092c0c0708070f020a0b0f0a0e064008101a0a030501090b060d030e0103 70
    0x8011100107884c02e1680d440030b01d0342110920045d5403009031f1a51120040b60305000305031142da0b40c01c020802c5c031044d48690321441e840070301480c1c80c5280d045600070a505080720203406500103000000c2e940c515003000400311004200c10340c000c41c0760507184407503c0c41da4042c1000c024426910303185000f18907071268041c0c1ea5801ea80414255840840c0100200203e841071003250108140303903030008250144003908000f41c40810686100c80e400843c204a10b43c000400c444c10241e024072140000c01c68680c09041c015104044203a035040d01401042080600391b8422683e4500c10001102c1d0114100251541e1000b14180f114203001d02c2c60014006014035071404150000740c9009103102c50310494003101c080111204140000f00382130501100300c07030b140103039500c9511600701000d41d40d00b2a40f0008031018811700c4a002100b0410001c0e04d010160360040c2c842d40e4642000d441400201703003d81e60010300454803a59144c100f550007401c10300c1c00034402410b040d40c4c0c04a245003144403116810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 563253246 1250 563251996 563252023
    0xd020d05030301181a0105070f0501060b0a051c0207080a0f020a060509060604061a070215040803030f0702010c020c010905010c1106031303030b030601030f0f06090512191701050d05 80
    0x907182c3d0f031614410b03149003890880030000242419148513030a100401881220f0300180e60719440d00700141c503040880c2945c040112140d41d44c0c0e00c00040d07044404070151080c1802962900d9503001c549030880c2e1104d60199600701c0d0310b4410007802d000948210304480c0809880d04007400c400d002001e0580c01d080c002c1d0703805000c1d58100020842040310104542d0301c80c2e0701c03c030340421440c0d4490700b08402d503040d0000f0341c00002c403040003444090300d0b1070703004019007088031022103152a841d801c640c0e04540084e00d014200c04030381c0c001d01040b03540a0060441403a014401002d1100003003000a08002d00c601c80e4506019500031b5035420b10080c00c910702060300001d0180c40da0b90600380665000e440d00f8034400d80001e4a07001700e000080c0703000b080060490350000c2c410900000203856042c41c03a907950004941c0385a07202d44c4100001c030240120303122003401d500390507129a03102d0171b00ca514030740b403124282c20403854110006c1141404190241540d00986070a58407a0301441c202d0700d05080c0d842c504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 563254496 1250 563253246 563253253
    0x52505090a03150e07050f04020c010b03010e0a0201080c0909040605091006060e4207060f0603030f0c03120e150a021b0304060e010f031d0a141b0d020d05 68
    0x22090000c11811029070150f81d00041013086191440700d911010180211548000341c505084914a4941c001d803030311a00c01000050004040e8000a00f182d0130b12940c200f064110f015010199030704410703882c0d07006007114046854003000c400042c02810f8014801031503940e0310000f14021600400841d40c003008012007c2003515113480340544001140c507050b61081010051159030040001d0503014503400c4130f011500811003150102c880b0b560903040407070000c4400e015040104404d03000f80c01e440316074940300040172411410000d20340c0d00328141ca4428400d609181d10000303503022022420720880c5040029149079083e6005080507507542007540320507903407414407004483c16130003082248041c40400c20f8003019541069100d000321300c0f45a010442c44800c0c42d1032540280020b015441c0945000aa15007500c0d4003400484849900c1c40c10307135403180414500300400c1200108000703190100801050b030300700c46c1e082031215103100640e000ea641c20301303070703070300b191180700345464500d07445003d5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 563255746 1250 563254496 563254499
    0x20315030634141303061116020f030a020604090c080a0902010c11010504080a0804050301050601030902030706031a062a01022a2803090e040309050402220605130801052505090a 78
    0x6011011071170000380c88041c81e00801d90760000e16001150f0382820301d00381d096500040d40e02000000e1220040b2076400d4041e502034940142d0301c2000030700141c4030808002a0303040d200d100003000c41400030b16150f800c0e458501410301503030700981c000c80d0841d030040e0240c1d01078007400012203030350041d0b52111507507109601640707040003d820044c2041da03806900820a40d903440c0011400c0d92000100030750036070030050b01030241601c070b50045103007142c2040c0034800c080018004101250304c000e00014401d8041000070014941c12030f586c100742d64945000f035007000c00d034004c4004000d81e00707440110607103004501103aa110050060610801100c00b20404020242c1c0684214680d400801c8000031390031140815541c00b0704a00c240034a8140d500c00c100e01341031400703001c000d60010300000e107900554030740c0100c0f01c0014005180079169030351700e0a40701c540c0354007181100d1066402000740303030b4182010400b21026003c0101c0f400248003203001d008440e40b900030f680c2c920a000c28160480d404940 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 563256996 1250 563255746 563255767
    0x90b0f0403020913081902030c1f051003080a120f0212010513050f01260a26161b09050c030105120d0906110c030102031503063414 58
    0x140c81181e000b6203c2c0d0026654030268466000e1034500018495407007448410f115900d8490103e12103100b90044900d411800c00300070b4901040e0100c0a0040108503190100115a40c0030b2a600019000c0310202c200d41182e0758884180281c46101d010440054880d541c45035550b00042018031100c8400c650301e403107000c072105140009004060080184962181006045203d181d00c5003842da05c041e2410b03400c16010364400360300700f880720b09100a200c0c0d141191142c10301440c5c2d0010b11620200150945401015000c001c0c00c0146e41140501808842c441102d481c11107418a41d000d400c103000070f4481810009082000d03004500d14600e81010481080100700046041e540103c07021206900c00100c116910240115990002000150100021030141c0e50002800c030900301075440388407012004c00c1c00c81c0c00440e0b0b580e0724500000e1641e041e5003400e0107125007004203100c404412090070000c00320003408000c410a00004c058080c035600070303c0740d0b2645c5035506002c404540e40d94907000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 563258246 1250 563256996 563257027
    0xc030807020f030d0e0907050f18100903030c0204050604110307030605191d04021311130504020a1b0f0b0c0a0807020f0d05070809150406080702010c0519090b 70
    0x64049014600b840000400d034035001440e0b481201c11a40c0f0407102a1204061007140400a020641440300903c0301501c0204914090701907801901d1641100002c0c040c02c000030800105060302c02d0040a010500c0481da000b2a0384c1450b6405880104030f5031140c8000ca4000e0055111041c080c01c80807042c803c60541c0340d0005401c480040b550f90205c41c40401b00e4190900540c802d00100c4000c040507134a1003081005041d034410700080a0740007252013820b1001c01e4802c0a07419040d500e200207190a405015042044007421041e1402c60400e29460009808507104a032410001c0404803c4842000100303040d40c2215035010716501041c0c01e081d02c1210143c0c0080c004580498500c1c00022501480007802c0c07040c81007010000c1011684441043d207090307100b1901503a480004124001003919004034060502500c81e090a80d11031508000502c080d2000c1c04040c11a41401d688180b850390042c02c0e501024004010381003511400c00c02500c41141c60b034000f040814011444014400d01d20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 563259496 1250 563258246 563258257
    0x9050907171b2d0f030715090b03070203030112080c10060e06030a080306010c0c050904080702012d03180501050703150905010b160314030a050103140109020f04180c0308 75
    0x20894914041606003008030106501541414201c0c44a4411814901c1919034095008024202034504a480b8022a00b0030034a41c00c045c01059026807c619110303400307203019004100e403d42c998118104030500a45038403040c40740a81c0084040202824010310710100c4032442043d1003150112804048880050b10013480b9a03101d40599200040840c1000714040203070030382c8012024910f6031003034015120016a4001030718a05285100402c0545803481882c0c0258014450103890b80c40c184001043d1089426507806528000803820301d08019000112010180c0c030304010a0b03041c80b0001e02a16099400d4000c1c03c3c540c248001d004203590540d0105119284c1e03e401260b40c0d64648412000f5200c00717110304410380c83c1c1000180440c0c604140d841ca03885109217400210464a40601100d513081078035051442955680108100450300e1035008074030030b00304001e1010422079000500c3c412910740c9218040c2c1d4403641207a106c400c0001c00640c2c840c2c2e00c580981d102a4407400c1059413034000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 563260746 1250 563259496 563259523
    0x150d06090b0303160b190f05091c08161101150305070f08060105040209040204030b04060506041b0203090108040c170c040c2a020d06020c0d0314010503070905090717 73
    0x40807908100d50501208a0701e0b00c030348000080400c8120303030782d9016045000900382d0004401c1c02d0100380d51800c003400b9507034110300b5110000c40e0394204102030720b041c080782400c06401e116940824030384147d00500e00650000c901c80c040300c4d800050700d41c01d450400c01c0d0801030040b07518210452648240184120301a82d00074002ca5115a40396a03412000d011103000c0c104e95a0701c0b07180108610b1800e50000d1900c004081c0016003840d9a0b43e907242c10100c802d0710700310b5016880d0000c00104e800e02e031103080741007821100c0c040381c0c1d1550a1000b81d00d910513046418100f00400300040d0510403039149070f00040c0500049981c1d260180c9c10400d44030001d401300756218900b440c1402402500c5a203415110070542009800a0040354444450040a00400300e8000302c1c0a40c5103c0400d0151001d03003182a070110281644191032280281220111801ca041840001c0014400c4c1c3e100010044244c0e6070323402d030001d55a11040851460f011060340b01240c50b00c061122081c000c800891204000541c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 563261996 1250 563260746 563260751
    0x20706090b1e0117070504020c030f0a120506150d050a15080a03140301151d060d061403070e07030c110f010c17070e040209011701030b06010f0201050c030103030e150d0609 76
    0x2c82d04c40c40782d901d584503242045241d00c150424485890554001e1006c401d8040403240751011185049155420407490600403ea048482415941503801090ba00c4076045400c40c10400314100c100320a8001c6200041c2d81c1c030741d0b070340c00902240629480706a80190000b044041199185503103955100590302c00c03000100f01c2403003104488290401d60f8140c42000d010340e0151051108211101c05c0704140e060341c08000040d1010381515640010011106e4101010413000c0c00d000e00c2e0b00e00c00c090181500c1c02507011000400507421100031050308840301345400719881000410840310240b8504081801d80900441ea95000105500c0b0007090162a00da030070555100824036440034000311000c0d804288002103105041c41c2c1640100301903031050429408000c5003200c05104210240c104440d0b003900b4005000d0740750713088009103103410700e544002c0c480d03840c0480040c01c1901040c4001000d01c1806071000600303946810025075400c0440c6601520345c01d107004208050069032040184151 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 563263246 1250 563261996 563261999
    0x20d0b1801050103050d230a09030c0509060f130e0f0a0212120d020d0e0d111b0f100c0803040c330f11072301170a020706090b1e01 58
    0x1041070085a0407285c100d0302500e140c03042c03a0700c00da03108a0003082911001200c0d0f0903104003240703401c001d0304c512a000d07545c1142580c01d600d00b0f2201c103803860b0086403045030000108085960740500060b085401561001c2d0600341da02c080001a00840905099502800101d0f800c05d00340000d5207041c0d0340c000c460a0110b040040d4007541c0312040000c2c1420074410400035000412500d8000b8010640000300005a4002c0240e00381d05001c090001c000008040c00081ca82402d010400c1041100203008000308000e0300d01e00041031005012030440c000c00880410030f00050140c9501c24100750800c01c001d94a280500d081c02130745100340508401c048004040c060001400d1410703000c0a14103071206034101440110540b1000f92440c405400c21040d0021400b0590050200398000c1418030640750707281110042c00c210031840e2481d0203040100729202601081c0d040c011041e0040c2d10303d00d0040c0c0c0d411550800390007514000310050641e003051001d0100f5656240b24040025085407000720a69 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 563264496 1250 563263246 563263291
    0xd060f0510080307141009141e031e040b0307051308011a090405011b12060e0402010e010807020a08070804150c05280609080a020d0f0207030f0f020d0b 67
    0x7140386008889460340107210b160006100001035640c04079981040b0703801c019900e0102025a81c111004682c4034045e140c114215130010000040e007138401c900f00601702d442d00300010b940e0780502ea880e1030400145038445400741d042481290050810284210360f01d2901050142240d80155581203041646040c0080c402c08184074080c07407943e41031102202040c88400700310090b040900150f40c40d559030700b10141c440e4440b120343c40c08a00e40780c0301c0410f05804501c50f1b40c00ca50140d0701c441803003051401000010707170b4403030b005c09440389003424075048540301ca100803850000e290b40010078403080081c840e028420618003400440c0c11801c0440703100c50364054107c46481c5072440c000e000768800d00541d0010760f124202c455100540c0d1014140d00c50b0395407120411f603141a0401e507403e0100007800035265506201c03d015500c0c6031304103441c85001044009541d22030904c00580b2251000b40c148040110b40502e5103079068008000840485d041d041070a140700055030f1804134080004e0745202c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 563265746 1250 563264496 563264521
    0x90a09020309030714190501050a0e010902092707061805220e0c0603100801060609060206340206010602160b0f07060207151505010c2006090d060f05 66
    0x5031a01d8003e982040119a50082d04c03030700d00580603803a402044440c00c208554040e02c0700c0c00900401c00491903007000107501044038580c0110300c00c1a4102803624015883d480c2d42d65801000d200b10210305681044a10781c48800c40d84802c1d1b1244c09841000182c00380d001036100400b0311100321218085035203230104200d50041c00213204800068488500503003001c4d0b4414200d0844040c140c03520545070000081543c1c0c0100c0d070f11543c0a030b080740f0502c00c118091103060301508503814041da0890602c1c03030180d62802d0081042200300340e140582403d85410b00c1903600002100113105a1103041c145003e500c13031209008100040c4685861101c6003044041500d0031601d0003c2c0f182d20300600c103014a00b080d400240280e91480c8c00708514000680807001c040ba540e81a074100281711030a4017883c001c008420303400107040002030b983e40404141c3c04201100c0b071400204c01c10060400480c081b071030501810002c141d201c42d2842c00e6400344101c0360000f076071280405804004c590754195040e01e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 563266996 1250 563265746 563265751
    0x618010806040c0b030f2403070303200a0302030322140f1005190506030c060c06070906020c011e0e03010608030c120403030503190605100c031106090c0f0d0b010803090a090203 78
    0x8900550115240705c40c80a914403142c086d1107421f038205208075010910300052a4004c60009000c5483d010404804842003d550807007580604043d40306610002e651780009010714503018010b80d0030008200640080c032135015400716104000d070f441e00b074041e0345801a4010b001c245028040780c0038100651441820700c5641c11f900869414440340701000020039005200030740611406003100c140b55580c4000e0310b15201c241c0010003451500840060079411541d000c4c2c4150740c8040c031594416a000044524001c143c034824910700c01e008c403070880380d00c0c0f07a0f40c400c03c0c5c040d407074414049000711010009010521021040f14051a0729094510146c032a07440003600140c01030002c074403a500303041510407180c54100c00100d08640c9a0f0005030715403880c80c0750800032070b07840ba48030402c140d0000715000d41560000050311132403610b0300040741c9900c14514402d100744c0411003c000c40340d407060024603c240d0015082141580c440fa0b030300f82c0ea0381c003042c0050300c140044807001411041238000c41e032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 563268246 1250 563266996 563267011
    0x10506010809120c03120108071505030c030105060304061812030b060c0d0f02101401050a050108060d0809420301030c060e0607200916170618010806040c0b03 70
    0x102c0303541c080700d419495007104e0b0b000380c140e000c100100381c440441040fa0f60301a08504000d4154a8070b090000340c80910300131403100c00c0c80014020400c4000000381500c3c1100c03800d4030380300e690780ea0300e00e000401042c0c5268500160030000d12071130113020800262629142c1c090b1420005da010000030008a40601c2c0800000b0794401c6d5001c00046100e41121304000c2c0140c01151400c0302d100986905407411080c214103054000401040240f42101030a8010a03080c2014052802c018020800c0b00d0140c0502400300d0100142e0f8140c40e40b5900201c600d200c01d58095040d907001c152480400300312001c03156030300005080080030f00b900500021a8101c0c3c5d4820039500c07420345000708c01c0c0d900107122a0542d80c4448144010300c0812a9028240312080c240401d00e00d076110000c042201e40d010107880b000c8007100850007200a01d401c5205a40b8038202091a040745030349044c0065024054408441428030b804400058065030010700140030340c0c41500f0401c109601c1e00d03c1d0003006d0004980300d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 563269496 1250 563268246 563268253
    0x60503011e0e010b030a0f0302010b01030b130905030f1c0b01030b010503220b0c03180d0207050105090a0f0b0c06060316061b140a02040f0b0d1401060306110309010506010809 77
    0x810701d004881c0c1c4a40d211000150001c90135005280000e41000d103100c2060742c400410464001c00c269080c442d0111481003428104444080ca0303010078011810011451003550741d0b00402c0081c0281002a12000e072280340c0d0707295503031403552440600864404581104070342481e043c00d1003036009000b40280040c040c1d40309800c5998030480d0800030203480b00d480c014560000c41d0340001c0307401c0001c541c1c4030703036204040c155403820800d0005c45207110107400c50308030740c121040c40440c0c0c603030204012007120000d180603903d0b50b20080001c1c51404040d0301075418a0058800064240804c8001e00751070408007017603a000b540e4403810315441ba09284002d4031803620801d400d0118a002e0543c102c200b40089058101100b01c5070354886010700402c0b0611070543c84a907640342140b80c03501404404040b158000c2c01007403d8600454001991984002d0410240701131a4103554404d42c450002180c010343e00b444030201c10310345441c80385d109544010703581d401c29000801a50050140318050f141ca82d004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 563270746 1250 563269496 563269541
    0xa020a0c02061c021602030607020705030304260f011b0302040f0e070314040b060a12150507050708040308031b03091b060408010519060602150a090f0b040309030606050301 76
    0x81207001d034441c4085201540c0d080b01e10306058031061000d017030603288903825808815011300400d490441c000700790808542c00300c441404070fa00c0c00b106950444180513111050000410340d07404069204611a50b13680c0309440c800c500f081015004120b002904200714480d61003052012820703031085000307c541451001c80208803c01020781426070040c5c45140000d03109040c00c2d00709140440903203042d0390b0080c41c1c0c4188529858480c000c100108103040c9689c401c1421940c03104001422600c84080040c0d5810000d400c4034058812140aa64060426540c558482c5000c08998000303445142d820302030922545804041d1208480c090341c04a401005002b400084c4024031402c01802690461018480000c80034801d024982c0507110070300c00e41d1200040c148000045408590003441154017030082c4802003064100e64a8020005c40e4001c11940a01d00302505600c05800340240a80056010081859804201802503a206070702c248801c940da0000c040c2680c030050b500564a4505415 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 563271996 1250 563270746 563270749
    0xc03030d09211707030b04180308071b020d021206010312020c0d0305160606090c02030919030b220819120b0102070608150301020c03130e010b0a050a021204060201140a020a0c02 78
    0x8025a110700384e86000308002500c200400c080d84d4211022141d038401c1101998101070300080441c0e400000c40c51b0160310b0b109084d1480e0121019500040e0080d580380105009544450600b0007110f1800000c8030310030b5a40f86000c560314103074001440c00601a000d8a1500c525150a480c020180c043da00c503800c040c2d11030200c41c0250700098040b20556510b490005680c80c0f40d01810a2205054014613240c02204060050303140c0c0c0380c400d403034880142400074000510034018503070b00145070000c20010622080c40240c690a41d500000d4030300480032440f00307100004031802c7c01ca420b001c0d035202c50303110760300703d5109003681c00c1d010820b4056005000140001032152198a41c007580c11242a07400c1c500b80d501081c221fa00110700c01c000750300002001030750300b01d00b440d210300206083c8952030380641c58904041c85500681c10039000f00240000d408043c3d80c070030010103046503032207000c441d40d5070303542d8402a00802d540102c040309160288002908044640300381c2d00b00306015194100400344030390 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 563273246 1250 563271996 563272037
    0x8070602070f0e13062d06030812090c04091103241b04050d0516120201020a02040f091208240a120201090b0d1d0318010f020c03030d0921 61
    0xe002d0707040342a0071080038011400c1401080e00d401017020301d5809400408808002e241d0740c070f01b01040031506041003000054a4130040707601e0301e0420040841c035a2240b450a9090030501d03000c0c0d6034050304106c02e260600031444203101c0b80b00b80403802ca400403141302920310004c007010300c0080c2418102d01d0000309008030f032401c03960184a103a03048038a8607449100281c864441088161107590000010340d2030200c6459404025044041c1048041c503600c2e40001d40e1040010f5000340160b848000760321031854941c014a501d154814802200190b18110040140704201d80e04a90b40100e0151001d84081041950404400180c21101c5071400d194401803140c0074001d04a0412030940c2001a0311018000a004268110351000c1080c2d5027016040000024070b10184141d50070802194a4510401c042d80000b0b00003800c180040d681080c20581c00c0402c81948180c25000004821035080703003e62003142c855100711114151384980303e142c00402100b0f44c081c60b02290010003040c013a0384124 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 563274496 1250 563273246 563273251
    0x302010e03070803030103060605040624051803010e06041b0614030612030a020319260c0d020a0c0209010f030b13050118060b0405070f0507140a0b0c0408070602070f0e 74
    0x181c1110b1682e0303076070354003146103510990060b5401d076501c4000b4001c914107400760704010404201c0010017100c11549610208003800320701c200f402000509940205101081150226001002040040c0021401c1a1122012502251510340700d40110b440004034850340c8003601d189555580050101030030380b40e8560300140080b54801d00310114260801402c10040052810650103952643c110001104000000e030910106012621141c4080c00c203a162b20103207190940802501282c0b560940d0103e507219031048140d2585c00010411030311034000d68401d035003901c00d542c0c1c10103d07070340c8a0b0400b40110070b41c0401010b00100c1008a81c8100c015102034404902030000040c80342440d92605002c1ca11140040703580a407114030b101c1440c0741071300c90b03c0d0340080c007400c000040c10300029005040d40315500d00104190300390300d030303409c14542c080000d0140c20b50f201003030f40001c0c10942240307215030b000b40c402d040701c9100384000800c0051006c00d001e001c55441c80001c1c030782941400c1451204c43c800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 563275746 1250 563274496 563274499
    0x50604020c0d0216050411090907030e01230a0204140114190e1305010e010605221e0902041214010e06040b090c0d05030d050403140d02120a05040c0302010e 69
    0x901c650300408000380b080120440c0705400a02005411070704c0c0c1100303070740c3c1a03003c2072140d40303406200002d0610480443d00c821104940000c416514410306900920130150560b807150318004281003803040c2c12283c1441d000035116801402d60742c0d080304c13500b0380c403c5000d9100400209443c10030705e940220700220841e10202441401c04801c03213000d50140ca0318070304d102e0015021410b124503506254062030a11240943e0074403540d0705140130400403a906208803c20040c2c00902c040504030701c1007408001c0000728404503141a0b407507103078034a4100406146646c003800705c0c800150b2424070341308840445d0111210b00a680780d458903144a180d007020311101855403102d500d00c03505e51051001700d00c554400c2c210b00110341403003d141850814855109400303445c0380d0340c0b03103c0810b0000058600b03010041c580070a00fa52140740c101c0b1001e068151345115040f01144c0304105901c181c0261401c100c0710b40b01040d0070b588802c10703481039078400e0700d0181089422a01c140095445112010201c400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 563276996 1250 563275746 563275751
    0xd050a031b0812010e09160311060d0e070305010608030c0c01030f0e0109060903021b0306040b0912040305010c08060114070b040201050405100305060a06080c0f03071b080712050c0a06050604 84
    0x75182c6811001c0d078851600c00c07107070840c00c03c0180526442c80300b805801c03c015000030a10300329017094444d8001c00310b010207404c00340048034503505980c903d4102e03800302d10954014800c00071050005680c03803000f030104450780e50a140000c950540300000b9218070b10364940c01004801924001900184860520181d403a51510f10900e10340d042406440500340c03040300e00041c901e5280c11300a080a8074070341070020055865000381e80d99500050201d4106800650542003030311a0050a1700e0710400d860080851040880c0000c04d110065210a542c000c554a580045a603a0401144c03651580f000c1568880c6060201c44040360301e1403445a0301910605007a490305841d41c0024900b6507800c50300b000000e403200100141c908119080078003c00c076904104c1c00b41e0422004002c07090182454442c0b030b048020002030310f041c0c412030315072512803007100078840006450305009440b81d001c1081661140803440c40031488a108204807075441c3c3c0b02e080a00192a0141e5a0780003030640035100560064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 563278246 1250 563276996 563277047
    0x20f131d100c051804090b0c0304020405060f0f0f04090210050417060c0f070f0b011206060b0c06240607060f0e0a080a03020d0908040803030f090c03100c050d05160e0d050a03 77
    0x18647c1082c0380c0034607005072010f6101d10306841000113440b001072125004502e142c4201d50a5160310140c482e0032101241d41483c0e04c40c103400802c0040041c03035406940b281c14103030700d9140300341c2180040007030741c2c1401da241417549903491610380c0d42c4006072225407501c10100115200ca80c480b00181c144180724031803043c14441140c50300160305400b82c01011140b41810148410441141f0481c80104100007006090440500c0c005888400080030029108042800040d2040ca241d5243c5080800181015203941c25418400b00030305805031940f18080c90a69182810700c0f00152020940d07074040140d078582009000110040d401010482000549440c01c0500058008002d48054003035a4001d50f00ca2802801c058180c0300098280c0c3c4107a008240111100c0c0c401086035083d8500508010900620403002100c5034455a02070b07040039031600003804a0b015041440554040c00d41d682e151100c034041c0f08001505141500084c000d502010f0b40d0b4001a0290010030070b4051050307046510303070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 563279496 1250 563278246 563278253
    0x11010207021c061e0b01110712110d08070614150a06030e0304090e010b09062b032a170901080103060b21010203010f0605040e04020f131d100c05180409 67
    0x444c5021440c1e151036100d0500ea40d0719640150b1110061f004031000300402484e10755508500c40d0084001b8003503500320907080c0d40544580340441942644680120354418071400c0400c024450711032202c50300948400032910003040c0308413103001e245c4003c0c55420054503102042c1d0042002d07544450486c0070a000015074006103100f44a0008090340c00840c219401c007041011251000705100c0c4030340d00b02d007040c039118071004a1031061441415031000340601c246c1015a1001c401c13100f0500303d02c0403205080803039001d000000c90014460794544500d000e15103030743c0056000e0f4203d40d84c001244100104042180c0e9000a5031000c1c0162030071151403403040340b04940500724050790504dc4e4001004112403241c403802017004000c24a8520701b082c1c102400c1e1100c03c0400340001c1d106d81d003446181d4907140e840b9404540300b440342d410208603041c80c461071011310480100840b4034074040c4280d03200040405014500350140d2a983e00c528002161801c46030306035005a0141d0060783c1c811402002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 563280746 1250 563279496 563279531
    0xc07031d0102160b090907050a0f0f050d05011211010e0f01080a061a03040318030c0303050c0717100608030306093d0801050601030c02060c0f0c0d050a11010207021c06 74
    0x1031300140303c0580e40e0b90400c00501082c0c00b00600140c040041c10444c84541607070100700d544c00e00ba140d01c0e0500000e04805c0c021038481c040c1090b0b08039614076240c0001418441034048960542c402d80721030085214200056450316a086901c80d00400300301e5058440d584684071135a407007500309a0004009485e8050103400d02e20078902980503250000030700081c50b03040440e01c104030030000d50fa285aa401c5640d01c190b01202d5200080c18000049100b203046003082c41100058402c40304440c4200c0c1c0460f0340c1c04da8034140c1d4684a401030f8601900800d0b440c0001c0101ca00c18a8045c101e40d40230380b80c2c2c1c4043c0180380384031998250942990040310f084582c1b1400e895100b00c505914100301c2d40e003010300d0182155400750001e4145031901501452007030b0003181035a842604c0340046901c580c42107160803d05d11561034180e41c00e00601d03815650998004014140000c00c5994081464880100b40c03400c03441030f510081d5100520190290345100e000701e05030449481820049124003015078204903 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 563281996 1250 563280746 563280749
    0x12030a020f0d05010308071a10030803091c020309100914150c010e10050903090a0b031b040905070201290d0311060a1d12030c030408121e0c07031d010216 68
    0x40a10300001d1f0310742404908404210301010a43e010421814103200030015100c0e603100082c21030070040000340600c00140544203d05000c03600060b0710444400700292a6405444039520801100e11229500c51141c2c40c4081900e002b843caa00c03421180404024010003c90303040074118208105030380e109402809040c4507500b8400051001071324009005050701d00041c02200d0303541c400c3c80044a1070307403641107400c1107404420300c403070790703511002c5071900c4031195039141e16007d00c0c1c00900000e00045603072016106900b2903008222461003400541c0560014040c03e810302d5070411241804d0740340c15009220010702c00d0400e10500300004215504040c003c59189440e165180840568021003046845040c00d1000203016010401420752074203010280040c95008804400201003020b00c0040340c072000302d02c94164a007032a001082252604402c10307090300c44884180404e8200f2076000913528290b605031660014600320070341d0015082c02e02c1c0b405904520543c0f520300c40c0721000810050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 563283246 1250 563281996 563282003
    0xa060b030f1207110d051005091216061b09031103150f0402010e0301270c0902120a180309060302130504061421150c27030d0212030a020f0d050103 65
    0x58650826052a8050007a440c42d100c5c001c060080207030001800c0440c81101f0081c413003100103500e49860329100d140041080742c1079810703d00000d211016500c2c074152710015921a10b81446004a44004016441605001c450100f05041810b0001484502c0090940c4502070119508400b0290044800080540d4042e1200c0191010300044d96031003007011381021020750017800384060001d01c41d114480004078907400e2103445c2c0c1d40c110800000410701402080b2880302036454100c010360140030850140c482c03214003440c1a080e4601c59280c850000c01c2207406840303000c5220301d400380550195105610759801608500d1011409944901c034070301c0542000c011030341000e1820014041a0088446c6108010403440b900143c01c80c40010000300542d0340c1a80c41c045038494440b0441e00d4000d11841103407275000400c0030345014800e040c5000952a04030111401d130740320b110702641c4451814880242e07001007000040e80c0d0084580042c6040482c942c1c045181c10506a842c01c111407080e0001c9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 563284496 1250 563283246 563283283
    0x509041805010e07140f060405031204060813052e0e0106090b0a0506091c051009022106011509030803100504110a0813020d02030a0311070b0a020a060b030f 69
    0x200305000003449041c84000b502c02c02440000c0c10701540c180d403100d0424145215482102500c1c6140d1105030982e8010b1001408072a0b9405143c0690007298205000f0030002810314800508400c83c0f0480800300207820802802d2241480b41800c2c9090504030781c101000d60042c0041951214030340710749030929044030000141c044c282105c160551f4400712000344200c4401320107004035500d11049880f0a0421240030007501200c441400d50040b0460024025014910810142e50f4454101030f411504c00c840782800382d45415140410314403044515503040d40424014480c08030290490705032192039082a049a5680e65070b070000d294022160200545840081040315040600400a0241e022980f190400322000c2e0700030f262210040850068840d82001007080d0344518000d441001c2c0c0107415a640140b050038080c14a482c01e001103001d602c80c9a00c0002d080c1800400d880729501d966003d40982d50341c0d51205c2c4080c0110040007941806065600d0408000c108a41c01010025a544 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 563285746 1250 563284496 563284541
    0xc020c130b030d090e0601051e13170102090f09060102011e1506083d170105010f0305030a030b1305090c011206140105030a23090f0105040309120c050604061d0f0109060f050904 78
    0x23004a2f8002401d0007113500da0042c03003c54401d5441007142080f00d00c00b51070f45080b0707589050040340500000020010030895803034148100d814a600040c80c0800c00d540fa111103030341d54282c102e580d081c040b260400d020a464204d454440540d0b10208580c0c446100d60344d000303140740116095405a1030b441345504e694842d501c5100140280106401070104412248440349103803105916841510120030826036101101e61312641c48481240031602e0b280c40410151030484101690342080340840d50224802525400c50450940101010303180c803003400408210991005540c1c0d5080500880a265100c46d10410481030344036216001200b006156111806e14802e00b5040400c10780c43c03120300741d043c0410000800c1d000306214003100c00083d0010306518240c2005420b064694203e00d0f4005000900011825402140c2c00c0400364039654400342805440100505030403003656031400304201d1982044a40e0007485950103e41c010305000c3d15008200000400b210102050400501e81070b000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 563286996 1250 563285746 563285759
    0x307081e0601120803010612020f040b030901050f040503040603020703051603020610080304030c05010c03050915090a14090a050603030d06081006091802040c020c130b030d090e0601051e13 83
    0x24140184402190f0b680c0c1e89200b0b48907403080d84014081c030f106005004040038440f00e02a411a08160b40c450811611280c03038aaa80002c3d030300c2030f503241c0899824070300410315900201845c2401075078400010b5217020f1400405401a42007110250180003041c095402605148048003030340071b00c60341c050001460041d05101c4011802d1b001440746034818401840011906804441030341e40c01d09140902e1780d182d1500300c03428450040d500f904a01c140001618546041d800380003810000c4481d2001c65484110000c00c40c1c0c901e01d107241d409030391031000c1a408007040e8031164101d54050306480c6051078070306407182620f0055110a04c030364800050506165418030401004e045d24040510052907007030301e0281365959034078000c1d01c500d075104405201e0701d008201500b12000c2c040e104801c075440700c5005d200205125a11240a03003d982d20b5022400c0c402e0943e9800d03104072005c06406911403070011038041d005105800048010050294148001c00e4040e003c20744c485403158842c43e045c000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 563288246 1250 563286996 563287003
    0x50420221812020d170105010309141605010e011422030b0f01180b011d01031508061f050d14011811040605030c030a0627120f02070b16020307081e 65
    0x100780104210485446071808050000024110b42003403a0125800cae009060402100550001e45103041c45010101d2848400e040c14800844c0c00917282e00d041130b4950001512101614038520185442c00c20000c00030302c072990703180603c0743c54600c3c107520840d40702d64808500b044c0035184226802d40c15801080428241d80080c40580c02207201400a51030400001e04040a00e001d40721415400ba601e090b2140d20a0388202e181544c41290035440c40e07590102c0c075031188015036030903179680068010700300c00710000d54588080381d2011740420015001903c0768060350703400da490100c1d01e540f01d400048a0340d02d11080091201c0c002e141c504a07980c4041c0801c8100c03800380d0f10190103a001a118800180e9001c14a50102a04014003194005445060380c042421060a400314901414070303150900010040076100301000c1d880e4a22080e140318401e130380eaa03284c0d1188814603682008458000c47c1d9003030045041910280498144a40b0345801038245a80100140c541c2c440030180490f23241001c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 563289496 1250 563288246 563288263
    0xa0b09210d110405150304052b0e0d110112060306020406170a051605070f1a04121d130f0f0e010f020403080f03070903050303090105042022181202 65
    0x804a4500c0c1c249044042100d4828891303581e4110b201c0400041e09000d02402440070b4090864010017020b121309d40b000c030343c03400361b48440030002c0d2740504084624140000440911508007004040012095004550f00041040079040a43d2200ea0000c0055254001703080580700c030f0b4854080e40881c034800445024030007008421076038100818401201100c01100c0340301040b5290040d40c03075a031410030801ca03003283c0100400711200040d1704204400004000742c0a64407892400b140d04102480480c0d00704800d403610303600b41110000d4460309160102d0000c034400c0305c0003008186040c180b6600d40403254408803036541d083c0c8840c00c90500f58801c0c440c0324400a1065021410f190841d01d4590207802096581d840740c0c0300000c04207442c180071b004d10300001e5034030100f02c959030b180100200c2c0c042e110640d000c5410606d410307040100192030300c0c02c00001400103408441e80410303e1540c20740e0310070f411107104100c0e0b03074400405403880810512248010300420501d05030103803d05000746001400d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 563290746 1250 563289496 563289521
    0x905070e1e07020d0807030203151201050f070f0e0108040309180b040e0a0c0504050a0e1c08060f01080a0c110d09050a0f030c090504060f0e0a0506180a0b09210d 71
    0x395107100e0304d604000340d6a0001054640180c507a52241c08481404900c42005a80443c12104000e4504e805410540c4241c000320071858413070b101c05009544515821840b01d01241044401c841d032548a00000c5510038000d1900503211a0b50319281e010241018641d0b503985516111000c840d418240a0200421301742c000506c0100800c0d200d518840c0200c0c020248150784a074040385105c01290003585051803840c0580b02503010300c0c840010042000c0c816040401c0141c03000455900e07022000014149041e11154016034401c006000142040c4110005216041d9020b0380f130220200400c42c902541915088421340c20b0804024080d03110f0380c04400c0c0000715040520004500301400703400c540c4403083c0480e26486500e841c2002d80145801d4030502882c003105da56200304001000443c3c00d02031000e45d6000c1d1070301100c65001c9060341141c2e0880358000c0c00841e00149111030800e9002d0001026100414048401070502401c4100c0148504101145c801c020802c00d01c207e80701e505a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 563291996 1250 563290746 563290753
    0x70c0c03260c1b040605030102031006030b0a030b0a090311061806090318120705041103060907020a05120702040b0a06050307090905060102070303110a15150b0310090905070e1e0702 80
    0x1c0a051a941d40740004800c0203603480010820f491916150020720140200400030340d00c034584082c0e1142d5a000e10311031400001d060201100240c109402840141e90b0030064811503550b401161030f0240400078803c07420060405185e80c3c0382e420034440640101003100c0350440070001c403003412740340c14005440042181c008100d001d04000d000050b4202d50007054481c102c18244405840342461015804240c2081c144000389048030340c9030000710311600c02102d55814603100e075481243d50f0080140001e002d5401880d80920743c030210350145c10213604c0100040b0b548101d141c08101d90b10141d60000e030100e50080306200c0301c02d41021585002c0c140410b800c01c41440c1040000f562407240f4400074080c06142900c1c582000c00c14002c61220980015014441d121304a0002004000300480050b40c68410207011070900c1110301128060b2207010400c007122070800038002c00410026a0444061044c00070000302c050010706c141c0d100d0344c40c400c070f040512038084841d04141c9030002d005104541 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 563293246 1250 563291996 563292007
    0x80c010e031528060f0303030f140c1309020403060515030f03070201050f0412050c0f0d0f11120d020a02040b0108060108070f030f02043515070c0c0326 67
    0x82e0016299901496107004480e0040000c3c18290310715a0500e031102078030303007400008104519204800ea003140d01c20f80e420040003071050040340850303100b41d02d0252403400f281e02040410b890f0f800a8103100c0070a1110302d5a080d80d0340c40c2d04003283d000344c1c411107080c0e0b1201e0412807510340712020340c0c100035401c3d800303418aa00800c0009071a8498030400070706000b008100d11a000701d011094a020703010350084001c05050f03070704215650f41191071115109e1400d0700141455402e12180a072000b40e07005524880500155980d0b602070b0038036000d505e0300101420f42c2242484c0080107501c40c6920540c02502d680501401448141c90342c132041c0e181406968000e10909076400400030707030722024910b0000e584404080c000c402030800d80058055007400400d0104080358000c3d9003003844c0507414806685450091440c440c280803401403140c3e03541006004c90074080800070510351102c640d140c91420340d1603507a102c851402103a041900c0705041403118a4a04503080202d820428030180d4445c00c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 563294496 1250 563293246 563293273
    0x60e0a080d020a2003120a0e030406050708161a0901090b060910030506340e09040602040504050a06031a041e0f050303010b03062e05160c080c010e03 66
    0x34414007100c0c04880e80e00052450040348161036500281452403180c0d45480640051075940790014103201c9a584070502c0802c0e618140e82c4500b210b801c100c1d901840c2030914000301900d01d5040f521040c2c0304070100300b0103005420f18141d03d11314503512803800310243d4010682e041091440081919030306030324054400c00802c141c0a03405603c03d40481e41c0355403e036502004500030b41810360005005108010900190180c2090400050301009003100d4044469001707810b04650141403c0005c00c503460101e0100e07040c9100e15aa2250041c40017504e4a555100030504803141110b0410001e81c1c0c4910900030040ea0003004031180703103008506001c038103160f1554085080703400818080c80070032881a00c200002070b2110441c45400000b035075200e41c1d540414403510790080307a4040c456402121440184043c0009951000495a03d0a13278040701c1c44905803115840090b180030791003003441500c000244c0c072005e40005842400b0180c40c804081d400007500303103205081c1180c4030341c20890008040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 563295746 1250 563294496 563294513
    0x901140409060507020f0f1b0d1707110f01020318040c0212070b0a050c0f0336070504150b161703010f031703090613060612050109060e0a 61
    0x155452481144901010600060010992007200500701c07800c3c8802c21070941d40224444002000c1e001c241c42c01085071540c11030303c5a10308020912841410150b0199a00740403d4600210b882406503200c1510445000d007481e401c0304004072208100107071000704034104524000d007142c0c828002942080c00c0e80a102c2007516071110440c4c002d560390b1210b400c3c1280700300504c407094681c080880707503181d91900305901211000c4541305107150074030001c19100140c0b18220745503102c28068035800c68a030352000400c0244224070042e445c4440500000b10900c003000641c54180b0041e00901d48545414188400e40d81c42d8041600d000500e00d008110340720044085580350501341d01c20900c00f01203480c1140716100d030365034074124001000c030010484a0b00207012005483c0201840d0b4407091521440c030140c0d1208441803001c0d50022004944062846010500c002c0d10840d40450b4007500c0341c4210240203294081900c042c1c0d1151080401e115242c85405007081d4401c01070181000aa11a0101e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 563296996 1250 563295746 563295749
    0x1f180608062806030e070b030702030a0e0f12030d05090712110d140f061f050108071e02010c08010f12020108070909060f05031614060a11160609140901 67
    0x5040c4180d04242e00c03105030020101000600c0070300840e425140c2c41c0c010001c015007501484e95104a503070200e051010703042035a214100a600462400c110402d0484078518540560b0343c2220401602c055565100c10506080003a044011500e410075607060030191040508444595005400e080c8204007038440f15000c0140c0200c18184840c04003c04250400503804010f0980c4804003820300354101c1c0820341000a00c804004c0318650b80f203070f040008100440a0100607071401403482080305500031850b0036845603550a05100c3c040c00c4000c82d030760707050f2402c0384400103035500c0c0c040054803900152854007400d006070518000500340300a4400721120b00c400681400148000074504d2849002d007400a410340c43d6042c88415502d102c0340c43d22006c07a004130783c0b0a028641004203515101c116800c11900c650409942c180c5210341481030344c1d809a20b040d41006070790b02e1100035080003086040710041c2c680364169500fa1034890005d1156007160041c00700070074141040e914540d512244e050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 563298246 1250 563296996 563296999
    0x9060b2208071e121202070b0301051c0201050c0a060b0a1e140604030804030f03080106080f1603090203010504120908060106050a051308160501110a05060a0f0207021f18060806 78
    0x2c684440e07455000076041e40302c3d4403da002c40d105544c0c4000b008083c01d154140c146043c3c007283c1545480d60010551404240961a0001c1c400b44c004080d043ca0081114565401030401502d4190040d0116060461004043d0f84c4680c4401d0911154104601c0c003100400c81d40500320540c2294030040c40401030140f146150440c0182d82e41d02056503008120703070085134000b40700d6603a40c5c1d592500840445081105501144004000080301c601864400380b00d0070074035461000681d030711900c41020300041d60340f100030141d40c3c80c0382c3c07001600c007442403a00030780c0503000044501004a9004010b01c0c4103800050707581d000100100140c580040a807240107000f420f146460b0040210510f9001481d50b021102e01c0c45041303001441103600b00b0844e015038000380c0c3d84050380d40401c844580c1d10222298001e010b540b04200091107400030f0390006a041132044009407400d4600c0e00001c900300d41410406a04500d01120030081c2c60b004800044040c8204a01c0c1402c14030309040684860001040342e0f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 563299496 1250 563298246 563298269
    0x10f080a09020f030d080f070c0f0b04063b0307020616080f0712141c0f020922270b06010309170703120204030203031b0709060b220807 60
    0x3101190360300307001003e0442d4007500700d42061502c1000140141c1c001d03074241403003c0c1c1070301c0800c10701e80c811140c015040d90050001603094850f81e940c82e0104bd0001d10545a8a0b0ba40d4480d40f00c20003141c56400350041c44210a0f031491007600c1041231056440f40800425074410800040161100307002d44841d1414118815148101800c0c0b28000b4416107500d4240390000103040e01c1000340c3c00f4807128580d49a550b4543e10840e04401a2989110b156004c0303c0083d0442601c0d10019600d41100390000c046010140c2401000c0b07020a6004c0040d413645a415080500307218582c01944c404c1010303114003540c5c41c0440001c00c1a200e0840854400003034504040440000c4050b4020707045401401e5004400c2e00340c0400c040ca8030840380c6c212042c00c030005020302c3c1c90f0312408240c40c000c0c1c4050361340080c00345140280384099049500c4001c031038a0640d0090070000200c504103031189600414103050399603500d140030941035032a03400c4821004d44c8070303500702424081d4990000d071302801e4948141c0714 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 563300746 1250 563299496 563299511
    0x9060403080f0a020c0105040807140a0804140f10030b03060c040f030303180506010608071103070b061c080301090504112d0a1a0c1606140d0603081215010f080a 71
    0x50007a02c03c20380418015801d1400780308c10421100c005242d580d00be00c0403c9000c8550109150311042403407406000b024040c8410b0004180400380d01a0140c00100488000c14481c004a00848200c0040c100400c1c0d0315010b00005050070701900d94040c284068103882c0c603045c03010781503010f010350001404050340c0740004112180300c00410700440d038110701261501d40c1c1d2401c008240d10801c072038003000203070410680c569152001080d151210780c000b8003841603640390303018014040441c291113280c0039988024400840c2003500194042c010500e8089414582170901d0a03800180704401c2e4015003018a1082d50012190600c49041f001040d040900b4020580040c450344840c2e040900c0210000314580d03107a2220720000c20758004020240e4045110041c01d1000d00b00e41d030310401d0041b0700111266640302e44000002c00031042c401c5000606d080e12521007200781c2d040345a0410703d0404002c180108000801801c616088007407801600c16514500c0041c000d45006d0b0002c40c46a0701c0d07685 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 563301996 1250 563300746 563300761
    0xa1814250f0e041d0c03010e070e040c030f0606060305100b03040201030c230409150e1f170d03141621110d0609180f05100501060203070203010509060403080f 70
    0x304014104014000c0c0600c200c01401c8010b42c04075010201002d03ca201000d85c841d05040c0100703100c24a80d0805806084d207070000340c02c012803009204860740010003402100040700400c00780089130042c1000030b00c0b141080000307011600003070410020030030641d00030021300f40e850045a50040d42860049010503100707500b80c400b09003100c444400c8403020154002c04c0898080500100c2c1d0100c1c43c240000091003c070841d05140c140940c0184041c00c200042000803181500d03062012416031a5a40030b584006031030715a15100c007001c00d16003211868034071450740f6000d8000002d400c001c56020a00300f022880034045003d230001c40900c020200f10b0319149110800c142c18002c2c03050424000c440e000ca411240d9a40403030b0000700454900480403410210621900c40036072942060034200040e50788560f503480b0031829007250f151046403008491784400d03004060007000e4a4000b1911101c00d84101401d540005050503076581c000c0040002081e44440081d4000c5c840341400c0301c080c0c03a60311 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 563303246 1250 563301996 563302007
    0x20a06180305120720101d0303030406051f06200c04020c01050f09010207050601050906210606011101050c0318030f0304110f0102010207200a1814250f 67
    0x1070028019004110603c0d5a041c1403500130598a0b10502860440a40540b407104286a203070402030380003001003031750300c4106000740d64080c1010111b10074440340301007010009246a0013140c0482c0c2c055260000d10400c1151030140342c40060f075003036070100500c0c140280242101c4401d14034540d9154000e0303a120010005016401710a5000380040d565100003400c12806030409480c0682c03640305d204c000510218040c800d49120540c000054804e40c2d10780410464000c07005484168040301d92074050b80514020314102e142905907001408481c030341040017400341900c03440710b810640d0500c0100640c86101d401100d6214100607400040071105206541c07a502074102c00c1841140000180020320100c00b11a0801d400111109030803170071141c00490a0b401042d0000b0b01c01001c90000c21200b00c40301c50303041b0b50650040d00e803145e9243d031807071881081d518078008141302940e105000324001180c4848a940f180000b841c00718074540220780031000040d20304054040000b103008031804c1c44c6c17055 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 563304496 1250 563303246 563303249
    0x2d0405030303090706020c03030c0d050306060c030d09050111160807030201150e161106042003010f09050c0103090b010603050406021b031309061a09060c010207080c07060c020a0618 80
    0x40c04894407840d1030100300e642c0342518012280076100b1a214180700385000002c4490402c501c0b000f0b4180c030390310281d0640f007540010f000141c1c000c10034442141200b40070000b42c80c0d40c440c40e01000c42c5452081c1407080c03c40340c1c9004220b0b5540c0d010420790a80d08020001403036610b900001c44c070b071b4030440341c141280144060005003084c084004030008030303141c3c46440140200c0c2186103080329030302c1481040d0345020075010301d040250455400540418040344814404806181880d864050241c00203400c560701c00075400441c1b135807598a1020b1090030031407401000e41c2820108120483d5071903101d4514414420801056150400107003041010f4040d6001f0013142c5010180c064001c08105413250003041c402541940108000034082c4d409010390400c4519400c801c0001081c001140099984140b90765a0801c00c1001800502c500c24401480394a004030141d50b150900c3d004403600381300b400d5106c1000c0002980c1227001603581d46514030f080300c0181c201082010324611207086078480c039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 563305746 1250 563304496 563304499
    0x8061c110307030f030f020a11010f0e090703060303090801050606070f06022104200f0409050705090705090306090c1c0203150405010501090c08040507060c2607060609022d0405 78
    0x820300b000040000307062040d082c0d0b5220b610750800c1811603d400f00e903900c0340c0c0e460241c41c0921450440e074240d405038446500c0503801d0300c2d09080e4040c1040200c0d10340441607489100086e95864200300307150707000f0103001c042e0020400030702403401d2540015506010f404806041007641e200480104003003035045614481130714070181c0c05800300c0c03504402458000c44080c0c032042508000c020110001d003504041074000241505240144442444014458841f048540c2e1041d210089082c2da2038210a40c8510000c0d43c1c0d69a450040406050070014042c2a43c4299400080360502e141e40d1141c04c1441039011841c0c0400d481c0007070000901c0c0100d546405030607500104103203c140041900040e0594800b06803d21050710b03100c6d001c49915101711000341450300006000d000c6244544e00f005104d43c010038100c40740d0302c0d008101600322814904240c1880744000303090f00402c03403a070180740014045101d0441c201148081d024a2040711203c40c0303588588110440d0b2405000c1c60280c801030300c2d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 563306996 1250 563305746 563305753
    0x13110705010612020f0d2a080f03031006050c030403031b0f110901060c0302030405091008060c0705061332011118090106201009050303061008061c1103 67
    0x181c424000103e0700c400c0505034041c034150060030015040c660050300c40a580103d8681904503010321541d01d0b10000b000216a191615100042c09601040000104181c4401940d0b036803c0a810002500000e60b1090741800300500c030a031a005004010f071070880e0f400d402d1128889440050031400b241006200400d42c21190041b032085c41420348240e0265030702031381c0500c90f41c0d80312681910000c3d500c100040c0140c2c404c000903c00c07400c0c143c042e107230420500c100b14811a525001110300789001160462440400031030004140501040f05580008403200802c8001440381c5825518240c0b4000c0d4040200644e5041e0900b410400594200c18074070300000c000c00c8c410030b1880c0c011a801134003003030f18090902c00ca0211a29206854904a501e41c0d15100035010380008846500c0050819005550142d005291a001054050703540010b214502440c2d4901d0b01e0000c201c0c405429001c0d0404000680003000219201c0103104500401003c0c410040c00d002850203802c90104001d1840d050302 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 563308246 1250 563306996 563306999
    0x30304030b070815090907050d111c211b03020a021e090c090f010f0201091703040311010e1009020a0f031211010506010807140702040c0513060e131107050106 70
    0x258854a0940110125288000038a1044c420054601415694100c0680261004200c079142c02080034550501c41c1c000400280d82d00030004040301c2c1121500300710b00e00c40001010400107840389003c101c0d9140203a0b10315054901030002c0000c0c41c1d445050700718034082007003c0189402008011308503079000f8078074118075014008100300032451112281c000c44005010604401461041e6010410041d09420b042c603040001142c0c001c001941a4080d075503240c01e990040742080c200c403200b1141c0c911250740e90307081c00d20380103004480960259603c1e034035090700d41800d00720104000141109a500c0441c400045000203145049a0707444a1b0b81031800040001c10000001c009400704038080c2c42e210700380323503103004800c0c02d07903004442c424001840107001441c01c80c014928408040003090724541844c0d440d80c045411038083d0440391000c902d011584140044103643c0d281c000d41454500b40810301d0244010072205c0c4009807103007244030f4844442002900b10001a01d1986030454001e2041e603 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 563309352 1106 563308246 563308261
    0x240605160f0f051915050f0a1a0301022a0607120507090b0309010501050a170703121103180a060908030d1d030a09080c01111506030304030b 62
    0x5a42410840c408182c041000b0006400c514918a012004c541840c14003051200e400c2d03903006007850708001010f10aa071080b03070003c2c0c020341d011401810801c40c684508550140b0705400d50301c045050001e0100028a440101e8455101640d02001004042d0303105d101c12650b100c0840d2030b88103000524400380d8002035204500b0301c0e1115016440e0005051194030545810070180e4407200140210304d41540540300038003544d1140b4015402c2e540b91070b07858800314031014002c940c1a031211400b060080d043c04503c0075444046d02e0380c5450708180c410b00004190f107240d000300d400400c042802030140529000f5a0a070500035801d215000300e080c80a000548051803080c5001e4061004213003003080a040c070201c180c1c6508000350b040c250b04a20f0512400c5080d81081281e41c000c1c004002c0c0801c11020400c020f8001f240141c0c0e032480400d04d18840c65100a0080d40e0a20802c01c5c0c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 563129496 563309352 := by
  have h0 := BRFrame.cov_init 563129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 563129496 ≤ n) (h2 : n < 563309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
