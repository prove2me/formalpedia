-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1288
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:11:12.931044+00:00
-- url     : https://prove2.me/submissions/39af795b-b61e-46d7-9f20-7e28ccc1a628

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 231474820 ≤ n < 231654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 231476070 1250 231474820 231474827
    0xa0201050f03280c0e031f0902063708070203070618060c080115020f0a120908010213060e0f010e0f0301060905100306150b04031518060507020706020703050705131404030f 76
    0x517022441a00a8209030f40110b01c04884400700b04014400c07540c8802003841195034107812103036481413048020070b008070020080c3d2105c1101c2040d00c1c114405941c1c84440703490044031143d1040c0002da00440c5082600c0d6180000340501180040c247c2005001000001d40300d070080c1c0c3d500303a1003952414407a40c50900c0c6000e41c2031800e44014203540140e202c07035060140c04500c030030b0081d800c224001c0702c10401e0351b1308403503c102a5010317a8055102060403810b1401c640310410465651390307030340200c0d0403000c0100680301c0d10502c0154003248002a101a050800c070b4400b495048006000142ca21341d1b0351b14130000d43e032086459811020b1217001c00e101b0403100780b05406418401c150b40b5021b41c1d08055050ba024419808080c154201c1440840c500e55041d4100e400d01c074031481c07030040050074142381c450301405c026205a005406400400320300b080c4002014012241c0200041045529200078000010314076020a08640e031070343e00245000081e81c83d954003491283e42c0d4014102441c0c04000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 231477320 1250 231476070 231476087
    0x5120a05070614121302031b180c0304032a0f121e0c0809060a08070806220905011b020307061415130f0f060302040e0a0201050f03280c 60
    0x4000340450b607582e60444003c06010389180740d044086004c910b89a60b600361004a1140e00001c1d07040c49860103203041c60901e807102180b88482034948130344a03180c80c070903900d00b0102100c1440c00050188002004280724145145204500d485200644400309030040500d0b00d4240040c0c030001c0c403000300d000c1041044802c820b13681d01107251485d03c3e0b6040300740120044140507901020400200c2c0c100c0c06004141c0111088a100100150341d10760200340080c005980444600b00440e03900b00010707140d42071982511a60501c0701100043c458515241e8500905503d10241e0360b41d96103500383d10301c580119640004422983d0020340e200c400929024041c1c1d10040d821254a81c100e2041c03100d802d458400b100302c0680200c40d0b0442d01c0c840200c612001b030000580206a0a003030010703880d071018882c0e000e0f42c1502e009490500c402d14980b01c4c103581e10f030403c1c4402030000d0703000c104030382540c021803010316007014241811480c0000e40000300014503400741d94025140c0c0c1d40e100782d040c807550040e002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 231478570 1250 231477320 231477329
    0x615051f1209080403031d060a0305060108060f0906040207150e0319020109050616030905070e0117010218010507050304231206070c120509031020030f01050d080405120a0507 77
    0x1400b000724503075100300c418061448001c060010f41248408288201e2095096091002c0c110944840720b01d54002c0181c01e040e14440d0200d20307060041000c0742440c000c465070505025000c0b0265490b00360620000398000c08061750b08100349548214001020300a110020442d40010751312000780c04c01080e50111951010029a8905501c0c10001000400e40350303030162001c0c00381507109082003800e5002d0709032084010414080c040700400c0728415a95000d040e81e246050380c40c8130f4000024164201d21800342c804810b841a00c007121802d6103e04010f1804920501c2500d0a00356100c09060902025a81c41900c00d03111003000c4443d03080020603051388900c0c01000b811507042480340600140d080407030192060942100e9148924094130486010400c05800c4030700d81858001c8880041507070000916110f04100038a4150702508001e49010315002c040c0607103680d03e030908200d50802940b0003100e00d44010700001889990f4060300d459650301d241d0151601198a2418600b0318426411 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 231479820 1250 231478570 231478607
    0x30f070308060d0b0a0b040209100807090807080303010b0c070302091003060f0207080904241403010606140301140103090606060302090a051e1e09040f0c0b0a05070615051f 76
    0x40340e00031038180d0076101d80185d660840080c205501502080c040e00c600511540c00c109950300c1c5400e000d500004036446801c540c2d54640041c0c0d210320425813101024840d881040d1304c10310050040f0f506810061030107c50503411903000942e41e601084c05510100caa2000c820500c00c020810b00213640200c41310640d0820003103180440c10f81c0c0c1d01100f40204410280107694440c0788084000606001100203190303512100e0010703984440b090381100400b4180ea00039401c0c079100052144c012403050024550340b288480c11a0b080c403280b07034a05500064514101501c1e8407824003c41d11034070800000e00242d48d0b025981e1181e04050000100350b03544414007591015011400ca03c8400b5140202000c08880c00c00c0c1030043c005a00d400080c81d0780740039a11481560522041104107005d02001c0c5105810841d05150380d5440241c0f64003405030b0b00004220300300410310019803a58000d002c0304c1c0068031402e0380ca58884000c5009a80c040012141c080f1585520200440d0007685c0c41080345001c14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 231481070 1250 231479820 231479839
    0x230c0307091406070b07030603080313170403050d0f0309061109010e010f0807180f062006070504050603090114190e03090f09060114070609060513021503060102030c030f07030806 79
    0x301144030f511a20030080c104c1e82c0f56001042d100ba00c2904540700030341d008154141c0301e0800201852180460400c2141c43d841401e55506070664005d05580031030f90003002402444842450036109610707143c64010405aa900301800050000c0c4500e035460304404443e10b4842c07014000140940d040f4090b0a418016800100c10603280d00c010902d9112886180142c0da4a00c185e07032421001d90707550170140d88203040c560041440c41d448600842540b0505400f0030356000700410303080c1c454809450100000e02c00b00402d008a04044d0011500850700d8070002510320030400812040c2002a601405440300600c100d140001c5240141340a450b0317000d0107145850030250020303101c1403000c2d254602480000740003030303440d038095105148040b00071a03920750382d1541442d0007401889003800c101c031968035080116032000102800107001a6018042d00c45884440c10503600c650001000241144010031840070f05050a00c0500300351045101d065849110502c3c7c09000d80100500e114044c11040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 231482320 1250 231481070 231481109
    0x40302010510050d0c18090602180405011703040e06010903230106080d02210403050d1806080103030e0112150602060907090209180c04030803010803190e060d230c030709 75
    0xf41c507080206d07482020b4000b400702942d004070b070142c0301a0f1005004684003280c10514810100c0101c81d415604642c20041c60b81c83c2c0d10281d00400b84006031a191b86e000740030030300414811080c3c00c0d800120504110028694039610146503045810009940b0411f041c01c16040b00c0e0240503060142c04280064101460f4040c40207540b01e0301d40360120740350144044840062060041200e026640000640714440e0343c41d5009092605842c21300c59032981d09807800039060703204000a6069075859a2014144100f80c0b00440d1000d01340e4000f81e80d0640e44002d5480c5500b085a8288020503007a00500520b00d0417000c6141040d296a000b0824940100013120f410307500d01c200d10b01c02d6070380388859103069100c910b04009580665080141144030000c000b051020002000e0405424005c10010162142107000c84910054081680d0400710602000c400c43d40203800005402202c00e14081e26a0b60000000034000c0007541c10449121303002051200c0950300c2000e43c0047c0911003a61707006103014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 231483570 1250 231482320 231482333
    0x60c030b10020a0f2102030301031506150c06060f062706090509090c1915180506070512120106180305120306011806090f0e04150207080c06040302010510050d 70
    0x1008402444081d540c4100401c02003546179450360f250076802d2090f26080032942c040d54135882030000351004140141340141d150000e000348030654615980f603611200803610159592100301100310f8026450780c00120700710710354400c204001e120a0792941100c202c45020180c90204c8104020f01b451000f4005100e5141c003c8625422103c0030f40380200f5558940000340c1c203268005181645c0083d103903240d840d00721241d4085c54291380c04142e011031240095a0191111000d81301d00d0f00303030900d091000304254a40b1002414640b4002c41c00c0d140038050010f880140707584484105082c00c5203140060000c0da83c00b1100b507016040301c1c40500c080a0030f44d00d92654070480c1005513102600b00000250725644581d014005510103c040390103600c2c0c0f60b05001d40700c2010381c0101c103400e140c07494000940f9400280024029a00480c0d1818900844c01c00740c00a0f500070303c030540c1c42c030714200580e02c00358404002081c4564080e03400011503060141801500c40c1e2035a00a07442803520030707509070100702c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 231484820 1250 231483570 231483583
    0x20609101101060602061e090d0f02070b161b080309090403030608030705010f1a010c06050a110304240b1c1104060e0f0108030406020a030309030306050607060c030b1002 75
    0x141259058120315680d1011642070095408007840355081c0003001404d681c00041850081d402101d035860740964981c051218200c084960b007100f80d1000c0c000c400041c3c05000c45c0c0240d01510302c1170311495a29040c140310190b101c8069410034109071040032007882941039800181048103084501311514180885da960b008900e40244182c21030400b10f01010b001e5130040b4010803540d01500d45070011828410f0080940314030880b03003e41018403503007a110f00e031000300741c1c01d020503120040040001e0f1501801040000d00da40b2034542c0da2411014031260340c002552286204200b0f40100282c40007116180003a003a8281040c1800c0200450055039070b00003210448140b9184071080b03c01ca800c024100e1840d003c041c0b40c11620b404030106070120b614020f02d129041d484a501d15991b41c071200596240301d28072421300141c001050100002e031298120380c500078001e24000c280140c0f9071000583c1640040c8085480c9940c442da644010341d018000e0300001d481c222b03083c00792500c18400c06503c0b102c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 231486070 1250 231484820 231484837
    0x1030302070e060a0e090610050a0b0a120b03061906060905061b28030207050d020a0b18040612020102011a090106030e0a08030106080613020309120c0c0915130501030206 75
    0x10040c1001501c43e480300e030460b00081c42d41072045c10460428800281d29140240c8280320421780609001c216801c0100900c41101c00800c3c1007403903c1d100d810101d03161624640b04465460303c4680d121104d50301001641d000e00d0101c0707118940c0c0301d8034103c03007002c0350340d10b40c8020180090000c080000d9602c201c00d07203003509000041c0003100801203042d6030512004822236454590300314080c3d8210440d03020307541d901e203102e07400b1509107a89400c10458429800d00d0000d500c400001014032040c0b40302d001a081c01c2d9600501000e00c02035250005041d0781480d080180180c5200803034000b590307824001d10301d1800c10700e0400080500c2c020049068070005014880a041d116501c0c1201920100700301c200d880d0b0401074040c2c03a561a154001c10a07001a52201c1c451404410300c82c0c0900d02503c00c4a00034400480280104012a040c03584540c0106035015024095202c00242ca41c4449042a10a052590708100101c00600400c01c2e0486440800110f1502c2c00c1c2c0140016152001124440b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 231487320 1250 231486070 231486089
    0x6021005060609060705032106030d020309030c040c14040303021b04020a09050603150d06090204200304170702131d070501120213170a02010807050a021c05130e010513050103030207 80
    0x400b05c605140d481c601c250100d62a841d8041d030840c00310404100300150051500300c0c145c03030780c0d1800214200e031350b400b80d440280e40c5a00032030040e141d9440c040e03010300d80b10109402c248200603504460003c0a030407962054025800c801801071700322208548c0004110400c0350110b0811000c1c500080c0b000d40345020300c500454001000c01c0b40e80f9030511000021b080011b003020b038420610701c1c0c40400303480da80c2c1089004a04040f01c442520b0000c0e10026404113500b440241907988985950304404d0202e00e429100c14410041c00003d611111701c080c1069444084c0440c165200c0ca46030742c450040f150f100f404720b4000a200780020781e413120000140f85c84019004da1103c28001040401d58010360051142009541070341040d4030011685080e070324001d80301d001c002ea440040039600c500c559040d03000140c001b0007900010400c1104101e0201c1e845190042c1003d003004814810141503800807200c0003481001040149080340c03404110030000e91090055516541e000f95499265014002c4207 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 231488570 1250 231487320 231487327
    0x5161e120b0402010305040305040f03050318040204291b03030f090f100f0b10020f0d08060a0902030a0b042c0f031603020c030a060b011d0303030c072108010602100506060906 77
    0x181441031007518042e0045c0580d07203003029a68907201c4d5480c0d20000040700753f2011443c04e0141031400b4400e80c4c04a401910040015101280e0307000c0325040340d801c5c0302000c00070034001054240702580891481090100045070340307040000d06041c655000500e841c40340d0b4810100c0c0c52038040c1c08664140890808800480d41c2d00748004082d003d4030320400183d4000078010740300d0b600c0650016140885004807030940d9001a035100c011506070f0821119a504440140c100700860b240355401140d0001c001c000019041e01a800041e003130f28198800c11551180071a114420b0514603454000303180c403560000d00c400f00750140c0701a241c1c0a035000040c0e04c0720f40244514103045c001e1042180c0d00a00a0a45041201d240b0308400141f4105040c036000030b00014243d44041d10b0b122030403c6d040700080003141950b80b0a441c840d083e60104004480c090b1094049a11020740d14802203040e45554813410607540c1801e0000745002c004141c280c00e000c3c1400d081c810291100c3c001c4500d80502170f118561f9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 231489820 1250 231488570 231488573
    0x50d0213080a06050f0901051006210905030315040b0d0201081305060916080307020d0b22050a0209060616021519020a05010c020102040803030606030405161e120b040201030504 78
    0x140c0d5840d40d8041c049a000e0707a01032404100180c0d12040c450345503a803098200361503603840c070780c00c84d8011100440c0e0303090081c000340f01da00e00482030306410504c507001c00a00c1c5014039070004240c9000040840c4c0a034404014050300f11030081050a0030305003a201003064562030ba000440850f5065000b0b030611581c0c41c04541d10b0491003000011207a0000115000e900340400e946035520640700d40c0e50030b906480ca00109800401004450090b50000d2000b280c4802c0368a80c000c00e401d01500911180280711985481d00c14582e104c408403601a4001e0300d40e0380d07030500510a0071040203002c1da01c04c0c0f104100d06500c03070918055000c09a074043c1c031b000d001060044081511480f036501c0200c92222014080c28010754002040c00ca99031140c0024011071400c00002c2e4240d000354000c50340700e034000b0700001d020b030f041c0f4101542c0d0041c014400c444180d0003070a20326005581d545c12410451030f41c1044504c0082c0c0b149039a0000740701101c0c0c3c680d6460010340301c2070503000380504000d04168444012a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 231491070 1250 231489820 231489847
    0x30c0b07050403051b041505011e0509040c0915050c06011a0d1b0e100e01120209060406170105030a03080f06011119050f070f0302011209060203040f050f010903050d02 74
    0x10080c0d6030080031184044c020010004e0020b20105c0b00790301c1a0306003e0440c03805003510405604407001038441c9041107040b40e410150b15000203403500b041003024800e0078002d0784c03a4064101404582d842d903c070918100301c12881c0d611901654542440400c01655580300c500240c07050441e4020709040e41c0702402514240c45034440c2a003941c1526040070702140e2260f074004c05c403000103c1c0948450642da00350100340310f86507402503980790205180c003155900c1d9500940d0120b103111113200c8010b151075a56000144107400c1a04884000380400d4400b0301c9120100c1d1701140580000c84c0200a141c0b20380d9001400420010840d005080c15280441d0a81e40540004000c40e0b400c0810f07500a400703000c104000c005000501614248030710305030148c01610208960059402d1500c0c0c1069041c110b030015982c00312071000b4110410b03030f00c0c0c42e4840801d030f50380301950069225151199a94030381d414003524120001e050620641d1500d007025000a1300102200c4485140c94005a1280360103200d11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 231492320 1250 231491070 231491077
    0xf0e040c0f0f05041d030a030c090f03050d08090705060304030309260a0f05072003030c031305010306060509100305060409080c010207030f18091116030e09090a030c0b0705 76
    0x206104000040205402d090740b00c1600640301c041e030b41000301d030035000101c440802d1800c0d03007030905420030002d01c0d01640c030036048101c100f012800c143c001d05544072000741800085900a07075298020002e5620700c941e103c2a015000201d00e8000d00109041c180040c0780b41c030010780000d041c141d07180c0745c0d50100300c200d41c2503103080c1312052041441024440290840303940301c41d10402c00549031b011181407407070044042d01e034040e070000c008091482c4002d0b007202c02c0c44010fa544d40e5262109100a0300009001c0000b013030612800c1202860140c038100024096917006c1d0009402d0081c180000c2005444407178400ca02d9564900c6c011800e47c98400218000b4100744170090a41400042c00c0c40e54550150000c0903c030744039036103c28010403100022104c10710050750881405045140c100301503080340e0466000014100111440d1505030401c00150043e80d440480c0490314804161809280c92020a070744960094080c0c480e6140700d0368000c00c203100307110008154503d05000f060440303100303800b035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 231493570 1250 231492320 231492329
    0x2f270603060f0118110c070807050103060b2508030a0608060708010303051c02090310090c0b09091b04051002061014030d0518220f0902130f110a05071a010f0e040c 72
    0x1966801c40d030b159132911fa604600a40b80b1510950100003882d5120f407203448115208094802d0170944000000c0041e040c11004101c0d00f05035144030040840d8000c801140a010308000c0025424508048203081c5100180018188440000108042034100046400310820709550305040410f00d4a15002400760b8a04a5018441e80c6510046034a81d0b80c0080205030060008035451a614080c0d0307030340da00c1581c09054101c0404004523500200c1e5140d90485c004108290340c1c205911203020402000d000c816074401a401001801850304911b80d55101804044801100b040c0072407000c04d81d10017800003020100200021030507506204d801c1c0c0134080150013803d24a40200c500464412400c0c0c03107030444801c61400281c1c0c4e403000c40e03c1c89410380031039000c1d01e58104030900e0011130303005000c802084007049071114408002401280020503401505440c4d454840c6101d085c0a441c60509600d102468801500113104150134010310350704070b4550110703002c102e540d61300d4040c0c1024032a600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 231494820 1250 231493570 231493601
    0x903020f0d030b0103050603010213060f050904050a06091a0a0530010b1c0c0b180405010603020d230609040305160f0204182f270603060f0118 63
    0x45200038640c15001080f0100003641c003408251980b0040508038070800454400c0c0800210301081443e004400c0014414460304255003481c0c842c3c40801d0503a07004840e0107a0b0b082d503a040500c2000310601c90303907011141d600a4003c41c401c21001180300008130703000c0e10744154a107009803180f103d06900744103456142031900344a60030810200c2c90103451101c00d5148600c2d0f1036580d00c403400d210606808191a0411880e110452400d66200e600d94450580162031003401c2c103e00b000e944890040d80c1c001c201076035005980d0010380311a001240c3c00340c4103e610030840d0450700c800c03245900342a20380180046501c5081902ca80ca070940d8584902240344a20300c0c60100d620091101c07071031041c10000d000341e0382409080300b01d82d10740c680c0351000c00b8001c002e900020b0340c07070701c40a010000d50b100d03400040c01021030044403032000980d0241c00140c12164443c1c0300851586200072000b1150308040c05400520700c0d0308200e0404000e014050040e62644281c003c0750052105032500032180301401d01c030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 231496070 1250 231494820 231494833
    0x30a050109051c05040608150607030807180b0d0b010908070b07020a1401270b270d050d08040203070e0f09070614090d06110408030a090503010507080a0903020f 71
    0x2422501038510a6010b03640c0e400b034400984441c0314145141d42c00703240b10b640e5441c542410070b50169101140541400b180c083c0740c1085001c2d94031224010512180241c541c08801c3c82d10140061288003140d0030380300c10748500201049003689481c05e641d4120700741c0c100401c06440078401200c61802d15803100c071551040314000646d004040006145850003500e01003280c60300d4080742c100c03040f00a1000f50009107107003c264607180101c2154100c04610300400440e4656404403041d09401280046000100902c0e01c0c206400111811940b2018180d80d42844552035440f03241e16880c5004070700b018004034070009000c66405000c9080a400c1c45041082e041c241000c1c80d0329441003c40c0c04512511500e8404200940a4204000c0c82620f402035585070250700340500c0300c0c82070f1000085500342d0b01d440001e51040e0710340d8040c102509041004540f0b41e44c41c940002c26407134043e0300c00d50080e40b400040c8800a50702400d0160701c0240e40f40041107a18980c50101d00c1d159500742d01c00e5041c001c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 231497320 1250 231496070 231496073
    0x20a02190f020411040806090c090403080430090f03030206040b09031608071505010503060105100e040e010b1804080f0c1c090527151507030203030402090106031503061a030a 77
    0x801420503039880100b07c41e01d03551003c045d05d688840001245500600940010340000e202e6100c0e0b03030b4054415605590b81070b4a5106418400007042d45882ca42d4103480000d2a06507400230440004242120800305c3c444d2450724040d449550240002d400044000001401040100100d40b185032442d9070400b03a03c1c2180c240f440550304444404c94604240030001c100892a0b4003501e81600e400401501d0140d180c00100540080c2c00c0031004107114812101e042256140d100309900c24852000105603a51143c0030051045000780c4901c182e0202c02e01880b000c1080702c01502e18903591940047d82c0d8a420700d82d02480d0960480c030985202d0300c06110303130390b4850380402080c08691043e16200402c1c06076400703411444044070a0080d0a40290000030014105901014074a0a010b40314403010581a8855207041d070000d10141c0151307000000307010840c2091104140184400d05d020008404450782c50700388000d6620019042c0783d2502036044028401c03401d91040c101d4001d04480c00d0650fa0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 231498570 1250 231497320 231497351
    0x305100b01090b0307120e0118140f0607050715060e100302040509010603051207020a0b070f110a260c13050405010608061603180204020403031110020a02190f0204 72
    0xa16060001d2100384001525020311011369008068940b81e00701d00d6828042030000800650500f400710703640b40c456081504007550030110545020b010340c2040315003035013081880c060024009602c036910402c00c110390382d580441039814003a409030b102640c0655452280020f000385401a401150040c1d060000021a141424040780c0c07082e501030016039aa030050500704c40f000c1c40090401d8100201d070340c40c4010901e00410b429031000701124521b51700d5222041c0c2c203800c03010007112942c2280900310140490100c40e503800540071282441000e00380000403205d100180c10111080040d64400c1003901d80a001810000310041c02c02c0031000c1c3c00c0106000542415038098a00d5480c1402c080b501030300104615204846020100844044404003100240148108194030108081d0000c004de9035a00040c00158006c1c0c0c3c0d02c2d01c84820f0070083d9424101c1140003141c01c075204021600c2020380110b800080c0c4484000054403c100c1c608116001d540c1c1c2c810020350243c42d080d11003640081c3d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 231499820 1250 231498570 231498581
    0x120408010f0b090c04030213021207050304050705090615070c0e13020406050a12170403080f07020f030c031b0a03050102041514031306091509030306080f070b0d090507030510 77
    0x1064505100106420341800f400c8074042d2840e40032443c01704030500250030042c550104284c04107d0043c41c14002c18040034030002c060b950f40f00020340003c00d1200744202000031001503d07084030b049403d410040d001410030100c080f040c5100141c0814030302d05011414056400902c030000d41c0c0c41e464a440000016018424007040344250f2501201184c80d051a2140710107454100e00c4400c41450036485805402c1e00300c80c60705059403010040070000682840203092107014610101d0b49404440c03040048154150303213011301036070000542c0500b0743c5c0c0009046400c085c080f144150f0b103e0600012600010b21900090003d40c00000d0008503102d0030700e040c0440d0b54080d5200044c040450314024103920050340e0120010190b0403a40021925a6100d1046244203100ba010004250000142540c0103100181d010990380d1700304014a0707205002e070040c070800450140c9000350904034401120701600c1d005c507005d5a84c4807803040821100300700000140d40c00c14112600c150900b041da501426 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 231501070 1250 231499820 231499841
    0x10807021c05030703060801060e07031d1209090f311b060801060c03120b0423091903080f07050c0f0718060303020d0e1f02060105031b03060106050c12040801 70
    0x83c031b80003000414040610510080c0c603241250000300d0b80ba142c200300d01800e206506104010303102c1c00100340d800d004000584074140504403203903c80840310100305920390020406455481c800003005006206221800100c00084142c9086000000b002c00c0c280003003030754010403104844000c4440c00701c05503443ca04440103a0b030b43c40c0c0f0030380c0c03901d10840300e42054000041c08a040c000082c030136401c22350041c2098030300140000a404030111080b040a168201d40c42c18051642c40c10700100d280144000510501c0003446510b8590b100c0d5801811080b00601d844201d07001c2e0b1000c24202446030040741ca036201d07650308603400000705054240e116662f1344a044100320301c204080001070442d004540403260160043c00007980c075010f095420056411030329512500d03850f080c1d940e02c1c80341c99091600d1580c0e0f90040200398100307030600d40342015000d03500d41e42201c841c8068040d580c000484a041d50403030718045441b02c0a80c4552844c08500325a060b01c1d403135011a000c41c0c0b151055100b0340001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 231502320 1250 231501070 231501077
    0xc060f0903021f0b1305040614010b0702010305092107060b190e061503010e0603011512020a090912050714030711090f07020c0409140d0203040f080d0e010807021c050307 75
    0x4582d125162080322903034540c0030341024210400c5c0c2d140b02c24940c881c65000340140404140091024410890729200b60004446030310f000c1941015940c0c544150f43d0b01a40b96001007004081c01e00f07401803890290780748880070380300c0012241d00b0400d1580141142c0040540b28841c443d01800078180807100d0350080207002428040026002d103000001c03808260b0341d0030f41052550342400762140121000400180d0190740356004038042030048460a0001c14844944800480032441008962001984291b004504101740400442d001c503190092030f079580d09204c1daa0344038600c1c2880408002050b091100d00000c5440e009000200303201c449413843c1103d00203001d2fa548400f207041c0c01c0043c0d51160041c2c0c0300c0a003011042c2020381c0002d04a6000751001200c1e280351000300d0385000c0041e130103000140c00c00306080001c80c6000041d00094110500a4011000b107120000c00d42c100c0c0c890360504006460001c584034a00038066481080301c003219068001c0c41d08103000c0d003035510965a24000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 231503570 1250 231502320 231502363
    0x1051203091c0302010b0916091707050d0f0804080a030e060315100504031b06020601230108220f02120106210203070b0a090303031118010c060f090302 67
    0x6000441140d00d1404001e01000c507030022100005405044800300f20103541d0394030b4070a081903541505071807141824074000030107042c02840007030901d807580e80301c4011042500c00d401a0908046142c00588405903110aa4001c0e40c0c2040c0c0d007038408001018000c00800503011401000201d0310b02da655000380c5a488441514105104030340c030085035481c06140d0000001c0401e45003404410401c01d66070324000e4201521707519401454000300b81aa14101c002540400007142c0600c211401070800b03200003542040c21140c4a464030b040f051045041140540004020600c6e8681c03445d000406914081030307083c014549070302e43e0124503805a104a25031203a03d118140c0500511080e280c40c201d6040d40440c420b11b9000140302101c1080380e060042400104103e0001005045501016035035031044501e14240501203c2c070703003c0c0c2404d15050420101e020640c0c6210001e80d03040080c47e00495001060034a0801020305150072440d042c101041d140c10306500180810f44a01c03103686101e507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 231504820 1250 231503570 231503599
    0x51e07030215010302090a090c15050309070e070f05031f030302030a02061b0909060607080304031805011e081803040602071d01030308070c050c1c050d090b0306040209041404030302030105 83
    0x20702d07402440002e501c1820343e000245e00d0303011504014000e40c03081d0003050040f91504078080c080400d01c150800000c3d40401004030026080181100505000490601d0f60800794801850654540d031407105100001010880031b80000e00b21410300c061000f4501020380d100c0c640291a5805490000014071405000c00c480100b901c2c480c0341400004100103191001041c10f114591600511283d40b0845c00c3c005c0601003403120000b03500c2540f02e03a442c09441440c0c03446200c1b00e29059002181000b07c0860b040a000c240800100e843c00e484d07040600b0a40c2c1d9400320000d1403526480c00c51110b000101c1c3c0003840c5500001d664042c2c421410452070072500441f640c001c030250910010340088e40d800085005140145008000c15002c0c405482603043c0000c0440c800300400c049640c250085400303140181b0005200095280380a0700c2d14a00c0d451606418072803600014040c5846958009100344840e03480741d00c5140502c9108402e4403141c0b6240c01c0141c0207402c01d21440c1c0c0a00302c1c9051802 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 231506070 1250 231504820 231504853
    0x60f1e0f1908071e03021b010902030d020a050606330c0f0102190f112a010e0d031103041a0a030612030203070b06120604062405031c051e070302 64
    0x10f1080d0f9490791180460054182c114001000e8044801c0925500b040301d048403408159820f4214141040045200d403054070506182c003013003a054070115000020f0020000d01702044098006100b1240c00c543d640400c40c411200b110700350280d400340040030541441c4c00355950080d004001c40c010966645021040c1d115080c1d220301c070b0790300708000300e200c0c86294224080d11410f030310342c4000e1920720107179a59041420718007500e41d0f10411100f00001510800e88544010110050724203180c03801070303000c9078008100780328a0820000c0a00050030b940c010340c03110800c1640d000705005040441d6540b094000034001d503115404200010b41803003008075003000556003008889505600851500700c0ca602c0b0f008130300c10050400c0f94400c0701c850910001c110104403240c05a80940e0001990b864990321603051709581d06040c9406a000450403c129a00031840700b41c4480c44000f1040d48080b44002100c90344901c0c04206803842400b89146403461b078680260554a00c02d40031245454111001403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 231507320 1250 231506070 231506087
    0x11104060c0803100b1201090501090b06070209040303180317010b1e03040204020d140601030b09090322050306093d0f060f0b0d06090902060f1e0f19 66
    0x10008a01035141c2440001c80000085034000d4125200103005074480907603001c10380c0900400019a9054001032040e0100c5e0300c01c007401803248500412240d403141000c07502c14083c0c660080e106010410015040c9402600145002c042d21401c102e554078180c82e0203400040500351b0a413610890600100300070082204980348024440c81a58000002130000d094903400180200d80080d001d10450322010300307a028a44e200c802408a49409180440004080350101e0184500c9001d240c8113014140002204854103404050b6081d410620401d0090041a1140e032005030188506020017803446804180d0075890220269411846880c42042c190310340300d0102d0365240450f00f400b1072551035040750301c0700940480103c40030440644c2c802407802d2807030240d03225003c0f6000000301e1a040004920645000d0818100b00700100d920729008100e8500030100340001c0c0741800950307000281003440c014406500409120f0380d0f0f070181c18140c01a0303600207003d0094608005240c0b05c0009010b0403c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 231508570 1250 231507320 231507329
    0x1050d02010206060d1b1710110f0d0905101409030301030c0509180601060207060f14030103060b0303130801020d05071d0405220f050c09070903060b150703020609011104 75
    0x43c20343c0d854241c1001118003014000712440410b01c10130b10000d1400410340002410341401084c130240028518a00b4501d0002031174001717514014101510701e80b654180d800100203282c05a4031180b4410044000b410051030203005803040c01f1099150500f9030f0002d070081520040c90421540710120400d607a40020b00004110042c140010b01c1035003410389200d540031003500d40000515600d00940c60803d0408c0c1c01800050b08482001e00c1240d8000c108040036029629184e0415184010403401c83c1c0010b000040c20340d40c85503210001980c0410a85280302c00d03844095000682d100038942c001d47c89600d01803c40c50402c0000f4207003500818046e82040d00c40302a224a40140b1070801009000c011b03c480b030b18000e03140c01d0146c210b58580000403464030881511011700c0841c1001403070010107400c1903114250020801c40b049a108441030110f90748a2000b00e0000565400103041881c16240c6220b0104003050305000d1660004503e8091001c01d070013000210300d103c0443d041071046006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 231509820 1250 231508570 231508573
    0x4030803010533090f040e0a0c080a03050d0c050903030a080106120b030604030804140703030c0b010906120620032a0c030714010b06070c03060b04061401030c02011509060e01050d020102 82
    0x3c0031003454100060030014001800030241c0081800084c084500b0121003500640c400c3d0b0400f0100506600d109000c0c02050008104c100a0b907a0000c2592061084031002e042d02d030f02d0b4a59001d03026400f510aa0003004096a455082c5050024036581c2d00b40b1485000401c10400c00e45011200c0c41030b454802e00140c003900c1e031641da0351015601800f0141c0100c42d8821001001ca81040c424000100510b00c80e0382d401c3c41e4800d840c200304901e080180c1000b01124074248040269550f50300142c480e442d8041404220031060305118001510a4190070003022000810445030798111440070350120381c40c0000d08000ea403030482112050080b03400840203548108602c00c081100103d0045621960030004980f0500c144045405500090805c855114a0f1101070017001103900400040c444140c4081000620340000d00e420648260300030b0381030664503a03100514600c01e400034824411078400d11905a40e0700c0c0703540c500034145441220380002803c000403c0900e441c003003414165805a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 231511070 1250 231509820 231509899
    0x1305150301092a0e041401050f100c050105010b03090d020105012303190302060603100b01020c130e010608070f0515041e170304060917060a0e0a0206040308030105 72
    0x240c18100403c0f100d495403600c00080078a002c482c11103c0311104039000c242d502e80040003102070a01050301c5003d00d01c20040c05d020310044c030560303c912800301446a0100c58030300c032400d401c06080c2c40c06d058516000c0c107103500b00f0f0300100d1840ca2540085002d9845841120b9191030b000e0b000700d08075202130045200f03a14030000d0030071008504076080b80340340704000e007501c1484003c0c0f40002c1c0007d1203541c040f409a0071203000c12603140b4061220043d1084032071010300000074070000013519034000c85480ca00c1034922079080b4800c0000350b0721a50380000f07060000c022240d01c0d5807443e41e58402d1481100d0710b00302d05220200309401c001050a103403d030b4041c15a4180350422088425840a0a560102207110b910001910031501100320041c1c0e803403440a15551400c02c80020f101a0302030300014228040300140e150a80c00009070b996106141c2000003420a42020b0000c0c10000c0405019500000204010003030206c6800154101ca40071a001c090781d40b0f82d048441c80708001c450b00d9a000c0311584 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 231512320 1250 231511070 231511079
    0x1005031b06030705120a0b0a050a03030e04181a01080f0114040f171b01060b040e0703051512010203090d23030604060302040509030702041a0f01030e07030b07051305150301 76
    0x310007a40d0050840d013016420310b08407081110040800301c5010480036101d80c1d808001d82002c4125001800c03098480d50f0282d070440d10003500c00c1d03805a500b180101e99550780b682600c0403900c20031900e1680550244407003014020402c41c0401c081c0914080760040407901428100148680c40c1da460f50000b14040c1580c0d140c4a820b400071090005941e101072100f60004480441d100908245421107014000c440e070700038500e800c5600d6604000440d2404000a0022040702030019500403158a00400c070396441c0034081c6000000c1c000903c0d04500c09841c541c051100640255100f0002001203642c1070441c007034211344c1c5141c06e0300e0359076820310030000c14010401103900955100760301510101c2c00079941c0c3e0200301100d80494100151380c0003ca40300d0110309d003600442d150401d5608407040c5805c0d126002600c0c460840c8900790600d56100c40e081800e68052061790700850b080340090060385441030700540700340e0250600542042021401190314904110318454281d009140c25045d0703030a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 231513570 1250 231512320 231512329
    0xa1a03040f0501140115020604030905060714030c1f0b01051603021c050d05070c08030a02070302010b091303111204140609030f1b0d1e0206070803040b1005031b 71
    0x80c00654203000d0003000c01c4041142405800c0ca6680300d5807107548290324220111407044956032100b42117400c6002440b002ca41c2c00074119081c2c2c0c3c02219003650340d05541c688070f0500044800407042c0d50101048400e011711000c24141c1d41408080d2001d00141d24034290803048078031281031180454400d002c0c129460001c00d0344482d82307034424012100c21501c0358081d40347e007003989100040060310015060600001c11702400340c001b40b00307080507203140340c403070303071468064000100369841441d40410301405042c402d4102c443c3d19400074041050b141401c3d5400304048103022000d401250300d440c128286148c00240c91348040c1b82c02da25560405080c40708400080c80282e15240d44a18180240701c5a5941032110f040305402d03410040100418405d03a0700300c1c100d10799819a01c201e4000c1e180c0310204804c01203082c80060b918560f03050003405840003038018011100040c0030000040100003c02c109011400d008045210000d04040d40c1c070810140d80e0361217650b01070010007000c0c40031241e9061 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 231514820 1250 231513570 231513577
    0x10915150f081c0504090501032f030607031a0402070c140a150c0303060b0c280305070209060415030b040317061e0111010e0303011701090512210708060f0a1a 70
    0x11884c0403480c0a5a402e1500c0903214203820030b0700d2102d80721500c1c02803680081030b050b41022107a10480c900c2110540020b44600000b40ad00c814161104101d503030084080380002c00b81c2c803004008540750005030800b14000340e1075000c1e9800410301d130509510340380707030440081040f03480c44034040040762005c4600b12180c418504048040c0b50700d5007070225062141e0310191603404060001403404035004060310f24002040d04110520703c040120303070000300f548081290360f80758041e80c0b8280b2a07181c0c000400c4c0100344c0c003105842c0d18041325030080200a03007504418080c50003a81c8040100d4040a091600201c003603444903072203140207100192140e9503a07900300d015401414400d07510030003103c02900791030810080d010a034000000502c07030801a0b0144502c0c40380b40c1030003041300d0002507807040e0350b6441110000703400b19008243e2092038031902e00810103000a0482d00580d0f41802c22020741131140649042d445040c0d000005080f5041840401080341c80e00c0401d419140b1385003246852960 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 231516070 1250 231514820 231514873
    0xa0b07120e1f0e01020c0103060b0a0c080405040504050a1218050d050c04020a03090302120405010906080901090204020703050406020c0411030a090f06060f030506070206190e010915150f08 83
    0xc2d607105041c561614485907000c01c01064880000038440180020f00740950303028014145450004203000d8520b80000303852003407084e402c10b000124202d0412403002d000316071115600c982403000704810480f0104000d2400c901c141d1155010680e2901d00703880b143c5c04170a460039007100e61482040640303410154100b8850040040c0c03014020181c01003800d0341e10500d8290042034a54030f000782096410008810b900340c03103500050506041c40c0c0020035a0001d8030503074041083c0f58000c1410b8071800c0d4816500385074001c000310350350359841c907000d4045d070041d00c50748001d80905d210324010b43c102401141c00118260b500c142c69941c85040c07420050030b07103010513101039119400c6a00094801d2044401908049c02800d205503d1032410500d044402000c0d1001c64000c941880041d43c1005034009901091754000b0aa007000d6500d007034010081c0710400b030030b2071110401407101200103501441c140c1d00e8954816201c0c50300c85e590034880b42e240d807188001d10741c00780058501211942d5924100c20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 231517320 1250 231516070 231516079
    0x106020c01022b2111090a170d03050717010905010311040506030a06020a0c1a0103050f150610052802010b1e100309020604080f0c0a0608070f0201110a0801050a0b07120e 75
    0x84c40d10b00001040780c450540404140400042d501c0d000e1400421405c010080d8a15030700c0362110b0b61205c19100c0301445101d0051680350f10200700054050309401000e07030188072130f0000075a5141a558041c0c00f003840203648242c01e80b900b032012800d0030300078148a0100540200741000c4143d8854000b94040390000b410807616500c9800000e0b1580c900e9801003c00e00c0d014016941141843d40c00d291035008085440e034400c02642007204401c07500780c2da010340211a00c144007a500041a600d920a01d00c1d01c254450950301e0000c20510003070700d100707001d00c1268002c0140840650a00c8248441644840c07420884a1401d50703040c9410b00400e010006240350100f0805010f40c0418280d41050300a24250b0700140100c640c0c3d00010800c400d003a440490b5001c002074a400303005442080060052800c1241c070001d4090b500d4003d40001c50001d903003d03040365032410341c00301c0282690300a0103130034031a284040c0001440e505550969a44039040001103414140e451015145010020301c8280c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 231518570 1250 231517320 231517367
    0x105030d21091505090c210709050f090f061b0d1b081b0403020f060702031204090b091e010b1606180201030b150f090d0204050106020c01022b 63
    0x70300c00c1901502c000c06100d001e101a0a808015541c0180d4400802503050356015100c04d01c410fa0301d900048282c40007a4403a0040605040000c03801c0401359008403000302c0c104024000c15111012401c1d2060340706a0075101440c0c06c1d86a010340b03504081c0d4040c0146a00c900450842c100703803074000d00e45003a48110001d2200e804460322050601c1c0e11054602091403502000507411200e103103c00c606030842a41e070714007800c640c0081d03c50480700000701e01409001c2845811034030200040401803424050f40c6865690303a9030040058041d0407001070181ea4200d02145081c0d002411088410000d090910010380c201014121241c0000014900107020440142e02040d800d1085440c0540c00a407010022005030001400740c4111002c05800b4034591595002c10140c003c0c103544194a1441055645461040c0001d2a030056058069881840d00000140c1c268000800e11158042a000d58068a40c000c65400c0b405040d903c811460705110040500304070300c1011080000702c4050151280c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 231519820 1250 231518570 231518627
    0x10f030f0b03070305210304020d06020903010216080306040e010e0304051002071a03010911071a1317040911070314090103020d15050a05190506030402061e0711090105030d 76
    0x1030200f155000343c0f1140c22000416000c042041d01c480d00055103080620326505080d400304107400041c440281c02c095000c100e070303070450341e080d0115220140c5694807154202d50038101340013070360320559042d0300c244c0c40c09102c80c00d44d0006024200b540c8542201650500341790209128076841c2c145501811800345c100701040da0308036410781c034400c000034520654030381d81022401c408640c4800c1c1c034465591410721100b000603194540220013000d481c212030004c2d469800c1c43c03800c5018190f000510365101400c41a04028004016004031400c00005000d60001604144494801c00c40054001303145200c0c495041c803c0c00c8010315070320700185001868640c905440100711000301038110a050f140b00010415442e00a141401820003203c000d812020b514541c0f010950091243c58000c5001100003400c0d0360350791007a10b5103090803034480c0c03504003100b1401d0030240d401500300700c2c0c0c03040a441280c0c48a00301410f900341a2003003d4000c1200780031544c010303954074090088050b0030403d40a00544d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 231521070 1250 231519820 231519823
    0x1b0322050d0f03061403030a030e0c0a030503070611030105130b01021203010e04020f1f0311120f041e080327160e15101404030204021b0d02010b010f030f0b03 70
    0x7050341070994480d03144185404005065a10590107440c0056240381c107500d2984c0e0201c00c8610716441c40c00c0025401500460b00c50600c0c030144c940d00e90000b4244800000c3c00720110080c58590f06ca0101080b207441c54100c0080700703000030b0081c02d0f08944198050081d00b00c2e59801840700100500441d201c034503900d0030801140d4000d802000584070f07440c00344030071802e128111144e1000d0449440b880008500b64808880c10061103032070405484000d070320806840c80048030300a0b00c05c0caa5541c00c9280050700111034a20956040700d03411103005030099021500780414000c0b0f603101e4070079403440d1200c0060030711126403c0303030a070a85802500080300c040c4040140d242e981e400805000110351400305070117000701000b001a00740081c0c00650080d0740c0c0c1c42a1035a0036058803401d040d203240041da41035244901680c0c0000790130a1000074404840c90540103071075048504d40f82221304141e0301103012404d03212048000c03404510050760f242041b038000d812075a403400074110002011511080081d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 231522320 1250 231521070 231521083
    0xb01051002071721040504050a0504051b0f060a091e0b1c021b0705011b02150a02031207020102090a0603090b0601080a090602120f0f0403080408211e1b032205 70
    0x600131504001400c00c61070801d40541c0e81d00200e8080104528903040e00da02340c44584c100c1c3c0c10400405140d50080d640e1f034610180201c0e0305c20140c081034403040315040117404019070f40110612004c1880410080e018107280725000d54100808480c180141020342500c2641800e0300f0382c1c01c4a0f0280142018003d4451191080c590746030000c00e43c051034640003403d1005071000341c4441140d5000d0120241e00e50791241044102d400f1012079450102c60b50490943c0580b41a16910190302818044a142d054001e82502d10003210344103102c640d036038400e60403550300500060140300403030002012503009603c4c20b640420010000b107150f504d03642e01d090482e03201020408003100c0407024070aa5521060185a000c01c40d4108981b00d030500ea02c02400c0303010000e2000300750010004022040000075131484612000e102580c4401341400320740c0300c10b540b0200d0954069114180001071611180c0c8a98200d681d0060020301d1468452104640a4141c1c10300014207100615103220700050040010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 231523570 1250 231522320 231522373
    0xe210a1b060c0f030b150a02011e09020907110d0f05041a12090706020a06111e1b160303050d1104030312050a060605180a210b010510020717 62
    0x20b00c086000d1400350803018410f03000340406240c0303000c13481151158414a400036a0b0b001e222921408288001c0b400b4181c0b0f01000d0544410250503084a4102900051091482281d600344140ea649c5411a5001d03001208403006600804001d0406800703180200168552131074964582512201c005052203100f000c101c03048540029106001010b181c03105030080ca80802030056107260004c0259030303a041c12005418250f0b40c1e910f2740e4490340384400305d03140030806195080d400c60040c03184500a0308201c822400e200c090300d004008042001c1400d026030851100500903990840d07e044a103504804688407400f6560400414102c400700c000e00002d62095035586400440a041034003501c8024114440740740c01c1c24801e10901e40c00c8400d88170b58004400309105400030100004500d00819401440e400c80c0c030301100e4003030255440e0481102406810040500d90381c3d1401d12114000c1014840010f0304484028003684007403900c4c0b84e5840a80004441d00d800c804220b10021a400b4040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 231524820 1250 231523570 231523583
    0x3090806071d0f1f05120117010f09170c03040911090a09020408120c15091e19121701090603030e0d150518010e030a02010e210a1b 58
    0x2500e000700d03000c03070b80405404096680c00d0010304110081844180c00e00764000d51040d44e0700240e613226120f03009807100c610000789032010950f525058004064080302e03065915500300088174080101c1c5000c0c8902d000c0d40300c404005201c440300018400c6401102d50b0401e039000800001034000c416000309040040740b20381e010345d01c000311420840b108903a9448004280e0040c001008904c002042c14a441d00003550160340e501d0381982c0150400403c0301145c20214126400d01580240000c2c00d5052141003080c50300003181c0500500d40d5410f1221840b02c2c0d0000710100c2c5400148441d41d04114100203401c0038119110f441d40089581c2c28240c124a11143ea035a004006160b402141c524841d101501d070b00d0b420310019181c0141d040e0a414561500c5901d40010030380500350146d1600130141c0380c0c80200160041281c0b155141d07800803c1c01c01c015030a21898407401000412217580303040001c0100100c80c98400c90b030381159000058502e080c050103494111410f145d03641182200ca10902 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 231526070 1250 231524820 231524837
    0x809010e03100b011803031e09031a15031513110909030c101b030b130c03020301030507061e1112030a1b09061b02040b0a030b071101021201050108040309080607 71
    0xc000400d520034140401d52411700f10714041003c00c0d041803101c1203d848400036210001d040701000d440e210300b20b03440240064010a0140d00c0c0509443c1100d005480f042d00010400396000708042e0703a09a14507280080c141040c1c0411401e80309480d240203080d1089580a130122601700005040c14002c44a07a08960800100320f80c0c6030b1803d200540341c6140d0408201301001d0805c00c0c11144000c0742c0b200d0014150380b84a00b80403603503506c3d1601c0d40c9900e050000d11140d26001c900034040d41082c41300701c0d03651040d4040850784501400b43d9034041241c0a05017148074005034000c450040302d5030b108180c2d03405991100300305132406000445c801c0401d60800308051500000458200210f20f250400700420710f4428007030580d101522148280c0c0e4401c0e00e5a010151707000050052100e10206907218070000030000411088650f02e91081d24180c840003103c04040300c849080c3d02c12292000d020103d1000140082d600a44800c4c0e00319003c4d1503e05182d98652001d01c1c9803120540e000c6000c201581d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 231527320 1250 231526070 231526091
    0x12010303030f0501031a0603010f060b0c1005072304150e090f0f0105100509030703121205070504030807080c101d03040302030a03110f0d12050604090b040809010e0310 74
    0x50082402d040d0030b0210410480d803458a40c0b03d081103103035000307203810209140400c1295a09410107124424488030401485603105520056036102109070850745c0554402c8250400b150b21585104070480e49a590304020104108501d6462821400c0802c0c0700501010403804c000c12000301121880b501c45103100d1503800d003007051481008040c08070021014040000d0081c1c204003042c111070051310506c0104a12500c152080c1c01401915130b054401d080d400000d001607501e80061541d469151810300000c90903c0e40243c03401244c0c00e40100360200000c2002928180052124500a44560741003900708801282441c4200800c1c1501a442da018950707c510110a98161000b505005524203859680866140c85045030060180540e80319254a0310310b007841140c01e203008003000d64004443c94900902000e000c100284521072070000000c095003001c0c0f20700c428081d00100340c5d50706c5640310b030340d0303031903c0c0e03200d151014100454044800800c0c1c03010400d05d080c90741151000709004080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 231528570 1250 231527320 231527327
    0xc060601080a0507020d05160b0915010605040806040f080f130510020307170a0905030304180516051c060f0803031e1006350a0b06040b04050f12010212010303 70
    0x10340b64010180c03501e0280442e9580000d042039000b1241d007403041d00c810055805d83c50500c00e91402030f081e06100350400842040108039501100740f001e00d941702c16600c40e141141c060280780625002ca03888000400d0100303904118001c9182e204500840c82d105901001202a40001110315180e07100000300780004d2624611413640190071b880194240b01c46625900790002e074103072921440304800500d07250030714440c04104028100c0601100e6499a80708075807401071040740ca20410320f070301e0030b008101e000e5440000035801d8010350391b8040c2800c06110788038030351b50921000d14000694807080000c0c0403503104030210007007116001a540b40e242503a2a01100072402c4101d0255110810070414201030098004058aa242c504098508840100c3c6150109203c14406002c02d890002b20650301c1c03d070000c140b1407201c0d802c09101c141d10074000c0c400140200c0c02021003904003403200340040c2c101045004521100105001d2560311141e00c02402c980c02101c4404985e03140b98014402d1680 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 231529820 1250 231528570 231528587
    0xa030e030d091406250302060915010302041e18030813020901170a021306030302010e0c210307080a020105100f0e010504020a030e1005150402070c0501140c030c060601 74
    0x1a0090201d260a0000042c4401400e0059030070343c0500b2a6400159150301c402d070340942852117020340306400d01081c0c0780c6989802d820202c00611810001070703d40000424120301740b6503407041594a40c0d0a507400c200c0a0f008903608046a05c80000c1e000e89109030700d000d0007003420440c2c0181c9021340041e00300140344150040c10158140031582601c40141c88251000381100d0050b442c1d0301018541022140c1400500c4034080c2d0b114140b40729070140d0902c0e1380d00140450703100360005c01c07504000b010303681e0b120044130a02c2c66000082e80103042e000100c50300da030007540b4504c80942e449d144c01540c03201501e412402100e0b005070755400400c115480904001780241460102041c1007a00e0601c815000c24814058540943e070045000300c000760003904690794015400040e80c000326040e100c41c1000f80b004840310b900740e522090301c031001402c1034400c9074202c6402407135099601d0304080064482502d0b03e0f0070181d210004000428580700244050721012010300003801e5142841c4000608441 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 231531070 1250 231529820 231529847
    0xb03070509281d242706090901050402032503020303190807140406050f090d060c02071e090e0309030607030506040507110c0904021306030f02042a210e0a03 69
    0xd040c0c109020740c40f65494056485621458180ca41c80c0c4c003620003064015541e01e140215606007103620031058074051800c603214070402d8890700010380d16184400c0c2030b04d1050307070003030b41540014550b803c10301d1411060f20548040000f440c060199030350301183c903584c015500300d0704200300e4204800c44994409140740e00101a0705d0810201032030110240d116215038030506090181c0060941e04c8100703040241c54690078001c1c84d04500c416581081000b130046104a00018001d14070042485103400d4054044a16500c44c1c4c0194681805510b1008048081004003180700500c410305550340c0400ca110f12452003580c01291a05000782030205031034010702140140041d80c030000c03144c0c0c0000204100402401c854140c1e2940319030000c1080e040c08a18003151541c180040403041c4044800351078481d030b00c20744003005416031805100c5030011407801d910400c03400000b902b5410500c10b10f00810220042d40e003240b66122070301008000c503050300780340301015049249942d0a2641090340e411115 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 231532320 1250 231531070 231531119
    0x161a07090b030f07020712140d051303110301090209131b06050d020307030f1d0c06070c06050703030e0106170c0312030705070312020d0b0a0f0b0307050928 69
    0xa07401d00038400c645002c0100010410050071001980382c61007000804010803060000103502422414008045c1c0c80002403140180724074030000130010310580032a14000101c1008149290842e620801c40c0500d4810300b55040d0340f02e1000e10003607a44d420b801c038041c4900c8101184150a9440d240f0036030715170110044090201968104449034200f402c49211007884140107a03a036a58800c1a8014100e04420030b100618103200480b100c030440035801248184001210441c02e80d2908101c080e02c18404001c04840030081c0410001d0300501c064080940b02c0e00b004681c800b43c015409084a015074440020381e00c00030811500e4403020310600c0320301c840640c054248401031040701c100c2403002a000b03408100000484d0b80074513101c0e5105100484201c8819035072211008500d4018000c1405041d01c100e5180100184041071029100f044624603086581980d450180a4516402c045552074004210a40314803140b40114080d07030585801003000091141000d03182040005030070f00030342c81c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 231533570 1250 231532320 231532337
    0x20d0507050c120414120a0f0b190207080702090910020f0403030f0309050a110d2001270501030908090d051c0509090f070315090c020d0305070c03080a02161a07 71
    0x41007a440c1c5017911000303080e07a10b0381c008258503c216203080b02403d009840544d4211900c1c040003400a01c050051100018001ca6054940b0405040f4071502c14010001340d4204429401400c00c000141d5101c80d010003603070310b8520340c8000381003aa0312400030720680c80e600140c2401090341001c1240780c1c2c00540e01d02001906180c2e5183c2d55140708642000c0c1c03100314000041103855407101d04c0d4018156000c1c50624481145000c42c090701c442c09400103000c181d81a448104030b80d111540209400e031640c07541c00010b864003006400034802d106c0261501c0104010034403250701c4185c14483c1062140008051003920041303410355914581040404010b0f041203089210b5480014164010300802003410300390700c41180940040c00c02c0d0320340420f04441c00c1170020705c072002580055a80002502660310140c0101e8089044036070848510001c10400140c0a001c00c0c03140207a141d000100405c0189000c015080e000c0c20340c8415101114040c24801c9600ca645c0381615000e9084a52030401c03444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 231534820 1250 231533570 231533579
    0x60c03110a0e0f040b0316030501061508070f0203070206160b01090b0a03080d180c0806010b130e0406060806270307020a05010f03060522051006020d050d020d0507050c1204 76
    0x207602050a00340d203d604000401c0e0a01d40d540e17880345100c054002d0840702c01c441d1034211010488040d200640346540f03841c0d00015070880c0241e80e00500d61050b511800d20f6079030300b11f0a41d84488085850000c5100610042d0010788901d4018240b0404550103070111a420707140c1004426030581000769443d04011003520703181c450507204030680f544620800d840d2401c100c2c10314010100c000b43c0982ca41484140c000610840c611290141e0301c0217000d0b2102c90380caa100d241202d00c5105511026070040d12410000712944201c482d80182c80349201148090b07070713054003914141c5c1c00d0311682c4542c3c82c0ba0941c81c101d0030000c1c52000b0030807a00e03406181403010360340000720410180d00c40c850620080320101000d1f18070a910030009840c004001c01c00c50440303440d0031030707041d0340f2124030001091400001c9010f600c981030f0481c0444440354000c1c201c0070b11080c0226100d4100640d544801a020701040c4d41c1151a40180c40c451205c59031403640b03586010075891301c1c2120000003035903000000c200902 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 231536070 1250 231534820 231534827
    0xa140a0b07092105100f0f0f09021e09070309030c020409140706091a070c08010e010209120606030a0809242a03030109090c0308031302091b16030318060c03110a 71
    0x50250b443d17203400150060030b81c280f0301c000e080200c0c5d40d00c030418501840040821000d50000030028001d0b601d0b8114000503043e09402c502050001580c46001000066030070340c03094202d464118441d1800c00070071026980401d0541d01c40b15022900490303180e0019001c0c0104000b0600140301c0c0d4a000500145825599054050411071100c5640e00008074101031140d035203410700040c100d0344d008008101891000c42c0c000d40090351110f04c16005148108244900094254055100100641070901d001d545145140d841000713026003000e40b2409141000c481d04090702c1180560302c800d982c0c0c880036003544101040507410003010080781005034043c0040d000007600d06480d03200d40c002583d80317490300388840000ca03a94002041d503a0008200324001c04001c482d5a4130b0b81c42500c01c12466110807240580b0b81c90848001005544180300743c0314000401180c41100754000c1c14002010394034011034004260459a0a45032591220249190568544103254192a0610800381444001100107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 231537320 1250 231536070 231536083
    0x1b050a090902030901020405030f0102071e050d0f1209030e0f030106180e03090d08120a061404021b0f030304030f030c0e01111501060905120f0a140a0b07092105 71
    0x14076009034040300085501e1800d50488010300002011500d40880c00d0041c3c5001c2d6210b004201c030464240f1414400c000c0094014038080d5900602605421112010890311121040743c10300400ca40000048900745d0f05106030034842d40260784000145500c0c400b03105d03e1002d030481d81400380c0c0c500300080011500f54100d03c2c0460103411804950441c0724a00545580200703480c5a90144246040710204240c1328010a5006900807908a40390b440013a90811101944030f500f20444201d88103560a00d0554010040c0d240c4c4900801e10810020600b035241c154420b1281343d956000000703004c140b582100c0f108642c040c003850244840300510900804012a018104c0c0c148042480d800300c100f0800e100801c1c61055941c510580d079070756410000c0c403012552054a00403014901c45640c501d80120700c04a0405220005100e408260350720084001c144c21141c03030840c055540a54009600d81c522a0700620090307541c4c60403e414440500f1080c8580d107070700101100340e45122030000b40c011581 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 231538570 1250 231537320 231537329
    0x90312031312050906040e06090a06080601060c020411042c060a2606090303071d06070b0910020f0702040506010f0f0f0504320603040b0615120a1b050a09 68
    0x1a0070015100d40d0580e0369004000b0900c1e17100b5404a00400c05041001c1120710403a0126026052610703400700c202c0441e400360280031001d402401c0113200890040a503044000e201500c000b0f1440c038404006401504503802100b824030040400140b600007152600c0300040880c0403544e21400c017500002c2000113107224131921142c0200181e40d480002d900d8080c1403210002c01e0350701c1d134540121300c6516944110b13a0000420103d1940e10014503600c141c41e0f84403500074040e18035018003030301c4883c01d160300100715510f0380c820050216807000c0e0900140807030888101905842d510700d40704101c2074a000500640c10016051303021401240c0c466210000d055850400303500341c581500c0c04076070354440c80d000808050103c2c90690701e080070790046d4440348441c040d610240342d015181000380750f210a0f40c000d41824480c0000c03492030700d81005412241c0c50b103480309900c2e0000550105401200403900602d00c0d554480c036030f4180301004802000781c103425107401468090a40c0300035040000794010b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 231539820 1250 231538570 231538583
    0x1008070311010302250308130804090203040f0c060815060309060a0c0e031605090a1107080d0f0501030308061009052d1801170102040f0e07140f0903120313 69
    0x200504140d009904844900180c8054908001c941c8045465240c41d0310070101c0001f0341240006a50380444800448910342c03012110389080c0c40e060505000e504058001e072080380c112412100000d42c10440c1800401d46a1150700307051404110304850028030a801e580a14010010418900c001203045903020039000400114415081070848800c1d10030040103030036100d1090a480c0300c00e451582501112400c895044140e074940320f1070011344031007420700308275200140414400120b0031009404d00e0754005000003401c0d14022007210680d0b5013a4001c0e00855601c0b020301c002c43c108000c101d160b0058a0818400451501c0003007400315401c0000c14818148100d00060b031040c440549007903e990081c8140c2d1a00070348200032070100004e1080c12450405030100010f40c12040c000c0d81e0440c1d486140031030044c0d15065001002d003100038171820800552112201e03844440e0005041402e80807444583c07510845018140340c5078496103c1039106074140100308100002482c1180c000d5440070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 231541070 1250 231539820 231539843
    0x30605070c02060a051e0903122d03090d0c0506190209060a020309011106070c0201210905010e01060807031e1406090307020f0108071d0a090905010f0510080703 71
    0x80d41140c03107480103000290b010300c0004000114960000141480c04001500c03400001c10702440b001c40c61003110401038068004169000013040048060440d014144c030076803e03402d00c404c81c094004045860042c00307410021080c0059030100700490210381c4020300f060743c000d5003a92509039803048014080080721b0f44000341440c440071581c041c0c941e08400a4000c0e030700c880003e04081c0d141d801044170213001071a480001513840360000f50590042a003522005521a030302c0d00111405e490903015910b86040300a101030143c0b2140c4031f12801e20f1b00620001888002c8a12200e00303580340ca621607405980132020500200f40549a03c1a00314031013200c40b1808055072078809102ca5010b4498a0207000d20001c00125000c04002044072030303c201c3c1c91828291446005462481040e01c0200004958040b0307441001140c030300a8040080050202c0c001c95650014241aa950801c2c201c895945588102d08102c1c618061250891401c0c04030140c402e040042c1036603988024032001d45541c0948 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 231542320 1250 231541070 231541081
    0x6170d020c060c0709020301120323090d0303060806090d0305011d0604021818041b0303080f04020f220f02190507110901030f140303060d0b06150417060106030c0504030605 76
    0x420981e401054170040c1903450750380d9a0066a01102c843c2c4054011440810a4014001044e8002122065042245802c03c540071082c0b114241d10000300b1003c0c10b80e10325000c00e980c00c0400410344540c41c140d004141c8400407140041c03d90304103a0021101a114891f480301016650000690001090b9401030f01d64803442c50a8020361280c0e0030b55604030000e580c83c00c4491200b459840c0c402c03809100340461008107581440030102440c44080e000403030420204d507908440b40b1100b03420500080c12203150184050000b13440f03000c13500301c540e00480340c400301d080c6410f428001e05100d00e089140440c00c001c0d0400c204900320201802c0b182c10800009580310420441d4100c3d10f06180c0c0240411000e0360b160b19100d50404580c1c0415140c40180c0700006c19110000011648242c1c400b8004042c001c1171a9288141c602c4050143c03033784010091141e060045108025200820524804240080d00c00003128203155060b000b0030101400d1503400c4001e00e4000040b90101caa00010000300307962503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 231543570 1250 231542320 231542323
    0xd1103011103070f02160b0304032010020a0801050907080103080304060e070b0d0b0406050120190803160509011707110111130518010e131506170d020c060c 69
    0x22814100e8245008814000f21903032007024041100d825800306d58003008a0018124900700303510509800e0780d010000034000a229a4070720720700404040b002041500300003100b41c1004c2029850b100e507281e010500d83c414543c4051554014081650b41103a14105150001e15150b81400040c00314403000012600700400c507130103000c8812050055412840c0c49088000003070340090075651401e030806500b84e42c18500b901c2040100d0300140c43e00c2d680a10404810038031181d03544000f5134240121300f90303042105503410342140303658440c588940e035030301e460040100300e40114103c1400b0050140446042640c100e880c049003070203000d92500789a80e0b81d2030212480e0070100021003955091640964034414031001500d103207140e2416000703c4545601c14400300782d190314030701c42848900400420074204525150768010999074518800d460284c0c5528101682400c5065415541c5040400400744061001d006400c180c4002d0114a032182000035500d40d50100c01d03e1103000300160b07010046c0e00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 231544820 1250 231543570 231543581
    0x81b0a050d06051e010f0306050f09060105041e051806130f0204051b070b0f011707210c03052119030e0708070e060906040c08040b070504030b0c0304050d0801050d110301 75
    0x4135402c4000f035a110066086a100369210407a00f040c20100419242c0d0040c0081500c200c1004008040c542e00e03241c00c00000e811401000c00303a02403024013004a100d90350081c1c5115050f2100d010201c00d101c0103140340340440040c543c0a11b210a180c0c0800001d14000340c1405560b011940800d1507101c940020141c0f461030400103244280c0018031104010010042c40d22412a100040e200c0d40c4e80c4800114081464080b01c0926030003940b42400030384800c0100038407205d5140c800880e0481c887d6141901d002e617070380050350a58420112030b8083c40104490548600404c8d00c814103081c02030508203241800b04d0280014503032114411202e92031f00f008000010700d20b04c1c04a07422540d403080c003910507110554229000700e4104000640e1814180214500b1041e1560f904090b1380c1c3d03c1c1c48003040080041c1440301046001c1100102150348921800e00502031f0ba01c0250303a034109841c226281142d1301c00c0b400e0034003105500410496540405006c003558001035128100300c0d00000080c010b20 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 231546070 1250 231544820 231544861
    0xc06090219060210140603100e010e0307080c010b010306050108060f011101110a030e030f0a0f02071a03011514090418150615020f0615040207020901081b0a050d0605 73
    0x210341d04000500c0350380050f804003451082c001c104440ea004100140b02001c00300d904a4056021451500001010341c2c0000300e008415000050400090900d09056500a00c0b0039500035501080162055800380708613401c00409007000c200aa14110003e06641f800500713651090301490001c28040c2d00500005410107030a0008220480310b400e1060101e0f00903400002c0007074039140d002840140c0010485e41a0014802d11604088000400300c3d0f01032402060703042140250500024512100076040300e6840c03a01c10555125814102c0d19050302104001c2e541c20010742e2901c1580101200046a005000548000c605408808900700c43e4441c00340000340020344402103802196880c0c1c1c04075065a10440d08a03865109100d82240d175585118621030140e0807000129610101844d103003e01d141c2e000c0e1015003071140e43d800086100600b60321411242d00030b1101d0409101d1451480800c0706c10885502c000f03a0b0900010501070308d000c0b0001440e240c2c0d500007017620071283e0311009003602c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 231547320 1250 231546070 231546109
    0xc140a06080f0408070510110d0f05060f0402090a0e04080414060711090601020106030807050601080c09160807140d050114040207030c0b2e08010f020304050606210d02031801030207030c060902 85
    0xb00c0b0023404c0c041030b0f2050242ca90000c0c642013072030107101081e01a0364040c16000307049460a0b070b8010100070007544079542d9154480040100000d02590310f40d00c1c944182d018a901c6901c0300d1908001c06d050280240c0340600c01d0004000e80c00008007009014100ca01042e650b030400c654030080103030f00601003a04054810360300840c409003003200004410f03050f280c109041c1c8800b250804113001300c5030000e54914204d4043c007008200e00c0362107601e01652001080c90001954140842500383c00d92003c11700600c03040d1100018009203038203800004203140140c50442c075005040c0c600a143c0d11050070024038401c46034001c80c1d0a22a09503414025410101c2003041414901c0b44c0c00e0030001c114030070060346500b0a600c08841c094184280ea1095030024041c011550745c410400011002401c0a01c00c000c1074240207041c00282040a00e040c0c0b010340c2c000307542d550b8581014540c80c55a0a102c1030405004010000c0041e034445400e044d025406240800d981806100041c40e1814891021514 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 231548570 1250 231547320 231547331
    0x604061518061e060c080a17090604030905010827010e030a050705061003201504080d02060c04060f050705010b060d0f2003160c0c140a06080f0408070510 68
    0x2050070b52107903040380c1c15004a80503009041803219000e01c02071040001040700c0104400203d0110b200030300203440145031021400202205044002605582454041c3d010608000406800121482c00307171409080c0440300786030448450f081c1c4804407130071082241203500702e03c950705000d400c18803c4c516208181e80e00c0300000c090052107a0481801912688107110100d01142d40342d240d9041a0f81c0c0000300c50b80036102c00320405011031040d06200d600201c2000c0d500c4650f08044016001400020300030300008560114020314241000d0a009045c05080008201580c1c0111b141000c807105410030383d449280c181800c500500c1020081e40d00010001800421044941d204c0c03540da400038030081060011422100400106005880090810401c042540c1c9060014810000031041c50400309020307850ba145ca002829592107800752520600c1c00b0740803460b1449244002c2c0010f4501800320f841d00c0404480149809080540480f0002460344140041070000c803a500001d260140308 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 231549820 1250 231548570 231548609
    0x90a050924241507050712080405040506011808030a0e0f100f090f060f08090309180604060810020403020f091003240e06010f060c0203030702040e15040803041b030506040615 77
    0xc3c030307900a050072a29405400c070081703649158440582c191542006105090901700028000140009803006040c03103c1c0c4a0040307203107a50342890002030510320018507104e2422400142140f80040d207118801d0f401161070301800c0e110340e42c140c01d005000389043c08450140c3d94007900d07011847d0f0008120401542d00101d00342d50030101103081000b05039503070701042c1c0e84c5e403100980300d0080380441c580c440640318000c040241c0411115401030ba005000042071951780c031407603280004808007031000d160007107003c09c04e510746550008192001928214164600341d00c1c030000f0003400340002410141d0020041d00781c20300c4580d100c04004a20307a802c101000702c0c4402541d843d502449a405c0304070070170f900803509500c40c080308481c10b0741c0540258200407140e4200405008404080c45007403280c618400c0b84070780e1071070b032113030142d0302840280e5903d040504002400d00b03440c00560300030094802c400c0002a0b80000c560382c5c019044907000482d04040da000e18903e80c0c1c40d0340314030300101c1d0414201a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 231551070 1250 231549820 231549859
    0x80319270c0f0e150303041e0504180c0e04151812030204060f0302030627040c08010506010e040b0a08011a031513030c030905090a05092424 62
    0xe6a01444100c0001c41d0340d1500e25001502d20300401e40902e8081e00402d048158580040040f4030005007a241050b85414111000c000c0050841b104045001c4003005a800c10348078a9080309403047c0300580c0c0360317940c6c1c650815007582482132030350000d07103c0b0004050104103016020230b040402014042ca001114015036003502d10801a0782013818809175816250282c402c0b10f0494581351204c14145030000001da00a4000615203034210b49a014081800030b1000340c0e544500070001d46e445458202802c040d0305011490300320443c607030300d0403041c4612a13800c80b0b0764903848a01250b011815003106004078542c0c0b016648a03000701e40c00c3c020b00d48807082903210001ca511005404484680c001317400d074000e4a000940740300b80010210341209011070300c560000c140c0d150003401c1101901d0f5494003ca0301f4400212802031900e9650000d0001e0020184a0342c0840444610b1000007480c45035840b030f0010801400003500011034422880114102554050300c01d04011b102c480c04003501c0c1000b1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 231552320 1250 231551070 231551141
    0x1707080703020d0804200310230115170a090b0f0106030b06070b07050a02070807061d10020d030f060b030a02070203010c0906020d08250c02091003080319 68
    0x1c8016005422159411610421945110303a07004002c541c0c0f04003130590641d00140c80809100d40500404ea002081940540164404c03800c00f44621040800c400114110f4081c3c10f810261300003551040c5000701d0390740072024140030402800030812640b6001c5507400101003910340108100c81010070440c0b0300c40040032240c125861a2018062550580100049441180340041c0340c440500085511380b80301e8001382010303600c00e00460b00380c0c640714a488c1d0b1410007194040c8000a03040c0d046000c040341c101120b0324041805881083d808012903101940b601c50300702ea500d0030550313217147d61000d00102d5002030b80200710080110781d0780e05043c21800041e501c24101640250700300f041c4500d07070301e1207007900720202c40d00c42c1d018280c04006e0b040700700c84444000e0710304661000504e148001200e104c00400c007034042070b504d440d10322040070b10502c00c01c42c1004241300d148481e0744108002180c1040c08136a80400010021004d50403c4c94560004001c0390121182023003652180c04007440b00c50100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 231553570 1250 231552320 231552323
    0x70f031101050709120b040212060a0b0f011d040f0b040906091103070501090e0a151d2404020c030f121f03080a03150513060e3117070807 61
    0x2c2c4015a00d0190644150400d0700c82d11468100503400a008501c1494016800620040c54281501e180c0c5050f03510b41130301612104c0c800c1e03503212545401440c003000c429001d08028240703815070101800704482020855005c2c00c0c0203a44400e403001c41180e59a101c0122807400500411248119040a1000704458242203449400003c00e1110900d0300003451b40c21180f05940f0300d8140d03400c08295100034080a4490580181c075080d0f001203d0301c0900c280c4000d051840c80c40c08582d42c03015030001345810040e03c45411011104030784010042410940d00081c407080c3da025035242d1048600034a0361040c4c450420045102044031140c50203448925800b401401d0701d01c1544000448101e110030f0380c503201c0100078181c20840012003038081d40140c003070f00344c2c08858040020b80e1100800c00b00d030310b45807600320341d55a01c40c0b05002074002e90f075105801c681541200c0c03e0b6600c424070b1140c1901102c0d046a898400116002c1040003180d4036180c011103c28040f183e211806072408460030342007102c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 231554820 1250 231553570 231553573
    0x2d04020c030406020c1c021e040f0b0108130506070f090306060608060102150f01030f260c1b0a1e150c02120c090a05070302120f09010b06040b1806070f0311 69
    0x1c0c0c0c03101840e1600580306d0100f01160380480d04c0c0b000b5401c1000c00d605080c802c021044c003008501c1d00540d074070b1103850002c110b201000310740081c0d0382c400100450b100504003003118880007110000314800144640c0c2c0f102e024200485803c0304201d00381c4034001c03070354002080c0c103080142c0031403a0b590106007180151b03000c0e0205e400030b0b138882d070300030160510441e44100200d4682c1300400224119002c0080414020f1000442421126540c00006170207000d4606d0712000c000382c074000015013049001100b0710920780d421281070045000070304030030040c07040094040700011403007505140d80101c0c0004025a10481072141c840c928040c001310902d001c01d07441810350825003020014045014051614000c000601c940c1d01c2601c601c00401c000b074075000c10140c1c2801040c4440c0e00401d10f5500030b01e07220b41d229071076182950300340d030035116915005030203510140010030040c4140300c140c42c0130040d1071080c02c513001000c201041d424058004003922003000d07520f0f000c040c16001501881c03440032820 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 231556070 1250 231554820 231554833
    0x106030c060504080c0906040f020c06011403031305060703030b0a080a0516060503040609051c031a04020a0f0302181f2a06020c100e031b06062d04020c03040602 71
    0x101c10740b0316000c0e83c03082c11202e403c2542d82c80038624000a4256100500500000307010302c00700c0700300d400c90f000407610341c0d410390014005200240b900700c0700551400040340114600b0078602d105d0540c00820f4811301c0c1c002c400208621003050f020350840c100b0703c0006050589500d80d145445566a480c02c2402d80c2c407400b80030341300740f00207a4500c0c80f0003c1d0703001a01d40c0e41c5141c46903a41c250040220740000d503041c0c082e80c000c02c032861403080d4245840031450355000c140e605c02840c12819089110750564856841041851980c540117021541c4151050070016112240804c4440c040d60203440d4003680401ca160804000c000d01c410f882d40b20100c26070300d602d500502c1c000c0d45a010f10082c20741103128031140300c054000411603002043c9a06124083d24001404e44400c00141d40021810420913080401c00c054280740c800010441c1840c0180281850309204001c40c19940740b04200c03d2030700d041810701611410034007441d000d1800b0054011552000c20741c0c0004d03202d82050140100502400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 231557320 1250 231556070 231556079
    0x110702030303040c033e04060905010602010c0909141315020f030703180c0b0a11030c031903061a030702011b180824100f0905040201030501050111060c0a0309020603090106030c 78
    0x80f001c220030140400340c542022800040d10306d0442014800c158010344504002c60710703554a0160038002d05542d000172a0003102c40e000a8655003941d00115101c6252441a1400c524201801500405182c2941580000e54180440e0540c0300d40300494100e400001c1c60f03544180c1880096106075800d6408000c1d00407810075004400b079011001800e1341002810504c0f100f42004010312000d4414140508409143c49009040d5080740b0700c4541e40740c00101c0c11840201d0b0090780d5800f115428a0204810383c24400d040c800400f6542c40810217500120014040c54000d60100000648103c1c0c8070030181440c0c200100380d2408510128941503048500042040740011090f101210201086548184003501e46d2235a140040c030f80117410740300440000d004070b641c3c40002c0c003500d02810041030fa460300c0d00016080e01e0341a81b0060411400c4521818803c0010601d41d8010304803140e0155902c8807090f085015000c0440042c0d07000c0780002c01c0c020742d82c00562107030007184d02c1280100469035a8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 231558570 1250 231557320 231557363
    0x30203040510020f12011203020d03050c070b090703030206090607090312030b0d061a0103020a080a0c090e0103030f02120c0307021e0a17060105030a02010f080702071203020d021b13110702030303040c03 89
    0x541f280200035030301240c4440312280c060b81140794072000c000e0b4882e0800c0255101c04680b01c00030344004181d0b8019013400e005050b418000658440000d6000f440741d420004001408200300d0b210103032842665050003240c1510076001803c40f003070010b00324040001603090140083c21049032411841d681c1604200351540a4002e6a0b0304c841d00e51201640d503a41c80400c1400b4103034800300c420821444d80c101051149007408024040e5001741d850398180d90388007001034134000045408602240007400b400540f64000800c841c6859030584442c102d0892032440a822402c582021a502680c1036502040b100b280c05500042c0350030b250100d9010307985c2ca0003810340b28054501e029001503100c108684070a0b00461460703400109610403149515503030b10320325694001100d411801600038820070300c0001d1f41084154603204040308880c4007903842000080c418840d207041d510100307440d00894948409020184c3c0d00f45900070341078030340d603103064034043c0d08500090104403025242d042c40c03032100216 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 231559820 1250 231558570 231558599
    0xa0f0c0f020a0303180b07080f06010216150201060e1306060b0f09190905100302211f020f07050606100e0a140f03072408090d030203040510020f1201 66
    0x1980c1d0060002e102d059101100074180094010700941005210100010391612071644190500d50741c0c1e140d1800c010207461400708010b00400e0440d408a0b801c50039038208003003500f003116031343c03407103001e041c1035004007a40944803a41c0300f04d118410346800c10416050701c05041585a02c9580100074164035445030031281d0040d0840031203c48410702202c4010304003444084034080112250681c0c1c0c5640300f1070001621400c540090f414040e103501081141001c4034200080c080c40100c00c244121080e06c056a0754928444040145100c8040b022425aa46d81107031072040c048407209564240c4d03030800703c0c2da404095403072600401100160a00b400d2298110104c04800180400040e510f800c1c4041401d110041c46e4541c1b0580c18000400e290f0b0f42000074200614641062560741100d000e0080102801c5254080c01d2200000400c00c1a10340450b0008510385c4a00300107841751580d0510a140118035902d4038442d81c40041c08125808c6814050190409600020b0b9010b0380ca070000000d0628 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 231561070 1250 231559820 231559847
    0xc0901122c0a060c180e040b06040f11130e010e10060804032001090302010501051804480501141603050903010612050c0102030a1e170a0f0c 62
    0x1551240e00e011040c2103004011401c05101d044030711200181d1543c1c82107941440052012652034081c4011000b00e070244003006108448064074545000d1311400c01d1407030011328045c402c6030b035801c603051013080070b80c04a80d0f4403860081c196100c842c81140d2803424200390081e0480380d142c807000040c40c0000c40c444244166200710301205124a403030f0703040c0c0c1d0380760000d4030413414454000d400e4617907408030f10440c0c51748960702000491240c0306400e010b400c684060300868014480310a010001d80005a200d90300a94400103a04001c035561031100c840c030010b819604052181070050708101040072122504060a18500c0180c07156140c0042da00380600907040c1402c110184441c540c1107603002e40000341c0c14082d052581c0782c0401d520003e404c40303e0035040131080c03802440340d003800c5c01800c02400300103100030b000461801070741d200064103113150380058030356400300d0b0120402d00d6482440d40d0340e0080090320b8034160700d040051002000e0030101e50464001c1d89003043d02c0c8032080c803480d40c0d0440304 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 231562320 1250 231561070 231561101
    0x2030703050a0207181a03030a09030206070f12020d090e130b0702010b060c100f11040506070f0210110c030601060f030b0402040509040308040b100807090506040906050c090112 78
    0x509039019a410381000404905501600400003440d6030840d00107140d580d010f41c070018a2804920380c13501101800076840340281e0061008000c035030780200c607400c00e5980445911f41c03100f40c94900480c4d80d1326012402080000064908a4042c0c2c00141f5090400c0701a11014061502c8061454134100e04840303982400207402940c90200e15007285480c0c00040ca8400071a07a1240c44020881c5607106044200c15980030280b038411841c01e234401d10700e8484911209211040f605c1e42001082d001e0f5001d5540b18900006014082000d0311680c842c2d8141e0141c001001c8603041403000c0e2980c4bd040c180d492a078022160b603642d07140b502041c500e0607102d5036181c0c042c05440321748088005008184000340c20550030000130866946422900c2d11541c440c1d69007031410328040c5403c100140024105508803500940240b018000100b070010944605140000b05692400001005456480e81c00b600c9036240c64240801c0000d804003e0404038003c3c0c03038440c0608866030b1312400f118000743d16070049 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 231563570 1250 231562320 231562327
    0x1603140c01020613050a0209011e0e0112021009031a070e1914010c0807050330041209090c09051e010c0f020301091506090b0609060d05091c1701080c010203 69
    0x6151407030a0b10320001d0080e412100010a21f9000c01e201050a0b04021015540701254040226901c18000b018160303915141c601549409030820182c0101d0740001d108452412440c2c844612a8000313038000e641200803108801c01c141070034040345005845035070020304141212200360034100302c16a1002c83d040007684001d0f14140da10942c01c00000b09a90401c1b28100031000030502e040701410300d45000b1405550748150b82d1240714800030f000c103d04508510407514010071081c840d0b031400d60064000c07080010b100344144040f15484099045a40d91501c0c2403400414a64052030004c2a210292040d90401d01d0403122080446085a2900d0018900c031900c180000c0c0c0c100c1803040c823140f0180001c1020409555070201008401d4844102995070b03000c208000101c6006400d03c00c9001c0d103d6601c1c0c40761107000700b03e00780b0034078040e80c6415444101290a40d40100302c10381644c0607450140c031906040d00c0c40204240200c0034040182071480c0e0020822141c0850f00c08001e1505800039860f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 231564820 1250 231563570 231563581
    0x403020906090c0415020115080703050607050a05040b0406021b0411071e0804081f0c0806010c02030703020a1206050109150521010c0807110d080a0e030c1603140c010206 75
    0x3031828010720848100f60300740320018880c1c1d8a0030700f1220000c0707540c00215100c01c410b11030200c1036403290702c88041a84000003c0001c00d40100c0e00b2a040381c000e140c115610400711005031624400d540c011200103600103800650284e011582102203104280419440400c3c0805c1000340c400f44a50302c5a0703801d04100c0000012440c500c442c0d103c960385241c4200e0002542c0703940500d82c000e50302610381d6812071b100003800041503054254004600a5081001c481075800c024402c0034001c11860501400c40000020366808114080003194014007420300c07241c8481c4840700381c0c40310071011160203040c44000314001d58580500c0061100402182041c14501001c0202c0300000296031034000d418403031304d072178242028061090413100307680b10100a41000c2c107000300210703141c1e02c5403003640e0809a00c2150090380115059040b122101e0045448651100344908611070b551205049100b1a0081186808250710004c1264041c0080e801501c019140c107d403640c62020f20540140c014000051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 231566070 1250 231564820 231564829
    0xe0a1802010f0e0112060e070206070302030c040317120c0405040c0203070b0a021b060406090201080c0909060609040608010213060f05040b040506031503011d010c0c0510050a022710050403020906 86
    0x80140f4014544503260a0b5000c909200f1030700203820580007400c020007001851601000f400380c00c50201e00d0704610b5841c01d00c01c460307c140100d01008040740c80441d1040c98150b0035209580e100380020000042504041c078554403540d00a203e10b500581c24000300180041c00070054a1403140c00c84411035041e50380a083e08025070092200394008145108030178034071807042049601c228810040010301100e180005840110010310728180e40508020100d56a1540c0c4000c42c5c12110035242c0c1600c070f002480008002c1d02c5a50090380844d032002c074803c0448e44c01207000004031442600d681c8080e28400c5c004440c01d20490142d2403402c8030401081000f82403036002541d004000c1c5c1c08044503c0041c0e0000390a44110344001003051103030f40c0b40e46410a2080c401c01f004500e80d810803050320091f99480a0f120042900c802040c5942c8400041c0840300e181c046464020303c007000f070381c001c0c6050510b080b803c8032051041e90256042d1200b009005004074210b03410b0702e40003051001d480d0345034001c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 231567320 1250 231566070 231566087
    0xc0306010e0a09080c070812030c0d09080d02121510021b0103060308040e0a06090606020d0c11040507120f050f0a1802040c03021b0c060715150e0a1802010f 69
    0xe12106540e614158081613034070029001d1941041c024001035807030b044e0b1681c503024400f0f9a549503004100b051240f200d4081702199412104008045240742003400c0c444858060202510200340c00041d0a40e40410074142c064844d041000b110980d41948205003c01c0400b03054032007025030b0003281c0741c01c03c07812841c2c00403c0c086014500803901c039860303507240e00054101c0e40c4810003158041c0c0510003091114000c0202130178152104202007403400f00000d50325039421f400e4105118030342c0701e90307401d000002203620310607136028206100c28284540014244071046a40f80c500c00e24004106049183c54014180101140e1403246030545a60343e40741e0003005100c0440102c40604ca83c80c2c00161220300911811041948006032a174ac035029203113454500601c65091160010280880c01359507135401d071145c00e074202080c5400000248030b440c00030a44284106541c107905540007078a8166103507907901c1001d4015051000300c000c0840c4118241e15400001d000c61000800b0300e81152188010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 231568570 1250 231567320 231567331
    0x705150c07050d0f0c0b0901110d0f050a12020304050303160201050112080a020120040f060302040f1a0c01050423060403080106050c1603051606141204080403020405150406080c0306010e 82
    0x43c0504d0440c560340d4042c1c984c80950044484900202c3c13145007a41e0010780b0081c0c88613003075010748001c09411000810383c2d514a0008400d01c0404143c02c400c240c407139241043d024003080800c56032820141005030741ca0300100c3c0c00f141180d034406254118280306000c0d403812500c000415025003401665401c00d142c0000b04160308566849941402c00348224000302041d41105414942e16400c0a86202c0045110340154003898010842044882c50060f00c0c90129400d051849034201010041c0e810548200030700d090403982010244000d210724100da040c0c4241e0b0012600050141040450f52148422103004d03010401d80401001a64003810060441c440303540d054540c3d00e941006002d06003d065081a62980d00000140c28524514291500540101e0401d022000c0300440c2024580c428001c41c010442030100208042001c1c590a85016540c000c2c003e101a14141d07845c0c0701c0c90700d0200c01d454810b13418900c0016144901040c500d141100c054003030900f9030300340280b030085100040d10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 231569820 1250 231568570 231568583
    0x40906181518020f0903150106020f030f03130515010303050307030506040603021f0e0a06080115081009021c0515040f06060f230c0d112404110a080705150c07050d 72
    0xb0320a50350302803100c1d10813600707035451f01da40c19410f10310300920705815076800608981c002c020020001c038000c41940c0d400180c800e10030024820070301c1e0450400306031141c0d0181024050001104240d0410060b40c490000c654040100d50381c0c07101000309980c280c2c4000703034100014446902d00722a8010301140080074505040c0001d0050101003164000b40360f10000014440d04014081c6c2c80d010382548541050310b2400391001c5c240180f43e450343d01e42d1449002040ca0b4001218520040ca81003034940c0001400400c01091601240004100300c4416030281304034601a031031f00c508195486458181c0e0020b0f174a0042118612505a590517030380e070389500c1007031410000c540300d99000600801c2c1c14030154019240700c00301c0d490041d1103802c1c030360100c50280c1c0002c0e0300b52050311060107490040049070030703400c60b4503201c5052544c03070b40c0b402200301d582202c40c1d840007203441d04000604e0000c0340c0050751010198062002141094003800b60f000c6515040b202c3d0401041c503080741c042c1c00c042e000e80b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 231571070 1250 231569820 231569827
    0xf03030905030a0504060e0a0501020606060715020f091906021f06210b0108060c030406091a0a0204060e0307030b0103060b032a2e030c0302040906181518020f 70
    0x1100c080c555080b43d00c283d000900005030511095911190a1542c2d9105940844001c1d0070180040d440f282d004084c18002c40b4085803501c10b00042c2d518405021903105421550382e62040c5a0703139a030340e10040405000300000121140c1c101c00138094a0304460361a4050710f0780045d044000788155010019070b942c41610346c4000324203042c0a0342d4420702e08074400e4100b541d500581c035080404545c1640050240d404c408204210fa41c4040d003100d500a07440000001e8401180c0340c60445110182d050044d001030700c10030405400000d90061003030310b8483d120a16820f038180200f60703440809000c01803c015050004000040c130030f401040e00f000c402010703902c18290301c5000404c400c1c40c00ec0c140035403040d4240001c03840d05020f02000b91603401184c0c46500300c00002c00106080b84804400420103a60b00c150400c414031950568000d800d10324030038000c0c1c5941c0c200c03645514101c5411035035100d1800b02501c0221a50201501c12200390030200445103d03482940c03030007034210030303c0118a22400c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 231572320 1250 231571070 231571073
    0x60f1d06040e09010b0415060509090408071407090501080f0a08280c1505040b060904020a080312090706080105031207050304050d080c010e0102090a03110a08060f091b09040f030309 80
    0x741225032141d0010f000005003d82405d0801003541c100206c0703947c81140301e007414040301d5401011a0003059059503103604541741e5152a185601c612800034002d4604140c0b86400c51901080800444e805940b0601880c0d80ba008001e0b1614115030000580b41e21100310500011030900140800d8040c0d6420660701d0280500d201c200c2d10903d4054200141c12400140208007045440c20700c141c08000c0d0800651401c0e0b80c42208803071014001d00d11464148001404668898030304002070101c4605603504d03002c01c640542d2107100c3c166070f482614025000c0c04240c01d40710302d0340036040714002001085002c112549101c01540900b40c00c0d901070100700404103094a038038029210962140320300c5559000046041c6007114201c40112205900402c1070000702d5903002e00800036250808100d41050000e40000f072601542e5500c0700000c0d014060800142600c140ca02c1441038003800d0581f84100c1220707480c256251b103c04209507001d2599008140400d00c1c5082110045109080004010946 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 231573570 1250 231572320 231572339
    0x5010819240e010513050a09080a0e0a09180b0c0d020307050901030b030c1f050d050406091704081e0102070c0312030f0501050a0515190c0309060f1d0604 68
    0x1842600d000320003694503052100d58010036400010000100200b61035410500000c0c1d44105000c0c00348042038079070001c80c0b2454500e42c050408944d00c84d04a9a954031905006010450302d0001281306059620001803180700501600c0a00300d20741f042c03040000b0950fa5940340080300601600e40101d020320042551040501c0194001e0829844e2191102c0c0c1c4980010140c1d10122a000e001340c03c141c2c03020190351912401c1101d03004441c1f00c2501100c1c00620100e480b4010070380c0c2c9111490030b00c81804140080e80c2c1c44280400c1c003443c81482281c49201440d0380b10300c0fa5208203c0164062640c42e4404060781c204030500c410100300240c0340404940b5034090341350f15a0002c1d1108a0003200e001c3c9016010302c0ba401c0e000d915a44107001d01c0d071502e07000411040d101d00c03d15000d101d03045507160140c1c0030750007154003072051031121030164803901100410303802e8440d1045011803d056000700d0318602884000b507801d1425590038070240d0000c01d40c102031103003c00d0b040350042030510021400500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 231574820 1250 231573570 231573581
    0xb07020a0c06020c09010b090f101106190c050f03072d11160305030702040908040f08010506040506040902060304020f12121909060207090b0f0d0f050d031505010819 73
    0x2000d9008003070801384c440c00c0210071030041c0c0c001c2e000748000b00603159007600c40e0402d070810103004403900b0400c12100380c010360b041290000b405c02c09000d09010003002131f110010130b01714641840020000007100355403e9900d4400c11001c4101c7e07034014000207480a21920130922080d40182c00018512607940104804400602e0f951010a010703445141c2200700402c01102d1442d0f451400c2000ca5107551642500c078407410f10040d0245485440520500c603103801100c3c010300508252181459403608005d0080070150703241845181844040782e00352415014562000741c00a02c50791940c1c40320760030000f07031500c0c01c0c9140c0d40044580e0704081c4c000b00e06210300c004207003000140c80d80d512b00300101a50b00881059040e814041c02d01d8083c8003899001407075200b80d810105000a1481524000540418001140c9036214242c60300380d01c200b1400c0181e40c10018804e404882c03100103028820340554000307995444000c03040c404100515841030240d241c10000c050a420f0100250309008800d884 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 231576070 1250 231574820 231574829
    0x90f0d060f050601080106121112040f030206090d1b020a05060f180303040b19110a0c030317060f040924060f090606020303011502030d05010305070f08030702030a0b07020a0c 77
    0x903994422501d2603421805925032101091034080c040b503061210207003480340d4280c4038100455942c6900c4501210b00d0080f01c482d0444211405100d140ca8036041956401003003045005020b0040410740c828400a08058209055221480341c00006000707a142d1a803451000e86e8441a401c00000e1207461303000091504920300122a9900c010550074048040c100c10b0040e0301981c800c000400200201105071081c130340c4540c07041c031038601d001101203e001c0794204503041070340141c1a2800030010b0100c88030003100e12a0300e440b52031260608810070100c004961058001424110480e61460170b940301480081c81120303c49004070a5001e003021003400d00c4012141d281c0e83d40400d000300c10a40084800400c0100d5043c0649800d0540094807400180304001d1150b10311007419642c2e0b4002e005517000da140081d01000203607917034204a941e480061182d50f204003080c030400701d51040d000c4111030f61a5009401400408000d940300c07440b0541c010565811801400c0907840024a03a40c203450061 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 231577320 1250 231576070 231576083
    0x140403030209120a2a03050304060207030605150d15021c050406060b0304030210090309030b0a0f1107080f18060d050a0b270901020d020c0609011107030c08090f0d 72
    0x10b5861205203c0d00008080c0c9184695002d03c40490008061721a9041c1050400d0b018000c55a06410300302004004c94100400174000031070041081a8001600c4045a000c0c007010312642e00c4010500f00701c1d0850702d82e09900030220021034004541190842e004000c0701c0074005181c030402c0e0480b1031030380140d000218071903a103c5061005200032809403801501d141101c862840c10540d034040e41d10010140140300c81600d400c0f0b41e030140740c0143c070300b08000c6030402c0944d00780707250407a0b0344801000c0340d0752a4000300785003007100d0054003014000e81d00b104d07510446041c5007400f48084e45a042c0c015aa00c480c1c4050007941914180d242d5070007501c07175801d0300d14000c03c2c181801d1040a00350f46a0654943c001c0041500e00b0402d00e44040000b0700c429503a0294002c5919028907441c0a4070840314420b441500000300e808442500003101881182c061002b00100c3c11110407021892090000140014243e40540c0d40070400310001000510b000034103201028540b503020501c5014254810b8898 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 231578570 1250 231577320 231577327
    0xc120609060e090d0503130c050607061409030c0a081c06030506101a0a0c1104020310030302160614030a2d1b0207120507080106080d11010c050703030b041404030302 73
    0x80820380c102c0680c0001c04000030300b20030500d00d140246075004c028020103032507501c1c0c030b08001807104000c1d408020300000781c0303595920750660031300713001409511090300d22102c000f000180b4080e6000c0f003902c0031807447c500a0700003240b2903110106250000304001c6da00020310101407104410b94803d034001548a00c5c0608500d1620b801c42d0015604280d01c500503200e41100403100125912003219070100c0c030343c1855004904507041c580d00d0003000c1c161076038100d0720001c1404009070468642c0e904881c801c0c3c1c00c49421048000c51004040c0356841002c002c02d0341d21480740001803001c0091680310803101c2d4000792041482c1410511418030a600903031441e0751169107440004d01e4022112002c41e840b95045c0180280b0700000d6440e0100c1c814203404a000c54040c00403c501408401c00038a0420300038080241c03a0b0541030345038100c000c240c9021070703040d118001490300180141d01d81300e842a110203084c45020346058000d007000e6016254003654444855503400d0030141110f016034002d80e001601c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 231579820 1250 231578570 231578579
    0x10e0a0b180318060304081e0c07080a0b040b0601050d0507030b210c1e04020c06070f110607050901090819020109061b020d050102070210021005060405090c01030c12060906 76
    0x244854007526900d29400412207181d204019444041d1000025240035540f51384600340200c032030183c41c0607105103140009044a840b15240090181c4501000c00d4440300c0b0b82d201d1b030040e43da08241c1c0d401810b40305580002400b040d100300344a60301ca4418100246449080901c51048401c11228080869582d207a010040d040c51040c0b0603004021200321b24071341c0c06400300c1e2a51040b4608800d440780300042d10307107811402252107440100310050802d40d11113820340b8905032034000480320000094944104000035a21800d450302c45d138007141d806086651941041120b2551090441038103000701c84c00d00240f51002004042041c80c810700c1e84041009861000400e210307901d178480b0701002030105810b50003000303002d004100180d04941c0b9250040702803620fa406802400c01c0a980140f165505511090f00412000d0424403166410040c1d9074070803040000301c450a50341c0d00c0707081c3d000345000c1201794000e901562860b002403c008a04005545107607060350100d030002e000c0030751156001c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 231581070 1250 231579820 231579841
    0x40305011802010507110f0301020a05040e0709030b0a02070515011e0506040f0e060a0302090906040b250503040309030c060c050f0d020c240a053c0a02010e0a0b 71
    0x118060041c06070812842554000070982c0c002d5160150548011001d03075003143c0c1e03400b003060043c210081e000795268111100c020380f03180c10030f12452406616400000311424890600d0030103896103c01040080e4580c0340000000b5000a0011541417040408a00a0720b20707989035a4000d00090307038010209440c4405203040c050307036030f403213140078a10500c002d01c00d00c480c4141d554144d0741d01015440c0c1641c0d8000004542540340c0d070001e50090880030500098180104201d4426401205552400e4403241624505e0396001000524010414680008014400c00c000c0d0f401600a10f889110b2645a45071005c8065190b4410404100042209020070070140008082111100c0c083c2a01400c07401c07019448070000c0003810310402c2c003d100e101050035903122460144120f441d00645611690101401f6075201412500d60900220b041101c402410115040311041b81324151150749032103001500190055100341055549924000c4040901080400d00003030142014030303080d09000f103044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 231582320 1250 231581070 231581081
    0x30c0906180f0d0309120c0e041b21080a0c0507180c02010e0604020d02060705100504060b030307030905040e010b18310209070306080303090703020118060903021e090c04030501 78
    0x30f000d01d90005110000c241c01c444800201c036042140f081d000040391400740180d9209802400b100311a080600042c0143c0d00250001c0c83c07031080041c804251200e0000c909100381511081900c01e00d07450020000301c1c420003608040303801d410020b0040c031559490b03908180540e044025180309040c800486800180244651480540001c12640d0b00c4000d615444480003400a4000c00300c4000e400c01315112881225110798006d030584149030324014494000e0001030381c0a5401c0c600307110480140c2d18000c03003102c0241394541c0b56480b40c140b4050602000d01031000c40c1500e036550b41c120280a0b0b84400140e05211000c501502c6a6031a0800c680b25003180b0308140880944074501c203008a032038440e02c02d0a22990101c4401750340350b8400310200c0280200e5000720300140008424001c90b0800000c007401070768401d80f1210611303001e00c00e2034a00b4031118440d40c400030300c040da030030000b40c1025030400c51840c110940300d50700200b644011415518090302c2d46108001d001400b00203000c428400d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 231583570 1250 231582320 231582349
    0x1605010b1212030c07020a030308072c010807021e15010e04080d0509031605030a02010c0806130e0109021503160f120f061e0e0a20030c090618 63
    0x18041c4403820258426900d80709a001400505000408a804070f00c03520107498001c4d07401050380c0c440c40e84900e001054000c0655035040480c1000d00000c82400c60095080c1090b40802603282800c0d8407800111000175014101100394041c002d601004228a80c50b481100c19504c0014a03050341e10a132951543d80050b40001090707221501800000369200301160f1451031a0440807800d0344a1000a900b184580c43d0024041a041c510160400c440480541740620143c2c008018032500744009407100d000858065500014221483e1403142035503019843c101d080c0c07030001030701603842e6010030012031f800001380f0000d0402004019003009845014000c03000c0c070f07140481c13490207a40c1024048020103400c0302d200c81e032a18860b0a180c28150711540042100d80c00d080810034142084d4100455980501c0e0091007403540014120320b8a80200c1c403c03040030894400003907260011450041e08041e280802000c01006018141e66030040034001c0366621041000f40b0b28284410000180403036001c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 231584820 1250 231583570 231583579
    0xe0f0402040f052b080d1509061805040c06180305010e0a0c0614070605040f0c06120b0102060f01030b041e03030605042f030a02071b0e06011e030b06040b1605010b 72
    0x180c0199228003400c44c00c4581c000030450701c505c510700321000604405140c000f14000340b01000500740400750000700440e41e02000d4140720f48203280e8042e0542d40111b50180c61400c5521041054074030900c00c01d41e0740072141d00d9000c1401d841e81d50342400d4032440e240003e403503401070f050a03040c003004000807002840541030020001040c130804030f0350741c051254050080d0f607482d8002010300102500d0000704079403002c5803076100b549a1502801491165000142135440c10540140b25400009c0940c090b01c0e424580000c681e00e035549022070024000c004441d24541d821240900c1c411802003150103d110b9140070400c0c40c00c0a045c0f1003107a0034007882c09441c201c0d13a160701c41e49116040d244803a62a200c1c05041d507030343e11000408003038400c6020041c00c8010090071400d404c420084402c041d80d0500103200c6164035010011114608160012a19960440703400021140603a010010b01031001d0461401c0558078884161560804007651400c56601002d20707041110030320507100011745c00c49 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 231586070 1250 231584820 231584869
    0x1e062321160905010804030c050105071701090209060d05040602090306010f05150a08070f091215150605030f04020d0f0302011d1c030f2a0806011e0e0f0402040f05 72
    0x100c0040c00c072411403085905005c0d0ba800882c0c00d05104816141d007070f035003080081c8046d090030440140340002500410014100c613034000700d00701e4014022610304042c010801801d240c0400000e0000300310241040390301c03503400c008000154078240320541c000c1c0440e00004100d0352908003030010000b021840e6050400082221450407600703d0314030360f00a0310038502001580060348d029901c0b103826030403801c50f10301e00200d2002002204488046d1080c0da41809010f00c080300003000325480c10300d004050100c2c0c0b080c80043c0d09021801c44490744103000401c0030b400503401da1141214002e40d0300c0700741c0050351254034603e100386000d10100c1403044d80c0002450030007007030900d401101e04c00081d00002c141e102d241c81200d07000541c00c50417000c1d4001450300e4481041507003140080c18045062004144800001492503014a2020701c0310a1491160290580c0c0c0078000c0b45e1160402450301c0e07100f040311004842946440c0301802c00350006000c044011820541040021030516240191000d00c02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 231587320 1250 231586070 231586111
    0x100e0412020d02071a03100801020d021806070201020706080405100606080405010e060c160c15090602120a0e0d0f05010504060b030f030408030a0509060d0e01020409061e062321 78
    0x30542d01c0c5c03130700510350440c90304c0e03868409020380d1000a641c4200b06c2580045001c041c0c0b503555600908101d514a030601c4500354040342031000c9070040c03c1e40a401f50304550010080c0d9400f940001e61311511482c1030301d003c8aa100014012100b040d00083d002405480412040200c00d104018034581e81d13000030b14540c9003440840c2c180d441142d000ca0350318a8442c041c14200900920300030301404050000c42031020003010000e00303440c001d00c9403100510503011103032030040022080b141ca003084da070740ba009414118001e205409400341c0080f601c820b588241040460001e2181ca4003a610400022844a000504243c0380405450b0310441e1500100820861698000110340102150707050058482c0b41c86400038849005110300303014080d090000080740c20006600800640b003000c601000b0150b02caa4003807440d02c1d080320b500900700f424182d050290034000e028844020000030b100707070980b81625400c030b40c1c1da03040b18804021f00010211100748000d901d0340c1c41e60b4040d401c50f030b00f060444c051 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 231588570 1250 231587320 231587339
    0x14220804030f11090f0703021b0f0a12090b0a0302090d0206030a050a0501090e0c0f0406030f08070b0c041521020705100b0103020a08180a0b04030809071a040905100e0412020d0207 79
    0x86e00c05c105140e0b000405070100180115580000440b40080d12031100d60b802c0c14640f5140030711402c90341b05a0902240c0040e83c0903d115500b03907004c241d07100d418000500c0d4294002d61042d511707140e0020950b80501e006a40d680300540c803454a0080201e0b0509020710540291030044e005503130094100b840c5050b52290001c1c107102c1e40081260001508001500450010011034001402a400c010040d0040c08000c1008008140c0b1445d5142029910440c200c445070013140500c13127080080d0041d0543d05841034502d1940004122070010b0341c0007a02003588220f031b00c145021036035074008843c19810340d9190b2181c90000c07070080c2801c1d407a190403240001d281e080d0003411503801c602d1601031a640d8040400000000079800b4800002c1e0b4103103810041c0203c007080300c8010007440b442001041115004803406111840b866200e82024103002c80c05000d080020711500000310074620004243c1c608102d100c1c040c50041040f102c0505903108028101440356001000f558445003080000480 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 231589820 1250 231588570 231588601
    0x50910030518060906150d030e060a11010c0215010f0608041b08100615020f0d05090d0c06030c090b04050f0904080c01060608070e030114220804030f1109 68
    0x11500d400111659080c100d5065191a000b5001c4140714420410800c82c02c0010320314040c1d84040d440c2042544040704115404200e040c0003000038a0700c640d410014140300024025420807414182c40d0800c03c510000d0860700d9030041440141d002e06e890501c4030003030002f11405171408221030014942400e202800030f100c0580014440c00c0034040e451000b08040c1c14580103840000700740d54950368030700035400c0981018050b001c0301c03442e4909001d61003800003510f1a44071980700050800c0241c0c0a0040d50560800403600342c010300e603242004006543d0f030300c90902404442e01d0010324a510140c0090100c0c0c0c86820642030100108803d21540e5a800001d0740d0f4150100c0b518403460303a840c504103000b4041c0324598241e5600380311010480300d030085081c5e44506c2e041d5a03141d00008281d010582a20030841044105021601c00300340000004921004a1101e800c5007055607022550760100702d038490361044c0c0303600100c01c110008000e0030a1604291070412503001c002e604040c0c0443c2410b01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 231591070 1250 231589820 231589849
    0x306141c08160b01030204050a020306030a200a03050708070501111023150102060c0a0909110f04060905010206010b04230a05190e070302161502070b011509060509 72
    0x505500c4004014089044940300d400030504100400035038900118000c60a0204921403820000021892040f9200b5240728a0000b00100b4016074240c940030070b4034030844844503622240c2810fa880d15226000c0ca540114414001401501c0c500500320381880c2c2c268005504000c4020060301c21000006443c41c90346900b0400020403402c2e101d409949010503d0b581d601d03000b001c01c104171031499031003c40481c460080e02519030035910203811502501c510340880020405104c0184442a4240d212950024650280e5803a140b4550000011604642d002c8000204001000c0c410340d641404001e0040660900365070800d410403203445880a03480184401c42c0018010f51040c907a5584a003030001c0c038001d0802445041e0150050400d590580102014510f0800100300101e129100b116200b0480840b0322903000f51581e5161100c103248440c00080300d8084c417901e8003141c28086414002d08503601800b03d62555220054100300750750f07200805004007446000100d46035402201400b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 231592320 1250 231591070 231591109
    0x80402131109091302150a1d0a030f082101030312020d060f080706080c0c03030103140c130e0607020a0c050f060c010e01090213020f0412030c02030a050d030614 71
    0x440715000350074118001e81040365400300c155014000001801512030503114001c0d01e0880070780003014075922061051042c13200c0014441c1c0c049220324150b04d800d00301c02c40401041d08182a40c0c2c4c2e1108601034089120030348402070b00055880c41d88219441c940145008600344411940c5903450245c80960f1009240c0d049075000104164640104d91042010b4851003c451000c1d80c3c0b190b40550742c46030300d0b008100203c1c00a6000c5401e0780c3d08801913500c070001c0800294039503070969131140d481030601c095802d60ad201d005105041c41c1c0e130700c1d0580300107000c590200084a10100b84000d00e07001001e81960159040b240905020410780921682502c1043d0748d0004101d4036036000c00e01c544034564aa40760f9520b000d03401042400190858500c403402107590034142094490403908a114491080c1007881040200f0032007810315211000301d2034000e0030329850300592a00440e0a15140701d00844003504042c1c0c510b8413054161007000c001d0155007031900c2e24001d0180114144401540d0311070200c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 231593570 1250 231592320 231592331
    0x50f0a06060f05070203010b12061602010b150f12090a02090f04050601030201140708180324010905042301050609090706141b1506030d140702041a0a170d08040213 72
    0xa5460940000708da03100050711036020300b07180f40006078548405980802a842d84185090700080c030500a41c460404020200681c0318081c00c0752421a52100000540c400414000740035a0180e200e41c0920540c0098040c00700080b662040048106e0024501c550301c100d510140008200c0015480d81543d80c20300b0007081c020307085034100c000c6005150f8020500800060300310808004440c0f585140d1a050301120180000c1c00e0358404000640402d2a104800182c01006500715641042d038001c0d010f10702c8881050344000401e035002184400514241e074540c0c09000c8903003049840b00c2d51004000000d0010360f4240b503001003142c1c00d10f00509480780c0001c20803400041c0000705481581c004501280c3c2c410300390f041e0551b92200c08030b83c818864001c40300760412950066803451560803101c0c418518004c480d6003008010b1083c80d2140000e00d2900c4445d006a85070980c10790058003009002d0540c3d04c81d524207107442e140480c00780000304007441042c80300603152100c0322004207140e907101042 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 231594820 1250 231593570 231593573
    0x1b070905131209081b030105010b12041704120b0f0601050405030304121a0907170706080601030f0b031906050603010209090408070618141507050901030e1f050f0a06060f0507 77
    0x40a10321038004d51900d01070040385242d80d002120004003015004e40080c000c5a1382d1f0320004d030040c00f8001602c4051408080064000758543c84101e03c1340c2c1e595140103080a8591062600d02a0440c0f4101c0350741e1041001d020202c82000c103003541c441c0c03092070600e10389401c1c0360200342c60b0b0090b80f00703903581500c004000f0b8041008014820f40310b4400d8592010035494280581c3d99181c041d481600f50140640c0644205224003049c9003054a1403504e442040b40ca4200c0114018209040380c0c08640b50b490404d1101c41e6010301c01c15410075401850307600c80d5001400c0038803c490000d090580f1a81c4100010310b01500d500902e140c0c4035802182064035860300703007012005441d0b03803c0c0254450b07291811040800c030400507640401c40840046802520496065281e860300980d90100894424400740000e50711a0300000402c00345582540c04580582c500241000c62070003c5050b00b541314070410201c010252851a880300ea1007800380012031030020040c2200440c03461500401c140006c4190 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 231596070 1250 231594820 231594827
    0xb0909031804180503031602030a02030a0f0c05060f0117030405030a0f1a16031802010e0f15030907090b150901030f06051e0a050a0305100c141b0709051312 69
    0x340000f80c480010529118925140f0348907407045aaa080c050904034582c59502d1002090b1503004125800031840c0110484064500c0c41800c0a00c00800000c48070b940000303501446070b180540803c9865100b95410202800115424990074800a42c070030300003004203540000314070002e2a00289410402200b034101903140f61006092070100b6209179080c0501c10449010084281f4100d603410810a940e640000d101107a0240e0040e0000d0110300207180b15103050702c0e603034007160001040610300185540c17a81d880e5400455801c4169007000c0410131074044c8901075000e100c40b044540000c1000001071038a81c41c000c9d4000e050425a0703c41c48111201f003540d0140c0c001d400c0003070000c245031203410403202d10700d11701e002c1181c011030041c4000156424440c883c6030541f82d005002d05100142c40e680440140000b04100c010003015009080d003500c01c0750b004091079124025022440480705500d54607002c10b03940803c030744d1441c00040004091840c1002c1d5a0194061a249030b03155100380110b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 231597320 1250 231596070 231596081
    0x1b1202160f0b0402010212040302030d0e041b030b0306060102150a050702100204090203041a220f29070e0f0d0c0803030a0b0436030207180f0b0909031804 68
    0x801d807803801030410042c0000820300d240704034401d90848450311034605840156010f40d10000390540d000c0c40017090494021034800c0c0f981c07440604000340080ca00909129100c08984d201d50110b6611407103905181418030100750302c44c81c20b0004041c9a03040034840c0003d4003008200300341131a80c40c80400d44091090000000403508040103540702c0b900e4600b120001e40c01078504682024a40006281a160f0628442e2050355042c411f50f002c0340c8400307404142190580d0044820345040714a003000555a103e56107080c3c003081d4602c0b00500e440801c1c601a1050282036a42800700b4604445150342c2c40c90000b5510380f40a4032041556055860718850621440c1c10440e800d01011042005070032440c0d1100030300d1107003111706000c28011900381c1d00302410190400a001d03000701403040807070301500c50170350700051182c4116120269101c0c00049001505451840c01035154000251450b480380644118048110389200050400d26a2942c3c0d0b4850b4a140c4110b000035002900711075a42c40d80403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 231598570 1250 231597320 231597323
    0x1103040f0b070e090712050a140a021608030702070501080f040c03020d02121506040c0503090c0d140109030f1106070c060c0e030703120206011505090607290603011b120216 76
    0x100384c07450821305005081800f401035202010743c504000203a1495050280c5100201010801c8050b07444004401c4043d40c0300104e0100c2e040701401c0c1c118006103c0390300071449800c1580c090b0044505041c001404404090443c082c142203040911010036034051407101107a034119091b100145007031020640610552440c800c0901582c482a129440380c000014030620040307c0810260079400b0054442d400141c481213031a600460101865041c16856181e0303075030258201c1c460101e44008400c2c252102e00c10f00b01c0000303031605034034007580d80c12110480218101030f010346503500d070640b40249410104040a0626034940342c08944080c01486141e40001002d803d4440f00ea403031303082c954590f12015901e18014800c100001880725100302c01a0040011550f070503140c40300002c01c01c13000d41c1213050190f51005103402c102c4e10380307500c24658140f00031812490700b40307a01d402400c15084403104c20030105030211912440c46126403008840075107494030000161640c80312068010b415226520 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 231599820 1250 231598570 231598579
    0x241206220902030c03011a1509030f0304030611030402060904051f03050f0d1103030a0b1c150c030c05070615030c0b07060b01090501050403060902030c041a041103040f0b070e 77
    0xc103280e86049400c4940c0481c02a812210600881420305080700c20152160b0416128a051184685060b4480940601c1321a03040c606001a40c40041e0030054441c1c080061a40b000504004000881c01480c0c404107424649030b007540f9040d004107102c1d105606a10f4800d0356140000b50441c00c4003000c860082c1c1d1200351a455194076494095521110a103031039481344a00c4004001c0d807445221011401c48699001e9030030750b01c42c803000d103001d8413040c0c495503448004206030150303a003210350000640d180191003218000001c96500c900302c0d0482030100307003050304080301c5d8252250043d04880c2070a92102c0009007a6800340440b00e201c4036203420003040fa101104000030010702c0350002d465102d0181d08100000e41c0381c600159503106540c03140700e0115000b844200041541c56021184076030002d800d43d212140800005002c5440d03010501103415090070501041f401c040c401c505ea8210b000107114618101034880d90080685803000800f54249080003818180c401c04101189000262 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 231601070 1250 231599820 231599869
    0x30a06090c0f0e04020c0a02100c120c1e020f1302041203020d08100503070501030c0519090f06090b03060f0a09020a0206010302040b09041a0603010603020a0306050105241206 77
    0x7000145000d0300b12481100140c01000d04054a2074a8802c0b24001c0b00818000c11f0700e0788446d8280043d0040c02c001b64001d004813000b50002064200d0722108000146554051b80920145001c2c010109a0107003013040082c3c4112600060f103402000388151502100c03600704d401c0040b0008070182c801d681001070003800320342a5000305134000846c612030030300341c2e128496103540b00e018036a00c0f00414400c5c00d52550052104002a50180e4800524a4064a001d91500303032003041521020300e551240c5000070b411880100003208059103140c018000740d18004200078548104046203010144c641403161080074800003c41d44d0303c0980301b00400d002d850030b649421000001070340b580c00074403050740907a040003003442c500d03e441c0300e1a910031680300c0b0818055811141d10304d0213144008200540640d6103c0700400942ea40020041c000d41c818140820036605100501480d146e00391500e10426140003981e0200c2e188034419606207000185003182c41d0f40e03405001a03088104507001800541c0b004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 231602320 1250 231601070 231601091
    0xa080d05040b011208030c091f09030201020f03160602090d0b010f23010203071202071206020705190525050a030b0610020325020609031507020f0c15030a0609 70
    0x180c01803032140c0e000c0c0442403201c1e030362161a0710941c0340c0074030700501300001040090680030100c40900000b08000e00390100325800421007007c414410b240c040089507548900b04210341e070400043c0e241050041c0950b041c4031080038000301b00254180020031360342d004a140700190304d03118491410150020114001f0307503901c900c461018000d50044503400c240001e0f03120409d00301120011748020040c2d000b5464120243c4641a060004010020443c054420005000043e4090000350503004890069907a52146405494149034555184403424620140300c041080803d8803101d4402c140415a004184100310801d0001a0b41006522491141011040c0320441d04018803422003a81c02c00e00d04490348a00303036504d00612001e00b044520120504042204200e1701180b00792001d0300b6103041c071056500280c00d000d4001c120390707003006451041003c030582c10030001c503041a90a000d8036003000e011021034400407040c0b80054580c440000411018100e9500050080203002400c00020018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 231603570 1250 231602320 231602347
    0x72601051801150f050607150509010e011506080609190c110d0306030209010504020c12070b040209070807020303040803150d06021c1b0c05030d020409090b0c0309100e0a08 76
    0x12a500700d0682d40ca4100c0c40c1c244280f480380d5110035103d1020480d2000c82c501030400c01c2c240e1100c44101c80c1c1c5e10304108405050043c0d8010103000f446140004180780c03800312035a41c2140e80507418081030008078031080200c00e40003200c15401c88410b0390713a10346594807441160b105044807400308101915107003113015000e601c4100584d00d2030444c805e40d180700c85507410403000d80e6860300000e0340c03149003a03004000b149000d50041010100a0301a5030342c801121802601e1350300460380503507039100c055007000304520f826800c1591120301d80c2841c14403414500c100070359900004000604c40305000000c2400740b04280711070100100000c1c200035070540745103041c4001c0e41020442580b10410803148000300c40300350241c404140000040c10044000388041240d8640b4251000e0340c69020402c07801c034031014240010400340105440200d1361100c0c40c50041208640141820740004090042c0302d03e0340b50120701b40288a80380c0e00c020585140a06400307003840e50324500244035500000d13003101d041e041e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 231604820 1250 231603570 231603601
    0x60109050109051603020a260109050108030711010e2b050c1002100504060b0a0f06080601050c0a170f04030b090f0f0d080c04030c03030e0f0609010207260105 70
    0x82010500240e6a80d50024040c0d4500352083d8140c40c0320003054294141c840d602403c045541c51504a8054002c840c14045013804902c10703000c0d030000a40140024504d2303015090050800c100110714009041c1c4602080642c2100840e04102d150719a440140d990043e04003025a820100708800e0025030015420350082c040b0111214004c654503000070f850400304d640d107081030740c0d005030240350880745d203004c018113005100325000c0d55a205000582e881705040c0303d0140c2047c1c0110f4515a051103409000b0420040009040007030030424141c04500100d000440d6680c040701c4010a54408618041980200c41d00001406c101090010601041c500802d018a02c44001c1d20305c080c1314000007a40b540070115507900f02d5880b20b00300c2c9070749511443e241035000540802660070552640d590145e00300f029441940010040c1c900340c0040d00e403503070004400610840c0c2d07180c40c1c000d0100000c1d4440b08035224480c0f03041c0c9124600032842709440c60701e8503080d01c5032008000c03515022102803080395 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 231606070 1250 231604820 231604829
    0x42003010615111c0f140d0213030506100f05060706090209090304030605090309060316051611010806040504110114070206041212050408121b0703060606110a020915030307140601 79
    0x40780344e2400c52284401c4502c80c40e0f40000b503a5184043c1020034013924078002d072050030601418100015030406941d032019003100300084803408421455410220710341000a4111202080c00400030450408984047c0c4103c4200751503480d1510200d04014000b041041c20284d0095217440800c280300f45d01000400a0301c1c40380c881000b1980752a00300d140d503802640301c82a004242080400c0c146081030164801e00881c81c9442c520b08480960941a192881c00c0125080224070012082540c0c210300b0b5140c0c0500240c03820003c52415071034100bc481e00d0b031103001d81403060041c4130b803c2781c044210031070b80c0d4540c02410169941e592204500a03000720510145d51b071010b82c0200d104054032940803030301100c201c00020008403030000b07284582544602c4440491844e60707818280c2c140ea00b40304140c025030145500041c3c075132800380040d040000740e1411580c96084440c400006a0300c480a99421080c00760b40007485c51031443c08245148202da6000e0500c070000c21821039103160000f22070341030791f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 231607320 1250 231606070 231606073
    0x14040e0a03080618010e181903020d09060807020703110301153c0302090c04080d090f0605070209011208130f0602010b010503160e130f020706110304200301061511 72
    0xb813045040c1c9000c181030a00500c20210f00310404075540401a00414088042240980c2d0034500c04500708454a03002c043c003180560409050301c400c0c1c1e6004000c01d0300500d40c5040c42c42407803410650081d11101c05000080001c03901c00c00b051843e4800350b0040d40c1c003100c03c0b02c0101940341c07100c50001f0290182c403008404d001c14140580900c1750709101107451117008003070307403401d1900795400c03c0303440c020080200140c00c1d0144000640200208228904a891782c2c0b129000c40c0e081c8400420b481249421000501008010f183c0058031260400350458160084151283c0c940d843c09110360b2040e038946041294a00e6404030340034254040841c1140c0c19a0000c0020340382c90f00065505000445400d0a008462000300302018000c0300d03901440340005040031303604c00c2181c0c0b158048920310b1402001883d800708035070003049064429030400b103103a520801d0961410381e072070415030001803011003e48142120300d100729441c00d42081c0c014181007030260000444100000740090444207074240607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 231608570 1250 231607320 231607339
    0x20903070b09030f03250302120a03020903010e240604090c06020f0d140a1110051311240c070f0e220203030f0c070314030301030323030114040e0a030806 68
    0x600001161b42c0b1941402c2c1103200c10302c1c0c403a982601d01301070036802d0701503000e440136000c80b20404400810301c000e1321380c07030040e204e03075558061600f15000d5151455103688404080711600403584920703048c4c281005001d110582c1d4040104001d020030138001003040c0d0113240089030003038020942d45400c912400071107a4100d03651004440019a1004000c203440c020806901d02500c210310400d0341400d0f92045900000035001d44c82e08480040f60ba54000d8080092075008005103092445242d00c4100c5440940149100a00f1000322180107841c80120000640242503603080c00403000034040901c00b280b1450361040044030401040383e1407943d030003445820841855502c1480700015401800640c02d000e054070900301e140d800803068007403600c0f4490001000071906014020100e280002940e140e502d14a0098821080c0c246290700a000c004040120b141032401520704407800d42e80400c691501e0b080225000f0002040c072a18140940300400c0c0074190031400301c50084000b80c034500d80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 231609820 1250 231608570 231608593
    0xd200a0f020703120f0e090c0a030c02150105010f0c05011b030c1805010e010c0f120f02190b180d0c02030c03120301140f10030f0c0309030c0303090303020903070b0903 74
    0x702c45850f404001d00a03141100c00b91103242c86804003001c000740c54148861100b5840700000e0300180c044486022441c80003a08215840d807500640240d41002d00040540d030098204a1412440c14040e050400044c1c880e0781c1e40a83c1300d00000403146402400820901140040c0548010720702c200c1400400e003000840804035109810360490180070b12089a0907a0500c001110a00b440c1940300d410001000c64440110308014903080c040c9100702a046040501d03090041d0400003104000425900f040780c0c881c8405000100c4450703019440b1101090340e5449140d843c9401c0e4444084200798850501c601803416048094041c1d128000c50485e142e080900b81010382e0391190f50300b01000140140010440d07203860b941002d10300c6600030401c00d0ba182c1d504010482510084900c1400240c94a13a80b0881203550302c10706460303020301e02d01406816110b4030b024041d118454801000c140c3d452169805151107503064a01d40e484c01010b8032809941c444074082260070002d40c0d28401d000d0b80c0310030300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 231611070 1250 231609820 231609823
    0xb06031c0c030e0f060706110f04060c0203160e0a02070602130e10170717010e030708070303060906030b010b07021207080a0c080102030f0c0a05040b070818030f10020d200a0f02 78
    0x44c40c0000242040e19040540c1d680da4043d01c00d050100c00c03252018030000e00c1620400c00500b018102560300c0c81c00380e50305401014074101d65030204800201306c000090200c9000d8440c0300b6402a154100542e03544040d18100c4020301c2113020007940d0780030b24000440c00200611840c2d000d00385c01c02c00c0ca1055602d0380d10f00c8907010044000011a544045410009941d02080308012803090400016a004101003d182103600c00b01c008c50b001d0708001024010142c1500c15072029058400081240c542580d031400c0b601c00f81030123141d42518002c00e5030811035450301e28400b4003030b041600303a036a00b0b035a8038111a0307140f1107000308440c0c2e4600c107030010440780414030030b030703489410042100f0440e0786481850581c0c640c05406203c080103c10040403d649150340c0090a6891040303040e1903458000c0c465021400c000108500e100340c008003c00400e401c400184400c4882d41d40d88010b94030400c5d602d55500030010346000c05400d200d0261307080900001e030b5015068818903a10344d1048048a00006ca = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 231612320 1250 231611070 231611089
    0x912160905090f0624130c050a0801150206131407060201020417240712141b0a0f0810050a03080705010c020d080c130902160c0503070506070b06031c0c030e 69
    0x26003011400307402017a401c02c94051543c0100e000e000c1c640901e20034200743d41135400c42020031010440005000f6081540700701d04500401d00300c500c0b450010000c10000b901d950003c0e020140e40d00c682c09000050240420403071090203000000c450702c2d035a840707038040e0103500613200d51104181822154a050b200118180010416120000c02e0f0340e580c06410a05414010740b0417000c00000c08100c1814141612072442044001b100304682441c081d910300c1d204840e84800042e042c0c105010b00c0d9400c0340c100d80040e80181d40c81c00c0907405962030400d0a80c540e02943d0040d548110100400420300488000070002140104000d00a0174144003060307903229400800600010319900000342c50180b0749018086800030740c2003610800d9522100f5a050b0782201e502d195882000301044000c22642c0e08108009000640262880c5031522001034100d0050540240001d064900010680c4c1e40510200481c89201c1456000c44100b68074010042e00c40808102e020500781014414240344c0751240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 231613570 1250 231612320 231612331
    0x1204020415051822050606130c051815041d0a0e07120606030b04050309030601091b141303031e03050c0a0513030b0106120f0506060912160905090f06 66
    0xc0001c01248000c0e5100c000f0707001400810700c1d07001c50240b4084044075041445049000c0c100510f1036080000811000c8030510600e102030910381048000c1d5540c0010568003c101038064100d0208404004a102641050007021001e000000c2c0030810000c101c209018519903111040075582c1d40d914490106d60f186507030607540c2d6008203020403c0c040f0f24080100518483c000200300c3c41e650740d80d00d50b2742c40b406070303002c940c41e400100b007041207801c080088500500d03629205006004019a100ca001009006013808000c2903400451075258032008555032420040c119942e800da8909008080c40c94645a5100e40b80031204001813461290044034011041058400d207080710484007550345a2040802c001c03a110640f00001c00304142c616020700810481c0c803409040f580c0c080507070040760b14000c90054030078508000d0003001d0311406d0940d00f103020309442d0b4032007004000001500d881001c120341808181002c002160380103d98020f01e01a000c00303001c9a180111100342c0d191100c90480c1c0703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 231614820 1250 231613570 231613579
    0x3050301051306030c0905160207030215070c180207021306061b0212010f02090307090510120c0b04060c02090702010c170a06030515040201170408030106030f0b0303120402041505 79
    0x1402203241000803021814a40107001030b80c0c3c1da4079603034030700c42c182141d010000c06941c2c1c104001c2caa01a10a808250354560300c05840e110b41190300192000d91400c075144d51154000c50b43c2020092035a0092010b0f241b5038509205031002521117402a50140500300c0c09440701c14655141082a0b000740070654840391601191180316960b80c0040081c511010390340102c1c6045a40f0703100c0703420b00c150a40810f217018056500d041e0b60302031514180d142da1268500b20710b01800c0080400307200c2032010640d440810001c400080078101000c45203003540001001200014000415a4002c452900418802d45a47e02c55944404081e03080300ca00c050818003003011001d00955a810030524203a010f90100350001d02582caa0b150b02c0d1801a20391100f9884d007800d8000e200c255030f000365081c0d0700a440c010510407649072540e1600311038001071095800b81174890300e83e0015184a80c0105010b148040c080780d45070f00410240e41640d080c00d0b02d003070b80124601040146503a0307814140c801075400160 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 231616070 1250 231614820 231614827
    0x30c090d0f0302210f0a0c02130b041a0d1202010209181b04120f0204020d0c03050f3123060403030b0901080a0b090c0909060906130209070e031c021005060a030305 72
    0xe400c0c80309076011b09207400400150b102c3c600010703541c03452644807521282d00d00080301c0302da48050008417581d151025003041d094407000c0006580d0390b180764088650002d54408000d00355042640a800342800392640207045800186038400f41c40c08584c4161185041800c2c51682e41c005480140312328041d203146c409130b45a84401040300701500c0c40f510b0b44003400051800203103050000445640000e810300180d120003c2c00f21404440c02144d42068265400080c4440020550b90501150b154601e007070032001e490190502003071981ca03583c0d10414809500003184510381294031508115421000f00740307490b4452a0750b092803401c142c141c070480401840340384c00c42e0312603c0004000901d2901148103801c902250307030b1a10b03244d0b0790103001d40500910316405c0c030f40805ca08040008020200e0713816036402803005139454221003600080c1606000604005600c0841c0c141000c0410701c81c0d0240d0001008440b031039002650318017051484e40104100e458410402544086d94800900018001d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 231617320 1250 231616070 231616087
    0xc0d0905010f050307020a120905030c06030606031305070506073806040911030f0d080109020703080f150d050c19030803070305132009010e1605030c090d0f030221 72
    0x43c002990882c0150040340d001c020340c0c1d40e4100c08225048182c800040e04240108001d0404110400300f1031001c803401da05524240700032481070300000340b4008010740b4034030491050100a00c1200c0191002509242c0d4802031800d006103400d140c24401c0d00c0a10084a20724413500f8000d00d60356101c03440c058904010780b07900d020030018003c44103003520903014a45605500e5901001102c0d44400c0c8800900041540000042c0032600e05078040d12045e0b004111a000103688907040d10b90000c01e00045415a8450303c05818145210095407030b08100b00440c60301c10301c2000644410000c000325445200d04030034000030000c00c0c0c468032009000510070301c04102d0040c020b4120680c80000031020041c447c2c1652541ca011484d03c44a0191000d8460941040e07428210308581c054030010400400c00e0414041c407200d4031500300150000c200740400415030018001c0100ca40440d4010503100c03000d0b45174140f0700b00c0f010003820100e02501c035000103a21200301240c000c003810700d4469101030030000b48 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 231618570 1250 231617320 231617327
    0x303072c01080606090406030b0702070609060f0f05070501091b05040903020604150e03040b0403050d0c030c020409060b0604080705090106020c01050a08041e0506090c041e0f0906110c0d0905010f 86
    0xe00a242c4c0400180000e001c5c90301c0d14440e0900850241032440c00c01c0c2449030005c1e0924407640c0040040210f201401c0c80125001070503004040d0b0f01e403509003100803200300d007150180a00c1800a080b5400c044441051290041c2c0c040180207071055044035240c2d8507002c10040351482c4100401580102d000600030540340b1441d0394140076166404034039200c0c0000802d040d5400740d04a03400a84021406000303002c4200001d40342c03130300c060603c0c21840809840140104516000007442a6202d0340840104031054001d0310360000082d104039102c9460301851900c641d03443c040c4600036500640009038041c80091040c141c1201038448034034104003030000726591440240107603008440d012904c40c10090803d100340040d40514041d2501c1d00b01401c2c03880c01e140d08035007042d10030350601d5140d5640c1c01000c0300c00800a000c041000030083c0c15000841c01501c80402c01902c0d507032414003113031403041c2800002e02d1400d00c02011f0300c1402c1002e01c03050702c401c0c01601609000070107401034108502d02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 231619820 1250 231618570 231618587
    0x312140d0911011b110307050603190507030504080f07110405010f0614070206040b1e070602040602010b030c10030b0d050a05070501080c04030b1504020c161e030503030a05070c050109050303072c01 87
    0x14040d06881f2490744840c04244194400d40342c004d0455882c8652065240507441030640141031450709002c41d00342901c80380b456010b103140e0040702c23080001d80c003000c00880080079180814090014095980e4610851010005034031030740300841c1048000145603003c1108441045a0041007181001e003007280c1c54219802c103040e04544010701d2487c00d01c0d1401d2000c040c003000c5204010140e42c0b28241038000342900c41900c1e03400c1c00381d0b000485100f9141c0c0c920403070615200c0300d40b500154840600300055100d448581002e080d5010700700d0180305000380412583c0c1521401c0c4c8400a080d00c401e94801054420b42c84041c08101540d008941c0c5440c0500042c004150000d0000d410802000d1406040c401c0c0c032000c2503152601c00400f0420154480c5a00034039505620070100703203e1541e19a075440c0c1c44006c142d1000c9640c0d41002490441c0034040069060350800b008102d000c2c080c2c94440d030707254000e490000111707889200c10b0342c40d5564507124a14441c0c0c5502a5030444214a006690950 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 231621070 1250 231619820 231619853
    0x10c23090d081620130c21110309060f0c0403110d0804030813050901120213150305060717061e040b06040504020c1b06040f0312140d0911011b 63
    0x2080103060b0008181c450f6002404e40f5000b804145541c1041c1080002d4186010b81c0103202a05003801090040c1e0001e01803480003080700c4a1034565100c041030380c002004c41e003a5490580c0030100c14450f0410000030400e00c03940c1c5c0012010400c0e120b03418481c0c1a40950701c40180400d0054401000c207007010404004840d1180815a0074580c4a940700c2c82d99410104a516003408090410042c601e01010300600600c0f14511140001c1e5403900451050400c060181d505152100c0240c00142c1039402c000c0020360304181514100c2c00c01d040001d00d801001d514000003403d040011881500c1c29029410340180407800d101482c02500050002500c8030f00c40c0241e10007000c0c0000281510303940000d10500982c0c0e03028041d501c00420308281d180c0d19801e82d4600840c4140320602a0300303040d030000f0040d260003480040e41e940f613a00f012540038080c0b035a00e01920342c020070b1580500903140c0000070818400d88810007104040c0c0011200302281c0e401224442c10402010804903144180c02401ca6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 231622320 1250 231621070 231621097
    0x120d09030909060602151609032004050f0907140d151b0201020c100e0d080901090510050415090308010614090a0e0609010806010b0910030e010c23090d08 68
    0x540c2d01e21044040f2442c07036011101680141e218441001d00800110740d124480d0321482c0c220700f59108000b4a00800d5000c01800000100b640d0151401044400c210401000380180a24030705880754442e2130105454640c0700303114003100850031301c442d4107000700e01c84406004188006503d40741c00b160320032203180034040c0790343c0c428808070280c000038030004034400c0a07000540d60344401c100d038030b240850848014003440d02e4120b550107420800700d20710f501481035140c40d4900b615681071943c010000c40c0300c002d003d4030a0745803e80d043c1c81280c00c0f20f445076014080078007614148442c840180d90807000c0040c00211100011b004480c000c0c1c000803040280c0309129401c1003040808605903000c5500805604079041d001c00c0300b41d1a0001203e07024191500180c00340d5454418010414020140424842d0780c044410003100741c4203600c40c3d850300c45070030001e00580c88010341c081c205170a00c5801e1282e8055a01d12411034584820031a07040f030038040d1541d00c0404058460740c50b250040001448807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 231623570 1250 231622320 231622337
    0xf1203071215080d0f050313030507031b05100b09070c02040c020a020303030a0209040b01050a05040b07021215040506090a0b010b0304020301150f1d0f0711071d1602120d0903 77
    0x912014a400c5800380110390001c0c002c4504c2600007424521180d001c010410104008004450728a00e44410b451941410a540c59103050319003650b8585017480006240101c00360700009122000464030030030705002a00f000303003c2d801020321060802c1218036201048401014000604040d4403e0006032010310684e404c070400f80d40013a05583c0259403250100c2c1d0041003d031524906031260049a03482420050302e010200346014000380564890100041000301d0808259114200540018040c40c1d05840c915a48502080701b0340c034043e03a06807030901c1140002400303060b0001e041d4140300d4004400403001d030700c0c2c800400c0180c0d00081c000c076019500c594255100d4141801c2c418068018450240c078114182242d0300e03980d4880e0803042000000c0d22062089410f040000d194021480d4582003010345a0801c2c000d20b4110a0351141d001c0c4a0000450019624003a00c070900800c0440040c0f0310350740104030101d030365500540401058034010040c2400102c0181d0040709154400c1c00c0c003011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 231624820 1250 231623570 231623591
    0x101d25020f03071b050603070918060308040602030712030b22111207110105010e0f131506030b09030304081909030203070b030901140c0d150b030403110f12030712 72
    0x1990060f00c411504000c00080c00b600d034142510742840500300030303540300d81580b60404006040c100e00d03110b0090703018003c0501004160064010030007a64205941980e510340d02d5200a60300e074491201070390070308000000030300300034401d0050080651008103007006400c0000400901c1404407040c4040340750740d42c0700c01950b108e50700d000303404800d203039000280c05850312000107001d0104071200385030741d6450400140f1681214680080c2c020700742d8160580705958003080001424203001014200c0920a28104180240390700b00c00103491103020005201e46070b0301c144079600d003c02c4d5801807241c0c0c41440103011840c3c960300503018201e007518003d100b032507681d0013107070a200c00e42e005230080000000421450b10030900440141c22401c074649641032402070310007003080c007445100030225500c0d6509030580500e80315603a0301902c0d40c5d24a00b035603403c092801522903242900810418025644815031b6940041074451403800107850f030510f5a600d0038803c40c1d420082d0048900b840d0b9071401010b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 231626070 1250 231624820 231624823
    0xa0f02100e010509190506010608060f030a0501020910050903030711150f0702010f02030702010807050a0207091404020f09040f08090418050609060109061214030c06101d25020f 78
    0x6030018401c000020729400d04c2e4000310b04295000182514102942d20303014005140080c503941125076500d08211076440f4940042c0d0286a14440c2e617905115219420b0705016065000340800e81003181d0402e85010074420549a600900060640c5a0002c1c00030b100460700a810f841d130350647c01807019452908030110301c41c07150000c100403061044080340740011540c000d080c10103800c0050000750704006841c2d0009101c96801083d42c81003150100b0600e00003070003005500301506c2201310a00071284641c1c2ca07602c411074111400d91141000d000c14101c242080c0e0151400390b900400300d82408002601c8085090740040790440e0001d03a00c00407402c0302c440d001100c42d0380500c144040d04145c24100009031030703e24180c0100d064a46021001c0001e45507440c032100301c80e94003030849128002d48482c40be0a601075584803030801d0161a041015858030740d40000c0c1582c540b06001c84d48412040300c2c44000f41c404075008200800460540394943c0000410000e07845a944112221060000c1358103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 231627320 1250 231626070 231626081
    0xf0e06060f180702071d15180a0b011b050c10030c05030a0c0216080a0201080a0b06071e050d120606030c090b09030709060f080705061626040b0c0616050a0f0210 71
    0xb081e800030040c0f01c1d08441c400c413260a02c08023169000c10020403244044940c0101801d614001d581e2103241c2c9a031030740143d895a50004000e60700103150406428807036100c003002015148914005110303200f40724001c1c880d041d141c041c103035145411aa65101c1e044004e00d0940009019803041d2440c1c0c100d20404241014081c100350006000c400d2640c0c80098048400a0300390049642407000000c200d440e0401070b80d0240e070304103d400442000e03080c0c4048600324901c601130990300510810103506030f044814084000e904074001c1020350794601045046414001010000640b214010010011220701500a01c4c0c801415036000695a110107000ca8080d5406854145c100704010040d01005028100042205a504a2818400003001c12444140c01c800402601e540070740081c1c100c01c0386160100780c1c1004503482d6641c50326007900e070700c290304014081e81907445508001150b82c950701008000f00700300c81d1130b10750611050003401d4070440c03074001c61442188108401c3c422015000d0051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 231628570 1250 231627320 231627359
    0xb01030311010c03090803070c06060b1209060a1416030f05010602070f1e1a04150518010f0c020103050a02090406090605040b03030304080f07030e040f0e06060f18070207 75
    0x102035842000c005100d094400704040c3d442407514090800313020800760382c116035000569141441c034840c0309161100c000c00458000382402800415641c0340702072480a4180500401401c8030030315038800a020042c0d88400d00d030a54486060404110141110b04110510415074100442d502c1441c240c10741c2260310076031055005074404d80042000381070128850002d08200750240c4030170001113600640c1750540d84500f43c0c50744130703000b8400c280c04009019035014080c502c00300a42400c2840004143e034210040300314122950380e010313001e20360040041c0f421400460f01d5506404075541c0041d0000c0100614440340b85408220b80807440d5958440d10001e07040004000810302c1c103200c1070200315100138601038002d034030810612001c6043c1e802541c405400300c480c1d560b6101002c0c50200c40212000285a412074100343c05000e40c030145801000008420004542c520f944041c10407607003080c0341c0394154020912140403200c3c1403850800c0303507004420340102d40d8681e0b990804640d8a5010b81d00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 231629820 1250 231628570 231628577
    0x103110c0a020108012903060a0f030b01060813030219050c040606020307261602060409020d0519061805061206010b0408060106020d090501030504061401081506060a020c011107030b010303 83
    0x141e04110b6030805a40d602400070ba59048000180c0380c00302200500041b5003c209143e00400094042e03039800800e10082d00d900300003121569581d10f40740c0f092050a0080e0030129280c00f000401440d09580c400702c001c2d400d640244045913130324215800c102d0b600c000c1034401d401140300d4008180c50718000c6d20300030112917006643d0780c20141070404808000d0601b050702e00a41d030750089a140900070913505142c80c9421640c2c0f00c4a2140300261081c0300b42e50284003054000302e400c05401f00c541c0c0c0114804e040880760300c2c13161080582150100d03519030240030404412201c1240c413900c41c0c0d90186603c0180601441c05d850400b1303640c940740240c05d078485100c0400004d405d010141c0b060080c6401014140000d10682c1a065406030611002d4003070b081c10156220009003d1040075001342d07029407c0081d0020155031992041501c9250041170800705005060101c0c0d25030521408680a10243e40e000d000380e0704010004495902001c460700415220b040804030201d80440c080d28001c5200e40c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 231631070 1250 231629820 231629833
    0x9150901031b02150f010303020a0b0903040e0f220203071701020702030109060b0a170a03081f061e1b0b07021c091d1303031d0f010e15040c140103110c 67
    0x1300700280960020100401003c0c0714004200091300084e020f00341c9a803048600e9466691442c88a1030340c011540400300403514042440024000c04418a02419494000c00f402401a9006050a0520102c000d42591002d0701c2046021600001140303d01440d00003d4074010950300002d09442c2e50a005852682e0340708a0080c0601c0c11484202c01420100d91084582d01480c501302d440b80c01140010301032204280018001c100900805a46028001c01c2004400d480b208010009108144141c11104900405949550141d60001c2030104c1d1460360940c040d40a50320610041c801030243c009601c21144001d404040e0307200c94901540690380c4072034040d0700c0c2200041111680103804c141e041c0a100c1405010f0883c20311000702c2980506005c15140f684e5440540d20396401d90f881546805600140c06940e2410741282c4003041000d000c54000085a1401d8103610360103072001421500402c0e002c1110303a052030010f40f044141410005440c1c5500c1b00b101c8926802b4000164042d040b04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 231632320 1250 231631070 231631093
    0x7030c08012309030703052104030e0102010f060b03010b13120b0402040b09090c0405180703050a05011b020304090e2404030801080c0d0215070501060806070e0609150901031b02 78
    0x46044002558042c25034500c07410504a600d44a100c0c1ca5130140400c04000703030b4801003c0c9461064440c03c80b076841104050710b064180200252030200a240c015401c0c40b414410083c81801000d007a160f1142c0c2e900e1440c0d10701300003d0141e900228007016148032090340000c401e0902d62044c2c0da45170080c0038866042c606481000308407211500b40c50f2081d18544203100c0317004000501d00c40700030400e840008203a02c54980d07135500c03060300894580d2203105211010041080c045401400b1610420003444184120b1160503c04490041c031000141d00034072003003240c0c8802c0d80203120480c41800596075051002120040c44200200ba00c0d00342400030028801010f500c0aa032500520483c00641003c0c41e416002500c02c0b4000c0c03001a01c80d02c0b4403940903980c20424801ca90f030055000008000540c0c1d031310255074030307810308548400126601c1c15940001c1e0500300c0880714800c5000b025854003a100103000401d5801039a0344e00d04069a03480d0041ca800c0011003001004c2c0f038550010620070148 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 231633570 1250 231632320 231632351
    0x1140080303090d02150601030203040609020307080c04050a0506150d0b040c0c110307060e0f06040e1003140609101e0606120b0604141c0503040303030501060e0414071107030c0801 79
    0x56840300d0455102c582d280745d100400035141c6030400002d2030056a80e40792030400e1406055026001b85d0716010f9080c000031080b50000d82d0403901079040c0c40c180040d40c4e4100c4948212003017203a45680098900003208404400784005001014204100041003551b400214041740c01b8080b842012035071040c400824403045d00d40303260a1190840c0108081c50074588010010764002d001903001f0b8801c180645803990740c150950b03000d841000c64003440ba01e01801700006102c0c8900c403d6030491000401116241d8000c25070a1003004414002d0110750400801100180008020900c200c0141d0881e0f05441199010f0b0900a10300c3d0f03079860481008681c4100110f0b0080142c961140303800f000308014508090b241c4010780764084914003c4150f0503000d00780420708801004040b40400140403040503010b03071145061310010394501040100b0103081c00100d42000ba0583d5a440903a4000b43e007142c481c98141e05201c00072030640c0d1001d6620342d1070104d8026582c00c50100d40c2d448040c801300c104c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 231634820 1250 231633570 231633583
    0x1b01060f05090f0709140d02041e23061c020d030906021b1f09050d0507060306090e030d0b03030c030c0f0f01020a0503011202040204050a0315114008030309 69
    0x100c030101000c0b18107003108041d00c0401e0034406c222403d02c0084400c2403540e140082c0041d06500a030040c0701da01074441c0740004042206041c15840da2034884c205041802c000d412902c000190700110089803a00703410086034031800c0640600c082e00c42210344005071100f000e0890708520035140e1221080c14007030007a06150b0360005100144c10195070702d20b030503550003c0c5100e507104050f104070003a040c054030031500200e1940120341c0260039400c810b0104040042c0708002c45489550400015890301020b0041d40d0f007681d414907a5a02c00d020b100d440c0741d080c0c1e10040e40c200f001400c40f403821020100c11811500000c810395615000a26075001118040c4083c030070f510314200003107142ca1421040134005010600444101a1511200300c0864685504442c050070008000c03d0100c1e81c0c0f46001c212100000c0300304c00585042419070081c1240741405e65120b0504d05480d03a5101484044040d0250000c044415040d8440601404007400010301c54001d065040d01842c0e0381e1510403001407034400f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 231636070 1250 231634820 231634831
    0xf020109090c02120c032208010605090606090f0103090203010e150c0405030a030503090a050106090f0c1409040216020a030c030c06110607030911040e0318090105030307020103021b01060f0509 85
    0x1402c090301818040c2c1d010a00380b0440b40082e440907150840c0e6010213145005605803050315113031100c1c42c0383d0103a4012641c6011204414002d01c800ca45807401d00c100858265100d0390000d809202050700c62030040300301c4540602c10b240001e00b00c0b0360b039000242900c00b5120f83d10415080642800080880410fa0f164070902c0d0340030071440d1610381800701e5514091b240c0007600b000004400324101c02014840070369a10780205c000d0010b1601c0c0c000b21001081d8848202070a10b103001c0c006200580640761074440000780024242c1803001003c14070020b503009a40e401c41c0403001c0c076052001a51205080d001540c0107039024100035056281c1034805038015080403042c01840b0040030380c40d24001415591103d2545800b2030a488580b40182d400154a248291b1060400030303240004035001000d482480c0d000303141690b9922030f803010b011604900303025003501a0000c0046c400903502940003456641030300d000039416004c501074168212842501709070019051900e01704400d05c0c00b01c001ca42c204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 231637320 1250 231636070 231636089
    0x160b1b0301050d0f0c0e011d060909070306050a1d0109050111030c0a030c0509060c060609060d03020604060203070908100903030b010305010503060f0903040b040e0610030603020904080d0908070f020109 89
    0x41d41480d000988075801c90800a04c0c560444100030100043c0c100c00000401c2c2d10302102c00c00d561900c44c0150001213151a800323801c3c3c58170001500e14500803100a026002d514042c1c40341c5421901d0f400c010308401021049880e4954a03041c00d61100e521400c05010982400018241024903180c0e0944141e14044104008240103000a00c0c403207030200c801d207840c142000102d00d04000e4040da04d42c02101c80d0340e5841705d808180d10300310f070710007184644c030404044640c10702a90b241d00401c0305841d100000036005910101c00507000695550085403c406030f424200b07070361039035818070a141156051441c041142c540704400700701074060141408207002420144410b40c184800700340c2d5a480200b01d00d001500d00804240c110030140112805442ca80d440307156078039120920094502c20603261a80200051100c801e4003610910984090726801001100e60f52076a03203e03862190400300107149403070b6a0b04241e100090580d8020503040b446172041c0e144849141c00054200c030365503800b90240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 231638570 1250 231637320 231637327
    0x13080d02011e0e07181407080108070303050912030a051c05040b1512060702070e09060408120c1306090303030515010f030f020c06010e0402091515070602160b1b 71
    0x4492402e00b6101d42c028240e00000342032a0000f15280c50225981d02c188032032036502064117000041078012130981d000020b01030909488003002226001402d1282c4401c0e60042c0d00c0a1000900c01d01c020501e41e10002c0500e424460700f24481411035214400c08804070f24002103080041c26140e0340f040f0704c51500321007008a8500794403441c80c0c42500801240282440c48400074503603607000d0b44030a030b1160031070440d5024a003801d00a9034492003030080038400d8000200180e22510f002960612a990040a03d070611a4154003c0708002e00541410704401d01800301c00117520a07102c011008259940e580380b8000e195050160031034901a04400c401c07980a941090140d81141e02c90307004072520f1400180d00c840132501c00000b4042c028002c8680c0c01420000a242e2242c5002180640e000b22983c1e034194841c104101c9000b138802c0c902c2904003082501120503103134450b0280c40440c2c01248090701e07118110500c2d04880307100c0c0c4402c95585804105129092101a81c03221000140c000d19628 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 231639820 1250 231638570 231638591
    0xe060a11090105090d0f0b240604030f030207080f1501120b010605030c040b0d0c020d0908060432010e070501030605060702040207020604030f030e13051504050403030e0313080d0201 80
    0xd80c1e2294000141c14890002100a110303100c41c4d170f1740140c6a42107070b601c184940349890300a480040c01d44007101a1f0380402d41101500040032031280b40100b0080a0038582850355135680352600c1c000806509600402400007000d84041c0300c003502c130b00c03050380181c10080300083d40d000805074181c006071f04140c802d181d03030b0f40051121200f4074191072850810a0b201e03915076021010703d12494001003407d4001240e048150541608018050859502611401664100d0881e0780140c0b03441541800d6000c031000c03901181c0e1810428502550301c8000c3c21001c40c4803a18015142c0d400701040e4600d07035469003501301380441402594045c10702440c061044919283c0000d43d17034010420003910a0390700240620840d965601114020b40e44001c500c071950040e800c0207400f001e140c0c40400e024040014141c42120380354498070748a142d50103a80b039001d010745814400103040043c81103080c0b640e81c0c45040303e03001081000e0411642c0c115011046181081000c50804202c52581c8041da8100800000e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 231641070 1250 231639820 231639851
    0xf0c011d061218030a0c06050106030908070609030201020d051303090e15011409030d051206040510030303020d240612050c0a050708071502071101021203180c06030a0e060a 76
    0x2c0d00454a0001c210440c0c4580030080b040e00004520070f0040d1100040444800c2c0c3c1040300b881c500c500455081081fa82da4080940948480742c000910034a401c02c00c01c00092000d501001c501070003480014184012502c11504481d0151030400d043d20000825004240d4003034841c50140502581035031180c24076580c0724030124a0f4108440c1844566880031244d00c4110f000d4509862000b8100c03609000462006407041d0b100d00100b16400e4030040c001507103400d140c011140120003003400f502042d031858404400039000144101c0845859150002e50385c00c0c520900030103502d21400300d80c501451324401402c55a14103140c6200d0341d05000030481d20b81e0190050722401c1e21a414090750f80d0886190003c04c501c10094000d010315484803003003002d416030794050704546200e544483c100c0c601300d500690303448104c1a0050b5a180c01000001e4040c0003003000c182c0312619060132a045900000c000032a240c1084542c0d0007216900e10300c0c496007480810081c1d4002201000c108000c0c1081c68895 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 231642320 1250 231641070 231641077
    0x4050a0b0304142d160308040e0c0702130b0112060b03012c01050f0a1e1701021306030b0301060909060b030d110601050103231e060414040b0c0405030f0c011d06 71
    0x44031003200305410903244003040c0074142d00d0b00d03000317441c202c103d90b01c0c4d180203401a00a8040c0b0701d00c2d03099010005414503441c074100c66803da00140998508010050705d000540001c080040c10818000400c842d1920320f40910742c040d060981c1c4680e10781d0b041a9007040b4941813503c4a10260b100071136500d200841c01440c0c203055907400d540d50500f400200c00401c1510f50540c6c0300300f6216460b002072200d003240209121065070522049100444108410b1500381d0240321940104900c000c0703000c0007118001e03841390510b40d0000e800804c005540d5203040003107884207041501c0d01038071022205007604d4180208203c0c05d070b07141081821400c0c240c55a50b940c280501442e03061603a00d001095400d20a0000c00c1d604003101c154109040c0750000c07090300e100c02181084d5840e40c9031000450611b1809001d901035442c01c0380e02812055680b5115002c0400d0050801d402c440d00400000c105c41d2401d01a072640c9a52140040115204003400104521102e20420400c074203200c4c03c6606a40d80c180c03c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 231643570 1250 231642320 231642373
    0x50105130207080f16020d0b07021204031a0604060812090a17030a030903030b04110705010f0506150d0e0d05031b0315090403090f08010c0306050307061b060204050a0b030414 77
    0xa49840d00d418406a0102150002002c0d60100f18146180200708c210503006110f0030b41503090b40e99070300100030303180308c0c0340100e000041000d2643d02080208030f11180b103060f80040300034000700700c2c41d941d4500142000e0101501051030500000d500d64141050034251000309030b0a400d030000c1c01c100d040341d181c0700d0280341d241e102007544800d015420305119412030074403960010300c10484203810032400e551503441180b0440b115424070f501c8803501d0345240700303a5100f00c40180031400200003120b0b841e042648072012084a060366199015408402080b0103100f00c2d49680f81ca990f00e040c07186a1041000c100c540020700040b003041004a07840e0000b5007820380070400d070344119050320740d460155011700e02600f0010043c041d00d00d00117202c000c150041d43c10000d032620308000071600d580074140c0790f0340325000d01c201150845100d010310084886040c8070301c60240000505194560707000070100c0309541d1028464040201c240000d0050780d081c91140129408014800c00e0103403410520b6280d0702005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 231644820 1250 231643570 231643597
    0xe0c060c030415030e030a0e10020c220207120801051903020a030303050a0b12010b0a050901030b061018080a0b010b070c0302060c030c01111201080610140607140105010513020708 79
    0x5083ca20780aa007201d5a40e600e0030040c0c1c0c1d11403e582e280180301604601000c0e03c180c80b04405a040b941c0041005500d580c00642001034502080702185420484040c4100000ba420061706002c01c1c5689041c0c0351102ca076680d50703060f0b94944400c0020160400e00400c040441c030301c2c400c00040e698070304000120f0341d050401045540c6d442c41800c1c0200307040c40ca05904841c890b2116400040c041d032003480d1201046507010b207215220014409411002d0000601441000c0041101e13481c0c01c041880c64940b1602d410500c1e01c110031600d5800c1c0a95a002c44125405a0406402c2040c1c0000c041d0250150500b03c07030501c030080d02c034070804030178901c0041d000b90030020321903d000c5800c0c002c680303814011900901c81c07143c050042416a90181a1480115030504000310302c000c40490040d00805403034810b410141d050140c444c40d0a00e21030301c1240c2c000700030040f40000544400d541c11041c00301e400001000d40c501303800d024009540c0022071504610411a00000444030001d0301d002e68480c25 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 231646070 1250 231644820 231644849
    0x3070b0c0c13110307200a0302150a020403020a03050d030c0809031603020c04150f06090302090a0b0102010912030c03060501022d1009050304060f0c0b0114031002030a0e0c060c0304 80
    0xc500b00201107480340000e1000c4004208020a40c10030941080001196000080c1c090b0740b12040d911010a044010010780054181d03850700c1c00d1130f496442d0804031000d00140340958a038009040948c00313034400c5805030840d0210001d4650984604001c0383d0040c00c0c5040103141244069440784141e0307a8144a2030042031803038050600c20011032140c0c6001900800410b04401414920f65110b84100c1240c42c102640c00700d0494420340c4240b04881e4043c24080c000e4440520344c01c00340101e18012411503684410303600c00b04400c000e10030410441924001005c0b498000000c2c169416500254155400b40802d1644540214840c0b00503811000c80039038007280d80380071035003000c844a4110001900b4107159105105020004000310341880d240d200c1b1409508405032106407443c003002d00359000e007800400100100070041d515a0b90b0040c20b95004c43c19006c00e10040303800680350141d0341a50360030f0020b0320341e004100301441070b9002ca501c58248910906125520711840c0034802c1207c641c4c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 231647320 1250 231646070 231646099
    0xc030507030c0506070302040810111209100507030c0e01030606050d020c1006060e030f010603081204020d060908031032030f0706050a120902090c16060207060b03070b0c0c 76
    0x600d00b2200c0c8603030200503116a42881000240603421a01800115020310750a103a04000244900c1c0c1c03003501c0c1a01d04da810214260f2601d004060010321203001030040700c8000c1780040c0303a442568030405490b207000589001d1460024031074000c10351164141071410200303101007034001d019120803c092850241e664100603004908100e50046608407081c18640007141700b41c4c0000741007079200070503000c8901040130128458242c1d1060302c00544205010000075501035041000c5036130160010341040305000c119070341c81044a40344001a107000f003010090004030450004400010a0030b02101508188580308140016200e0b0142c1c582c04001103828501c0e42d241888181040a02c030300c2507440c1030380c1d105000b400c0396015070040c1e000280b0001003109619158803421643d16006401000d103507994070540380041c4e0007442c13100c03000f10b00520071500181c45400141a01c611a0f07a001c03411007904400c0c10300e020055007103c80d15030000e002210740013200007041c1041c800c04446401000400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 231648570 1250 231647320 231647327
    0x30510141f0c0f0c05010f0203030c0a120e10050f07020a0203120d1503081309020301081509030f0c0106080705030604030c11130501090c110c10050306130603030206150a060c03050703 81
    0xb0300304002c002100c548840400e220304d0081c1da100b1070303d082e20ba1005103000e140049859101c2102c0c420b4030560148020446544250700b103072468481c0e03000c0022402100ca113a24500441013080b0218030752030b2010800146030ba040c550340c100b0640d00040c07424101a6001a4a5140030400341c0f401d07901c003103801200000c690300800003410411840c00751440c0c85e820700b60110b5105040e158840c41002e4000501000c5902c200c904960601003e0325045c080d03951014184100075200d5852448180902050b80011030001c1c042c07407280e500009141850700141c01d00303106895000c0c42c46070f00404200700110790050040d00c81564450303a1708000200703070000156904000c50a080c42c841c64640081000c040c107034030685541c0c006440c1c00c1c240c0000440c1c01030360742c1440d24060b608001124034104005010b48040c5400c00f400a004549109940300780500b29401039006500603440307441405500c0c1910b202d015080801035400400279410308a001c1c4c821900300740024200b100000c0c850052610 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 231649820 1250 231648570 231648587
    0x140306040b0a06120509120723070f0609050d0309170a050a0f03030b22021803030c061605040503060403050d02090909010e0d0c12030b010c050d030510141f 69
    0xa0080078041d22580303c020003482030405030308403c0f405240034041081e1240c0002c452016402400c1c2da01c1c03800c1c013141e1b00c6000001803241c0c01d050905c0441c0ca134040401042c80010045d01c446400c0f4040c1d180b504d280100391054542c0560301402c0081000c40100e64040082000d84900c0c0000c07020b000030800105241c00e5038580090480d004079074281c800c016524619000302d034020f90381404810025010441821203d080505000040c084c4e800c9151641c0e4001d0417020b02c400941c003483c01689004a801c0d980702c1101c0c005290000310811580d50003a0a4204c0d00c0c10091a160341000c0c1444080b964400e00680080e05202012411141c48070f283d804540f05000083c00f001d4050620100c0c00e4060304280ca4004d51601442c020601014071445c14500345036003280410707080c1c1c21140030540042581c01070040c10840c01d042100c0c0410fa00704840c0704010082e9900007102d2030041200910030a0b1a0001401c402e8080e030810481c1c2d807078000317a042c021143d8640b890001503101c41980d2b402d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 231651070 1250 231649820 231649841
    0x1f0b0702041d030708030a0501090e1b0316030c031412040509060a05120114090c0109051014040e070815060a0e0f0a1206050f060a06050c03131512020a14030604 71
    0x3000194031300804c10880090350080d00042414030041c1d0301d0344420400c0e03411a40058603e548040035542c400c00d048a24003000000180c150f03141d6860000811014081c95002640c0509500004108028a00c3d43c51016080e40b1000f500707012a410450b81c14a00c12485264803603001c142c0407800654030241490000d00b401042540d0341003022540303038040e203245414040c000041c2e80008000c40400f0908a22002c2c1c1651020000b9085c1020040f240749169612010005140f5040c20342d285124014006003914001d0b140152500070001031900d5001045040e0807101c0320411525a104c50050300d05614490130465400c0003e1b13070204141c5a0b0a101c8145d02906025000880aa8104208039034900810b010302c031507900d590001e0954102620059003002410780c0400545100382c2c0038041c41c072004000e0342c2c40c02390203080da40c1342c80302140c00c0402100d826040812101d60440300f408900f0038030800079414801c41c114060521140e41c1480c00072500008001180c558881c1d00200d284c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 231652320 1250 231651070 231651073
    0x60d1b030618231609142d060a020a060c05040b030103030e0102121602030c040902061b151501120510050609010908150f010803071104020f0702181f0b0702041d 71
    0x2072504e80030002002c522034501c84041800904041503215580301ca42d50f10003c060704124040d03100e1481114aa444003000a1510400303c004284070741e20707840144005004c41d80284008421400c140f011262260b0125007407107030402c82089040800010b49044070781500700380c600052070000503410710f41c4501786041007a1f000101503031150000c00070a40e06030b009401301ea40a0203000180021906802c0300a58000c10900a1200b1004040904084851080165104000350842c2c0c42c04000064a60030011440355000a01e29617010402044c41c00e00c840080c002c909040c88030054131b42c0740303016160244500003241000c9902400c00c2100410589040390070034940f0148401c0b0100044c0d410b00c0c00e494071140000b4125900000340c0780340c9030f004000d00e282420980c04100007948280307190800300e90b050240ea400760742d4000c0094504101c0e0891465145410740c00d444a0001c08040603900101c4400244410448013083c0d0340903503411784000075207078488032511244401001c60002075 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 231653570 1250 231652320 231652391
    0x201090c0e0901110c0312190e030a080604051e060d0f050309030d140d050406090506040c050f06070b040f08120901150e0402090a1a060d1b030618 65
    0x28240c00c00d224a1040420b14000c10041450400741600e41c4101c078003401803a44144002c120034002d9801444c0c00809062035030351001d0214001e00140d400600040d820b640000c0340c00382c69a60480e21103a4030100c1107504201c58908420b00c00c071029190700881041f210020005a050f45900c5051068140c000110056201e40d40c90266601d52003424818000d01881210301005400303a43d080d86407010042100d03080900c88a409401004000c100342c071650346541808010400c20302503a4001c1c0d014082c0700d0909420314003400f44c84205008030501131403040040c100400d0011040e10f800952004031f82200c4001e41c01d240c8101d004000e01041c07229501c000b44081c11005601002c5a5220805106d015981e01c9042c01403c1e5800c41d0301035006490710b030020307801100503441008841994294460644600b03000b10301e09802101803000d1a50b07031440c40312a540407010402d084c070701140c5000d20095007401640803040c42d1206162200c181c56001400c4d00349014070700c0342880b4100841a490 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 231654676 1106 231653570 231653579
    0x60e1017030915090307051f050c030d05010e180d122406030207170708040b1c090f030f0f0914010e0301020313050d0e01020a060c0201090c 62
    0x2180010001c1d001c042d07581502c0c1883c00301e031104800381c07100303800780034185000d020f42c2015204003000320303800e1040c82c84d560082029074418584a07403990500b4400618600a060b01c41203007030700b040c001140c00c0c0c161540302403003a111108113a103040c1c0d0701075000c1d4940791178100d480005184103103080303091401904040d0441e41e011508101d0314012244600c190183c6400140010360000303100e8041c03044032491f83e14400a001300d11407610302c940d41c844c4814811031040086074400810101c40c03000e02d40a840d58000c00344001030113040d081d498041c5c0c140c0d0582004038086807030481c8040324030344a01c964210319011501c0b80d8000d2810315110714006010094482d041007040306144925403801c0c0042c5016940c964240c4810034603a00d0020304203900121082c0421000c0054004540e0f03000942c4081c0e203410803000950a0940c00c0b08a0241226160103011104100c1001030b = true := by decide +kernel

theorem cover : BRFrame.Cov 231474820 231654676 := by
  have h0 := BRFrame.cov_init 231474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 231474820 ≤ n) (h2 : n < 231654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
