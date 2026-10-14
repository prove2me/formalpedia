-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3434
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:39:20.060365+00:00
-- url     : https://prove2.me/submissions/3e8a5668-bf66-4b64-8825-f3fc94bb4f76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 617446043 ≤ n < 617625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 617447293 1250 617446043 617446061
    0xa0e04060b04050411030c041206021201030b06090f15011407060603081201080a0206041203020a050106030b0a062315130b07060507020604021513170d1e0203040e19 73
    0x1201c940c8407480c12050205544201c14443d0a4810601c10000351001030003d4030120b4003059165054602c4c070b820460000d01c142182aa40384c4001320012041c040016420b50180c402030b03441541b0703036079a01c960348820401601e000c008681c1c401c01c00c030341035803050030390681828188900303918180007039031050101d40c0580d004684882c4081842071a8544625001e030040c806030000d41100310706a8006201d41c032540c066150040031025052007070501c20020500e10320f91000c020883d650300da00700642d1a0200310b40300c0d08054104540400d5800707104810341d900d060300c0d0782901c0c0500c0100301004006001082610385444061213030990825510a41c0f100506008081d99030f00c4e070480c1000420340300010039070402c0d0340c48801441300584840800d400c0f2008104a9030b0307102c15020200d07081a40c400d40c0b100d00702010014000400200c00300300290840314030744403182d101d40181282d142c0042411003070310140e0400c1c88104440c41d03e19607500e50102204030043d0903500c091151302d040b00c4140e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 617448543 1250 617447293 617447309
    0x10213090b030d0c12171003060c170c0901031e09030e06030405060a05181516080105031906020415020c0102160f0308071406040f03080f1003080a0e0406 68
    0xa48108224a1948036203101c114054015041403105464080d20f034000c1e8400007070002500d5060090142d12400f01d09111040c03840d11250039050030100038444005900094407003a24000b20400d0f030501070600c2d180e402444e0401000c44d83d42c0d400303907400c07070303400000704d40b410b03d9240c0031000e0b20780300640c0d034018001030410f50010314440300e4100100340303001102455000c0c480400602010a8000446690048261101081e5566840c603a0000d000c0c1040c400c012070710505641254814400d1220b42c440c0c2810090307c500103030600342c104c82c4444203100c0c0035015006010070346251b00c00303080c1c00c820b510302800380549095a40d501380455049603034a000d00682080c04030403040c3d0b905200d545140c1c024190203a81060401003031070301103d03d80c07000401c0d00b0000a020010030002503121b43e0449041826110b90b480c081c01e045588146c542ca0840c00501910001407a100406440038003945448564200c1c65003140e8502c0c1d582d50110a8076070500c50300391310308802548c480c010007000d04904 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 617449793 1250 617448543 617448577
    0xa06180b180f100f061e090e0907050112050105210c0319060f0b090a090213090602121b070f030309050d110f0609100b010504090204080d0e0603100608180102 70
    0x2c45000503040006402c10f21640c001c20504008155020343d00003421450314000c01c0c03078035000400c140c8859181d48c0c82401007820305810001c1d42000441c21008860342078840c100007581c0c8044400450b10309024043c0e00042c08540301144d22401c02c01101d200d01c440c011218041854400a4501051900c2c1c070310902d40e20021400c01c02446004a4080f107001140a00c89003400800182c0c2203400140300200300c55455020f80c042d95680b0301b000f10740e015000820003034103441c0d05245020b540800041d900900350a80402c5e0040f0440444d0380000346080340c05030406d0703510341c0c462660f0740c0f01d500150109929061204007040c01800810500c903025290024208800c0d05042d00b0444420001c050940003241007005446021811030000d2082900004032a44c0c0e480044e2a68029034006140903407000c100401e02e103c001a08030850348460329818426140f4504000b11403004517480d0342d0345d088290b000c100080c000c00c100d039000280718480021201c01c00460500b26001022141c1c191105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 617451043 1250 617449793 617449801
    0x51c0603110108090705010503100b040f0801060e16080a02120f0a0e07050102150a2706290918010c080402100c030203031b072003060a06180b180f 65
    0x2080d00e80c001805800e00b00f0103400e01d020a1401c0e00c403e2140728260500030004002544644070700c10031405845201c10040d01d850700e13031420700c04407130050281c014158608100801c80c00d4102011500c03404040c150b501111340000303400c54460340050310024940c1d80130302401109186078201c10b84118004101e00b000f030328003d040701c401d54000b0080c5008c01d41021000b44a5030341d011a918007100700290f1b039004c09442c2c2080100c02000c10100350141c3ca0910807a0001c06445041c6482e0030038010041403100300039020300c07500100c0354414045100e68600040000342c0c10b2681c0020b6000c920030711542d600040d00f400300c0d030940320201310810001e41004104402c619001107041d09142e103510b400490b60078103a601968901c00170b0036a48920a4642141e840510000210386029512006403c1d00902e400c10940304c001c55034640303501c2405050b00103a43c403c81071140008440f000000d800566003003040078001003000111f0302d5000a01e04013070b0b8443e6010b841503540103890302c440710306c0301e13143c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 617452293 1250 617451043 617451053
    0x3072a090f0507120b06160f02030f150a06061d040f05010b04050a1703071e05070f210203100905070b070c0e070203070209070f200c04111201090b01051c0603 70
    0x206610000c03044c0b403030a01001007586406040c3c0c1c161305139280c1e4920b85c140407030510600e0600b003000000e5040c402d42807022640c01c80030500c5d0b940324000c3c1250070020703100d003246601a941d085c0629800103155a540c5126220787c0d40000030a01c8005c0d1002550000d8400300406a9601b604100700b03d481c001010011400c1c502604da00800102d004c01154001c484030741c1ea05c0e441402c0c0050620b1015015886a540e4850540e110301640b00d0110b0300a140d803660b1072040b480c410311034404418142d4560340c19000200440c4069598000e000d400d0904a038000c606c01002e11501c240c40b94072601d40080713607004484005114542c05100003800481c42c22610b80c88140004044030215001807041d0b90040c3c98520044d5000076160415000c000101a03045403c0e001c1045128105418600740c48164040450b0351003401d038080e2428800014500c107680141d109100400904140020042003040020b500200b940081490000d24003200c3d102c02e282518040c081080155946c7e4074104100302e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 617453543 1250 617452293 617452307
    0x14060f15010203090607030c15050f040209061c0611040f030602040807120c0506070809030312040b1003020a1404090c0305010b130504050303040b04290f01060203072a090f0507 78
    0x40c009200861a103a05030f000300c3e056000721540141030006400c02c210801c00704800030803005454850412030303442c1204028807000800d440503030085410901183c140d041910074010800021104445200c0035580d0307140c02800740d9503032404c03035003800d01c17000c109954140c092500547c0100c80240c3c603503082610a60615001d0b5122885c2b1000120403440012017040d4031034220b0354122412030315201c1500b050007040c41030340c091b03a81c140800100e410341c06000c4011180614061741c1d0300d0416943c3c00800700010185404007941c02101ea01d010016205802c45510042d10003800100d03900c012952a4102c1580917042150a03945444107803495081102c14003480c40c8d01444107200900346504d8031030f01ca02c0003a00240500401c0d03000a002e0000042030394150011421080086071200452145d041c0070030385120364031059400000407828400408d81c0d038071b42c1c0c00c140351b0398900d510b00600903c1101341d00d040b0100303054180b100140c0c81319217114034003d1700001c81e00404d4505d00312000404003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 617454793 1250 617453543 617453581
    0x90c0c020915030604030f0302300c2b14070f02010c090b091018080304081e1504050c0303030109020406080a11041203140d020a1206080a030c14060f 66
    0x8880c100c2c02c007900c295400108142c01c035805042c0035510f00c8081c1c13003c901922454007118082c50766003c0508c101c90722100b03840c4010640650310145500c4115100b00706115800b0140380c050100052040a40d60114682010406110300003030010104810104565411295000401d0a0280c45000b540e0280600c0b0504412460052444c2e4100344207800d40d4002e2280241c003408181d03100010740d500a000600034000502c40e0000ea40b955090056072380d5000d030089002c24020300340d4074104cdaa1025a20600c2c0500d08003a042070040e80d0411a20820f0041040d0b5a91040e5564aa8103440c180015030103048088070169840b0b082040140c51054083c0141c2030692a1202e2880504d004600b920143c1720f0420340c0d010454410b00701111103a855005101d5070540000e0903450401e401d5004000420346510340b0b94007001e0042d010780480714030784501c50064010b00009030001c0d1158982d1006144224200c04914500e40716562600340b00710740401c0d080e040d000a04c841c02170b00081003c41 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 617456043 1250 617454793 617454811
    0x220305240f070503190e07181128020712030215070203160b06030703350f03043002010501031b03030905040c020c0603130605060d0807030e010504090c0c0209 70
    0x8181400c500c020b00904c8014012140d00b45071320140300c03a05d0340c0c0d60821071004400008039001c198494401c20426440040840c07560761408244440d101ca50b10141d5a209112000100081044020300440c5014081e04c1c8000c6003c0c2c4000860060304810440700442d009600411700e1400c02d426150310b14030041c200405560080c0584039282072800003c9008c240c2c0700241144036161000424909001501300401c54840c41c0e2104180e801d11b0b008000f0440d008401d803101520241028140502c2001c3d61514109000c00004012130390040d05a460340c041a81d042c004419844603078459a41c103e004040142d440b10300400600c8a040400400c0c10012010501010701d143d074050580c02d40351040ca40201c4d201e5038540d0b0518000d020312141840c0151400b507032490669070780106502c0800c4201c03445450200400c1032402d240140601d0349601c881e505142c0310254070155000c0c074030540c0007810018100000701e5101c02d0350094400e041003545540d40c11111030710401c060084000e1507844 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 617457293 1250 617456043 617456071
    0x250c0909050c1e010f2a051504030c03050711040509100b060901021b0607080403050f101107030815040c050c060f0f0430092922030524 60
    0x1043e4103850110a5200400b400c00c240300d100090303400e40358000300000d464001c4000c0b46440142d800c402459043e5544541c00b6249a005070781086840510b0542e0058001242d80ea403d400180c0100c0043c0305040c000e0344400444a50400040e0580724201c4040c3c495402076410900440100e00406079240000c40e01c1074101100d00000030b55076902c1008402c138600001e0410300403600c0341c07401c4560082d088903841d940d483d10781c18082ea880d00141030300c1f07205100315040403d00c0388081c0703d0f108100d0840308c00b951910205071400c462030784001d441c03a12103605d403000540b5103640b54800c25100050070380b9685c0d02c80780c10021390f070704007880144110201c3e0450010862441c480005807903119500c1a02410405241600940a6800248000c1c81e5a06401c03008620790303080b070100d400b1144100c151212800b140405401c980d408081a141c0d202010b001076444004010070000d104182da15428022a6403038558500c0c208140d0b50044075200f032036100d414444819503000c1c0d401407007008084 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 617458543 1250 617457293 617457319
    0x102060a1116020103060305121905030610030f1e1b0804050c0111150a0b0f0d050717010b0612010e10141c050f07050103060911250c0909050c 63
    0x1007040c415034207070741c42ca070040214440440e8040e602010185821804840c001c05480b03440342400c0e4045c001e0244c85010110b002c4140a203e84101e9214500244c84072061a403044010740c00307803210a0f0a0a012a1103410003490482da5107440340c502c5820560200e15066404000d00d21000a940c103003007006216800c100c0451800501c500307a110080c6000d988414034a0316560421103c0c880b0098900200c00078410000b120740c10288128408446500003103007440200b1809040f06d0400030802c0d000204100107505844038080350030108200007081340980d1400203101c80d13001c038002032010701041c001480036156840c0d800d0b0348100300141e600b43e21800c180315032909540041c00175124407680c0c6156904009425805000d680e031140850701c00d0713064000b00c1903c1e502c55015030350000740380c01000900c6c03013032502400c00c0000c140c9402e10300d0440c4103411900c44411441c0440040b03050319400c42c0020b80d1030b003c0c40c1c0007801101d0f00040c08804c00c0c6070140c200074032894010f102d036080802074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 617459793 1250 617458543 617458571
    0x15050c070302091b070605090d1d0904080d2c122b05040f150501440303040c05061e07020414012d030b070c030e060d09020102060a 58
    0x5401078940403103d90a642d610248019000d55440b40210f580d000089100c0301000200c0d000039000c0e0503860107440c44010640030880b858401d1004201d52010500c00f1030f00076040183d102c580003401a21a18941010005002c00b610707807040401603a042c1c585000e0740e01047c2c4203500030300445c000c4080e1501d6041881600c10f5030185044042800c10200000f421411251902400e0406a010148100d00e4141012074080c2d400300c0003a5502550484004941c0e6418070405050310108400102d01d0722500340c06110500540c9815408031041a40d1650720711300700108050360510321402190390b8030341860704111400c19640198042c0d10144120f41f2080c228507203001c000900c48422903204c5a2034000075010704007120b280d0400710781c040004030b0141ea000c101b107210100546201d5600d03a81c11046404400300038440540700440000c0400c454920622030320800d20300914103144c1c0200d007140040d6850b40801309242d403050f62230304a8011560113000e480c1d84813003001d5003002200e41d201c0b00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 617461043 1250 617459793 617459803
    0xe0d150c12060509040305120c04050a230103050103051b0319050a0201020f01140109051509012907020607060518010c05210708150a080105041b050919020d09050d020715050c 77
    0x40001088d240400051600b0491001d8038000e01c00240840030466460064200d0300140440400130440c000b2200741055005e8000c05040b039903c0b07001401e448403110f1101d5100320240705c01365858006c41c039251804803191001e12140c58003031409020410224800640b0b80444503070380101da6410074481c0c0c480309444100050454015190100e4142d4503810b00c0001d050341079640c241e101d088480040ba45503080c0c1981012400c03521040003250045e0f070807401180c00b031424001c2d407001d003c0222400280b015003203150040016510b2010401c402c0b035505095404481d074001c0020000b140302d14540a411b40e1800b004801e9800c3d0701090b04064000038030a010043c04a41c400514026400058907401d00325401003440e04000c008a0900e8500200c09041e81c1820003003507132080c6c034049180d00c0e0a800d000d00034851101144001c100100846003e90440101504415a1003011401055040c000384c038004203e0340c082c1880e01c2c24222101720f10008641c500041000c2401284d10715000060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 617462293 1250 617461043 617461057
    0x1061d04060504020a0503030a170108010b061602040b03120a0818060f0c13062102031041010914060d020d0b04020a020a0b160e0d150c12060509040305 67
    0x5002c038042d0358034004510100401c0e81b149415110000c0e02000450380074181b26210b5401c40701c0c90714580d0781c42c0d07104c0742a5000c103030310709034040010458104880b2002c1030802140b0301c09400440e902c802100028106180400d0900c845c0b180095042c5180d1b80c4100902e61003010b0403100c1c038102c40c2407184550f42e480b0051000051002d100042500606480d0680740b0010700a0004a121525000014560707032070f00040e005011104510302c00d000c0c4050090b6446100e041c014400c40c0c92501c0d000c000701401d0004d00c00c03d002008440412986d4058161604400c03924860140c1c100c80c0030001004110f00f9880440750362240c044440d00d070340e680c504603442204440307005a10b40340046070302002070558185559115100103000459180c001c07410307d440d1801115007500135601c11024402c185450f5081c00c0000e0032040072101c0b640390030320114840302d024020340c05861605964400807502c4209014012420881503081141103600464010305030a9a20fa07519050030b550141180c06044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 617463543 1250 617462293 617462303
    0x5031b0711010503090a0b07210903020d05160804060c11041401120201180e09240a090311063102060307030e0a150203010e01050f010f050a030209041b0201061d04 72
    0x800f1843c60175040041d01c0c0e00c41e4000307155241da404c01d00005001e200d00b240034014032110400315003080c2807441c465192103640540103403800b100011412101540519545c143c100c04080c20030b0041016080908040c11040e126610701c0102c60030100144002c4290741803040307040c000880d002421011300141100c112000542180e030304d920040e240700007048900381c525640c500c0c0024815400ca0303200f0340103180788400c1d580c50214a040d03442d85482a2840b081803035180c00b0100c3c03d0b5000c02e5000d8a4418086c2c03a00703403814144c0c078048030308142e01501c0700a05216102005201d408038840c1c2c800a5101000394021108081c0c1e0100d49603010040003401131503501c07246084400002d00440c00d140c0d030300c26a00300e100200310b54208020b400c2030040c0b03c0e100342801c0003c40c090601100d28581001c2c1610340c61031034608024100d541c0d03440001c0030010940c092000c9455502e56000710464681c020302002c500300a0843c0007400c590341c550248020703c1000e2040483c4804224540d5001134000f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 617464793 1250 617463543 617463547
    0xc040e090115080d121a06030a0b0f030604170307140a0201061401020321040c0f080604030e0a21150e0f1606080a0b0103091403030f010503060c0d051506040605031b07110105 77
    0x1186094440080710f011145c00000010070085049c24941c0910440c01d01100c0807550341c440c4005140e50b85404607801018010880c5803400d244e10004051035014180307151868188040303401c9034500f90003240700e680150791181c4003030001807030901c2c044414000a20046040c14520200180c03a0900380d00d03c412501c1c101d0000c1414855128060005482052241e05243d691420501e5079000100c0d016400600318843c088400d01d01903055200f111100f5401301d201c008840085490010662400c5500c1d204c10010912211101e0061200c1300d002400906280e040c405071060400f0000861007213180c800d5a0306008a40c0c01c050060703005000c807600012440c0790f06005800030842100080c1c40c964028040d00c001140000045200312541550248180da0310020b1503a1030344140d42a42c1b000c1d1081c40240041a855440582d2041d0b00411400e04510504041a8590301c02e03044000003500000c1041518400a8280728581e40b501c094140b4041d41912640f0721150400c440904000c40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 617466043 1250 617464793 617464811
    0x9100905010b060f0d0e01020301060e040e01090210091d06030601150c02090c09210d050a091d0123030a0809041515120908120c040e090115080d12 65
    0x30950141200030005080c2e10750fa280d54503001d41c156008a004040d01d80d00f030250542c5480018000d03039040300c200f91034000c1c0994007141000003802400b0403e9895650302c031005c0c5e003d6070f5019104003481e107513901c41c03120440c1084803d06d07961804c4c40314444205040428880651000190107044400050310030000301800b400c203d40c2061104e5000c1d500911140034443d000c0e0b0420002c2a003071a00f211880400c01c45000c8803100c516058152420325000f2180b81c41e6664001c10090030851403e15100031200d031100788042c154120306038080c400c0c82d81c40c0010f00030240300d0300c850b0507020300c860100401d824031140020f079181da00301c4c801001071101143e0010b944c0c60307039081850007845a9081c482012344690681d8200f14280d40b1a40000700c40c0d01030803040300000c0c071699211640044602d841d149000d50b1001300885d015041176400c4900b088001804041254030f140a11340c10400401c54065120440c81e601442e41c11104d195080300c3e50100b24660040100c689614124002285203a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 617467293 1250 617466043 617466053
    0x30f03050f0409060905060f0d030801140604170114070804081603360f0b0d020a090816030c0f050907030c11011820100e0f0406140f09091009 63
    0x2568812420300b81081360100781c3c801d00d0742103584170343c4040d82c0d01e06480c031000c420002c94400b1a01b001d80071039001c80040c010a040a20f803031054980c0a80320b180761681d144a81e1001c0403403115800000d9564072000444046d1091036684c010a10746000409414203480d106d5880c42000034000042e0080e1800004140c095041501d150f4455851159418480a501e20342c0121030394461024030a103040100b8140f1100e400d100070303542e86840b0582481a10303000b05000754071241c6002c003032144915000400200400000b45810003002600351020301d98542441282c2c0c864001e401105d5402c14140610780b10415029804051071501113454080c3d9001a0740003c1c4042d2181c550354201078000e80b013100b8020026881501c1007941c6212804155455140300e1400459a81d200349a40c103000605072007040605450035005024854644004000400721b500c03a6000030a17041102400000d949805002004074840076280404c107850282e881c1074841c0705218143c0c0c0859910000101444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 617468543 1250 617467293 617467297
    0x11205100e130b091b0f151b0f03040501080a02031008100c0210050702070308130e10060e030f101a060403050f070f0e0c030627091501030f03050f 65
    0xc01c00c00420245414000d440150501c0060001e41e4440501004210100c0340041d00340c00d1100e1451080e001803160404002c1e03442c0e000120340c1d03400301512480b0042641004e0040402500b400c1030210b0460301c0b00c1c074450800c642a03030802400c1c1c05c1403104003c00d0342c02c1134407950f000401545c010b03626a2900c403100902c0d581c54000511500c00c030240c0701400e092a500a5001e11025021101140150341003c41a40c008036000001600800000c000080d9400e0117000d00d0140914540780807a10f4040b120741038001256801000c00320031a007005036540100b00f50b010f01e501500503080d0301032240441c80da2401c2d0a861000350030b64a00080340c02500082d8508900c0b01c0080040381c0c1c65942e401c0c20303555142d4004000c00c0038021041c0000d0b0f2140d44a40311411a80f42404c42d5021380c2e501040e003042500020106904017858140304c1d0803500c0e90080d000340c07620317801c82c0070285400c03c940c0c0389140c000403071441c3c0c000302c029400500110344070012071800c09515103089130f03451024914100c258 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 617469793 1250 617468543 617468549
    0x2030106080a0906180501020d06080106080d0c08120c070c0509040f24110a0207240503060607022101060603150b310311010302072f03030d090605090c01120510 71
    0x814107040c8171410000190014408500c840405214941c1c84406040c01c0700c519208103085a40101854a001d074020840002040d002d4901c3c2420041410700c1c03002000011140600801d07000560344003004001510716018143c00d880041a074500350b9250940103035982805040c0070a10b41e0b03d4418062114080120038a003074405025650007417a14101c2034200421000250246010208203c490301400310b19242d000d600085551040d02c00a481d5a417010703040540100c0200551005a100c1f110040c512041503100f007040c822890600c07500310f030f07000e0300702c3d40c2054101201020519140c14171901a612459440c540d42e0303800c0c552241001c00300748140881102030101c00e004120286156404882c00780c40000e40321900c0302c00442c2203101d49100100042207501d0f40c42c400032541030030039403484240e01c0f01c0700a120404c2d001a24581001c0c2d6a8080b094560410100b001014018503800c01075840080044c04d81031000605007207a003540b40c3d402c15175940000381c044007910001d0303401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 617471043 1250 617469793 617469821
    0x1180b040f080d02010c02060c090a1a131a090402030c04120503030f0702280c03151e090c0510090b0406050405011b0203210408060c04031502030106080a0906 70
    0x915039480d01e5055011a642c45a15150b016140c01e5440c454010301030003011510355400342c0a01da0b502d4000e00010340100c480d40e500031007030140105410007c040100314044122400546030300f0135080040d02c80c0d503260400524911921500b0242112080907074291240031500940c490351030400d1124240039560024101070b004541640a111020004600860742d040c50300602d543c50381d0060b40e8030221050b030504034003c1d181281c0b43c18044501c00702d030310521a140c24011981d90361580d8400500b98090f1400c400e503529001e000241810520400381c49240c5014000c61810342c0350540f05440d54460b00d80604180307151450f03a14815514100901a1031850944a40d22104d009000360058001c0e68042504400041d9040d0b186921002c00603034000c0c0204200a180c1c40360300b820980b043d804001140040c040810022002d002c224816408052480c0c4c40d603103103007040d201c01c11140309c071094028410001031014551010348103a00004400010402000600e4042c1c01041c0404802c84 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 617472293 1250 617471043 617471047
    0x402030a0219020607140714060a240509010e090a0c0e060f0405060d021309140f0d081b0f0c010903030c0806060408100e0a0f05030919050306040201180b 68
    0x100e00c40399640540a80110b2414207440700010041c180c0e43d900081e0303603a40200341c002100001d1007078644c00038409948200c2c00313002101903c081807460170303005032002e007801900e80c000c0407903076080e402d100a1194401550700b00210b142c0b401107070300c008040c042c041a40030304000082d5035607000c0204100407984826031481050350341c62044110007068800d1807081c15201c1700003800b8235003401040d00816004010242c0000c482c1d003004520045190f4110b0000d0300c5242e4900801c54038201c0070380d4032404d10064140780a21030b500c0d03824243c8850107201408031741803c0c054003030001030004050416521080f03540310808230b16034915000700909406150700380210f0704101581038029440000d802e0302e40d007a95440e40000c0142900a0303014a09250f070000040140c85046600300390803002d002c00683d242902c954950241c41d0000b6071041d0390703680c00050044003900740907203a0140d43d085060711031003a46c03c2c10b0000c1e8403800050f0019041140340c030001c3d001c11900d0441c000c020280044129 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 617473543 1250 617472293 617472301
    0x31707090305010c260921070204140705030a090302120d0e0c100518040e0a03020f1203060f09070909060609090e0106050d1502090a1706360309040203 67
    0x400303580c2103000c1240c1550811090910303040c0101c240e00300646031141040720340e502d003a400ca101c000c03004294541501c25400007500980f000c1c00484070080204100f04d80d0b95200380140402e0350508c2c004122815040420450303040d07442400d49800c0486c3e0000402d481030f00703060407460200d154545424280b03001820b20384c0c0715020f500000c0030a03402c2041c0e58034070440504100b0440107015484000c10301c1000001b124000c40240d00c0821800204005142403550808914003142071204a000d64000403100140207400c0110092041d0b1840e02c1518524002c00031134070a4160141c4c0b04d001e05201c00104065901402030000604007980007003141c2e41c1c0e9244028406205c81c45444800c0780b41101549182c4010b00034802900c0300a0030701e00500669695403182204811002103c0b25030034001c100c19507035102c4030800108401d010240300080c0007050503052040c00742c09290780d506065107083d414030404140c09060030680202c4c007042ca201c122910308521038881c100380e2040c8008100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 617474793 1250 617473543 617473547
    0xc0703020c0f0622032003160312031d070801090213060b04060e030309040c020c0f0405041a04050709060801140108030a0806012f0319090e01140d021305151813031707 74
    0x403808006c412011580f403100c0000301c00203104240d002c00b80840c0b28011074404002d0194003c001c0d5022101c8400031001d4041d40124205076264000000903519142240305516010581c0b1041646100d010480c145ca0a07503d8005886140304100910400e601080080e85d424016100301c0e2102603c01d02400e442208000e45589001002c28400c900b0036140f010142072a00c102e0744610b03401583e80c0c041e40380002020091380d2000700112454460010049031058a0b0f014402c0106001c0c1700205988030341a0109041c2c06058002e0340c4198814007180e10803d511601d200d0300700c0420301b0910b034122541c24030903d04c0c0d611000100c40032442c040760745080403400001410b80040002d010040c03946a21070443e8080d40c1841090092074000c401807011340840d518a81020f10020a040308a42d403982c0401c0240006003103c0c01d803640d41d5802c00607000c0e840880220380243c11603261064070010645403800c464050b041c2c000ca200e0b910203101c10107010343c03584603071129041c0400100d89444800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 617476043 1250 617474793 617474843
    0xf092114071a0702090114030a12080a060501030207030e1504051e09060d02010837090c0806070c0809210d02151005100210050c0703020c0f062203 65
    0x41082242c00120440061015002a030b11215801082210584d1a1a2032010818a50403007175525009003004600003030f07913100540005846540303034441c0514201e1039040458500e54001814140104400d0b0000b070b500c10241902060704490308041e4841c424911a02e40c003a0360070260f08960005068500000c0407001d0888140b01200c00810303613559801032104000030321000a02040107a40450581c101c030f80007a450b07000d0314040c102000d0710740016060414050b0b10401c11403d07690ba0705c15050001e8002c0781005080004028282410081c100800364445c0750070217403030780902050b102c510b40c2d01c0e0481d03400c155541441c040703613100078a09002d8540c8106d444c98001340c41000c4a04040040c011100c038400e02003a8000c003c00ba241c0820b00501f10100e0000b01c0841c01120058680c0e020203200350b0740aa00408045070b100c046500c4e021740f428605e401403900c03800341451101d0882d55810120340026071880111610a803007403030095081b480c00e400c0101034805902d440c18140312a007407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 617477293 1250 617476043 617476049
    0x16030b060406031505120c09070201020708070b011d070503060d020d020a03081c06050a031104092312030c04032405040b1b0313031d031903020c010f09211407 70
    0x80c07406640d40c0d0781c00700901d0383e0721450010707447d4214845080843c0313440700b051a4401c1090002602d840b0b031035528000c069200d01d604a0b2900c06001c01800304840e01ca0280c032070800d0785030404a09081c034040141ca180801885540b0070b041d501d10f14002c64035240b5400485c281c1c080c0c0f454100e1130726403030500b080750001c006440c400d00c424600054512014041e43d01154009003140c1481d5040d602c034031f000c48011400007900326840b642d0000c001100a4020f841481420000190f810035003034485050000f400e048544404c024018030544281480444085036030040040c2c1e4041001e201e140d00c040c0009000d86070b490714010401c814016040355003485083d000103082560b007110790491529001c16034690034903100d04201c000019011340301c0b00003131024a07410b0002e012000c030000b07450309509540310103140d001c0020032410150100701940b0549002d08044004103480c0c00c008060903294800c01440000600c0080040120011080c3d032660b00404580885a03a400b581e5644400c188 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 617478543 1250 617477293 617477321
    0x61e060e1b04060503010e0a0615020c04110702010914010c12030b1f020d0809030d0606030f050703050f1311060f0a080c090f0904051c020a0506010602031216030b06040603 76
    0xc511401d500d14102180c042d030300f8a4072134508690810400b81d00c11a401400100421f94402d004190f1000300040c0c092403c0c2a07034010840c407440710040c00706680b0f0200c6a100d100c4428050000141e07002442c00d0103541550003640d0400300d12000488403482028400f03091070309003120b0700c03061980c950440082d08900360383d10605441c10341070300d0b102e07001d08540b00801070b04800d000305078003440350130070b03e40200d11041203904150b46647d040e0200d80c1c09510010210707545103800511100d180c0a2181e1003040c5040410052034842c03408000084002c119a180c07003140403401c42006409260300361001c030702508031a242c00c070b03e441c18602588400000c4010500100c000342030342c0e8048003162201c440140c02d140e15140c002050000c240340c05041156039025600c2e10700c1040c1e5455080710f0485002da402003d110100d8144141018130603003003007003150010014092242c210061507074100d000044881c0d020307060088200d0003405802003203648440005400680c6a50541040a00c1500b0b2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 617479793 1250 617478543 617478571
    0x8071a0c040e0f100b04140a0b0903070303080a0f0908030a050907061e050c03160b0906040f150e0a03120e0115060302030c070f061d01050f0103061e060e 68
    0x24110085500692180100c1e500403140060210f140c151586134002d251440c1004c0e495031540d66030311080c0c00680005d07aa485c4800325000c0c407850b0030f2203070100030320425003494a802d030b0300000319407900034030300025090102c02d00101d0300c10440d56100b02217045046500304200001071902501c107500030f807007012502e8240300110324580b2021418030700721901074561031644802036400a445010300385006044c42014000300320649000e20040c40b46003030a600510520501e80780400c0412030190024001da8049001c0000113203000c554082121741150305861301401d40440d48002d05529003001c0007501815092004041d0004001e06040c0d91030103090001c2c45118841500301c48a5100c1314001500104e802c000e00c07030280d0f00540c0c20450981e071040ca44145a1100d08002800d08411245181e5a040c0000a4911601b00c1e81198010308028040c034107001282c04820706041c0000780c0900c0e555a24148845c01d5008000c103c8180c202c01444056641c85890722105003c440e004101e08031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 617481043 1250 617479793 617479801
    0x2607060509010203100323030f07050106150e0919090b0601030507030c020307170c030f130e0103020d14010b03010f061502030a050d0b0406091118011803060207020d08071a 76
    0x2043c003e40744141070040701100201d00d5a2079101000301e9181030340007000028a502e0b9280e00092004003848140c555000b0b54452007803030681d0845004e544581208030a00e80001404d662211441454031000c03641c10400f0b495122481403401602100c886403140350080700000c0051240c042486000d00340c800f0445039030340001c140c094428040b07100c40140c004004040000d20100681c082090b0040c0348142405204080545580d01c9682c0130051303e000803950045240000760200050200000c410046524544c00708240480c3e411004145d090242100303481c0075001d500c0500ca859000b4002d2003401003002824000340814003c02c0e0220301c0424030101c80754000011102c020302d1503540c040c0307070005d1040c400000b49802031750194440d8844400180c0421140074a00011000030302965489403903a080000e00000d10408905000b0014000304803907504640c1801107a820041c050f80d114071500c0000c080980341c10009080940108106050100501c50070241500055895925840d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 617482293 1250 617481043 617481061
    0x2040f090914061e04050316030504031202070e0105010e031c0306031103011a010f02010908031014030c060915070804090203010302151207110c040c0f09060318080726070605 77
    0x444030345a0004010121003080c40e003103a804c0d9441401001940d04000396000310400740103c11031301307400086000c0b42c18000d1081c45403128513400010300092401ca46002100342901c2e00521803141480344040d0112301d59101031109100030f003401c1c403190100f00908480540180003038017090b03c902c00740034030309505820305101d151412540520030a040c4030b180ea004403040d58400101000315500c4004140005000e0b9000c3c601911000071202c4401e802d19206001e0018140003a5100c0d41c810800015182c41e40d4089804121050b186074001410401190f036861081f035000501080c0001070006941d18a98044c40c1070300c0c801c544924085103a41c84100143c021440d07502c3c3c00c000d0f034202084040e40188580b500c00039854040e203241c0340b41640040c089610b80d0035840041554810910000c90f80199080080c00704c43c2420407020404c410f80020011981c003000f0100100042d40d4014080309150401d184109650081c60040e08407021001507008007900300d90342c40c141404141841 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 617483543 1250 617482293 617482303
    0x70e04020a09111204080d0e01150e15090a0c02010605100516031e12111303081308250b0c2109041a03121e09030102040f090914 57
    0x64004001c4011142041500001459615102000c41504110601d0720b83c0c0321103051440b0300d008040c040e49400c0e403000046c0940703850000c06442645403410580d213030521b80c00080e0640300c611813003070240e50300d8015541450110103030b295845072440c02000440c90700c64112201030b411560080c0300f2036031b039401030000120205080601252052101c2c2d01c06561121590304100d01038a00780c0e00521007414814a0340d4030a041e0f44000403c00c8003071318400d80c09030103840c0301c620b400d201c40c5140030207080800c401c014050000600b003c00000c5c40f0024880c000d1030300c1010b468400c06844541401da007580380401e4201000d4031310000d1203100001d00400141c10380b0715180c0c025000d8505110b00e107030b68010444d2181070740e0500010a0102c6031a81c1c440b48107001c2d00d1070503108400761a5511500b014a8032580e0f41d02c011101d50108045134008244401d190210704102d810583c981040d0380029019000d250000c0d1500300c0c0d51a000501c2c01e1040d041105450f000314411204404d004001c2c03519a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 617484793 1250 617483543 617483551
    0x210141f0b0a0e0d02040c080f0c04080a06150503070611012405040c170c0408010b030616080430081501020705100507080a0f020d0207080a021002010f0e0f070e 71
    0x85400344100300e640350140b021550f00c01e4006081c204100013542c00103040341e010448181c00a48203400b005414844680e026401080300621103050038034090788a6522502044001c2403944c907040d00c01442c584148061000c1c25005054456240c3c0303070100200074101e00d0400301c0b4907600b41488000c0340240d88a0984603100740490f51000f4500f4502440090240c00c0d1080c0100005441221045000f481c6024024500403121a035540d290290b21402d4585601145101e50040c84c18060403541c640c1500054a04a06208803195901d040c5141000d00070303400e0320340c0011400401d04202a80d071210303008802050705e450200da21805810214055200c0c1d2540c050b91102c0402d210914104141d03441000b051324005240c03100c15036440b44140c0007100c140c00410540070400c2c8643c0c1d01800b01c400302000c60310051501d540b50109195542071a404041c0c020440641e080b40e855200390070405d4084140c0200b032001d10300c0070106035a1040f080c0004d4400d809540742c0400d100d1100c004843c0a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 617486043 1250 617484793 617484809
    0xa020a0209010e011202010503182505090c070210021009050309010f0c02150c0c060403050303010918050d0509042304030206070207060e04020306010e150702040b0a080a0b070210141f 81
    0x307505c1d4168015111507001400b00c41010445040b459001078041040c070345e040300400c03c41211808610b04402d00030009410031b034481d45d15503080102c0c00160405480e606501140c40200301d10b4101001d07030401800001c624080d504048030a0f0034001c0000003031400b060702780d0300c209031031a41d80000c640b0001110350095209914181c41082c00720404080c04c00506840113031800c0d51071100008034542c0c0a0b031310480f2250030100040040301d10a00c030b00d49a5200d0501c92000700c02d90b60303441c2da03100c10300111880306015000c20405444e4585034400d90342d080250074640c0381514051042c041d40e6100b00c8040740144981700000f48614804101001155219211000100800710400c000b07900300815030381c100100c1c0f07010010036590b00f00000224200c28901599520928014041a10140a8002c3c0500082441003068010001d103c44c80c01d0b40009020200352142c0804074206411030362100d41960804442d24184205c101c001402042403050790304890001880d40c03a00c0c0d040a10403046 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 617487293 1250 617486043 617486069
    0xb06060c06070305091903090f0b040f030312060b0d0b10030b0d26070b0a050a020702060301060818030d0608060610090506220924030b0a0915020a020a0209010e01 72
    0x40030b0190f003140e1780056a80d0196054400340701400d0304405220030050300000c0c10800204151406252100e002d0116000d68a243c18181000001c0580ae20b2000030104011001492811990ba60000000e488a001c0c0c0c1d6a86100b040394030f801510071580440d205044802002403914000e11070070040c02d001500823410741040d034844813a0980c40440360900b9480382100320711407490880042000c0340c80b440103d00345042c49400101100c03c010301241a0503c1044041c016a840e103007a28115100c6160060040c1c1e203002c6000c5003000004400c00c1a4440490502c1c3c1740079042d00300d4410b950003041182c5e4241d07190410440c500d603409111360089402988140010700f006402011220303061070b8014111400c050080c055400158805001d00e80c1da26a51514039403298034030714128003540300c4410303881d0458070b412400340300c00750684010030b546821070010400c04201440612030114821510740942860103516000d2003c000c0303128201481c008a201403d941800341640c0810003485 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 617488543 1250 617487293 617487301
    0x3090215090d02030124080a020d110f030f0303150a0f0902070f0506070e0114031501111e0d110a051b2e0f110a0213060b160b06060c06 60
    0x16038495044650468403000408003d80c81c00d0203180b0340d006c21a04950320415003c289042d20550b03c2e004140c00d03422401c0941c000d80d50300e50040d4655500a8815000c0380c2c605400541801c2018207000c0d01801115816107031208040051849880c0d03404407400200c0c0f9230020080045614010301c00e80c1d022204091005141660140c805c084c413407106247c0d0f0866a460341072a00c1811a042c0c8001408036003c1406541e002000e41140e8699030203c0341141003d2140c9440c03001e503119401c0c10010003415240d42c0034020405c0d0010300344084041080301035040b800b1612807101d802101d000c1142d800d16000c82e0400006c4030105580c009025280e05540c985000805141d42c00f40705a003d6494205480400100300703951150b5001c0c0714609444d020b03481e101505c041d03c4071030900203103e580001351041700004607000c400b803a0b0407580b1409042e4118a600000c1c5a1604140700c0701d08003052803030350f02d2400000c1c0c030505405491900c030b16545040070818144030390070011b50f60790861004a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 617489793 1250 617488543 617488579
    0x50705040f031203091a1b16030809031903140601110601090c17010b0910110d141e030406061e0308090a0305032a06010b07240203042001030902 64
    0x3c02c070082064034010170300c0d45040d15203440c0340c0780a4010140488090040c05041d402004030940413101c03242d146401d00060b208041d1411456900c00382c00c0c0412240021031103c018030403603269855040d203001ca500103d000081c01440007200700c24883c2d030300c0c5010030140d6024120400311034010500502c1e01b81c3c24032000d0750182083e607200d04d090120740940d004c1620503804001e80a8a5900312060701e0300300307a10400c012041492040d4040c8030200b002c0d00310202012401c0703104400386007060a441c01000714581c13114401c1d01e10b10301401d118561884091401d5400031401240104070512525480e051500c1243c52480b40f680d0b03071145500400c1002600007800780103c030340002e200011860396911040d04541c13020701c1c11800c0382e16078540300060041c00164018100302d000700600b031315030615404103524486d50340c02500800503180d140c406285140c1d0490603580c0c8101d03080d903c0c1c0c00e20386440b074440045680c072081b95280540342c1000b036500c03030f1003000c24680d0000d081c4015a00c517100d81c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 617491043 1250 617489793 617489813
    0xe0d03050c19050d0b1f030b040e0705010c1e141203010b180d051006050a1d070e0a12030806040f1a040c05160c0317190e041d0f01050705040f03 64
    0x2c64000d41c640c407202c4140d0fa51800d40d04481b511450300b072032000f500703140000c041780c11490215100740c1c0703042d0001c959142c000445406a50080c24034034044002400e00d41000c1c0000d400c0300c9050722600c0000c00c100042c5074a454103643c01070040342c1007804000c403c4c500d640000d000c3c00001c00350900c06a203071400d280c2901005464040e0107645c84090588410341409125610141820703141c00c070800841c00c00c1c090910061a07440300780201e6880c802566041b8602c0038001c0c004015003c40e41da0120b0751400c098400410007010000102415482c02414041040f18001d03c102c0c600b21500455924500a19106009070440c0308074046008041000420795411207004100c01840781b81c001003074504c01c49800c1e80c06140417186032483c520f480740486d4807a6040170320b145028000c2e03040507849031201b8154041c407410b00344103800160001c0707401840e500240c070b0980189800014249a80459200c80406d280002030000d5a1402015a410720071807041c115840031048041010407500c041c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 617492293 1250 617491043 617491057
    0xb0c07121b06150e092415060a0306052d0f010e060a02060603010f09032f150612030f0403060b1f1805040c021e070b031014090c0d09020102100e0d03050c1905 70
    0x440342d640003011f680400e545410081c60840840d030780702070601c4186001d110040503100182d809c611100d25981010304002650b003c0f25001e26483e080c0c00303580768081d0f6405d814081025242948610808800a55a000c10340e01c2d0f138042c2d4609020060100e00c107000312600300f82c240e01d521450388840381c1c08841507040040180c0241500320381c040c0f010131041c4840c004c1070114101d000ba007810a141003000e04c20003001d4600710fa600c00c204c40486a07201d0000d031402c807500150b000406940041c041001d0300744850505100c4015112a10f10480e0850180b4549a60140e00542c0d01900e402c00e020449401c5045000984c0c0102c00726500c0c4040d0904c0906140385802c162407801d80c1c1c44c06441c4440e08150340c0810380e131000b10424000c40691441c011003400c1c2c01c035039482860402e02c609220f00d02c0364481c80c09406840d0342d0b0a200703590003003062041c650340300801000f0302c0c0d0702244140d03110f01c00e2202c01000281010007103120140c00e5415180350301014104110030385411001a582580404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 617493543 1250 617492293 617492311
    0xc0d1e0c2301150f080c0d2103020705121b0c06030a0b0406150906020f0105071b022814010903020f090603280b0c07121b06150e0924 59
    0x380742c180c3e40c542c82c200d44a009120a400c0001d020342060350313540c100811102a180a08408000c00d030219010140005034011042e41807503003100b00300e100b20040e01c6842d40290940c400d203820000e601a80d00002c01c11003580d028003560700440d900d86144c46040e030003006540200e0038070100c0c4c007203a00d179406003000070350040000440c140e5440c280304142600c2ca030464081030050608101240e0184131030b02d02080070000800c40d501d490800a054042c029003800c10a600c00c4440c4403c5494002042c2d62010300ca80071642c0b05c0e281000586c08448140c0141006003408a010302001c0d4000c0b00351000741d0354000c0810300030607601c10502c404c0c017400421455052180d24076607038001c280c01c0944012445010320030b4160f01c0c00c038101018003400c0608446d08070f000411000c4e0200b110804c4000c4d00c8515454150588026200034460b04030010f40c01400d80e034644101c50840100c180d200404550003040184240c0c0d850350b01803920b03510403d42e000415a0f400e03210380319030511a440258002048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 617494793 1250 617493543 617493551
    0x140f04050114090904060b2202090414071b0f0b0a0e01060f030302060a050a1811180105130e0106090608071401080105061c0626010501080d0504090b04020c0d1e0c2301 74
    0x87c0c1c10f00b23a00c44d014100c0541c01713582d00007226096070038203008000b080d6040e14018019030610f440003e0141900a180c40c0362118480600003c201140901010403900190340044905080314401c0c000c215852241c502c5620f40480060109503000c10035040340c2c0c240d0041d01d03a0f551400e520f41e010b00b4000340030401c101d1b5540d448800551507414000076090064200c0003240781c80c00140551020b99014100c4c88004060040146503580a036a2440b03c580c0b68000c5000311000c9080f5015081e25040000c80b1814880086000b00d000201c0000300d43e492a50008500344000040d280e041007030141a400000c108400b00d0f003c00c0c80380b050782164001100005441c0c1c0c1d2082000b503240c050031021003078030f42001c0f0f020020442c24003505003d0004400509081c4200b01c4019059101300c0c031400c041191206800c052a03591340c0c0c162511201c540080d650407800c400c1d401000d088261110420303003e900807007680f44901c200a0308520b1580305044814a00029441c105881070011082e4055034039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 617496043 1250 617494793 617494819
    0x320010f02070b0c10151d01050904020d060e07060509030105010e09030f0c07080d0e03010f0c0813050106051003050f010b04030309032a171011041203140f04050114090904060b 78
    0x50707102d11b403514043c18112210960420140c411071906080c090f07a5000c2d58500140016651202115046179048440010041c407070710703250300070785240819130009003da00c40016045401000402c0c0e1100220000c0200baa01e802040340c000070160b80b205070a038410700945000141c1d0400900002410f24100c0d0360b40fa0307460041c5441d0618103200000022410041001503040074010035410301e20641d0f05200c551015003005002001c01400c8403044400d50040509120342035004170302409014100c200b4620b50b0043c0500a818203860180b120003541c4000030f1156200301c2982c06403945940c5100e0b2280c034640b10524090b181c1860700540040d006a0f4074850480489800018a4000c4c038403030560350780e50029820080015410382409040c06030000041444604035025600d07010810000c1440e01c0c10221114032038079510f80000c1d80300240348000c0380008030142040301c600341c2e150f0401425012600056000f11203549400c5041040803400042654010900c140005019040d2801c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 617497293 1250 617496043 617496073
    0x20c190b162012190204020310170102090910080a170c1e070906060c060f060305030703020705040518030318100c03020316110607110111040320010f02070b0c 70
    0x550400c0961402c12640d441c4461420822145070070308140e000a0442113402c80e0f05041c3c0842500e02c002d108aa0000000380c0480303442e00b103030010b4840c0d08400b12060203404078290003135020500d41f61141511100060499050308842010744515070041c0150004559441c0710f103060904105000030810b20a000510000f013117100184400c405180c6100100050102d06124030f50304010011420300400340030442d00419403088041d40b0080c0001c2544607407040350001c1400e60002800ba00002540e03409050340040c10a06030f07481110108a02d8880f403d60019101d0154950540b0b90130500c0003c1c0c00c0446a125102d8458155080c0d4840d080c24140240481d002c0035500d00200741d02005000010004000b10580d00c080c60030301140040d1000c842c6030b0380b82c000030002d00822150000d441900c1c2c00079006003000109460080d5120b0703840c0e14101006102401880b2850445c2002264280d845681019103c0d0040d40180c01e03024200346c0c41071200d60080c40381c54550b101d404207072146c2c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 617498543 1250 617497293 617497313
    0x90203070e041109040509030c031b010e061e09070509060d0c05060a0306031b060e0d2a0303030b09060603160537020f121b0f0c01020c190b16 63
    0xc000807060039504c42c0010200011902c0150020406a00610100f6500e4200104a62248000f20b0108500c501c603034203003d000d01349620702981540201c10910520f1007000c205028103034003407a40c0081c15030b21501c045644049a2003100e6125074910082582400c042e005c8d424070746d005001840700c0079120070200d0201e82c4039915210020b0794858080090001c1001511010031a91606011040c60b180f8001c00703c0c859107080f148a04507542c0c1c00e404200310042c005840600b403444d8410303184a028240f08070500701d440240c0201e4284001e90719a4030788107194501c21000140780c02c0c11602ca03005007106140e001100c55007440313810410320380c120400088541c50300e41d945400d07102104081c52984032514140300024155440405c00a07503a9101084541c1103c44000c240e031b480300180414107202c2540780c0d4080b01c1d11b00030403100c1030a01e40c1c0441c0036150281c007a02212142c0700c1003014000107503085481403c5038144640c0c2484041c040d04010084111908141c1c0038550050721811044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 617499793 1250 617498543 617498561
    0x50f010b0f0d091b0504060e0606250c1404051e060301020702180a0632060d14010509480301080607020606090f1b0408010212061206060109090203070e04 68
    0x50700c1d546144401030000b1480413070180c00c041d20103001c070b1032030308540004041005d0300c480c0c4070f80c4020030300c1d580e8001002c54040b609031444601020741161801c00c1208403405000c0c040701e24102c055201c1844c02d040c040d40380550000c00348040700029007903d50180c4080508034a03031654080002c040543d0318050214500040c038031401081d400c003040c44c10b0484480d50f0041841d0305c1c0d18200b11500d003c04146000c1e01845510700011803030030340380c0010094800d502c8800315041c82c0c040c1601e805034000128074182d5400f59001d40d816154404d10100404025824020400b0104054a0050a48a000925480a04141e85101c07041989802042d0800d801100d000d9010404002e03051703504018550b0800e0041c0c3d0780b0703000c2c0c2c241036048003020380c8010a1407856681c03002018150b8041350040714002c00d81503001b1512140ea580848820f40c02c2560389910480203240052041c0602003011401108140c56209601e8500f03c9620013940000708404280440408404601c0c0c0381d500850142d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 617501043 1250 617499793 617499803
    0x80c19090f1e17060f0a15030303090530090f0607050d1e1d0f03030a030f150605040501080c04050d03090302030f0d020705010516060c020d020d03050f010b0f0d09 72
    0x100c2509200b403009662050f070300205000080a50000d00b01c00086210358010600d007404468075520500b00202400d030071054510359450f400c600001380759066200b000e0361403050702501c40305880c034030008407000d081a03901803041d0f00c400030700000c00c04003800030b080150001e065003040e50000340000d9800e410883d41030360280c2040c020210b43d00e07030000114001000c008a800850300141100034030321504501c42c1444403122286d007254035642c0500303001a0303940050440b0f54801741402c0c010090940346924460b598200320000600071380d0f1394407100544106544c1e4500b09443c103801101d5106000e024994402c0e0304103c00724180c0c072020081c1d80118060384881c40e040d0305e5403043c90328005e03000c005e0000700d0700034031140c2034025030100d03001040799000d10703103640c0302e00e1014404440300b0006030005040c00c0c903014140404a4000c54802d02c1c40346d840c0c00f41ca10803000c49030290196202140e80880803860100184000301030280503211143c08503c01e1070801415051050494035040000e0728 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 617502293 1250 617501043 617501069
    0x8061609211203020403170309010f1b020f060402030d2f1c031803030c11071d0108070305150709030203030d0504350a110d0903020907080c19090f 65
    0x9200c0c88145140b45001079150071403402d440d6480b04440744255201c0883c000c000080481c03141d100035040b0480320003080740c04100f00400c10881c08000c400c0400103c001d0300a807208070400c0d41c0e022801c5486150060050900c03400d400d0012220ba40100082c1c1921481002128000103d910400c501c800d850800a1405540320f415000042050000100806040502d121105079040507000c5105070326060200b0000b0030080c00b034030303400d40008072107400b4481d640001901c0f820751411440f0401c0c80301140c00752070342c130b0340245925822640000380c42076000d054413030404003905419660100c100c0ca0030074005030701c03540001e0a40d0304c030381d00b100f03512510f0320140010b01520010880348412001040a120a442400d10900c40d402206900041c0310200e4480740a9001d003144150707141d6a242500c481c081c458002420420190005034010024500051252130107070001e103015042c1848114140350340003049810b045001c0380c403001007104c068000540508070811a00c06082d818890b02c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 617503543 1250 617502293 617502359
    0x40b180d030c0e04090f0f080d09060f050a020712260702030909010f080d031a0406080304090506040522020d0602040f051504210c081009020f0102010608061609 71
    0x808443c0c0402e0454810303031802c000c900c0050381488203140c0b01c0354803801580d040d96480c00e08800034014440fa2109690030b1803c1d11382000040d85c0301d000c1d80034981504100a0701c0f000e1508040f03028080004010107801204141e0060240321460070003803580e10b50079912003029101b5521444183c40d11809a44045011111454043d13002030141c40840506622245030100c015911400c0100c8031003419a10380900c0241c586912482c00204400380c410300c000ba0303a803410300d0382c1d9038840c0c810700340a00e00d044003040c03052410340201c1d0b0045c250040b02c8001d03003c014543c03400c0a940103000700d0740030a840240e0710029002d800508010702c0d021000524441c034210500003043d90405800300448000c05c02400f0544a0211302c1d44000e941c003c5682188000d40382c48114403032030350023650607031140800d4049800780c29044146030300d10a9510f001501004401a420b0380c41902030900d03150819070014151102c20305882034903401c1850600d4134166542c03800390b000740201300e403004a118801c00311 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 617504793 1250 617503543 617503547
    0x15170c1003060e07022a0103180b0103021507050a020618100306150c0503180a08100b010e10080705031302040504080a1403010e0406020a050f12011401020d0503040b180d030c 77
    0x20380d04c11028006460f03484040c00340346c112000c2000c0d041d2200060016001296403080e40858802d411170300345850703481f0706801c103001407071400d2100300e02c0344030002e650105184581050703c4d071440d482002410410200d07820060079400c00340b400445006100002041950391400191034117000d901d001902e07030304111040e601410700c0f4072000d06000c4481080000908000f0031225240301d9015082d0b105a00c150000f00a22102d0340528418031440c03204401100082d80085007214007600c0704014004c03e5803e001c50044c1460120011400c1d42001a007001c3c02030700116807248982c0440c6807102450390002c0c044901c00d03102980c01c0d040c00b003120030090307800843d412102d203e02c4845606540c03412003558a4000c0040c0010311458011030805022402402596100030440d1501c545030f50752841c2400d440d103024850307041c0480300ea440c204c03007650004c103808a098825945040c915a11a00e80140f414405058540004440101c44202c0c041c140420300400b0b4003954080b440346406c0303c6c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 617506043 1250 617504793 617504819
    0xf09030905040c02210702060406020d0f030b0306070309060213030b0f1e16030207170a0905060f04031e0503030916050301050114040c021c2115170c100306 69
    0x205002e2072a101e0303208801500016007491124a03071003482d103405e400c2106030741d0900460034000d40080021034085059500803032201480409682d814a80001da0042181903580c0c1c140c8403601504994080b0b81e02500c81d0700316818070750042c10701501d070036401c2200c040e081c1c21941c400d0311402048030500c00d5140c03040910381c0d000962110b8000d0803d120a1248030400030242c452030150b04404d21440700c007070003030701a034852540000030315070311625404442000742d0129445500007204200301150f50f02e4900c05407208004690390f0141030508540c0c03090700c42c5045140c2c00203040e40307141a410008504200851003000740714060203112f0b10805020780d684d00e280d00200e00c40d0f4180310052000005001d00e03036885030070403200400d02d40984041607017401c14000d4809208000321100d950001c0d040050f0b06150300b400c0e2100c032040303502040001c0480341d0080d90040c03501d030540010484013200c03001c0b904038075400300c099405200a0600003004114110700c034402003911400c0c1080b4080c84800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 617507293 1250 617506043 617506049
    0x2030c09010e010e090a0507030c0302030c09150f03031b150a1109040c201e010515120f070e010f05010c0b06060c0f0a150e07061e030b040f090309 65
    0x1a0016107504001007110001c10500035a21352489400000366481810082c0340b1025400c10190b441e1561241403401c140701740b42c082a030180c400c08064080b1810945802d42c8200c03026114003504e00786000420811900ea8078440e607041c0b1090080c012480c403440c100e10009030000006104080319030410b41c201040040c000d02140f403410b149442220200e1003180e960420480380080c0c0c10501040694500204102c1e0419800154084040750b4000003411001003800d030303407400386c1800e00b84101802d8071011542e0385406003111070300c185c4504110320003d420350580c10a0711030712142d10805130b2520416902000300c0750b015000421504142400a10180000b868600718a405a489444082c4409002c8a004d03880001d0036030328200051001c0e841048050701174502200c40307410b00e4040e11043c5180000d0403480c1015034443d0040c006012400c45925445540302032099062203141c0b40d20030041c2c0402c0c50f880700707025a42c5e540c0c1d80c4111038030440410300010310001181001811441160 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 617508543 1250 617507293 617507299
    0xe06090c0111060a020a031b0f181a03040507150801300f140d0c02040c0c050d03020309120403081b07120209130813210b013c0302030c 60
    0xa001111025004030301c00b5403051070301c070025030707a00c04401b412402010851608000744540e90000c2c840035500c0b54211034110510b98441200034a580070040d03d110842c4140c0a00448a411001da400c80382c1014542c458010415905e603a945c036100c0c54000c0111111307100c0001c000a006002c80035903881d00c1403015001c1103500c8006202425140400c10015201600134046110440304211950b000810a60800d01c00d45c0d4200c486000c000d05640340e00c1c00c00703e208905150303034030384000d101c4ca00040255400200a0440d5560311034150025440504409564021241c0d0700610b490390500070b1005500c241d0509948902c2c2c004039260840901c18509031070707004240c0030410345190100c050303c0782e0340484180050340c03602c0c1380584404d24034030401007070b02e10302103501c11040f59403490700801c6070741d48007140307c800c41c01c1c49003400300031100d800081954059030010300017030b0307441515004490000240c81a08030b1001000e03041089441c034884100601015040c800c6060901040a04a10039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 617509793 1250 617508543 617508557
    0x40317090313050120010c0c030806030309060301051e0d03110d0206010e0601030f06090501060503091c020a061a0a030507170f03161b08010218030a03021c09090e06090c01 76
    0x82102c80705814061155504201d409003030032025481c9a252002492808002003010204a4801a00c2c003101114142c012807480c400040c82424048121104a04001c110a25683c01c080c10041507140340c4017030841840494020304101d4680c0380f0701070b11070740c00303625285070354589100b00616001d0841c041c1c0e0b085400c94001000300110060301260015400d080125142440300340032001401c0750783c441d94070350341000300001e109608400110701510549041c0c81060031040501c0306461200e0954070016400f851885000c0f800643c0056410b990010300306401091803c001413886940740c005495903081071004000a0b249040b490100b241108090800b4404c0441c0f40b03605c1c1d002d6000900081c2800c56440820840c420030104880810700116100d01034846024038001d4001500041a80e0b2940191307a501d8a40043c004200e10340c154018800b07104156143d514400740c0c064402c05000c0c00c2c84000ca45200f0ba4011006007405e10401015140750403c1c0389450403813083c2c40722b4107109034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 617511043 1250 617509793 617509807
    0xa05090a0b0103140321011505070b0a0908040503100f0c0207080c19050607212d20010911010e010804030315231806100e060706050403170903 63
    0x84500c50450f40c04c880702e00c1c1a45040201907045120b0300051029500e1130304090000e6840130160035050b2103025503a20801900810300303842e0340c812420080c0140316840006680c1000d96000344007080e20401e201d40c101595400820702c1c00c4400000d4030019603c4101c1804104018403c00106c1c1c1c130345200405040740b074114140c0c2c0307d28880555078001c41051850110203c04000ca04008013030241c4010340e981018141074190080a40f900100980a80810140e02c0e200740c100c61940d409043c60403921000142d080007002c0f09510510f018004c40c0030b0f484441400c0525042c101c40e14040022503040154980340020016210761181848032103900030010b42d91203803056500c680d0600f0006103a0444c03010005007000c00c5d0b4051009444901d1241e44400150320f0440e401080030b44001c2110514126085240300049640c29005507035442c051564030b224003d882142c1902421503442e1008585a02d41a00d008803030a8011804000850701110304200340c256100c401400a5414409 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 617512293 1250 617511043 617511053
    0x161211042c0a240b061314040905120c1b0f010507020d0821060a1d0a0e0303070c0b3108070204060b040f0e060112050903130e070311071e081309050a05090a 69
    0x8060241600547e50200c98036115100c5034881c1100c60b0b00441200d85084440080c1101039020030304440d203d0040000f00710810000e100d12190050005041e041d8000c12030700111495044100c0681e44440c0882d04140481c2c5030b00000d10242040e942c01d00403040c004500700d0700e68240581040d0141a0340882000001035203000c010108448404012554403000311407c06080e803c0003a6019000000c240000180c00001c42c20b00540300e00000036080ea03407480701e01c030381e00140840b08bc004c0001c401c4000300c00f803084660701c501511030000c00d42000c1290b00031a007107541642000320107040000e02400351150350707100079004180d0004c1800c00380c0b9084000808000181144502150319540450341254050080d03800c02d101c45c5603641820390b84c8400810602d134058a51202091504520b4550f003102c0000b1a01c40315040f070840381d03800001d48500280c00142c03980507552034405000250603c0400d0903000014150340e200840c0505000001c90210361000e00049806d901440289000903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 617513543 1250 617512293 617512327
    0x1090506030c0705070b180a090b0d0b0a0608010203010b1803061b030a02040b0304120f180b03070207031205040305060601030603120f02161211042c0a240b06 70
    0x322500b0300c000c1d00d80c0858070302246018210381000215002c0442c0b04203c074040207191303005a0a013107034007041040d5104a5041215181003035281c0000180e038a80c0e000c100c1036565503402c0320b04018000b80156680401c20700b2030300280c004640c81c0e40001807140c03015241c2050a40c0c508012000340c900380c1004a14a6103032a540384520541c0741d0040f0004810340100e505844c01020001e0721190f03246400e10f811520340501c0b03510f031030100340744280d0450603501c10511031412810300076102d22510b0408031244480d802c010b0602d02103124102e004000101c00e4040c5000c1440307a910ba0701e48950075403410701d0170540024401c5040614192041010420480c0801f00b1003a8030301f802554002c00080407814a1003002d421341c8000300c2c0b11800600c0030180043c45e02040d00801202c8441c159450412054682c031038040c00000000c44c002c2102c15141014000c1000c898408544d0403001950710603440f4007260314089212640340c0302c5e06202d1035160007010210902100da1620300600c0100c841008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 617514793 1250 617513543 617513551
    0x903072936090c0c0114070f03090204091b0807082103041b1206050a020f0301030201110a020a03060b0f040b06250609060b10020a0b0711010f290109050603 69
    0x21140c911218640300c0785491062803030060002c4400d403800a2010346540c4c840038120705258070b00700c146100407000003030f4030b8003a080175a01d02003072000c0c45000f1000b808038580180d911555490b08000000c07a13502d01810072a8500d04040703400c52130031464a080001640c4100c0403604a451030101c000405001c03180d0030f0200344421034603521641045c0c40d0383e1507016055407186c1da010002241b81140c031000d00008610804e01400565900c40b104801e074010441c0903882810140010700042d8050080044130070030480c00c60320000c005800241741c080140d40150b81c0c0c55507440c6031002c0ba040c00440000c0041c02510188050184140480d071144106102c0c2034004540949600c1e0030703000301c00d013000303000c2d00901c0a00c000221410610001c0030394404062203042201c001c0090b81c1d0011503c4da00d00ba410514454580c3c0d14900e0503140b40c040c20b03000103001d540c1c404040401c245580710fa81510940c1060005107401c00a06069000110030740303c078180940102d081005039107038412a540 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 617516043 1250 617514793 617514847
    0x11d0c030706111e07092d0507022a040e0a260705010e0d0906170406090812071e180902090a150e0103060b0702060706090809030729 59
    0x3d42c182c0c080b0607800c2140d1341950701c4010100509040100000084120680c2e000340300402600c400c00d0492050841481c0782c052052891715241c4046d880c0136400b0710352050090043c3c800f500d422460b911040e0801a2125030010036020712455503040c90303c140c007003105074800180242441da0f22144640080900c0c1203014114616082c84a4030b01c1c10282c4452560050086c850200403c40c8541c81d802004010b10008600302e0b000102d45100e1010b1814102c0c1c44425404d083d12251180c1014082000702070f070300c525003007004110108034942d1482c8509820354403148181002c001c0d5001c2503510501200c10800c1103510201c12074180300c0d0a408490705a900181d891300d444e800708003000c403140e20000080b503000540103107141d00584d1001407103e09a0b0b08120690311600007143c81d0190420280d0081000c0c042c000000d40c4507441503500d00e000705010341c103001d41d4000103841c050054021845102900d4a4800110008070703c1e021451190400581820140d5100703c10001012441c451 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 617517293 1250 617516043 617516057
    0xb0109180209060a05060a050c0105250e010201060f090209091b04120c030b0108100c020313090c0e03061611010504120f0c120807020c0a0e0601030e0f01050405011d0c030706 77
    0x940d901c8104c2c1000800018000a03112020b0020190458000b109000820350030700d0f00044540b444011085400d0091520702c200c00c4c1341c1940f045070101c2c000d5507100c2c155136031602d02184407018561703598001c140505c070141c0d44501420900c0140354001c0c01c02c0c074454105054000301161400c0c1640d041e20403515110614068038101244d40d849507a1015040b0002d2000100f1440c4001c5614143d01c0b04a0700240880c9169050481e528840c0701d4441300704001d0b1810070b001c464600e4001030440b9801c1d1420031000c090780c500082c10580309071042d00040082c804280d0540d9041840300300909181c00007080985015203440700c10510115691b01004050100e40c45494016240743d011544c10200480300303800c130902c1c00340c58034005a074410054843c101d0040203900d003028110701503643d95204d03050940c840e10010f5014000c684070110741405141644000000c0901c5494880c85c02080042503600240d02989000d801c0c0300d01e9615a0340181000680c1901e0005101d41225002d10300301c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 617518543 1250 617517293 617517301
    0x60103081e22051005040e16020309040c12060b031b0f251e110108060a05090c07020414010b030130050703060c0207050f040f02070510090b0109180209 67
    0x70503184100035408146a4200b2401c11118414015440a484050b9901184403c0e0704500f680c06000341d1142e0050303949400d00048050044010340c10b035080c080d00449080c003443c1c0c000501aa0902220400061a2030304450354441144c00b42c070340100005d020aa1540c2409501c1c0c029240d881441c1c000501c100054580c0795a500c1e03001c4440210305020189d00000000b07442d504100007465003030720a4183c44d01c00ca88078556244014001641c0542c01c80b148502400054440c0e64006100960040500c00300049a03101c000b0b2182c0b107901309080842c0e44030700e5881000308071108100044e00c011400c000600110182c0400c803410f454000c00000300c541041c88402c0308a4031000304158108004900c6c54040140008288042c1c0744182002d01200e07019140890b52028a88951035110036402c0c298885800e007940055440009048007510f0108152140751425524282c40090b0341c2d924885842808001e1075614050102140c06100311020004003050301c080f0b12602a12407103104c0003007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 617519793 1250 617518543 617518597
    0x127020304020102150103051f14150a09111c09051b15070602070b0606090d030e06072310021306030f0e0f1b03010b060729190c0206010308 62
    0x160a140b940075000c01d4151f8580c40e203d500d602020702c100340c0141d140214000c00c031500b40030380b8104004400f00a00301e9540c0b00b10600d18944548240c54001c048408085541c45c84d80c01813110b410087c00d08903035a07841c5040740100c598042c070203140005103400742e9100090b40224440c0540301c02c00301d0120110790340e08001100031710220540d28002400051010401c0a95005003890b240a80c01c038002ca5070361401440010701c40d280307031107a1106c108108500000d0260007480030320900a0002070030800951303030b260800342c007800850704a0300044030716a1030f00c5000c02c60441462800003065092500c05101c82c400f00003a8054a400e1540303440c80d100c82d002655118805104505044440b00a41141c185490302448009008200c81c0502c0b499650300341402901d80700e01006d0710756480e09900303407145071a41140501000c901c0707900400448800100b2070145000d510901c41445078402c07010000b80c01c0301c8080030b009081d500500010070100d01e000090342e07482c40326022030050400b180084 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 617521043 1250 617519793 617519803
    0x50f13030b0118060e0712091a01150908070504050c0702030105040b011d010302030309010c0f061103070f0806091f030501141b0301140409030c08070f0302060127020304020102 78
    0x145004101090600100703000300038075094102c4080503c03501d100c181c0c000e03003941510068001e9540c42c211314000301c0c10083c881d00014410520380400080c603100e107030f60707040100400c880b04500034170411001807240c08102e00f0f00c81205d50031410000545071400040b1034a81100e07108861080e40d840001808604070070007160703400755008000308500e2234503141500d1205020700520700c1002044c201001034074400c807107540c103030b90300203005506003a4100011148003a40b450100d030500c0d411030f0701c100003640501644004a0003a09182d071070f4a85444014488811034285c80f040042807000d002140e180c0303c94558000443c3c0162a0300301c07110110b170720400b0915520042080d0301c0c0c8681b4409460041c2c000c41d02480300032030050aa10301c800c860180502080c090b10610208450301d40c01549840e602c000c0781288281412000c110342c80e112012680c1100d8400e44038141d460380ca1008055051025074050b1000c0060003c181c682c112014001940070b904086c00700f6800030200d00bd580c001c103c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 617522293 1250 617521043 617521057
    0x60c03090503061906050a05010507020d0309050a080105151e0111010e030c100614011d03100204090c090806010f031b0e180d08040209040204150312030209031c020a03050f 76
    0xc80740181007001064070074001001c1800004c918101c00401c840c6080d08615045500596030213062107625001c01201844040003102400451f243c001003945801400100030950032000055178581101d032800c048040044162184521400100310720340409003c0c1e8400c08281b03480c1d09014580c0040720300401c8a4100d07442988804100180c100000140381540b400b403d6800f8800a9030f02d00000044ca81c0c1428140e01249102d900384d03480100303c188442c000f02004040b151003075406580c140403644650442c1201a4a03030308012555608000408010280b601c010a565850100156101030560000602009541c915200119204411007001e00492a076a403024203022540c03015103504207520b04d1441c020514454003180c02105c10501c80c0b44c018040112584d129803c210051880768105c0204405a08020011a80700f0100301e294031040e40303006030399140900401d03282c6001252400c181c540d88400c0410320303d0b408600d00502d1581030038031a480c1c803280101005d15000e100c0b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 617523543 1250 617522293 617522299
    0xa120b010305151902360a0503070e0711010f050c220821071703010602060c031012021201050f010801060909050a020d02281a192a0f1218060c030905 66
    0x700020075860003000d0700007200004407281c1003e1f40d42c800516032180503034421018a044540300044541d40503c1c0480440203202d0b000060100c070811803201181c100391b500d5104854003151041010148101a40402444544401c0d4040c40d106000340d65031071104e0424090500e4101e5240e000841206943c00d040d07200d2421405424003440700c06407500240310b0600140308940204940c2c83d40481124060041d5041d40d0f010b440c18041c84080c0041042c00c1240c204011511014140c0d00071b104250180402c2001050759500d003400140c2076810540004c1c058504e0800035900141f0700048415916905640500511829000184240d00c2603040d00f8440724040041d00e080b20307020914501a10b00f0030350366074402c81980c000c40c03102d4000c02c40b18500503060f00c00e680e00c1240c007070307005003100341c600800360300e583c04081d01d641c90500f4000e4001c803181c5000481c0d40c0b04000718104841d0600c005481d0407000480d500504842c0c80000388108424400700401c1c8509041c407616400004c0e140207 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 617524793 1250 617523543 617523607
    0x6011b031d0a1d070c030215060d140f0f1506040b0307080303010e40080919051302031b03130609120906080606180a120b010305151902 60
    0x241403c40d8140d101c0042c0034540e403010800a0a154000c00b401c200194259000708284000340421075807100015120302ea200e204519014001110070003030142e001000b40c080c0c040040f0a40f0840c0c604008598451f025800811310400f842d00e44c5006c41d030b403180040b580840d0202c101f80c0800d040c500340381c0004110b03000c000b0010503400e0f08081c1031030040c401d05c0612524030880800768561001c1c005800d003040c0030944040e8480d1040c3e01155403a46026101040c50090003800040da4120b070900700342d0700a015110108600c2c07819400200c20440720000c2540386241a90144015960341d24540e84c0c0c414020010801d503150402d91010724a034415820000740c50903003000100c1c080c01004880000d10081b03000300e551441070f0f040502808001d040281415611401d09443c40310800f4843d0700550b00041c005005034254694044107401401440c0306941503081c00c9007000c02c0391403102e2081401100703001841c04203501e0300c081a841d20b100180c542402e1661500304c844840c500030255000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 617526043 1250 617524793 617524799
    0x160c0f12020d08130b0402061308010501150809032511030a0807020405070e2b08160b09011803050c0a15020306032b031121070806011b031d0a 63
    0x40d41840b5030819141d5020701d5445096035000e03100c000c08018483c07801d40010500504081c006441808120000151099110100745085501c03d030300050410500b071945544a50b0884000b98010f80c840014602e0056600402c0d903404140c0c101c40080700801440d20414000d41400002000c3d100600f610128080c6040914058028440507442540740c0004504007500682d50800a00e40103000d030300d1620201a90380c45561003113031034048100740300b0481c90300081400004000b1041d5203010384400c103200f800c003e050000300034a1805903a02d041a505958201d900b000e03a40c5a5042c07811503aa00b600183e0b940c240a00d064000300750441001040c2c00044468020314440d1800782c0403030300300e5485825640c4404a16103007002c0c01441001d44542894841e401c404409400b42102c149041490000c80042005940c0741044100d41c071400c3c000402d502070701003030704041c0074070700704a60001d500d507000d05034030407000000c052100c1100001a072240481c03510f408240000d0119a21560b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 617527293 1250 617526043 617526047
    0x10e0433090c0f0e031f0213050904080c060f13021e040203101a07020d0204020714030a02010e16260c0d0809040b180112113303160c0f12 61
    0x40f00010704404500c0c8030002882a04002891500281401c98584c001510f28490702d0000c0d40070881268440b0784095000c5880c4d1220b0b083e00b40210304c1020442c0e40c50041105607402d101018008030a16007061003131141c410488040000c03d984c048901d101d0101c0c60050700305000036641c101540090000c8200315803201031034002c004175040e90703a4005059501d402c54107807600c140e8038000d510072031401c6000e01504007a800380c03c0e114031400b181c0640c40c4164904620315000315013540e005039181c648202c04810140502500c40c0f4a10100302c02c02410006200340c021001114801d000002c07001d44c425100c01001522100c04002c0e03c0014854040d0501d200a5407000324a680030354204900300d80c5c0c50070b0460024469a0582c5801c1c44c0c3e84c2d00f4401c62165181040320180c9580c801c0c0f803069081552510700441e00d094048649416603507508498042405c554500c2c99580001030040001210044e0900c2c403c4500c1803808424101503840c102400c441d1802014140248440c542e55000d9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 617528543 1250 617527293 617527307
    0x403060c0807030c0e01020d0e0a0902160501060501020c1806041b0c1110021c0201111201140d0308151804050c030f01060b0f090f0d030509010e0433090c 68
    0x205503503000d00c0030f0044d485040c1c582000c0d8040b800e0061303024804a8110342e00c2940f41c14240b44000340018100c5588036107520030b0741c0040301079000801942081c00d080200074032484009000a0010f40352030045034002959207145100406004801c04000800030b903104e80c080320140c45c00e0910403040c1c3c0d20a00c0c0c028806964080221541c40031101c2d00381d411320704049440c0003840b6541c0240584507038415007030001c08000b8207000a40d9203c548030650100c2c81c00c0600410140601403c41c250700d0600c00d507158514410007540640410b00e00030b008207074031098050f449020300e0030090b6140820000301d400c22505080c00f80c00543c15209110030024041200e540d071803400c40440700d02e409070482160884146105501005504000145103648914054502d010000f0064449a800d25010951b1030076294421000504009506841d643e04451148070064040d102000b020101c258000c82e007206504210824840e10940680c1c60b03d4401441005000c201106022844481001a1140c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 617529793 1250 617528543 617528551
    0x20306040818010905030304260f010b01080609040f120c051002030403080c040803041e05060a0921150f021308161a190201110a080f0c0703020d050c030403060c08 72
    0x9581612076800656111303416071010f94800401552a0500d050402d012516800d0111a091022100781002890713040c40401c184001110002c01c0d04030034800010502c001c01421148a1042c030024031001c140d690040c10802039204002d620201548002561050031810700201280f0603018010b941450030340165001d40e00c40e8980b2a42922200420b1203180910702074282142d20502c401c019100d01c10350714407842c0410f2001d80c900b0603181c102190956000c451180e02260044408001164800b0301421a4003103206001380500b00f41c2d625030440654500584009a803100c2c1070406c6604680d0481d042a4001000c3e0400646e403281065103504107070580b10b0504003a10800540700002509540e009a5103481440c900306603140302d12203045081040c0c00071503680d000c10328190b020b407400412510445440d0403455203400a08071210000c02000604500c00900a90780000e0300054003a90ac1215410304030b88840c00d2080141c1740d4007955102a200c182458040c0d40d105070000c040d1801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 617531043 1250 617529793 617529817
    0x160f020f10032a08040620030421210207080405040e0d0f0c03050901110a0503040914060402090a060f050702040f02031e060f1504030602130f0e01030203030406030906090203060408 80
    0x400741d507401e0f28000c91103148518030118180c0000200000c40c80e5102c59429281c01e43c80381c5018154900254103900100e03001c464802c0400d029054803011680d691001107020314104008034541e1125020480c0d091260410694000c00d082c020481013a050328040c002c042c10410000d0509990749642e0500d210441011070050958140c3c000d10a454208a554154950340c1c90210181e00440b818148004404524021404013400044041c001400182080340003c1580402800c40610160001e001d0b14441c5204200312030030350b01c6074001c070740c08c9402c5410140654100c5400994040c8205440207602501d0b005030a83c6c0e008169001d5400b4000caa8821180d8550044950540d600240c0780d02d81c3c001005024460586002510300c0402040b0400781030a081c0e881d66070405a80104d103010030381a130400001d000aa041d405680c006091500c4032030b105500d990003081e145c0c8264003440302003540f110b503040103019607500a4164603601a0817156645040d0a100d4400c0d009607084580c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 617532293 1250 617531043 617531081
    0xa05070608010618050618090403031b05090901030602031b0a020303040309060c020f060a050c031303020306090a11060915120105130c0e0d0606033302160f020f1003 73
    0x14890302c40d40c000d036100c038210307010404210b0912040106580204981e200300010340800214123841d000c1c0c1c4607016a100761004502c000b0442b4110006090b96000c80041007010300480c0ba02d0b0b0303207401c00075045a4000303c005a50381c84603200c0f07002d60904440ba9008030700001449699a0780c0c00001540300d103020740c2d94100025100c8100b104d00400c404800b95100110f0002c07645545000b000800b840d0800303007040d5151030041440c041c01c1da0400c0b071180b01c18450320407041081d820148641580861408068140e258075559501040e0b8034800e2828083c01e00800e181c81c03141c503034844400d0001c1000c0b4085071240131070b1081c5008904240951402003c1c0180300f074405800d05d00454030380c00711f079403501c40a075a15041409240825007a0640340e0540700c8400001050b80c6a20b40000600820445206000c0011054140500304045a16414030400141500c0005e50450707074a9551b1206060020807194000540503200b000c004640c400844031403898641d0300341e0312000540500ca40022 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 617533543 1250 617532293 617532299
    0x80310090b060d240308070b0f0907140d2003010c0201200913050f070e030601030c27061e150f1103070605071d04050411120309030a0507060801 64
    0x8081d0340301410a0703034120105108808003148250000c040c401d40151010b0401030015104012003401c1d0f6009983c822400a00c11007400325621000c1e074425003044021038035090240a070359588410f0300c0780c600032544005003228103a640441503040603400076180214002c2c0000c0d03400c0905d00700e4000510a6103000c8e0760190050040c0a0540a008901d4851315880458110f1045661115001d15440000c000c1308a030029024410a4003c9100c0d00140c08685052000503240203890002c4900c40d070701143c0100006001c00f03450b00103032002d500c0d01c030303146145400405020f4a2002102c0e510359052100c0030850020094181501459500c950003001da40c45035246881c007803c0300f0800002c1c035001080555140a11018030780180d522044a03c0c01d4600d031101d10454000b500c2d914000750303550320101d500c1c00301044010444103040f130303042000b13003440c2e035039241e40000e1140110301403581c90486452030340082c01583c000804c05002d40391b86007180d162441c2c580041c1d0081d003010803035000c008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 617534793 1250 617533543 617533559
    0x801030807051f0b240f090d0501110702010f030203190914010e060601020d17011a07120203030a050906130b0606120f1f0e07030f2d110a05090405150d080310 70
    0x40b11a028109070702c1e6241102d40700206c5019844100129080020714a0410004e0130034401d510400b03c0205034551a00440e10004150046c0103014608060061040c8298400e045020a40400c01240d0010b040700003032400a4a903410060555055440d0075194800c0c11004250f9500ca503034242d094400c11940c1003004d4070b000c010780c503020341c400091500500204554400086c182d10725003800c2420085260f56480c01d4262419500300141c00210a0011000140c00f480d50403118040290040b85410034062910740c181d9403001e45002c21140128040d52141011a00100300c51041a00d40d03290030441041c4203d4280c51190703420345a45400d511071400c59500740140c031410b4441d8405500c8284040740a000b07289092014250764581c41c082c00e524450145039a5254400910b00329a40542e11300c04a855030565407208050402c02001c1c1e059002c800c442900c503085070006025115a100a40181440150160402c418280c210f013400307020005148141414050320310019229500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 617536043 1250 617534793 617534839
    0x20a14070b060a4707080a030510030503070201320316020f060f0903040b0a11010e0115090e07210507120f081c060f1d070801030807051f0b 62
    0x70b2120f280c40840c4c00300f80050207404c904216040303541c44074110311034241c41c0d40301d081c0c1c000c100869044034009080d0340c5564250007550b43c080803800307141c1032151454035102d4a80c410120002c0c10803140540b402d154400c1d2403c0800b64a01204d4252940c0c00001c500f4581035109440420740c060840000901c02c9100060301d05040c404080600129180d840d01e84840042c0680100900d01003480041410040e003000381106940036520044001c40c1005000d084841014000c0110b03410301c64103081110501d5646011202e00040c00102104e8191580b401c00d4041e402c90501c4510244c0d161500783e80300a04010664080e0381039904c0e5980e03514001b00360401c840001048084005a203202041d01e02021302521517240900740901c01c6990164030403100d4540040340d81321036207002800350402d000002250300b60f051400f0030481c02d215030040c001410500c030003800d0100001c0c92a08200051022521b010898881c1c0b0a80303000105103240505800703880725002d0068045038680318050f00c0e070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 617537293 1250 617536043 617536079
    0x20a02010510080a0f2405040b1323011407020106030201080903031315180506011802130519030503071a0a0207030c020136030b010e010f09020a14070b060a 69
    0x4010021080285d80d1040030010b03010080e41c84200c000059882e4000700ca402d081007003844500000d2a14051621440718800680141095414520204001492844001828012400e80c20101100c0700346e50f50150541094800300c00d001d18061181d000d03015040401543d01c02d0b221040d541d5248140e45e941c0e07000884961a06103001456407011524900303261388100503106020811a602e04c0b0030300c0740c18080b00c60454655102000400641c14080030711200700d0070b01c45096160401c82200406021031501500e48103d2843e0002c1d0030071030311180c0b403100441c0e000090f242c4405140c14801312860071a00100000851040040c8420030213100301d0f010654075032a21030000d8015001100c504034010032440e9040000c6001c100b00d003803409070780a03154a1005c1c20544580c29890412103400c0c040c1c1c00320300082003c03401848a001c0500b840001d45070424001030b00d610000c901240d0f401046190f90320000000500c0105100940044902c1040207a591031551607886c039100000704111a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 617538543 1250 617537293 617537309
    0x6041e0e011e0905042901060210020403020916110f01051510080f06040e01021204020f010c0b0117030f040b07020405010b030114091b030f070e060a050d181203020a02010510 77
    0x10b6000e0080580c96481960010700818080410111140e04400e568610031010309a440710480100051541000031341440154850254113041c1b559020039541c04000c1c1603158024654200310821900c281e000e880e110740e44c1c20881c0e80008802000c2030007400d0503030308443d4803191081102001d0600c1444400f00052030340d14488150350b02001d54100c240090711003036100d80c94820010107014240080c086588030392030303624094182403040004001c1c5002c580340c1400510103100e00480c800311a428111812004042e1314041c0200c420303400c501c140c01c40072040720004103012a8100d01500a403001314820340303040229907210340282500e03000c02d1046040c0846000d12000b81810300c00e4800760004e018a2841c0c0081d41403510403516500211a00c440d440c008500300095154044003000032a0002e80b4a207180c83e8000500610510500c09498212520b40e2142005803054400882a047d00300100312003c1c510302000401a502117118200150300381004500301080965103401160200e0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 617539793 1250 617538543 617538599
    0x70e01030c0e0403030e060c2104081903021e0306030f010e1e0708010603080316050a0203070816150f060b0c031b19050a020111010c0905090606041e0e01 68
    0x4008440d400e03050040041341015240c0d40c2c20300a612080003a60b018505e000707035182e1560140021446c0c048079400d4944440c1139401e0074403000c40c21000465480b0b280d110103040206141d006e050b000b030311840b054141c002c010302402c1c11520109401840c0100d8086096442e50001d500d040c1d42a16036421846116030809035400c600b0316200c522403d00c00d640c01055400c031a59881d20345084030016402503401200000801c100380460405016100045081803401c00c6202c4800959174050684c0007089030074000340f003c80440e2040460103800d54000d0919a0440202038048050703e603001d00000360b1800c0c45004900b408064055900c8004c2240065040c800542482445242da504090701c035400780c182c903040f001c540d2003030058215010354000d000044c0716100041c502001e24100854a92608040d01502e5610425030012602e007254030081c83d458550000b0464400c40d803020f10480f80f685060b4641c103001c10049412141240c1414415a0b40d8003120710240801c0350040300c0c0d0a00b8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 617541043 1250 617539793 617539799
    0x180c040e0a05010351050a0204030507050d0b0423100e0105061c06050a060b0a021c05041215061509030c171020040909060b040e070537030302070e01030c 68
    0x117036907000701c51851003404a0300d0030200c0881040314002e4036101d40c1c0b00e800003420710030b001c820072041005110a4a05c852001080e488040031000080c000070030140084000102004156602c184240908001d81d60419410132442004015030130115038a0b50904000510381d25102910010059100c4406185840190780e4000244801400224483c0d41d4080c0400c0081d071800150011007540c0d00101a0062107126090400100c04079950801104000510803141003101110386030340e004000b11a450500c0c0d103640060403694001180fa8480c07410101c5000703500240e6001100e0040004c1c0e8a45c80c2c80b010b51f40d03020717080405925803036804040a007251402c01e900c0300c00380f04000001d0705804115400c154056500580c0507021043e151b540a4061060910035a4485841141c040040e4210503031200d86507589846900d22404420030b441c003852a010b107006160311064421058064441c12680844c4c5c891400140e0052003182000301e00c0316030105103681603d810142c00d0002500d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 617542293 1250 617541043 617541143
    0x1f06090b0306060d0c0206040507090501050109090c231209030306100809011b050c010e0d020c040c03180503070c0803030c030a1109150a020d02070302180c040e0a050103 75
    0x8070190225822a8040280d078400318064443e03c9030030000c0780d010b854541090304096203460320030f810484200d4505801040130740e800c503a90728111500c40c01c01044003415502c06880c184400048040e8600c401e1082401c55801a001001080308042c1d0009840c0c490442c00c690b20b0004881158001010010704c040302806014680d601c00204000443c5001c403180e2401c1440c890701e0340560120308045000224650207000f104268503601c8018400700d004854002d55407a016070255000380e1340c0b0010017881e94400e03048400c0700b81002001e40545015858450750b81d5104003410303523507500081008101a0008801c890051390409010303415620344441c514021f21030400b120003206010031031a0f2182d01c1741210b189400342c580b5041a1141c0740b003c00a81060004110360007150000b06003400107a0740e0301c128502e854a613008280311a5606801009544142e422100190340660100170b02c0340b000d900141c0c1a24826609245d02c41c0702c2c1715205186d61700b0540d01240603403461001400d211 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 617543543 1250 617542293 617542297
    0x150111070e071205190209150a02010b01030e0c0d0204110904020403230607120b0a120308101a0d110424031a060d1109100207170307200301090b0901051f06090b 71
    0x4800800d000d407031b6440d40ca861103040d400b008049d40907035141c1028010781e6070140320700c00b589603643d005040c120825100041c0c005034009070084c0318036a20f000c44e00002e2942c07815030345230681c0907101315521512030034103c48680380e0161000802000d202c0b60318007114041511402024a6110481603d6a1201a074007500c5c1e1036600369000600c40c040040c1d2026400050030200c0c0c007a0b215403150b401d02400c48a008852a00a0200c0c5603c80c40003280101c00340c81191742501c15540002190101002c821415200e21b074403003101e14150100b0f400d034200420301805020640c50324200211100e1846110344015600c0302540e004405202c40d101d401000c0e004070f80d05038034210886141c91502c800186414480100d02c4005030301620b0284140c0890704046544034000c0310055080a00346d5440210418212000440041513160502082d0302c00b50020a1900c5e400000040b05d464080500e034001c00007104c07081c0c005020820041d002500c0f4007581030607201103a4641c41d5407407e107042c4116036 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 617544793 1250 617543543 617543557
    0xa030c05030d0504080315040209030c011808070608070201050603190209070c060e0f010608191e0c14030c040606050d150308070c03150212150111070e0712051902 72
    0x103000810030451009030714403d00740b00d030344900300250b100d04190780e41c51020100055a240903600c104045143c540d00091844a40c01c401d29050f8810410020188040601da50280020303108030080401d00340d07008401c06104560940c0204555519181010703501c0c060034682d001c840d0012208000036080154000340d0102071410510310003280e0390740e84401c43d54100c00c01c10b4181c10070840800c5500c001e0150f03500402c2c1c503e0040400078110301c07220394000c1c0c540703000804407508804000705004e030120000743c100d600206107160706692500c0c500521000800000c0c800c1c0201a2100c185280500c151800d0f5019682e40d1410848404140c1009040a80c8400044074060790008001440280103240c072034450504180b1280c51032400c6044210724150b00949580140405d075004503491040c50740c041744490300d144400c40301c607006850342482075034241c03070a010340d400108540d0301c011001401100c031076827040d02d41521a9000400c0340c50607125000119035a6499039050703265074000d00b0300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 617546043 1250 617544793 617544803
    0x603070f02011b020f0705011403010506070515070306050405060909060123030109050114130503190e1002061504140c0a0e1f0e0f0102030306012f0c0310020406020a030c 75
    0x10340341001c0c450050100c81061803c0040c0d002e80c22200c4840014042840182001e0802036034040c821039001200e800140030313060050300003244940900408101c40551480d070078065148034203045030010041c0580f802100e02440c10300c004030340c1c103040c440902403064034944040c2c20142d08080c489038503d4064011032034159049881080513a90070300c40c004401d0b21800002446003500415296901001061340c00744d02074100324440403500120032038024001c01e40c8443c100041c40642503c441c5102c0300c0c00741e006440d442c60034408030740010301e050081c030000380081e01c40d00c0030a00300010398100d0704c58400205080000b0600004025000d00041001d80c02e04308008021070000c80c2c8800c0c0e05a6841c0b660b0b01c0e44d500f400280c99001961030852080a50309403682c00845d50020f03617a488094031141c1080800c800502030582c20f001d016980000300d50b921101a9803102c0c06c01d50b04c1070f0181c1030501c44c0c0500c0e0f5030700c8015070b0503100301c40031580e141e000340c50600a81c1e03c5c26143c0001174041526 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 617547293 1250 617546043 617546051
    0x1050f22091b12060c02010c050f070c0e1305011d0d140904110307030e0d08010311120d090603053603040906122f130f0e060609070c020603070f0201 66
    0x4601409442e005030101c0d000880ca04803950800c00700343c50041000c1c4042d03914141c1e00c1c0c014550b108088400e40001d0a03103140c1c1e01e00e400e151004810545070f014403400c104241c2848200c000680c0c030051308078042c10091040950600a60000002a0319050255400b41200f5516180108031003503081010f8092141001c0c3c4810205041d58001040c941e080100001004a695051302c40c0d0a011601074008044445070140040c03c1b2100600009d4900c00081000b0301c0555905032140c0380e40042d900943c1d00c84084032a019080401790f004102c00309003043c0c0011140540c20843c9411410f070404c01100300c8560000350810207020690000041c0000c1001140700b02e1a8050000100080004001c100c00340c0e00b0090400c40c085503c200031072071902e2298164003a000c002103040720044664071301842400d00403100a0207144600d03d400d900f000400c0c6202003020070307913078070640c1c00f0340d011035190303031503060443d44030b501282c000390300c0403040c004179030b0041c410680b8840180203800001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 617548543 1250 617547293 617547323
    0x19020109050d0804140705030d050f0705120d0c05090604120203030706141008060708160c0b151504030f0b070908011506090b0903030d0b0f060d0501050f2209 70
    0x29090400350340c1030001249143c030900c410010300e245000403402514000e000c40e1410000007035140c110090f10202000004510000c03022100b60031503009503803100c2141c151462465904001d504040c4c4100c1e9402e1802009150041c0a1400c541c0c800c1c2005080d44c2ca0582400b41101009911010a07a094030041c01800c001500318030035103024180c00010032120349025030107002392800a40008840c0e805c880140860306070000402904002148402c505486400c40200c070600840c0e0b8002d8000030b0003e05004294881142c0030714061416548400c4002d140030410905100724480204000100484070f0301003540a000c045d00302c070051410410a0750ba45001500f599605110340d078641010086c10172410340c000808200926005120380c1c0ae040840001a0700e07401922110f07002603031640c180c0c150303c1d0740d10b14081d00100700c0245200d4443c401340b42c00c04018403090149600a6500c0722000e8002d24104400c02046141107503079180844080d01d00340007404107500c0444401303022075509 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 617549793 1250 617548543 617548553
    0x201090b0705031c0603050616050306010e12070f051018030602161403091008090a230303010605030a0f0b0d0f060609021b01051b0906131e170c010519020109 70
    0x203200104c2c0b40c0355002c525181503013055070900c4005000740b030301c800d295007055224642003400c3d264864000d0074444030b0568a50301282d004001d2100070b03d01800760001c0464044001c2c010481a210103541c3c1e4001c42242c628152a0500040301d841c5200d07115100c10400a8140e80041c0b25030f40031807400341c0fa141a07544d108196603060010000443c1c002050700030050400400c0044007a150386840703140e5003400c030000c0351a41d21aa0001d0651a6081842d07400c180240c1000001002568116035407981c0d00c0303800400c2a0001d8604c148950300b03102c00d000c3d15100b10301601c44040b000800c01124281140d451281d814480c41d4101d07921602c40100144680851001d011641112108600303104d0502c03400340d0071500001d00b040c1d80510101e91910010302040305a900802040d98807035501c000d25002300d010590340382e0100c01170115443d100c1648565407620807040700d14552890152500d64a100c988552074561903d00040c402c0c0403035020303c01c0300d44030001c1e10340190000181402981d280c0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 617551043 1250 617549793 617549827
    0x403080f160308062706010c0302011103010f0e01090912030c110609061b160303050711061303030501141f1b0614060108070507060b0a15031406010c0201090b070503 73
    0x1c150081881c0408002e032508040c4001600310301134010030b04040a40b201680350380b80000d072145040103540455001090b00035440945a8111501c4250b1a5a50743e0740b00401d90916000760b003079001d0081e000042c1c1242038000c5910f40e40d404880700400a400e04001c0b40107103c8910b41c8410444c40d200b020400030340030712004e801207108001800d0f261610f002c0c1c801c4c41d514440d105081c000c03820440d107026001c090190b034451039410300d004206c9850340c0c0011030b00d0200701d03281f4410f50702403c07050000902c0a01c0420160b41c1c0b003602c00344080d80e41c8450b44406100c902c0b00c116000440d00c2d814000318008010059000340803400d1040545c04650f000c1005084110403c9615507614001d44d5413600c0c011004a0b80070700e091074480414541201c00501d1809104002010f00e511141424040d54074145000040e15001c0010001c000c800d580044c080c0c226845140d00340310f60b030408603d0315446010392211035601078407081101460008107000c29844001d0076507013800140b10f000c02904c0006c2d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 617552293 1250 617551043 617551087
    0x1c110a120521071803031403042d11040203091e0f0f01060f0e0705070305090a091e050105100207121403130608010801061409040212120714120403080f 67
    0x108a001515001e100504150041d80d02c43c000000f5540040001a0703000380c00c800c4e41c90b00c1c201515103a82790307440c01d00300503600d01c001d41c130b242d8680c41e24114803602c0c0c4c4054000c006024070b103100d005120010500080303103c10384101c40d194101c2111581c1d0401029098603040010f0300888480d010700e850344a05050079085d050301070f80d4545604101914035528850040c080c815840081420030700030142071481030a030024203018012032440d4155544c0a0404000d0403031038002d00070140d03820603020400c44403401c0e0300401403400e400812141004c000e8140c02100b83d4000307010440c1012400c44401c08418412110003030b0000c0710a00f148418030251115107903121005081501b0000060441a0140c00112180c0c1c9807040c02c0060142c2c0c14100c40c00d01d42c0c00d0741d00006c00d4641e400840c0c02c0d0301c074452000e40320784140c4a2503c2075920241c01496464007400c0d454114001c001412900c484084900040360a0288024070120710030340b00504d82500c1417840f50389070402c0c0004042d41101914 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 617553543 1250 617552293 617552347
    0x2040507030b12060c030723030109020306040f060e0106050f04091107020102060901050606090105070f120e0a0f0e0402091f0308040f06021603030f02070302121c110a1205 76
    0x41000403801c1406200c0c1c404250b0b0405414a85050002510175020080410702003140000700281002d485040602581008801c07040c1c0e65a11002030402a50095507240d0040740340c110690300310707500d41c46480151015039410001036417a2135400c40300ca4001c482c0a5092160400000034070810500c180706d101c10a90004d11349607013050001a0070403074018a10704990741031030104400340d80d40e181250500380707007403c0c2207494030b005040102640d03165200003080303410b02000c50704025030030004e0b03a000000c00310b42c2c0d4040c040c0c9482e00401000340c01c2c426015040010350100d401442c16111a540c091554081d11a0122040010310441c1c0240d900607620301c0d00c0060306002450380c4400d00c001070105400140380c950005031601c5c414030034901c80a42042002c900a040051092107180300070754001349851100b0700881c1005440f80480c051000704a603484000702c600b0703030013060310b00211590040a0a140383d160746600144042e40180c0704100b12003004075494103d560652030300011180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 617554793 1250 617553543 617553551
    0xc030212180d051b2b0807020d050f040312080604110c07180209090408070302010b011125090e15070e0d1202190501020903070806011505090d140a11010c0f0b060d0204050703 77
    0x4540034000b05d440310303c240e001c000010080240e015000036a100007251507280c05540d40340d4000307808405029680008181002250311150520307800923400b80560000c550403ca100025031007928507100e1411000d6868101e0341040155420300c42d542103202c08850b40241ca0071801c440052080c4100f1542261048000300303000c0207050703091042c0241e03240c0a09068041010315007030140d80702c2d840803104080309003229482050042c40c00f0010028a0080403d0041c1010b00d0084d41d150119800302008040740c0c80c0c005025170307100340700d40402400e018000825042164503018846d00c5441c0782101580310305400060a800114448520300703006000068440c4070040815040c082540d02c01d181d1580100014400b082001107604185401030070070f50395a42040c4c000c038504100b50400540000c90380008a0981d50b80801c1e8079200d03034414820950010811001962400003600e0301400660b03015a80310000398041c0040c64020780018460414194658005400e940c3e04070f81043c0040c2d22 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 617556043 1250 617554793 617554843
    0xf0e13240e0303060607120908060c0c010f050c190507240e010605030c040e0a0503040b04210c06030b0d020a0b041728080d0c030212180d051b 63
    0x851045941c0c00c0c012070059451410a0340014080d0300a16102904400c200c25188400754000c050b6240180071060a5a4061603c00304c4011280c10402d000401d6500302050404114030910843c3e11a00e0300031005410301031a42c1c090079204452000040610038100200c0c40800c68440e0092044903000440041c1d205100b14140f00340d402416008810ba81028414041583c0200351040030050136500042d8010b12050b031286807111038003002d400c5010000f00490f120a68000400035601c40c00b44003444000503000240c0b40300c2514501800354218420103200d0140300f50014240d00c0340c0101441018401c80c0c0000780b0311940d40d4418802d00c64006003c014014a14540c440070380da104001d00091030b4013003500c12070700051080000740041440503074000c00020206890380044c0b1040204459049460007900070752000c2c0f02e81d02004c1c044c00000350410029008a840b900000024250740d030948030090705c06400440c4a1030940107140c0c8034400b916410040c02600754410840c80d2a2011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 617557293 1250 617556043 617556113
    0x30604060e160503090a1e050c090702151b0a020d1412040803070203040803031302090610050703030b1c060b130608030a0807030f0903030c17010f0e13 67
    0x3034154824141c544200341080000c032650518100580381c00d0070215600e5540002090500c0a1100000c1880c02c04000703414141948600004a4500c201d0840b9a517520a40c10031000000c11208000168051a210b50500d54540e240b2a003291481d52140351040d9105840441508000042da005030301c090400811203a001c41e81078118813030708a24514042410800b8034902d500100b018000003400004640982d100b0800c9070000c00c1f00e04c05403a2a800c0100c4400394107108403030107903c1000b8010106039545002d21000c011110180c0340c40e841c0c021280c1e030a03009049418045035100d17030021315040a5000305a6200d12581c411200003802030841c03020060403540701120680014035040040c4942d0b0000411101301038410300b000e110079510800f084011300100081ca4020354201108441010303015002101840d03960348450390b1b095011860780e0b43c448003d1040d06040b904940c0300b08204070741e42c40181d40091060703001c12000d00994640300c4400c00c005402c1c80c071603501c400364132005903 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 617558543 1250 617557293 617557301
    0x260d0f180f0c0609080703021210061706100605030a092103150b181c0204063c140a080f0c030712050d0e01030e011b030f1b080403110f0102030604 65
    0x181c41c20445139450030104c100340c0d52422400700a00420b103038804844030120401030301e001014001001c5c88501d4550000c1c84040311400c01c051080d2003007001103800c110b031491070704050f82c105642d031030708558804910501410742c000c030542d94810410070054881d0b550031041500c080d0700d030f103010800808070700594440070794540c4500c5001a00788012062800c1403200405508001c8400c40c401c092444800204540d400d08002d40c420300c0c043d40098001c0440c142524010f84103011100f02c10082d00704a014a4895102107607500300c90340c0c09120200313003110803030480440506942c180c02d0315080c020b4900740c41101180f8440d801034000d000c440c9400c011a90190400c010b0b001c5500d1040e684051351841c2607080c403418411403a8640e407850f4030a41c46884141c40390b100a001090003c0078202c80402802902d80010f800c1c40c6407600d206c11240548840c0703481078100819408a07200e8100d51441c0042d104130201b210080d040c03081c2d03c030304110b40c0301c0c5154820001a52828004101300c111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 617559793 1250 617558543 617558549
    0xf0d08032d060d0c0f1203110105070c0206130308070c0503070f0e073506040f0207020913050f0f0601050123031602010b03010f020403260d0f180f0c 66
    0x5219002034465041ca92054519000703a41034901950190061402c1c1510b04883d400151000040150024a01651035125005113000e40c807100e00040f00f60301c009003640c0d01114401d01090b0304480341c01c01420b00d0303402011a0040340c0354800d929a180c1e40e40c102694130500003644d2100c5920300901040c80c2c10702860004111543d040c4540303070315250700300d075580000500c084c0c140400c0400c00c1260a920900450500404074038013050420294005030910500f604c841340598034140c86410781d40698400c90f40201d8000384800043d9440440c901980682070900b100e16000d12540380503405010420785803c0300e0301070301130161581800001400a0764920741d1101200040c802c14a2005c8a03e00311f070740040c022050a00d60a041072416800740201c2c1c582e00d40c0540c80c00345031860070a05030b809007040d01d00c81d40c8000d1040c1145082e80c50030b20f8040340d00c40b1100310304100b02d5407001030b035078480b801c1d9400c0c3c42c0c07012951b03d1001c012103107441c031003441c10303030715103450071a0202000b070700345101406 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 617561043 1250 617559793 617559841
    0x3160b03190c1e02071d0f0109181e170c0f0c010c1b051207060e0607080f031e0103030525050705060a02030d06121b06020a030e0f0d0803 61
    0x80c04541e400b00400301c1844412030b82e0f4030426840c0000602d4401e01520000e01503520341e00740014584241c1c0b1861041c103d50703142d0704102080000c0341641181c001c00001079204103440d10405000d803240c0e84400c0b203040d0001c0c565580d00070414000303180861042c02c2e5003085d0001302c0e06e0f0401103680740e0a101d000f04c14810107800146039492180c0c1c104c1042c00c00660000b400d4413290b600380d101c8101c4020b4580005038040b0100705079a9100c88002002c20503110307655a070b40b03d8054054140642800b84400040c41d8880a000c2c08803590902c0f40515131142c0b854aa042001d201170301500c81062003a002600000d100103424800c0c60525550304881e8201340383c072220b9442c418bc581c42c1e25209103006803842441c00013840d80380036108006442c1c45c03540c64a001c0084565901003140301e442109411103024001c2c80104070588011000e04003154001d0b005400410869941181c110707401d059510362103c00001d09003026190f900020a465210b9188a6a603007816034040c1100c0580b0841003203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 617562293 1250 617561043 617561051
    0x7081608010c200c031e120319020322060c0807110a06020d140109140615090d0f120903060e160905092506080c12060d0203160b0319 59
    0x4075640e110791044a1083c41003440d041403907880100354186410046916490320034041c2074104510808400f45441080ca01220034000ba1091102101c1c041200c40d103032600d1042078412041890b40c0c0007543c0c009100744131000c6a03410200c0e1200d120a4240007030b99001e0382e4480034510395821480003030b00540981880143d0380071108110307a030350f4480b039801401182c001c40c00c150044e62580018040f1005075418030340c15071316034000ca4024086070510b181c0300c100510101d05542813010340d8603440340003190014079280701c09003804040c1d031008008a840300d240c00c013a6000b048644070740c0145146c107a510300c00c10624505100040d28a05d01c09100c59400090090ba00e1401c0300c0c8654088070790121002c80c20350b030382c0420300303050444074542484640300c44058000d0300c04090f86040140c44040e1a0a00c483c0c46083e0108014000e040b030111541c803414021407450702d0f040c003404003580d01c014215242d85220100e00070100d90140d00c1541949008024003503110001e0b1180c103028080314000300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 617563543 1250 617562293 617562311
    0x414010c030207050c040c02010617030903070b0304020a031b050907170705090a030f110907091d04120507061113080f030a0203031f050301050c030a0c0c080406051b0708160801 78
    0x40d01c0c2e2440c0300c54148101d47d2540181c200b24000c1d0400f4000b810040c000d0090101881c2144d81c581e44051441403107030240d00703004120300c030407074098030300072038001c0c14400c405821582c0d1103403006011048000390380d8180c040000c407591f07000003143c80b23401741c3d50303401c905034480d40580926803030b0141c1303c071091080900184c0c9017a01c85510301e50860b034002e000d41034403c9160030202c01c60740ca01d40e00c05402c04104d03020880440d8003d2130305030072200006c01100d00e0310354080790785403a10815980184005407035004103160511441c00b07004060700440c0c1c00180c110944036440850390041d0365206c1c0c410303107007801000714540074440307038074210140000b1303520741101c0038002502c03440b000784840541d00d003680c001941c500c000701582000e0315024000304030604160b42ca8113615002103c001001c10f06110410002030310400301c03d040c15510103071490800781005000d032aa5001a813070800c2806079600803003c101c0c0f04208500c02004d0317450140040740c490541d01c0c04080000d40080555a05140c0c245c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 617564793 1250 617563543 617563553
    0x90203101d160f11010c020f120f0904020d1d07050f04050903040605071401060b2a210d1103070f050f0319060e070314010f05060712020a08030414010c030207 70
    0x250000b103116103005100d40d42400019070312030031803000d115810761070030752688060ba80002d1900d9507141710504461200482420025080c17040031401420702c6030074040f00d0755600b440c0e005070001a018110109131401c03e4170700780e45845c80301005071a581c6d0000c1006c00081c24003c1140403410740540e0207108924100c542c0b1540c81c49188111001c2100018041003882401d0385220582d071040700083c44001e41e141440e012a80064808007458495100340e110850034085042070038502e624003912003140403010f4a11340c044907220303070074400504102c01b400310f2085208080990304001c803030580b40c2c00d062000034001e4000c58810018003100300700c4aa84030303124400307a80e031005511300c0e540c08400e02003041901410043d400300c1405042403007030103426a0550400222140f40400101c0217030382e52071001020040921446030040401c00000d80402d41803014204043c4140c0101d03034000340c042c6d60f0081c0d0766004a0b0f06580d030030301d0ba8411000c005020302580c42c4000e001e26095050601645031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 617566043 1250 617564793 617564821
    0xb0301141501020c06031602060606090f010e040e0a06020c150127110309100c0311040e1506070b4507150e03010513030c0b10090203101d 61
    0x40c107410800e500d0080da0990380300300b1500780e880c00091312582e1241481d16000c05a00582c0398aa4003501848000030300c503080c203005450031003034001c007104001080b000042d1064035040d100b5580090700c1d10701d51700c0803010411030346500d248101c00040c2d941001014041c200600c2c0541100700c0305a503001081b20410241040f0003601c00390748420314554040106074010030400e0b000e40c88080c804020000c480780c0101d0001003103034448600707016100454004174100d030010018286100010b01040c001d18450784015a030184000003090740c40d43d500340c001901a042400c1c201c0c3c80300d00701820080312a60319414480307a0f90440c0c030200c5001c0c49581784e6612000c0b0209414030380505445078041d06081c100300c03010080007051211062140341c0c110050062207070100c081e02a40c24100401c500c002c21130896080c00750036036902060058a66201c0c1041003010345010510440c3d00008100d0400910095010340840001c8244140ca850b8035200c42c010101d06004810f20b0b81e8007003200101281d45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 617567293 1250 617566043 617566051
    0xe010914151602040525030903050414030c0909030a0909050402211608030316081302040c0c06060e0406060b090907050d1404120305090d020c1507150903030b030114 73
    0x40361100c1c080a20720020340382d1000041e5100b03041070140141685210114070b00c0301d40c4801d80c41c85246401c00154141c9200c071302d0090000f10108004c0103800c10f180c103400e015210007401d40b9a110041d600281c07010f00150f0340381a29800002e5000c41c00303500070320348000800400409205500d40b54000580030f1603010260400c2e044803c4400511184c10b0045500e0241c000e4440101c0ca900c071164955a078204403560100d10800344002c4169030f00907100e10744601c05450b140f5092081c1582400050b04040566809000c0644000d02c00101c950103402c2c003401081050b4030b820714080c140442541c58070703400441070740400c108031001521042c1c8020792158040c00c2c40c907580c0001108240003414041c83d2034482c030581c1400d100c00c1100010100c030039400360f40d406100c652200c45400b0340703452844002c2000f5a20400044a403410003107000729420b055114110b00300b01c0d058580d007164805070184084100d9841a600007019050312440d00740e600268000c002c0d00301d60b00c1c1c4844c02c075100a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 617568543 1250 617567293 617567329
    0x1050a0f05040b0f091e06061611031612031d061b03040b0d020c0d02060c070b070918090b0f01060903020f0310090f0b090c0a0b0c01110a0e010914 65
    0x41140700c282c2c54580c813060b4002c00103807081405103081e105840750034503e010b203160704513001c01c00b1450621b00710301551114091b0304681c0c0c41c404481e594002c40980082012034050180c0f0641e0080304800d081e80c20000c103102da041042440301854014012007042e0000c402030b440107800c03140e450329a10207441704e4225115101a01d04000d81c080da207540079a0703110081000c000544404e03034042ea5009000800b85142c200d80603c50610030a0b625514200c44101090000b40808404500c104085940004560030811451900e40304040e280313083c60b200c074034402500c83c04410100310240d03a45075440500f46900c1780155040c080f0080c225012440003a100d400c008601c40e010382d13000d014003c00c0da04100d0007009424040c2c90440e105407605c41080e1801c4101100140454030045500c4000c0c0347e00414180000f400c050006429030000428016159a070b08403484010441000410652030241c81e510680c3c00020001070401140e508103065001400c1034100da10340301d0810f10042d0421072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 617569793 1250 617568543 617568551
    0xe010b160203100e1509030702010f0c080c0d1e110613050708030d05180105090d050a0c0210020319031812140414010e010203120121051005060901050a0f0504 70
    0x16000083c82c0041280861050314503090980350020070000c0d400407030341050580320821b691200505034482c055010040c1c08210040500300e01e11740710383c0040180e40c1c0b103107080070f0810340f080d04268a40440c003201c2001161030f0451b20500c918041c3c4140c0e1020a60385000081120715800b401c1d20741c413015280c00c200710b50314624501040000e0000744040d11260045070b03210030702d460500c0041c200c140c4484481d640d101c0d0152f071034400c040c05081e1141110000404a8210783c00048926a0100364a03500308030405c0c2056005944140e00d800c034001d040d0f0300450b2114010070202411181a00061040c540b404080025016400e01d81120702034001c40200c98204030420156000344409415458640e4001030110b0000850210038810780c1080e03944652000311203005980d41d120700180745051031000c00041292141c1c0500640c01a240d00d00705488005259882c0b40c5080349210a0b40c43c030b60303159802c21142e401c0400040e4010b240880e004680a403a03c4009103400105001d214052030325 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 617571043 1250 617569793 617569837
    0xa0e0f03242706042108041b0e0f060f04090519030e060c0d0306090506010e0f210c0f010c0213180f0503030402031204050f01080a0b04020406180e010b 67
    0x101d58a09619211001c21141d42e41044070a140d200c031000c03507045603071400841c07840821010f01c81c03601140b5804c54460401c82d89994440802130300050402d401d10341584200803e90403a018407032802004140c5400d007180c281281008124082280e0032401146400b900d03502107800042c40411000542c000700059544a0034100c4d28520600032086e000800001c8810590b0700005180700038402c80d075000c014050711f40600780251201a2002800184400241049850300c00300750840301d8001010b40307402c184241140d0b5000c004416494010383c2042d1b9044a503828100c100180c21402441e08007480708469000035041009951501080c0381d0302e02010440c0312000000400882d00b100c108441440c003403074015903940c0201c030224001d0041201c00000300100d0400c0d00c0560780c0040102d80388406c01001100c0980d801000000420f88500c0001900d89a51000300f02801059507a1410074003503c281031a440c03915800b50300090070340001005440402025100e0340350314010b9010965607 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 617572293 1250 617571043 617571061
    0x703080c01090b04030903050106080304050d1101170c0c011407020a230a0c031104060b0d0207080d140108061303020705090411040c080604180c03030c0c09020a0e0f0324 75
    0x520b0600041c441c001c0070b07090109041e0011010000c80e403064009001c1e140d203d00d80f0f55280d01680c860250810444001e00000860300740703809641100c10701d00744200ca10200649440c920080d24540341c0e10400080c080f174501001c3c010589180901d241c0341d4680e082040d0300a40e50103800e200a00200c4004984480e04020104c0190003c4500c5084510a1a06040400741e20410748402c894080303082c002034800d4102401344208540724004c03c0c80c1800e80c244005006984000802c907014141004107250a6219110710813942940c0001e17410f0542c108141c41d07240010180006180c9441d403200500000da000520b04107503641540c5c400036036100c80c0741103d0b8130203044002940c003604200b030812619510a00451080400703d905108070820f420141001ea030803a4405032200c0c01e660401e10210307000e03040c034a000c54400c010340c40c9010355840303980d012600008590f00001d0340c503590307503800340c6404c44844800000c04c070701038000d10043c001c1c40c1c0e0417811640c2038401d4100302c440024032011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 617573543 1250 617572293 617572301
    0x2061017150106120501120230191a010b030109150801021b010b0d0503180607080a050c0105010b16030e011b050a02031203070f120b060c010c0e04020c0703080c01 72
    0x102610059409961030702800341060f4241130300410003074a448000a0a134030640344503a010303500074109908150600101c4645d4104131103a950360789000419081d400e000802c05600f6000c07005040c805a280c40303140c142001c0b480ea400620940d41c6c44070050151040343c404403070440e90482400a0142240c2d81c1c03000e45206aa0300c80314081d480445c1c483c690700c1a01d003c2e8003003010b419008000402c003c00c01c01030343c8142604003406946c000e00c001c400710a43d03d62000030f0300b00c00808860524641c0d56501100398081b4000303000044000c980b40d00015001d0191038054600700700414202544c0c0d00e06010140e0b850103014003049208a40c1403c66401250180103548000f81101c0c1c0140700e600b00f40c0d40e40d21004404a0003481019030300c10300c407514031042c1c0340a55660796520100210100301201c20581684010714001e6440503503000558a200040c1403000c2d0950001c1800800c405002d0854000d903400680600c0c010802803268400100702d94003660b600800c110f4882c0c042040d014010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 617574793 1250 617573543 617573563
    0x80d1101110d05040209090f0322031b03031b020f09040c0306110403021f08060907110d030b01081b040605130302040c0203090915010e09063c0102061017 68
    0x700710000382c04100302105401c0300d44200c1c020780e1403400ca512402e24081c0d840469400c00802a0414002c00c0d106005403000759241100006550f0241c41c1c40341c41c0d10b40020344044488105d44c0141408004140d0061030041c201c000701000741039410266004101c0c9450307001340083c4140d102000140400041d50b2030140659041001040f01090300c0c0c00c0c900d050360060200fa803050501c41881c48180030b00b140f13101c03400c080946d0386040e02d488481c280913007414007500640600006441401c03141c0d030100b00b8451007a5045c0d0b404242c0610078000542202000b51058204141c1c0c02294100c040d011030031101201c0e054980306036a0000300c448902c00c0d40050300025400750801d248080c1c1c0c1a40007001e44052001250711005176202c003901c050203100d00e110014045864619031030342502d4601030003640800e004e4850300a15040c1c009081900413000310400030910540201050303044440f141d0500e80c8020b00042040d801c091043c000c0c00801440758042c1141c0c8260070b5881c06070240410522 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 617576043 1250 617574793 617574821
    0x903080d0212100501021b1e1302070804060e010e0a141c12030605221122080c06040f0e280f050622240803040306050a0204080d1101 59
    0x560914080703c00700c049003803003a0f500520034040000300c41d92841c20110000701c40100b209050012600340e040030b1400507452645d1041c18035a10304296550341c0003d041c49803140b040203540d5402c01a01610200c10002e03400d04010101d040c0d1840303138541100c190150791500d01c031192001f0f84000003032410030400d524a4450510041440204101e80328480c00d0481161801c3c00380030b8a40f0b0500c0030a141455101800c4454480317189a0ba4102d03500510030941146091131410315100d40c4000c5204121000c0e541c04041800c0411030302d4010f11100d0a108001c5581031710740b502d400c04515017604c1c00d001c2d003064402d040000c40d20505804802070b0309503040303862010f002d00c5103450300d6000b081ca0031003004600d801c0400040d15458a82442c03c1d80695240702002c10341078100d85e040003010392102003080215080f070b80c400c031100420304140041c00030f00000c5903a507096251031816520007402150446005106c18018200302181c9032004c80c11900c1c00803140b030903140708a0702400444078040d003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 617577293 1250 617576043 617576077
    0xf110a02010213090b03070902031003230607110c040510050d150c030207241e060315090f02010f0c12032405030303180106032a080d0903080d02 64
    0x602501034000c0c1c0190055100e034404140d64034a402d0050b50b18594005505800100f000c0c0720150540c1e02031a00603240c480b0b2080e0050322580d609845499924a0505221007a0203c50300c11208026060b0701a01500e4070750324980010040340d6544400c1026203114030b4484000400400ca80c0300e440c40100300003440c3d05480f10950409200950364260894400c5060001c01180300b4024000c03242c070300e5841101d030b051400207004541503603000503041c02c3c50192100010310b000c40f80344540c401084282400080c0c2945145090fa10801c1e000d031a1400c0203041810302c00c041103c1d03040300c070055902030900c81078032424040e0489140c0300144001f41413580c101450b04e0051b40c503601500c80c14404c40c0e20340542009800341c100d808291445010b5240d0f00030000125000403c40b81512000c900030004214181c4a81e40e4040100c4074002204403102201d401903210710054020600030f00c60b01c000b900c3c50440e1040001c0c000c2d840b03400042d056000008500c19081d000d039040320010050302c0c001031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 617578543 1250 617577293 617577307
    0x23040326090f0d060f020720060f03091f060602070603060b0a1b0f030206070806010c260403050304080604210503070503040c030f05070e07110a1101031404110a060c0201120f11 78
    0x5d4000e42004000740c88000b0f50b10030760700d107500040709188001400103080e68107000d09140305443da0b610044c103402079406103100d0703d9612a4085113680e07052071501c40110b19103041ca00000e2511220760b01681c105030418004208280c80c1c0001c80381081c003207290240c500c106e2041c84c240d80f06904040101550719001000b81810350215040d030180303109542d19001912a48011202c07100c0a400c0507101d00c5480120428803181507401d45812116030700d00303074203190361398441d1410758200e9408808150840e0080108100c1040c0c5010035141c1d070310000c09400820b0b00b03002411070000034100e40030302c8000808034052009200c800383c02168025800a40c413a81c501d402c84e1a10400d201d4110301d046030101140b000c0e4041c01020b03d00300d40300030041101c0c07151506c80340541c001c01e01d5000e05050303036002d03141c00102945424500c00e9005e20081e910b03070503140b0107000d416840740d80a5000c00540090300e10040c0c0c1d012840040c080d00030040484c04210b40a1808010702c501c00310007841000010301d103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 617579793 1250 617578543 617578571
    0x90b070c06090603050f07030902034912021c02040306020a0807020c031f020c061303020f060f0c1c023f1623040326090f0d06 56
    0x1600a6440780d030303a0208025501c04003a010b83d48103032a07001c1c0a84040e030010356014803a60000200600003003c59444010341c81c00d50000790154500005440908002201035103409070110b420540c100e282c80d4040c07101548000d0170180542c4449a0300750300081c00101d1580ca2f9000d48441d07100c5120708554895503840c0c00c0c03000798401010f110108503a8400121030034008070b1000348065010b0080e181d640301e0644486c4d1101813180001c080240c0c240321200d80b032241046041e12800307650031020802000c80c18013034034014039110324110f50303032003001040400240c45040c02c1e0817200d0b104016071648000c4030b06920388104c04d0088010350788042862030103004100d103641c4510480c04980444040407a0807180d104060a0f4100b41d401f00c000d010601680c00310910300407c0f2034a00e483ca0030040c0e481203080742e4442046440c401c4c08804582030041c4011100403540480040f00700d860110007502010905000b402200b0744240c03005407020703c45403a20300b1404580340c0e11580820a20385d001d200303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 617581043 1250 617579793 617579813
    0x903120a18150206130203060a021e030a090203070b18100203190206010f0819030f090801061508070809100b0a0e010b0d05010806090307060506010e12010501031520030601090b07 79
    0x1100040c80b940020844155841603040179a07a000340241c0031990307482074540040d500c000c20000f400c84020202041440c0e03404090760003104502000f1558441e1401054a4600a81c01840074640100a512805111a04003e8259505441c041100c4030404c1d4182d00390b010700c031240300c4014400300529921603400305019040c1c60032500d0041000e034640c89001e903070b002c40c5803030300e031f000345000820f100031074000d40710071101607204d280030a10345480d00b81060940d40319502c1442d082004d10303080141c150f0031440ca281d000c2d0407460886410f24011900f1136070703222030b8021030000c50394a0300141010f4488101a601030f01c0302c18540704095039212160f98241d40001d00c0c41a6983c6020b00100341090f01013225030254017880e004500f0410240c03140401071401400b003e050107100d03050241241c0750a102035642c2c130740e180e00000d199071543c00d1119540036649080740704685002e0a225403282c48000000010441c880c4164880d80d8480058561900540000901d0300d40403599908004d04044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 617582293 1250 617581043 617581079
    0x40c03061508010c030207051207020a03200306130b19020d0608160510050711030316030302130819060e0f1614100c08070501090813080f030903120a18 67
    0x402000628542c1d40d04500328001c7d05001001e640002c004001541c2c043d5000d828003d0000b04100b2010707a40c2e07a9450102040c242e04d0380922170505088000034541406100d03444803446100c00042c082540d02d046913a0b030700511076903804103180388001d8000c12643c180e0384e0014001d02c04100594849080c0c55035101c041c0045500d8200703500300807030320341058020b204101c222a1161070804c0c039240d4411140c2c89005403070a030544000e004c068100c050000c1c0328010b00d4060340300141d6404e02034120540313680240e00411120f80c48503082c18001100b031200404030f2508460300099a03d4031268050411080201189243c821103651207094200d8292583c2142c0c181001c028403400f80605004c2292004065035001c6180030040a01050041d001802002d1040e030001583c451a40e84000e1960000b00f415143c4030441d40051250720000c20a02c1440c1c6211001942040703403a0002a60361039204c000e00c072a042c008a501907007030b40550500801c05184007034986549480752150300000003840 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 617583543 1250 617582293 617582309
    0xc07080609030c0303061002160f09050f060307060c020301090f140601060807050f0f0910030b0307090623011701080604120804030f14070602030a060303091d0609040c030615 77
    0x503001ca00380754000812105812041400b0b18115503440d4204021510607814010960043c0c005070902050a03080c0c4401914012100380c0070103051811010403030b00018104003070942540203009071603400140ca4022240e0610b060302d0710003540d102180c05048520310091120342d200014404002d0040c040c007000c802001c0c212003050781d84210407901e09505655510124000700301c0a480700d4a9007008010081325217803020301c0c01d2411000720f0f11000c030b08049080029074814146001f0f05d070600c111070052442c41d10078440142030064085c440c44101140e16100d281800ca900b100c1d9018000c0b0555500f03403c1c00c084915070b074540100c0c0e110801183c0c100e800840c15110082c0c0380303004405031405a905569040c80003104d440301950f02452007145107181074414404d020014109000562044000c1107000c540c2e103281d07240242c2504480c0e0450301041c4010700c1c645481494100070554000c204440c04101615a402c2c1540201c5490304003500707681c01c104907190300804074028481150182 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 617584793 1250 617583543 617583553
    0x30106030c08010609050108040204390c02221805010506180f13080c01021606061a160606090515011413090e070b1209101e0f110c0708 60
    0x45080300d0842d8240200fa011501c0c0b0a414071041d4401d001c04c640c80303031015000044043c4404d04040b41d80700250840d4548550407100d40c03207042c2d07441805660b11826828404000b000a40c00284400482c041c01d10190380d5403518240e01a4041e00726502140029a0194107500c860074124043e241c1111842d0250302000c0d02c0740306d250f280f000303150f00c25440001d4040c410744503000e004607010421a829155014180103451451500b80b00822400c2070441420211422514003402510016401281c6686040032290300031801d0004070b0701c21756400c80fa182c08942c15032812400409807034100b078468034540300400000c0310700000303d4030b55910241c07540340360440818045441c42c400d00100710400c1c0754011003045043c2d86034005017104006002918842c41c0c49151010303a0b50071a06a10784c0b00241002840000b240602c10074107a00701141052281e4000c100d405024495002030b4144016514012650310b04650b61248820340003801c0c00640d1030008070700055449040d070280724164090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 617586043 1250 617584793 617584811
    0x30206150607030f0804020103061707060909050f040f0c08061003020f030c0f040f140a061e064103090c010e0d030e0a08060c0301090b010f08043503010603 69
    0xc14010741c0e9060b90f0541d00c0c1c4011804901c0c00b214002c2002c0d1049042c59101d02c00460000480807010b0120f411f00801045001c0c5407440c014480c0da4aa40314a990f039280605100c0b0980751800019489500b00881c81c0f141450f920341900d0381b50315540607030380f940603100500c240c500314100220200c034000c803050300519603044101501e070f00c3d103d0880c0d9800361000081c00403904043e00015960703402050002814026940c1c1d4181400c01112890046a603500091068441e94024050b02c030142d01d800100707007800d01034060210000d1811001d502039040c00c041890f00c0c00d00580700c070301406d24281002c1c0804029011a1907810a0703403c042a4000c40d00d410280754428165010719410040c50b01e90b9841d401d0b201901d910b100410b107a40c114101060100329803908001250080d001903614681e01d614100d03d1000b00ca500c2203100c2d040109480c4120421a0700214041d009074001c000d545404040c000307202c00c45001c402c00e4603010106142d03c1001a0340c4200a10b0480d07207240c805000081c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 617587293 1250 617586043 617586049
    0x4021203071704090e06090604021c0209041127070315080a030e040509120414060c0d090305010b06071218080106180510030c030f0816060b030c010f0905010309110d03020615 77
    0x1104407030307d401540c0304000140241c64480d182110310581d80c108068170004d90b8001c112070440c215410b0b90300300c03c000341005050030043d200c1300f408807000201440c040c866002040c2c90110141c40701701016111141111100580c140322030061642400704c2c0e02d400150b140140490820407030481c4517034a407000158080318041550250390722108056441c040c02c00a4801e40c2484c0c030154103402840c24010303d00055401c000300303440c0c0c80840d214644518a507140031800d4a5000400318001c03d0300740420f00c0045c510708108856442c8905100791a40e200f00d18800c25940742d540b01e4016036003048400500303010310204440b20301100c00c80a001c103035220030010b141480346100041060300d4102d001c001188102c1e55038054103104810451401c030420314040c081c040f40a03001d90f42150750342010700c0e2a1138100f08000100e2400e08010210b04030a5501030030450180c410a4103041d01c4408400400c00c402030014880c580041000d08400c0305824000c0d41d8802c115040c191820080e411041c05203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 617588543 1250 617587293 617587303
    0x9051c201c1b060305060a090e032101090c030b1e0d02090c12010f030302070b030a020f030a1a040c02100c0c0203030c1c030b060a050d18150f02030402030604021203071704090e 78
    0x15806048400400c0c41d181c4d001004049101c03803144940020f100c0345542038030f00220200e8034100d43c882c00bc10b07075041078030300d9040741c00e04418031040c50b240c020743d14407035185c00314080904034048001300c804020450110352180500d2200a5105030710740d0801c1804240b50001e0700402110302d01c407030341c0c40c3c1c0c0b44d40400040f00030300d002c040c000d6070000d00c081010004200c0119404800880054146013a8825802d02394005030b407522135083c2c0b24010800d004000c2d04220f071304000100ca0a000480320000040e45480c01d800e00e64041c0c64031417000f010745502990f403251850750b01608596a0301d1044170019140c02d1403001d11110034190f1032498481d94441c0c042c814054000924075407500c00054000d4441c1d5000035074807001c1c0b40e241d08000040040300400c0109a5004108040884140034403803000c541c0da05a8000103240b0504c18800983c400041c181c0e0f10039030584054a034810545095071a40c024158018805511720511003542a5410041c00031100e021105020240410441d503480e5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 617589793 1250 617588543 617588551
    0x18120906080121081209031c0b011d01050c0f03040504050709030b0141090c1c050903090a060c110a030510110f040609051c201c1b060305 61
    0x3c0ca100c80d060318005080ca0f0440398818468156146440480076034500945c60496030710300c06400104180d10005080c24040300b07c03446904003003041460b06000a0021032018001d0b920151074484941050f90141c4202d645040e400d808541ca0401001e400d40c1c4c1d00d1380607000b490700850610380820a0355009a14002c10359a001c40b0b00061a805d01c03c1e031000200d200c500d4802a4200c00130510b400300f5120504030407408045400d44c42040c0303d0400d0040c01c2c5409007070303c215108100000c80504035926070032003010500c00b901013915101c800d841440c44c02040009680220030313500c00070309d2071703000a030b8010390911401084c00154031000c00c00400e0303500d6200c0074006401c6a03000e450050030541c00740854560001185060101f500e140c040d440d04250040808100c050100340450318088800706220541c40384403915507116071742c4100380e95540010411076948901c1300315480f03a4031415544d084c001010191130b4407012900b480e050440040a14a03c3e5848a91000c100b60380f00380102881 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 617591043 1250 617589793 617589809
    0x9020631091b0c030c080c150c0405060403031103040902130305060108121207120606020c011e21020408031612030c08070e0a03120c0201140418090501181209060801 73
    0x800701d0308000582d10803ca5040440030002400040c0b4000b0b2084006000341555520040c000b40280416044040380054101851000144420416030351124111804d0780d40c0740c0741209555011700c0c0440c1c95406a900302c8100e00b400452048155200c0c00d506004481c0500203c82c3d140c7d988106a030703144d0303c0030fa00d49041c0da4400c0001c20411100180901d0708510300380f030310301c002e07004802481048441640000b40140c1180901807941c3da030240c00340451607c1640c0200140182030800b03089440021004e03586501100d250f1078841040d541070720020505582929541c90312400244003ca21040085132244690b9000548503032080c420021200d4454a82a0817a00c1d220300940d9480341611403540d20404200e40030000404404403030344040a183c851110142c080d20014041a511a00f080c4131310200303010801c84404a0b52550554404400300058154003074286580540102c9040340e030400040003070759003000040080030082408996440b403801d602d4803000c480c046020310031048 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 617592293 1250 617591043 617591081
    0xb13060f050409020102030d05090f1e0a0311120d0203010501091e05060d180b0f070c0302030906160f11130903020c060a0315060806090c0c060a0902063109 69
    0x5a8281030f40034200e10340c01401120f0608001e8520310050394000c80d00710301c4035005014483d1881e030b001c1240d035508190303c10030880c10780d40003c000c944d202489500641048502168402e0070003051000d0a030100c445000d040d561400741142c0c2000c0d510a1140c00d0000c0d0701b101d00001d800b900e4181410780000100c601300b128500d400304105d01a00441803950304580e4a030301c0080c200320440072402c10709101790510141c81c541450551103080c0010444810700880700c96040010380c0c084200c6000d40e00c1103031240e49034070410240302441207201400030500f0100e4500355080c00841e0103014078440301112800703c400010140c240c241c80b00184000c2c0960300c1035115051618015000d40030010a5142c00114610700a00c0c900d81420258840004100c018040c0016401c100311056889044040d560b481c0464000780a50754100003441614447d55400401e41155180c5017269038403440d190060b6283c0a103201c01403098036074000d0005404030382200024513015140038040c1d0b0f0010a00c0111 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 617593543 1250 617592293 617592299
    0x5102606030309131508010f0501140307170a1202060f09280206071a1801091a04051c050406020c12061f05090f0a0b0f030c13020c0102070302010b13060f 68
    0x1c407030030351403038804c006240c1c075074484040400600301c003400100358440002ca200b08100034204222141071b0484000443c9c0700c1151409034800058100403960800350762031400c1e030200c0002c1c0c10010201340080c00c05200f021001d000d590b000920758061011041162100d8036040442565902c14842e14499080c0a40110f58490410a0802076882c00034001c140f0703028040e90344010b4200f400030b0b110942040700d001d203d40380480100522054802c20020060800151900e2112800c03000715481410b8449000404000041c84042240303100c0210b0401e00302c03054540a841c5400038002c080061142901c003a031549481c6402e406480e03400c0e0b01502079900d4016260350803914115410b40d04d41c1c040c0900103174640324003031900d104000c043c188605030305200c0900c0e400c0c0c6174907410303440c8604a20800d0b40401d41d404a00203c01e0b803402c880d6480141050203500011740252a42d07040d00c2d520200d00d0205154041d000045080d0007107405420a803110008031044486c01e00440600540c5c1c64414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 617594793 1250 617593543 617593549
    0xc090420031204031a010b09030601090b0f0a170d051201050d0807050a05010f06170d050c1501081c090e150a05032d0a080708030a0605102606030309 66
    0x840d080c6001c1c081e6840c106100605000396446580308030765000c440c218807116651010000c82c050a061050985400c0c40b00b00080c0e43e5110600689000a56941542000c0d07a00d011a40c480c3c044081e0504440a03501d43d940c010810901140c002103001c1d0a0101078103a214408880c2540c52800003983d56908190500980c50b40f00c007811510000200040710100d0400c00006c2c2105215600204440203a480000180e40c280d600101544d2182c2003008000080460260382400700b502d051a00e038000060200d02e401d0710502d1083d000f000307c00011514483c0491642c840750010840c1081600c41144201c03040c41c003170f100e010380042001c00820803002da08007004500c640f0080910054a403180002800c1c40d9240c0c0300c02080c4000054002c0082c0140484819035040010140405a1503503c0c0c6540611440e000100310080000000d0060100d66010b18050305014000c0c217201025588080d1a40b111002408030b00c00e81401200e04a804044805100c2e01004c0c020b0750428440c40c6c14 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 617596043 1250 617594793 617594843
    0x8030918070c1a01080d09060816140f07061a01021507050f0c0c0a0602010c0507110406080109051510030f02040504060b090c1c09080423031c020c0904 67
    0x81c0c00400c4003110303241000c40c1c2c44900314580c0d00041000d03c0490f500d000740031460b14405620b0324051002101c010048207420514643c1e005c400e03101c0d840d00f0400c140c03030101c41d50207941c89100c024010104000016100e14400f03807500c40d114000800c58042c484cc074007100b4502031940300340164840791402e03210202490301690054054100b21b824210030b0301036030358031b50010081d03001340d035000c40c01426046c81e00745007001c0200740c180000c0080f80354040300244184949440034001c0b01c07042c0c145140d1516580d0048c0300503e07403440208030a0b0746d14941141c58240a0000e100c1825088011a4078800840e0b02e14044a5100820740040c0001d6420701c0080c0c10010f00507a00140e4411000903291204044c99105001a0108a94810841b02d050b08070035805060652900e1a00440d0030002e41681c0885042d155040b1003081c98001122030b114200c05a8a012038040c041e8881c800d100304032021500440440f281c0030385640d2041c400521118010444000c0c01d1780385141a2a0010814508 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 617597293 1250 617596043 617596051
    0x60f09020a0303120b060307030c3e070504062d1202040504061805031b0102270a030c0303232109280b07050c0318060702040e060f0108030918 63
    0x1c2981d103c044c0008070243c07c02c440d141e001c13039196050034a03c00d501c41351010301d2a0b09400b680c0b8002c0b04400c2c03014180d003140c040d42080094000e0b10341c9150304041001d0b030010b010040c001e00c1f00b591900c022540580484108101685c0d1012000100c04032102002040c1c403511341d48108414000d8007004060180039005032002ca50300d40c4010240000308001505040c001d4004659030b44401c1d09188282104a100614503407050241441444002030845006501600c00480d86002200000d4984040358001007840071240f800008040e00040b440340c8640f40c80d9100c030440e5000c01c440f03c403344101107008000002050ba4042d1a02002c0b030101c1c2c2101c0301204403000110648140c204443c07031540f04080c0c080301c48103050304200c0750309032580e480407241c03034980d0800140721400f69a81c080c01412020721100401030802c1c0b9200d8006a805064004009110201581604d65281d600c1a150340301c0c60400940046a20500041140c11080700a8040314299400114031104940050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 617598543 1250 617597293 617597327
    0xd1d0a05150c0f0a090602060709060c080d1104140f060403020f010c0c05040c02030d2d050c2502010e03060c2b110a02010615050406110a02130603060f09020a0303 72
    0xc0b0414400c2c54a40018011415141e1610385e801400c0ca0750103442c06a00500d00341c1048504117060140f42c0c0d03c8004c6c1113501d60b110f003030075465019216284000d050310440d0401d5401d400328001944911502c4901000d0350242e90400d4581c40640602155204501010790400c84140000740e603540b00d02e512039074180c040d0000603011910742c400030301511401c000610041c0c0c0040b13103200c0a0040c2c0e02c522650046001c1d464020b400030038145c42808801805003031a000d640f0380001e041481032000f2503000b170303c0601c0e05090b000402c14040251031a40f0700164000307004803126404500700020a01d00903500401003a04180031001d0389207000c0c4564048407800c80c51146422000c1406009031555500018105910344a1005000b800c6820aa00c4100e0210032001110b420981000456080e1141498900307840f8002199041c03030440d000800a40007420008001a0b100c1c19901c208196885040700380703ca10910202e00090307601800000e0b62204a107442040000d0240c8612206110f0031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 617599793 1250 617598543 617598547
    0x10608071d120703060f0c02120a091e1706011a0714030a1116030201080609040f0209010b03180102041a030619120b010914060f12030d1d0a05150c 65
    0x2075000305980c040d4440320b0894a81c010303a000d0082040b00e004070030b040c0b07041e0a01004160561403000355203104040002140f01e400044190074644505540700c05054649010176a0300948184441103040d14401c132407189100701107041e14100013040700b0741203804000b5070840403020124a4800da40c4a0b007000c84840032006100301701d801052001d000018500e8580170303401c0110075a040e0601d000c451004810b1041c056040c0010713a00400c48680000d03090744c00041c5030782d032850100d18039010040042c0d0b002068100000360000c00f40c000314410607006e06810907061181c01c40741c0c240c0c040c0b80920350440d41c4240e03500740d4030000007001d907a001c0c0d8014040c3c03800b00058611421450425008508500d40c1140307202c0c280903000c441d25004012829040102038010301e4030141242010301403a103e1000c0c40312a141556507200a803900d12103a200b03036a5590401407001008004440142d01c41e40c2404880c603845140224803251070760307042009403409010380d096010040800600900c050001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 617601043 1250 617599793 617599847
    0x11030102070c08010b010f0c03080c0d0b130e1606090b180d1401110414211504050f1207030f1b03050307080f0c0f090d053301060807 59
    0x1440c542e8200800c5000000035040c2c6a400004100c951081100424801c4607041750000035481000140c1c0714119941c40c07606c8850900c00c0002401e88600119032028100c2c00c02440380005511503280150a441100d480400c2c44212040c1d01c151885502c001c507030324000421200142c60024003280207040b810100c10b0401c9000502c490460180650300b10b10032031003002d0700100034445c0c212216a100d0000f800e092404005101d4884100210fa0181c44051804004000201d5010302c0c62100d010541d07042c0c082840c5440d006c00000c0310155010300c50082c580d0440007000c90000103601031521441d00d01280394800b0398980003250420341c20072011200b50403804880701107103440c2038800d036101e56913802e00540041500101a06100d50504074000f03004840d05084103d0321407a01559000362035a92000000700104900380740680103000c2c115511900941e2401c4038a0082d200b0f824403640e4000040b07a020000c042401802c01040340035010902003801a8020044050b00031461010542d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 617602293 1250 617601043 617601053
    0x1f0e04020402040816360c03060f270212040b2208030411011107120203070f08070e0a09050604021c0501110a0311120a02070c080a11150c06041103010207 68
    0x1a94980b450b0120000301d80c1030103002d500403a20a90705d4110710195540241e05a1803c0783d0707040555a062545a6510b16201c1c7c060181d00040001d003041c0d9103218007a070742c1d01c1c01509030b10314075065444284c96043c3c00c0501442c1e1482130350486c8003000f4048566a0b9180d803050201000586038081c0e0042e00e818000510007107a170b800082c54410003250703072a1304061038110034124894007001e060000600005202c0040020104c040340c12030f10380300c2c00c1070008c0e00220341800c820740c021004c4005603110108441c1c07030000c0d607103040381c8a000c2c420441d6540e211003c0304860070148000c09540101c0007203030241c1f8040207229103031503001c001507002102c156242030848080c0c16591109802c041104204550144104185a1000c01946240c10300b4200740031441000140300045566000c280402803005a200c070401a003044002c60f08508440c0c2800341ca42410001301c0c520404031610814850380d250380a0b100c0181d4202c0040c9a65240e5548480d00e8104030401181c043d0b60034003806c40412 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 617603543 1250 617602293 617602303
    0xf0b07020c040b01080601020a082a030c0c01050703120209011b110108060a0302010c140c0307090203190216021002160e1008030f03240d0b0601081f0e040204020408 73
    0x108a40c00034a40780250100744010b48125442440c1404180010002c41e42d030040b860600b016030009107541d41c5e030b002d104200307080c46240b000040c1d0450061300501005800200078002010640100d0307034610b1240340116541d109030030000300090b001d8992805448020340240c0172021050511031180503601824205a00301d80500ba80d94a440000694117540c2000141d0303045002a078a4005942c110380000e4002c500d5040c0081c0920f50000141e015370b01c1c280030441803094001c044d290040c4da242c0041019401c01c2d01d041c14020451050a07007424220b10031120003000b02548031a084c00c0d26000c01141d54038441c404020750041a240d0020340d4900410427010742178440003400241406081c1c01a503d4036500b1640c5113510410219119442c0070741907035484580b1071800c20041c107001c0d26505000c800c20402da80c11180e500da01030100042c10089a200d2142a81c07803840e00c2d40d07040c100c080c0060195080c8010385090782c60a10000e110314200a0f805400a8400f515003651401a40c2c609 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 617604793 1250 617603543 617603551
    0xa0e0d08032d01230d12090f0b090d0602030901111b060a020a051209070b04060302030a0b0a14011409030f06040201120507090501120905010e030405010207060819090f0b 75
    0xb602c202c10003051180c21807441c0c03103105080c44100b107a15604040c105205400b00a10301140c08030303201420826a07603000c0b1302c1c1000651046e072043c80e5408104016004070050700031003418114006002ca5010010000c0d10503d0304010030b814810681621a00003d52015003c4080e82d52582c6040c140461842c00030880340c400e40401c00045070800d050315040040c0a0030079000c9600400490848542c46029581701c2c1040351482c101c56228007041c00d240054562008080380004940014126010b0780910b22511100a0900c03155a9090400680c104540140d0400000000804555520a480d036200725040a492140703403c41042c001780c078003484d542c0c0c050701c25405082008115603111810010312031502c10280070906244070090100d000c2e0703000e03290400060003401068118580c02141080e5003010080256071002a4203503101d900c54000c003400741c4503040d00055500e21808181c1e20a8500501d002022481c1c4001d25001c0d050310401a40c002082034950350106040191250007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 617606043 1250 617604793 617604811
    0x110d03020f0c06070206070b060a03061b0e010809060c2505030409150b070f03030b13141e01050d050a0b09150604180b061f050408070801110a0e0d0803 67
    0x100070300c00388500d20380024034000754010301044c010100141c85501c1600e9180b070744188481c0c1c080e9511004034038880903540c00070b011107081c03c201c40b00300525000c00c00c20001d0a40d40c0c90f41092140401540d0341c0c41c2c00d030382900e015403100340000d510030400070140517880d20f00c1d404036400d04800f0040d082140c40d0090103650301e800000341005181c8041c42041c002c5014002d00d20316580c505081001680900407001d00b4100060711410704040c440d6000c0d40e0454002000081d425220b042250020042c02405d1030f0140c1c803c0010609030900350381d103c1d406208050100029a08100c10700400408000044802e80305191041001900c1c6039205803043d11030a004013541010f000107482d8020014003094011440d01c111140040511003044074419003060005896031030700d90200310000b0702c00c0e41418150102e04030001c80d503580040180120743c440c00c12a007003103449920140c221240740490f04815001041052003242c01200d1140e8024801403409d10041c05944500b40564011140414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 617607293 1250 617606043 617606053
    0x4020910120f0201090f1805010807180504020d1a07020c0f03030703030902060910050c0129310b03060a0b01020a0308040303020d02030a02070204140403020607050d0902030f0c0a1d0c0304110d0302 87
    0xa0344510321310030030b07004082442c01000030910340140a24417000c43c8203140cc501c0c1d00ea4002400350f480e001c10f000d44469008da2000b918049030040f242440000f40d51107001402000d07010300c85850001581c4003c684000d02540c9090f0f403c1c0e07010341c000e0030442000c07070300001700780002225035a500c5c41c24a9030b050683c84031541c8a1146800d14219002030031240c00d4141c2c0e0b19130624103400c45803c0382c0184081903a880c095800c3c0c403240310040001743d03580004401140041414040322513040080400c100345c0850300203454120401095425a003c07141c0140c1c40ba110700804280f1402240c0e8009001e400d00500d0100c110395a98281c0c0c0c011240310a60a40000d403080441c00e05124400c5440644d040032251800c0c650341c000e4545402a10f02800c2140c042400f00c500e45450703100c003c00f940c0c02811202c810109140c50764640c1e40282c3d2044c419040c018001950035020b010281c0c990070403c504c8000c5940d002d9049402d03400150099030b8400d091061440652103010110b1240c6010382c000341 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 617608543 1250 617607293 617607329
    0x309051002030412030e130905010c0e04110304080304020121060608010e0411060c010605030a1b15020a0f0311240115080a021b070e04020910120f0201090f 69
    0x1258240c0811121801c40d4010081004040c6a158114804507850b240c0007014241d448001841d0001c040400f0075800d01d0100c4800030048158003030303003001e0b20944641c6900784003807080100326604d85900c809403200c1003001800082d8a00000c2d603200d4814140203400a40400b82a0030624039007200d030402654945081c00b106401405440c01040701c1c0c03007120b80e185019a12044040d90b00c00c4910300440380800d00056202c420f400c442c004c2d10700034080324403072085420308011100401181640100505902088580b0102c00025010101ea0004c01d1510225035038022884003050080e81040881190004103040901550350040700e401c00c11000b49500c1d111009030010180e1042d41c900c02054480518290003860b460340c4030401b440c0040c1c4074001e1441510321141089402070242c001c8480c0400d1041c40030b40b186020764025200307400b080c1d84550340041c041c00c40e4024100300182c50f180d0000010152218400d01c0c5106143c10200f440e518101402e2510030b5401110400404502035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 617609793 1250 617608543 617608549
    0x6120f0906010e070512040c150228020901121505090120031005120120070501111c020d0f061d0a090f080f090a090c030e01050f060d060b0d030905 65
    0x7190142c0306140d51040395042030600609a442401181e4001c4410f8100090510140c010850000c140709030015122080d90103009444140842428000c102503558882403c08280c52800c15560b000e82004180d90a0001224035441c0d000400c4401d13181e1500c140881c03030503c0c0542409440c00b1400030a19401d44920076421454040c1402e00c0d80310240200840c008001903082c08072a0203880d000442d403d0508581c0c0907010241181c51505024000c1b8107084100d18010000740d40076500070440202c1c1080031840910881c1c0b05501d119551502c11256001198010610304000000000300c1e12102081d4074141c2d00203510400400c00d48800d141400b40e000e44500f5400120701c00b0070030480c442503075200d807034020300c59014162040100e44a09404050f01c221003510000425600320b866503200d910019001c004100c1c1d00290070306045d910b40c100f0500400307000b1903840c03d445d00c1554a400c140450051000b0302650000d40300c040c1ca800740e403254000b618046000e903a81130925802c00d024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 617611043 1250 617609793 617609803
    0x7120b030d2c13110c01020403030801080609010c300614040b06130b090a1205060124090b0d1509090c05010f0e041505091906090603021e06120f09 65
    0x2c00c0c02074048240b100340c038542da41c1d1207401c0ba01d510404001401e1101142c100500d004030010540103620004011082c103820810141c12114010120f801c0c95460030700c0603090300e031a1103040012941d0250410a4034180c10107218211010032041004007502030b10032400e0f0360090703000b0002d01e480c1958144807070900740105440420255111858080c00343d40f1801110624071981c2d04c100004030302842d045d511103207080000d060351240a0b250345140d0602d030703454120038441e080c030000c10340c106607007800c0001002600d8842e491303c484402500e00242c0e189140c0c04420403881055440ca00c0910407080c0d001e00b9009440a00c10000b000c64040c6000400308540e40c00079070601ca289104044440c0c0e000074001e1010109880119400d0f400c1c0690030400e040c2500219402080c1408100804007016603d125100903c0c01c00d02005550345000b80c100c58081c04065080210030f22014020003181050032030504024101529103076800c603048806100566404200c01100b5051104104d01008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 617612293 1250 617611043 617611097
    0x61b020c010306060c29040302010203072604121206060207140103050603030a18170c210a03111903050c0607081312031b020f060c09030607120b030d 66
    0x2403c201c0355040c031001410380202c820006040b41180b42580c401d9000954480c9201c0f2000c0240da1507074205490042d020390000c9030710030001098054000202d900c10449034025904030040c440003601c568035914806000880c004052000e0103100e581c000b501d5208250052480342c0c080c009081c148200039110116103850a4101420f0100384132946d42d010040344c03424000c500340001911110007044130710011651150005590303d0b440c1c0b440910002c501004216421955010440c95240500200b00443e4400100c103920400c17034000068007403e40e59000403105400ca4802c441c59200101d1032010b40a0101c00040740440e02801c0319504101441c4c10800a040c028040d140c01540b900140c40540005010203864560300c1c10824040e510604552405502c0d0f0f441e02040d55202a6403001400544034aa10034580015541e0031280300755801020014041c001507203e00c50200e845640e0380e0f0900c880326549105410441e0760400c00021056510340711401c02400622101e183e01d50111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 617613543 1250 617612293 617612297
    0xa0b03030a0207140a3203030304030323012106090b07020a05070602030414100e030d05090a0504050103020303220e0f0414031608030709030606030f0c051f0e0607061b020c01 77
    0x1135000c0c040e00a070702840808140d808000d2540501b030070590f0100b000301500781141c040c04004180001d00d0790541000070f2805000301d01e456018582440c1d4a4110401d10909515152445810441d1000d100700000e86c20b000701e20104480300300c0e403900841958180c80100242c1d101402d00020880d01303101003c018a1b281c0041c50034140f801048050303080c50302c0b0704c1d14803070340040d11011200381c0950404140c0307010240c03c50306003000070b000140403a4000b10aa03481811081c0e00016980b07041d0103018182c81c0c0c040c4c0a1410701e445034170b4210101c074000280b02081400c400020a13a1003a49a0140c881d42a01007002c203903041c142840490008200c1c485441078104001070000100105441c505040e80059032507a2992001404c4032100515000205a1070030f21900106101c544d5a15480d003600a14440300c1f815500c0701080301d410001a24064107124142d0040c17140707070241544c00d03090f42e400781c6014a400c030260f84200c11901480741070000c0504c0202c542c5045d0740c0c10052155400350078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 617614793 1250 617613543 617613559
    0x50408010608151e06060f0f0a08071e050909040602070206181804030e090c0903070311031209130504050309120a05060714070605100b2b050105090f0a0b03030a020714 74
    0x1402008000c54008007058052680000e1f04040100100116502a903103441a01d885a81c004001001e02405403801310008407411051903902e8540b07030100c07000c52115115145000403440503c070007034100800549010b0b07828030641d40076807100c1000b42401c514004011200b0f55100040089003030805030a040000604401c003c0003035004034180c407040701e0803146002c040d40c0b034a0301c2e88201c2c8500400503425000d041000401c008074000d1044025200301d00341c4500350315a0058111a00504110341c5c0c0c0f00100e901543c03403482a90b440150800e0160f402e40780343c40445404034248180d131480c614007540c4090904c2d001c0c06018003441e50010018a001c0004072603078801c11030329014516001c0c0c0015aa0700120340141c0d1035202010040c4250707540c80b529005078548a01d80000440b5001d5407910461640c609408114424981078440082044000f5141c0c0c111603120719000030801c00c122070341c920051580317a034100003400fa8500c9603401054604d080c20007400100c0e101d206110700640030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 617616043 1250 617614793 617614831
    0xf07030e0d05041e0f060c05011109061605010e0102120a0c030e030a0e0301200403031e1202031302120c0a12020a06111002070b100501180e0705040801060815 70
    0x441000c031412644268071100403070b00d0484c8074016100c8954400c50042800160001e0011380049150f40034030300440080201c00010180c010f41c900c110440345502c0102001913011001a0302c8500401da4040c000020300e02d40398040e41800c99002c1c150341c1e20a80800010420241001e01452032100e0309841d05001c1c038040509070540c0d03030290511440a00c56281415065503e0943c000b504207a191484654150408004201d0580c0030740401d80000d003801c2d031404405202d8420800710104c01e07a840381010400caa0024000b5040a441078800580d00c40d44000907a45d588080509440303800007070441c22010804101300004103500c00b800051141021101698698000c601101c2d207034208403000c2d00207407809900b0020a106004041c0b07201289040c103120142201e03921071600c8106408007291070f900196140d102c003101c05c0030a045609018000744400155480e00000b1a0034442d0405840701c0c2d8807800c0d41c0300351b040040c050b4440400d510854032490074403500001d42280200c02e03404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 617617293 1250 617616043 617616047
    0xa240203130c1e05011103121e0f040b011221030605090106090b120601020a0f1a0615180609060c010e120c030d0509030d050106020a120207080c01080408040b030f07030e0d 76
    0x40c40c0c0c41402d0612601e511b81c2c0420140600841d103022640050080f0285440e140c2a48030345040703500080b024501d08000307400000800ca9050180341c00401d2554203a1130f18480c03451810320740343c04803003495107109191b8001a0700030501413840c40381c3e18080341c107900705010710032030060591060b07081108209041200c0b40000081b1024188203d200000c01d1b84d070800141d19101010070f00070300030700f01c41c405d0205016220b54000d605030502c6c00e80c413400351600c8040040c000004031800c1c0b0004010403000110450500100c001607201400203400d141e020b20003c2d03066000240030400740d075141c0d01d1038045540b09001503100d0f0110300486030b0910300700602e403581d680220607003140600da0300d40100d42005410010f0f503850100e151010300c4a5030311088000d40314a070b2020b00302c555280000c55070001d00d0020600c4810b03658524021b0000481d2035004592840c2e0140040d0323511942004046505a00c140c001c1d07200c1e00c0450444400c60401e40300040c2100d0a0840a68440d0800403d501c415a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 617618543 1250 617617293 617617349
    0x20304030f26030a2a18050d03090914010501080601050a021216030212180d051006121101140a0c110901030305040612180807062a02010b030307050a240203130c 71
    0xd41e8a0403000c40011040d0b02c2d82d1b0f4082c290040c2d07500c08a013182c0c19041540c4902e081c400c0e925042010b11001c0032030b03807035507984203030038061280071603202c10016040c2d5102c2c2c0064114400c0c10310407100100e80a11060542d41c4c41440400700d041c42281e020803d15404010551a500307003941c0c6246040e06c45050700241c1c4800704002e40c4902c42c40e11b4600d062102c1080220050380c0a10020000c1640d02c02a040386110001000c440d40501d014140710150f020f00307806004480010401407901079107042c102c030003200d40181110311034420080403078a9103400d0714a9000c1c500c0fa0300c4040d0385030b05100c0040e0101007d080e036541c2a50520301c0204414200c070714161403596111506684070b22441c41d10a0250030450110105034814a0001102c0030709040c10210500d802e8008000320708810b0117140c0c481c0311b0b249020b401030313009443c51000a216a000c0c100041c02446440030010044c0300540b0581c0d000303031091101c003040007501d00c086c4803580c034420300204185214200e4940071109034003814 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 617619793 1250 617618543 617618621
    0x61e0907030c020708060c0a030c0516020f030a1707061d070e060d060e1c030e060c0f0906030109090203060f01180507020f0f0714030a03020304030f26030a 69
    0x260325003040e0b52929008014038805864032109035040da103041560380c040307500528030040c00079080c000e04000c501d000300c040302d100a81400c480c1220203132980074400e06603d03103c0c1040e05445407140c4500481d01d015500c0c4c08801c030075080705036190aa070400d04140d400f64041320b4440c0000c4c01999044180001d60403007207541c010141029683d03900d0000d2200f000000c0c02618890400c40481e440000100b400702e204810054005d10b2404520307804c81c1140c08020030081a03074003280200d01c200500c80f000d8a049280443d00c00d140042c00d1001c18490741082c0d014401190719045260114036041c80416484a11034048001944c5040040441e09881d50300036101c040e42c80000c41e50b020310030311040008100700f07011144080181e207456a030742c41d1280324110240410f07400301c001c1ba00c0e000c1842034500b90181e00039414141543c40d0034400d00305107502202c1c039040e940945500700c100741c181c1c600705c1d4200010301600c80c94100054403c0c0c5003c880d05c0c603414581901c14202c5c81034a07520764054 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 617621043 1250 617619793 617619797
    0x32703080c3d060b030901050f09010605061b0109080c030705100513021c350403020105091009080106030f0308090a0308131b0803130b0f090405090a0c0e061e0907 72
    0xb1420302140007000604043c0c2180d03541200000820035200d105401883c003515442c140d800c1a075507240440c034206d42050042c2d42cad21020800c181703031001144000c0d405042c8001f40c000504031000b641c401c0503542c04011b070500c42c0d40020544805000050107048400c1c081e201051042c0c0c581007040318030300c007441200203100c1c4803988059003c15126135100c907105680f100c0c0042406c8041c0c507956802e1022008a07442002c032240310b90041c038a90340261802c4a40c1a1541414058200b003003004d01c041103034400c81000b00c081000110b0300d5017405600011030181211f00900003035401c00910001c402041815503620003845080069440180140d00c280320b551903c01404061406c80580f041008915903000201c2d040030613600c10200c010200c040122880d810110b50701c401c2c0c2ea032640035280509150745810b1118080c2814039800065100d4008000e0310324502c1565200d81a414007908186500e80003001003150a041060700c20050202d940da80d074601600d003000044c064500100a401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 617622293 1250 617621043 617621143
    0x415030e1b06120c071a0615090a09020f0c010921051206040c170405010606080105030d1409060c0d17010801060f09111306020607030c03020306030604032703080c 72
    0x1303100341c44020f1310b8003198010320080d888040d0005401c051041583c1441c402d512010b0100080104c990417581703841405024291600d140a128000a4000c40c52270740100300104001c03889904280b040d071140034410740c0c60640401000d541e2000178280c581c124000d04c01d00300014115011076080d955800802100c0205e5a4205030008607112810091040700792034080c03050000300f2406400103001e42d2070581c5c43c448180e80e00d03000c25540da5840c9402c40b0204d0340c44920a024034400e18008d09001708043d00c400d140080c2000d406207003810300b682c003100240180000f0384402c0e106606843c01814400c00a0200509001c0030702c11166180c8a61641a035540d25241c04c190200c009481040000451000c0d42e9507980f000030f512407000b10b80c0580081c0c600000441120300a2080e00e00404015000304820381d691398050f10108001848590b8023005407401031010301c5000c299002551264201e84d450b140703268030003413800400c500c40100d100b501461500340f000c1008498403a0100901e44c00b8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 617623543 1250 617622293 617622301
    0x20d061202030c220905030d0b010528020a0f060c0906050c2e02030f010303080a230402030f01151701020306030606150c06010b0a08091219050415030e1b0612 70
    0xc0f0104d43c080c030018001c1803c02c403e46060010100c090906020004014041007040342c004551620980c02d50200041c04400303000d10060640c8160500d506031401160020700482d200c08c0b03581c41c110340301103501e26290362201080d2a8408401c02c0246204c0c05c0190911410f002c1c0a43c503000c449a880300171000f9018006040e04803030055000c0e44000c20b1301150380341480706915070810350034001030740860b040c1d1340442d0440120340309503402c41c2e5101c40a22091804d0b41c840407a8001c1c0035001707076814850401c60070f180000a1251021044400c1d00481d14186026680342810350554405079043c0d00c10300030405151404500141d2003241141d0320300c0c0401e245c00c68295a07004400380b0b200c19202c0c401c004500d40043c07a005200000c5903480e91f01090f55528015030383d4003d500b80050110009001c1100f240000c00b19402d4400c0450810341e09164070303050040841118004a803001a442d10355540041c1418004000f050044100d20600000303000c0100d80f0350710482d00d4543e15030540300002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 617624793 1250 617623543 617623579
    0x11070e15190305030703091a0a0f02030d0606030e0d020106140108090a0f03023904020a020309040e0715052502010e04090303050417040e04061a03060406020d061202030c 75
    0x3060420050080803681d41c2d01d900380141c0e0303508003079801c030301080d918040400c2c0380a2070070100b500080c10045051528280c10812a040c0e1000702d81e2005501c824014846582a10b024080180c84580e500188800d03900108a107822000300c43c400039a4941541801441c0980403a200c40e080c0031301300001c01c0d8031b03600c8116249c801c00c60000b8107403030004011702c010141c0c0803920321040d80701c102e2500c610045036229041c00e4001c0a400001061481c0b10005941c1801c0d00a029000d6481c01a6400c0468500101c0c040c0c0b000615101c42c0740e040f42e84203101d00a83c20030070070071403a42440c00500300103065840010403805000040300418107801d500003107a228200300d09503160080c10034419010b42c2d1802901603d41520103e900500c02c46181038012081000c0e5012502d202e240d4012a440b181c40c1e850090140d1400101910704111002540c0d4030100704a6006500c034013801aa1524001f025404542030b6400403440d03500408052005039900060f06541410f04840045000c05a075010b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 617625899 1106 617624793 617624809
    0x4230a210201030902011101021305210703030503040510020a030b0a0501021f0e1e060a0e070b0417010b220605060726070611090111070e15 62
    0x100050740c46a04030701891313801030401030005030040072986d09a074490350b0400024980110304002d00d09140380c040059036000881410443c1103026050b0310303401e15202c050100240400814107010b0180400003115580708001c641c1d40c40e40c4800640a060403005051040715100c00005880d40045101359900d404100320402050b0134070509e000508140a9100d1a03103d41c1500050381001541c0c40c000d4072540034000c14a51402040c001c1c02d60310540d48410080e0480902013205403075003015901620200041d51315407400a0012030300401d1090754a941c020f041c00c50000111101c8840c52030b0302c0300c4240042c070819403510184451403103144001441c603000080202d440b0302d880000400c200c1122404070b45499881c0d15464286ca03036a244400ea01e001c0011004150f68100300c129000c20319800241810b03d1074002459160b4000810012503034480c0200305050381c0e92801 = true := by decide +kernel

theorem cover : BRFrame.Cov 617446043 617625899 := by
  have h0 := BRFrame.cov_init 617446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 617446043 ≤ n) (h2 : n < 617625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
