-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3482
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:47:46.051671+00:00
-- url     : https://prove2.me/submissions/cacf7b9a-66f0-414d-9619-33024ca77383

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 626079136 ≤ n < 626258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 626080386 1250 626079136 626079161
    0xc15020a11150103030c0b09120c01020a03050f16180e04050a03080108071214010e06070c030305090a023a1a07140405060c0f0307060e070b0304050d0807030b0301 72
    0x1015001c26007250800035036800d1200044020070a615685000700b030032030400c070014070025a40c00455a804010031411500c400c01c8410180d0b140084800785000b50b11041c041c1c00030030308040c0022003190090780668490346211403440c1c4034007000341040307038450a18521340c03100070f5440c01e01203400c1e0401140300b881603100350014019101303941000f514a05050384260001e51100300300780405144401a241360303070780c803110110408000f141114090030039064141303064413544082080c40c03648840002482e43c080e4500b00600c0c0c540c80e000644401880c0e8000e0b402070081c003a01144042032900107814042c0301d4140c80441c1d5880d002d05a00c00c404680d00752481041c203000d46107641c90743c01d4203036004505400c002c011608045092078090159200f503d11801c3c0203d0380c0c00c144401031042001c00c225a10960b513031100e003490110018400707400c0b0909144911f90001c1400d811082c01c40e070107140c201005080042d01c403c4110b64105006060300c2c1010303140d0f40210f8041d1002d0003085840d40a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 626081636 1250 626080386 626080397
    0x15030f06010e011d163006090c1e081b0703020313080c010207050f0f0604090204080705030307050309100c1415090c0105030a020703050913050717010509070c15020a 73
    0xd0501c4d01031910300d843d804072410b4503032082884484002c00c407889034000d4803401c214007004408142034100301050554045440b80c03560701e965400e495540000c056444240003041901c01f8643c045500c1c04101c1d412000920101c4001070207140036014960b88a00e06645076240c0031004c80c041103180d04040402c074050303072011441070390310040d41c41710601500006005140b002401e0b00000d560388014032a80d405070720800d844001a807208140380d48240005010710744d60b503030b0340e01c1c510000f54018800c101060240f07200104181c50084211061300d41c2100095040130303000010450520188080003092024117182c3e10000b0702049016510700d14140050204901004081703240880020700566860f044410304103102d80c0c004044d80c1e0040343c0c0307420060316940140b03030a071264401d90304400d230b000d0039190700840708c3c030b0080e040303070384508003550ba03180c140c101c50a9a1060040207004596024403440001050765214891041c0c00902820540c40a05540c502c40e0b4100d900100f0700308002074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 626082886 1250 626081636 626081639
    0x1060b0a0f09140d03030e0f0d020a020a0902031b1303170c120c03040b03090a06111801080103020a031e080d0b1f0e0613030501020a0e0906100815030f06010e01 71
    0x2d030042d8540d8010980d01c4080a01021444005030b920b04038000300809040d5551a45511076a00300a140c0c001c03a561421150300884065000e9916118010201c0c455810381e400440c0010071070007681d000d50081d4840359144600d102c00391480390400b841207403080400f1800007011030301c40d00b90711402c11803040031155031f40360200b18281042403054a0700c650000400100e002c1e580000b046400311642d1100194690315001050360600011481c060941820b28205281512501c0018001000220000c6880c81200801035030081c000b48000307540820361080400c0400c034941d6072130003c8003491074000804043c1e0b0b40c40d0742c910f4020070200c2c0e5549554000e44481030074200c41c0301c00841c441c00034200b5604000303c00203260800045030b25008400205180d50011001c500f541d010b10341c000001d544a210158004082800c0407149070b208503402d40100c0d109060100315400001000d9540000300e5503071496002200c081d10715050303094425400311030502c4c2411b01c511750203455104c18181255 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 626084136 1250 626082886 626082917
    0x906070312090204150519030203030d09060603140319020a12080a200a090509063318011413140604050904050106080f0303150906040e030a030f0c11150901060b0a 72
    0x201c440780c587c000c440b40c1d0081c8003681d00042511030254415101140d00c51136850403038054460380c1c4c0300914401c06420080c5c6016804400707468031051200f147c600710019124101e80c0d8004a0001a250350f02d49032100c542240726103402540700303050040c08100c081d19030628041d10101110708690060300894605c00e4654040240001050101c6d080d0300a810103d002555111000750b00314203800d803600c90350b542d2103030036403190003814144030341c1035110100d060a0002d040941080580050800d40c0c0b4860140200d00a88020691240b03007001c03d241414101003580c0da510b02c806601030410b001c002039a42c1c406170704030700c0340380b1907030010440c54a800c503858944480003030400b801ea00140108200070f00e00c13103010701c0044401c980229180d141c3d0700204000340141c068510b964000096103201d01074164115000c09100441c040202ca02825811541c2c0c1b0301510328031819401003c6002042c41c0c2c0440c440c3d0700400003c0000a802c0c1d5125007102d929801111400d010034502240c0c0c0141 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 626085386 1250 626084136 626084149
    0x2103021c0912020d1202030a0b03030309010209030610030302030a030510080123070504210f02120d1103040f09050c09060a0810050406030c061b051209120309060703120902041505 79
    0x502d01600040600d2a24424054511106100640d001503800700000b500c1d02c10507000500e803000b020302520350300d0400121a81c080d50082001c640a40b041901140d411261500c424045073b270594083c6080c164810b03000c501405c80a0714400040ea440c0c9000b2a0001081c403d044040030308000341b4015066100301a80c00c83d82c01010341040c07100c140001c0192600140c0c1c0e0303403114800520310b1401c404640c681082e040124030000394000380c18040c900f02c02c1c14005270780c0c0e00b0009140c490365600c0319406000740c1d4a200c4d5006919161684580400018881e904074642240ca09210b290504180b00080742e043d403c140d00c1000029009000d10082c00c22840b13103603020385001d41d420f010341c0b411754176501c90070040343c442c002c20080f0700121041d40c0000d007040c10601d250301ca03050b1070211106030700c8a41241c00110071540305000203ca25090607800004a980c05d4401074001802c10419440595035812034000c83d020058903551000b005946600c150300e00c3e0300703a04083d050018108400d00030b1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 626086636 1250 626085386 626085413
    0x121603120c090e0a06230103141005010c0201020a050f0304060813020618040e070603020a0f020a0b040f08070b01121101112e06080c010206090a2103021c09 69
    0x25803034500060900c01d29030181401c019a04040456106511a0440c450003444941d020540c54151011400d031a418140d1310514107600c01d9906004008034081401191402514000b1180c1c0c5002004c021650180080d1440180140161078504d1405d0b1202410228230800c406025000060305011954011510540010700c0540d40c095800e50f55020917481d10881c1c0d10081d000340705504c20061507850b904124024020303c0103035030304a540e54901502a40042c018900810762407450b0a0045200240c2e40c0751241d08407403c0191910390fa11240207100f50b0400a840701c00041040401160002c080c250080140c01c030000c4140b400c03414004107a0304034070700c840d040050011041c403520900041140e030540160506da122510400c044a02c03882d44251604c03645030904c403001030000d101042c0714940138001c1c0c09a4101d44d45514819454117501c0000400c3d0b080d840c240c3c8400d2412061a0168641281c01d0061800e01801048810041150010860301d511104d14404101c0080c11540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 626087886 1250 626086636 626086667
    0x9023903030f0406060f080d080a0209031606080a0e030f1612020a0c06090608070f0e1903020a12080403080f070b1302030d081b220303080103050118081b121603 71
    0x380b03281032011f280d40b12010090410104a030302d001107100c504440d4110392460340c1c0101101c4190300e0307401a10381000e81c58171400c0d012400d01000242035070302d1707401230400459040001c0c40c5446401b00704201c5d80d03004440038040301c100c0c4502840c0001c801d6500320225100c5900140840c0302140381540c0c00070810b400010401090a10802a0035080f2070030ba600000e940c100b40718600c0c1103d5003250705584059281d41d00c003100c3d1284000c52018180048140c0e4000d8030302d04900ca03100d450b503541c1070780b04000003440070368104420030100c1c000340081d000d500c41e01e00316285041580d0315a8016400292075030b00c1c000090341303000800c510741040000c0d421b0015061507480d515210441100a58100d1a4003440c0200040c0d0355442c2c9810000005032403d00305d50a01845449060080c4001d4090000f280c00390f1a080701c0340604029501800c1850b80d10581181c9004241003000444010545a003052803141740c11030121040070b00301800007407044070001c1b035854145040040803e0081036501 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 626089136 1250 626087886 626087909
    0x50f0a0f0c080103030f350117031903020c01060b0306031b100e180108061006030207020906010e0d05060a0b041404080706110f0313060609023903030f040606 70
    0x498459800c0b4201d203044a0701800c02c11050013079258103880d280d425449840a0074003007000c1f039040101d5808030394032201643d4200402aa2141c0c00514061000b107202c103c2603006100200810009491040940407145409030420301c69101071404e4550300d800011030580301204200d0142000c21001140c2c0c0b40b010303520140021032102040000080e01228400c0100303c5840054076202c00c0c40c2c0c540c40c1403804490f00b5156950b08000d5440b10310603224503a246100b4480061503a100c2d00940b620250020503035840d50311040019100e048120350155003015620680b0008034509001d524425200c104001c100450342c0d4082101b01c0d46400501c0304960380960a000c00b260065054410141d40864000b5107400f02d4141e80d142c600a40e4120700010760004100680b4102c40e00c100c40406100310f00c140042038880e041700041e4096604240c0040341038640070318600388510210b40084404008440021005c3c0200c40c2c01e42d403040304c104403803004180c24001001078a02c905002081c003040380 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 626090386 1250 626089136 626089151
    0x18150504030e0d0b150301021201170607301b02010609180506010509070e09161d060a0c030e030102210609010e04060b1804031e11030405010c080409050f0a0f 70
    0xf4559003c4c00a00030b4098120f04080020311520258104c80a500c0701011307004c034075a90b0b00308034103c1c3c01c480030000e05103002e2040031801103402110019040d0f260441080a00940a000c000705203000c0408506c45984072509140761403c11a202001e0103001e03400851030034141006201038036451048649411100c0403c1e0022410100d030340350641e0011500840592140750045500400b41c40616900c82c1c40b00c404d01406000138ad0280180885a4458145912464444500072a0300c0c9040c40d40001c000c01031200d44510a0401140c0d50b0f11900300050510300142c0070070700b282c200103025007004c00140e00c842803880f11941c040b540030004980e4403140d981000d09414160f000504001c04843d1588005d00279a0303a8120402079a941c95250b4120625050500501c66030761075a0301941a0742031780310320241c01d02c1061640307040e00c40480154541451311004403051212000c0540c0c843c101844041846943c40c098280603810074031101181c0c0c1050f182c01c0c8125003288880805d403c3c42c0416 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 626091636 1250 626090386 626090393
    0x7020414071e0e091b0c1e011a0d020a0902040909110603010f0302060f09040c120c0314010510020c040e0307030212030f0a1109090c042603070618150504030e0d 71
    0x240c3c40e25000b01a00c10385030a454805140200b040084103880074000045004400300800040d900000d0300c030709001c03407420243c0c410043d00302c50113032602a409640c10030310789030182048081070b8421840580000c2e04280e80c0c0000400301e030029005810225101e858403421300a420380c81e00000d4000320381c481d1555150140010300003525102c001d004100c0450401c0b24a00c82d00156038030488054014010210480d5000701811204510303d4012413078103a031140c05074032901c02d100071a070f818040c0080070b900380030801c4aa020040c09075404c501c035044c40c00d010354440740103090100405800070b544998980c0740c041d0030041c5880c541c0340c1c01030040c820807403414000c0040c99042807624600203103600607031a0960486c4035040c0d150743c00a04001c20701c00b048000314001c00444010703030290750075010041850254218011602c0718954400c1c40000c0106801c0d50100300e580340b000d0783c0c5841c101d82e150380740c401d10300d484040000c00b140e03258208003c2c03507001a1140072403c82203854814541d165035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 626092886 1250 626091636 626091647
    0x60c0f0f010614150919150215090a0b070e06040f0b0304020315131b080307140706110a02040b0420040905070503070c0f1b030609020a051507061107020414071e 71
    0x7417091245a5103ca180c00c082c1c200701219010304031503c85100e41ca401084040c2d6608035500030013101400c071000060700d2010201c0c5a0b006190b00803818212034440840844004450072222a485907040000041510740131000e080203120341e144464591416004040c2041130030404200d02220700400c103d1140c5071481e0020001c1d501400c0340a0310b9100303580c4900799075141d4100311102c0c80002a42402d2150300e540203c1c0c0881d0007411100d5250301c80307030220380042400c4d10324115030340035070400e80041c40c140e04a5565070201034000140c2401c01190300e24004019100202c1c5124002401c2c00000740500034141d2061090401030f155082079800105800700380c55001c1c1c44100c50b44414070811600190200c0745c1a61709101103c03140d12030601e0b40c01040c1c0344a00b00e100e0103e071800000c5905200035541c002c0c110060483d410000103032140300c00341a2540c0126140903003040160300590301c0b4440c0303400001650150004134130b46000701a10100d2036a1082e244000131034840514503030304c50b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 626094136 1250 626092886 626092897
    0x61101050c1630030b030d0f020d0813020603160305130230060a0b03010612030c020d030201110703171e45060c040b0306060c0f0f01061415 62
    0x720001d404945503001000110610b0b882140c01004401003103100c4030f41c1341d0048502020120140c489520b003c80080d259500c2083c1d104015800906086614034010030700c2c01e1b4440445038540360a0041980001c410f80e20840b83c1c007090461480034044040d9251261030703441030021890600b80b190b590001280d008021103140045411000c891901500715180044440a0b603000c44105081c80c20303480024001003586140258030b801c2001400200d441420300c0d0040d055224900c2c00c81080c5c090182c1e102c1c1445c070607070079592607140c1500008081c800038541c007030081e070340ea540102e52100e002c0d18078100684111101705902c2d0b0000400400c1c907080c075400110251921a895140d400d0040081207130810040c03100c1800004000c1c0c440d00c4101300c00c071049004054801c181d40310300c14208a80224001c0450b031000900c00030f2928140380c0010248682e240080b62403a00855030114502041611045583c0c0d44038901000711002115035001e4107103003200c04900c20304a61070601c0541c00782 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 626095386 1250 626094136 626094143
    0x203030c070602091905190b0a050f040b07030819050402100f0908060406020d150f050409020402070204022a010c08160e060c0601060801061103030601030507050f04061101050c16 79
    0x501c80c800c1003102d40c120f0310390000203850000386480920b500c0035402491b1250314002c03c4280301000107454000301c0e05003a01e909070703286c504003502190201c450707412a403000084010104004242c814200c0d001e040c1d600e200f90b40d03414203071505d1503600c91500d1010400f07a1b400350920080c000181d4540d00d1424071100705240030004100161805c80740305e0801e611051560048006220911044d0b4005010001c01c100d03040c85803c680300c54540c2400060f100345407104800320402d010915098020a8590340020405030038041300f900094126480b4a21680700d2181701000300781d40002101b41602d1061a1400030005e0501c0484083c11401c3e000700040d41403680c008541034400d025840a80e018103018002e05d4030b034182071101d10b0707540d034081c0146000310740103400000301d280c81030086456503420340300070b5070454486400642c05008068804414810140070301c072100e007511006000141a02e40e01c8036a044518841c0c9030131074001030408556038100b0407040b070749043e0960070006602d81c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 626096636 1250 626095386 626095411
    0x230f040c0815031e01240614071a070c0501050105060f0d1812022a0d03080a0b100c061a030601060503090a05070f05090901270203010f050f07120507020303 69
    0x1038000908113102001c400c910307500c4044a01911140552040640000034070101e10710582c2241d204101820601c01c0c00001131141405000811f450005421407a10a0410502c1132003001e40c01c08200740c0440354000026144030b04802400001d014cc50b0040006541c41031a1240300c0c1440100c03031107030401c1c05c0c001e01e032160042140204421101c040050300613a840e0403107085600001e4581400000f91640200f41c0c4840c1e1514184000e6204501c900040265811401e2580c050786c9407040140010141c4c1e41c0e5010220064540d10411541042c00781e4401405c440f071450000115140b176802105580781000703007500389031000104541500c081e418115141d076191b0345020b14114007400020260302659000045e4401c5c00d084201c15124211500b58a80d95201656422240d001d507030480210310300390a000c00005200c9170911110300103400810140b45c80000141500d400740c8181d101c00f0300010400c01882c3d404209000c0b0748890100900450401c24402941d80c00060040c65a050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 626097886 1250 626096636 626096671
    0x2707110c0d210302090a150503071b0f14070e09070614132306090a06080c0c1b010801080307050a1e0b1504180b0c03060307230f040c08 60
    0x2c40039a100120b40340b40940042e0708602000b0007000394000249042c09108202c20100340c0c0c0c1200701c031244119030340d03955503800c41d40c4500781281e00d001e0b02c211540c1141801840b400104a906842407240d601601402d12400c8911448910301401c5500800d01220520280b02c03460340049100b404171903280c80c250003c0700c41c5201035085c910a1840b8116120341070303100002c1b02881c10306031035814000c0760b8001910300844020310415110302ea00c00d0f640425141024018203000b510602d0308808000e0b8660300f4240d201c2000c5150850001c40402c5060303000460f85155079000d84e0150240c43e00354040c509100d44c1c1d54603160342d1030301c3c0080108411102d41042010450003090a01d100e42c203d00794078441c0c100f03240700040f40300b03507280a103010380d00b0042c86426075000604030f203a0041e4031006000880c2d5803801070000300d0f08050455030345070040201c005140c0340d80c200a9021040000311403183d00c8040c0d070400c950840011001c1c3e0059007070594441401e500245041c2d4441040d004050008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 626099136 1250 626097886 626097893
    0x17070b0a020c0307120b0604050403081b0c01020d0e0d02030c060a1e060b0717090d06090611130e060d1101120e0d020709060b030921092707110c0d 65
    0x2c40881450301441004c10005004515010082842c0d0280441c04201d0300c0e0b00c010712003074a1049a0150120384044085075034000e58840c1c00d8070300701917161000c0c1000c007590b5090742a64013040d41c1c01c0400da16000f408220085c18001c40c8000c031b50380d0004619141c11003000380d45403036004099810040e56401000000c070320355246000c514039400c208000c21a15a100c52025810665083ea00b41c500002c8005050390f080c1c2c111050300300000d00c0c03000d86051f107641301e83c09408584412200030785c172001103002048038007029002ca0188107a00c1000345041c0b0b0030b201d040352802003119104141c400080b001090410700230b803030320441c00c1c80e140801441011218010709503124010b0310620034041d80f514080e50100750034048d00e44540c8148a080d40d20305018031180010343d5045c60780e811001e20300000300900da01402844c5142c4640c2802c1423141c00011755111241c4600c3c0100d6095600000b0302e002002514030750101300c5040001c1003242030100b0b9a5650400c590440c0502140300c0c200d002e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 626100386 1250 626099136 626099143
    0x91404200319141612081c02040501080f0c0a2a03020c0f0a030c09230709052d060a17090106141005160f02100e03060117070b0a02 58
    0x1924405421125003841d0b80440520320499090709952400049802441400300494003c8800041c40031020603241064600060503900c0601286d440c081080449012401c13070000310640744d001200107803107916040c005041c0117002014030409054176810030080420090665040584030701c0e05441e0740703000d0f440004820108440c16502070040005050070940c2c00150100c0d002c0094034108031110601050014810b0303503010003041710003201030912072080c0ba81d00401c207103110300e1080b90900002c0414403403805000d40f180c03c009068140180b10310700386802d0081118007803cdd05504c0c4003500482642c5c441c04440742e001c0c81140d00045c8200d019104401d441318140180c90004091704103d00007500030422881801d600c0c400e2404182076519154410f14698202030701d42c1868000000c01da801450100001282c44942d1301040c40003507162424840801142d9841d47e80600d00020209403410605903c82c0d500014030301c031542c0c015840801d40d10304441a070004152107005001081e0b04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 626101636 1250 626100386 626100443
    0xc010503040c09091e0f0201021b060708091903050a1101080903030f2d010f060c0b070c2603070809010c0210111e0307080c12010303050c1002030a0b0a091404 70
    0xc00e80c0003400101400100c606c3ca4401501c01d0b02190703c101040b0816422042d15005c0da45c0e4002c4d0300307001c44c0c17001c41d076242d0040c070041000401c103806d03083c00501540e050b102d02e9002a030f02ca078020358900042090b189074020742d0703400900f040095842d002080c259203100081000b1044510500403501d04940350000d41405942c2080d40300329008000246408800c003480780d05110a031040700010b65601642c1c07405000d81d0410215070042d50b440750150361806c13001800712458070301c041100c5050300c010303034503492035003100078039035569051092005000c0c1c10050030240321079141080c142c11030303900014681c03a05092000c0120700c80c0c2c0c1c010341500150092130002c0880140703071b10480207100311034002144070b21903949070900a07071070b82d0a1951242c06000840c3c20340e00340c007200500c082405200980b01c4980000c0c100d0301c1400c0761145c0441070340c1041d50000340d40c81e11006255158035010b100d05001d00840441004480b400f404501400c0c41c0c068005000800282842d1b8502e0b240074a1004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 626102886 1250 626101636 626101673
    0x506010914010e0a2718030215090a060606050a020f010b0a14040902030607050403031715120f0706050405040b01020f0c04050c0c07150e0d0f1403090a0906080c010503040c0909 78
    0x5584038100b80508440d00b05e0070014404140c03030601d0b0300c10b000340c0003c601d8040740d406500a1018030040c8040440115025002001c1ca20503c82071030005000c9000b141c0c082c01c0d9a0380c0312903d840c003035017000c3d1401400300303500c1580344d0500c0d00380f44050725204aa00100e503243c14429000c1f00c240800700c0c0050000c1440650180240402c120106070010010030850740300b640c4416001340e00c1780031016812015500d80701130f04151450030071b030303460300c620345800c01c02c5c1c9003041d41c500c8828007002034a040443d031701990104c0c801240800c0306182c00d2280c512807075401c0c0054501d07014070700e40b42a11181d004901d184105d5450b0040f41110341c44006841c24121188100c03080c5684808000c7c0e40c80e80354948050005490b007880c142d49043c0007040c0030b0013640c8140d13420b044543c0703550303401d10240d400c284100003072106004803c02ca90b66810700000522184100040c11410b01c1d0711981004000b1140606101d010005d00000400b124404003c50700c0000001480384624035143c0c5c0c90070f03200b2080c038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 626104136 1250 626102886 626102909
    0x90d081308071109100f03060903200609062811120f011e0501020a061113030803010306060911030c0f190e190501020d030f060510120506010914010e0a 67
    0x400c100f000e040c0c00d415080401302d483c040c5070340d160242c0803402046401680c581c0c008502d01000003541680081c070503240700341407541c180302e074005c0600c071070310f010fa030341240d40c0c2d400700041c0504020203200703503504284050440101c240d10340c41241c002c4552048044d200c0c0f591210180e60041120080d03803182a02803400201c00e062500c86100800d2082c095029007488200700c10f150350360a54064800c0782c1e07043e0098804083e02d52502070040541c3c0c08080d81046081101c0140c8108001106020b144200a9682c6950560626000b1540e86400c140a45880e01807501030011081d07041c1c070343c00007655103a660380d030038064441c01c420700a2502400342c012054218021740c5400c80d5084110000039141490b816100d4110844a05030900c40c050161300000c0314480c0c014442c7e040141080000d21002c6803091341d0350042080f14070509851000614074070300c0d0880440381c60094a410010034071386010418100040f14100c8070b81d41050343d060021640c01d5002d241c607060803aa006000e450034a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 626105386 1250 626104136 626104147
    0xc0905190b0a08010e010510090504180605160305090102070f14010e032a0c130207391203080a0509010e0d030e15010f0306110d020f0703030605010206090d081308 72
    0x50f002d11020301400004020b81800403410342001203480c03004a8040d964075505500d0312080c0402170502c01c3c40107001102440850003c14824040d860242401e6141080c28080303204d00242220b0010b001002103034010014003001ca0240440600603580003556007240d03007031074030615005019082800c5400d00000c40c0b0701450000f0001c1182c02c2c0c1700c901800210221109000f09d07154070b010302d03c2c1030344420282c1d06a0700c06c410940c054000a0b00c10030b41a0700380040514a2184036030001403141d80d00d2426990f1900d091511103901008040080407014100c4655401a012010081c181c03002180d4410000d4540070303003508110701581e581d00651b800b1a83d02d0070010050b02d18a0b5030600385108400a00365103080c500c0c109812141c4100e06d0f03c2c545030555540001400c0c80c000661916042846240b80240d20b0b80300500a00c4140000a1740e40d010a140c0074042c0c81d4660302090554105d442044400c503000304d8030340301c059a0b0b0f1400c084140d40f0710040060010514001030f06a2401040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 626106636 1250 626105386 626105407
    0x304140d0b07030515101d1c0b0a06210206030406060306050421052503050903120301211a04031e050705210d02130b0f0a0809010c0905190b 62
    0x44207020b0710a80a52003000c1d5140b00600006d950b045000300005039207100401034080703003144003221103170000704000700c1c980501c41d17003401194101405031180318425080c0241070b03900740f02c2c4000811015000211011075503a40d650003900024000c0d005510000014080141a42c40980a07541c007850402442c00c140c24071040004110745c60304000b11107032803020301060151081d6082c1418080d2240400e010940e5140780455141c5404c800b8400e0610000315195800d00c82c0c44580c0002c00440c40c5c40b0340c50102803d049d280e00e002c804004100c048410008224401c07511203441001c02c0b5070a1b40780e240d914048411919544444520414282c0c030040348a0f80800141000c50203201103c8402500e01080c40000f83c0c5152007c0400100b040315400c0700800b07030050b1214a601c3c042c1c1c2c64031f0310b9960590301820b6204440e000e8615800040c0c60070307030541007956a50000250340080052400d80714003c0c1500c0e0752405a20302c103d036000c540880303445005500340050904051019111600e102 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 626107886 1250 626106636 626106641
    0x1e0501020a08101406070609080c0615041a0d0c1502150a0e0604021504050d030302070b0901060f0b130302100207170f0d200d050a0e010e030304140d0b0703 69
    0x180307680004000c2004541045040c01e640d6060790301404e00c0c001c1c4000c0b104c081000c03e0b4000c007001c90301103881c1d40d045030100e90f601028241a842c0349020300503502e4030000c0600c4184040101a101c0ca203054045417411110f0301340490041d6080c3c801040040e000e00704040f0144456002e03420b240340140c0d24100b0f0039804654030441840201e101002c070b841d034256482c195880308842c0c0010398029030024000d460300469414030100c1c0d42c00224030300368860010801d0424240e409401103900000e81d441013001041c40140d104d21601d000f0001c003070400d0050601418503102c1c403400e1752404114418001d4001304003c008540c001c101c2d60305c041c0d120f00040d40300c0d10b85100d00760154500c501c1c0a1581d4002044150f400d9032110094aa0107000c54ac0598035a440f4a007030b2041d1180419541d00845010400300c0b54800c40c90700c0d016180c2c45040001071040384d41c030b5a500d0410000000c01e4481d510000f0a030350070b82c2d0130070f600c10341c119200c40007081010b00c02031400303407000f031000050185861700755 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 626109136 1250 626107886 626107897
    0x2090907091413110d17070b091b040e01270605010f1202010f110a1a01080d051b0102121006020c04020a120b1504091401090b060708071e050102 64
    0x102010b00a41c000e100c0d10009011040700c0c10720f070010111114500150310f0141c0000042801040c1c014860016281c290200a504107148800e0b000000c0b000140f29602c0b1040343e0003c0704400400d10982c01100304c2c0c10902c8608551405107803282e11050301020300390400203881295281294000f100c2542c0c01600003110001038481500e400e0000c078400035510b49110503288981140d259030540c03507004480d50184241d4240030001c0341c140d0000780843c140440d0348218010201c0c4c0c0e10b160a04440c01400075010303486219190f00044407500c1003500201522541c1c0c140060548803a824440e80c1c1c2d01a1254410b1540440a080200292052452544000c3d11225070840300b071000954140812841001c01c0540441d000d03403800b2130140d2041c0c100c00c1d003070f40000e01014803100c1c4001d12840c032600190000e502e50f0351140808200c0480500c00b55004052100d4140301601c01c040c00716207107101c0d00d600940b10400018490b0284a0241003031900b059a84641c02c40c186000c1c18114004d4014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 626110386 1250 626109136 626109149
    0x121c02011a0d0503030705030901020f0f191b0605190608280b0115020a150c02010e0303060a1a13091a0a030506010501030903020115060804050609120306091302090907 74
    0x3041c80d40059810085602c2040e103500100440c03441c2c07200e110580c0c098000818800c1d241d074003000440ca903c90703000003400441e2603031070009403140c1803666a06803421901352564100249500c4502c0c032070001c03d0b000612150041800141a1031b000c4c80c425448514a641e4901603041100025013104000f030f00e1102020102c48105065082242d15080d24810101c041c0014820a005109000503900408900f12490040b2140c1c8003d40e583c182c800700e01c0301e480c8140c00b5030302c05030041000c0d0203006007422004140050f518618100700060b070351007072502841040301110a41d0f1401c090aa07822601c030020501e07846200550f690205801802d40403409211481c415224120207040c0300740c44405403a484030107408983e0a0030011030040c0007110b0240e045641f550070200c4005c49020a04c40a0038035659119014685820441d182c40c20241c854800d550181704440d0b0fa228131038042e2031f04004200c036541c2a6032290300304955210504000a584010060103000e82c2150000740c040842d41c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 626111636 1250 626110386 626110421
    0x61608010f080c0f060d05010603390e030f07030503030a0e011a040c0c0c0906080111070308040605060105092205130302060f04060603080304030908120c0c121c0201 73
    0x22500c5000780035640781c2c4242440303a03201c2c0055880720b140c448019104040c001d003600e810540c40c0020352060f90f2003a030000c1c000c00c6c5e6400d69202c041000401e61003107924a11100303080a2843d017104480a111155a182006000e002c4041c480d607060103036074000a050405c555005460b401c02949960060b901e001c041490010030000c0880d0602900e44201c03041d03480010300c1c50039142130201038107901ea81d0070208042c1344043e40025041c50644006485241000518181002034850848009101115081900344205400203910690b071a07403044d4003800110701e5884000c010b072000c1c0140041d180d40412032034039208401c0045506100c148038040e2050105849094030306000a80c4c40c50090010b8004400007a40f690074082c42581207842050700140c035070f40d47c0c0c81e03232400b43d0825141200056441c171801c120b12441041088125041d000500d0b1500c912079010316035071920580b0541c00f03461519219000c0560a04c015900c0071000105291548040c03980240202500200c4608401c1d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 626112886 1250 626111636 626111639
    0x1d07080c0405252109150f06030c030813031a07080601090513150b0703110c04180605130501020c010902090a0e03040b0d061220040504020a121406160801 68
    0xd0a50111442c84034a03e41900c980b6248100100e5884820760703071418800003000c0485000b0030040c0306030580c80e80103010221001340700641c0001581e101c00f44c404001410014144041103030720301c40c0002c40381d0042030315640d0700544821940400c22540003400114621011010202032000300c036104070126501c008c000d030340c0e860054070307142590b01aa40c1c000880c403111340c610040a42c080c01124004179440802a0b56900c505502030f408807408a000584103e00c407014041300f000740d030001c8072040301d042c084d0145000300c0208603071070034001410007512000401d020806405e0b40200c0c281d040030080d991a1541501c1da80a0980c8450032801346c0034080c005400c08519100d405506a20080507601d0300e89804c02c01d42280d0804201280855a2900009a20542c6030080c3d42068481c00040c42c54203a200741500c02010340c0d141e200d0069003000108001a032311a4401c00a0382c0b0b00d0011b0344080040c1d0b0a00c01500102c40300f48c2080380c400c0074140300b401c803292908414100365540c1c0c0e1241c2a07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 626114136 1250 626112886 626112901
    0x90302030c04090302100e07030507151715010e0f18010503070506070803040609051006080d1103070210180b0c060402120a0b01032613090c0e03060a1d07080c0405 72
    0x11402040f0150058202560f00c0111a4050b04401400440842126103154407610303a1414140c4942c4041401c08840703c211001c141c000c40002a80d5400894003480ca00d8812280802e0310045d0035402c0c10003085003250429030b550b40c01c40303958816009e851400e0151000528004011003801030314424807942e03800040074941a012604195030045a00e82540c1300c0f075680d00c000c1c040c12201200c10307000d440150700c01581e840c0b04410040c0aa000100001e0020480180118240400e0f4140b2074104000840158491000707005401c3e0480c5003143d0b40c004042c0b07010f034004a1641003004843c600040c0c3c0c94403c500000c840303000703034000c9640c10440b824402e8025901d0b00c003030b000280030f11802d800400104620b400070309883e558602c101001a2895005e00190707902c0310b01300518981c0344d11420700030a5564403401220354a06c0c1414000d10040c2c1d4002a40e96100a1890b411551542906e0880900410445010101039022103203800d458101c42921841003000b501d004078501400203c84 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 626115386 1250 626114136 626114141
    0x70806072d0e04240e040201031404060605150301030201050a0e01051b0609190c182309070506042102040207060c0c03030b090708060402070201200703061b020309060d09080a090302030c04 83
    0x13407030001102c034100300e18120101d802c0340b000400a906243d6285600d00d041e03205c030050640305071f104280015200341070404003c1103072000e082000200800344010b02c01030740c100703040324500c224a08100c020080c0600040368240704d020101584c2e02d640c100c61404106002582c01e008400c8034003560b5200d581030b640124010a51071000d42001c0c600442008101c40303e1024005c2c0024980d0701103000322134240740200b54815141c00a030085021020404444000d20020000e490704452191800b03107452550716400c956200341d5820305c0d0380c40302d42c5011981ca41c1d04841511f0361008040c00203180301c00c0054203c1452140680c082410f200e8050001d00c0c2490f0203d10441250b01e40b01d41720740b1004144030081d040b40f802241444140c1c2e080da082c01ca2180c03201e00740041c5907c0101642da0545c03410006480a20840000344a058100380c0102a008000c1d20583c000c295106034032140006480000713404000c2c8080c1c011840000c0303602e1129440807030502030382d000b501150945003038013003407004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 626116636 1250 626115386 626115431
    0x30f1f0c0e010f02120301030c03020310090201050a14040503101b0f020a171e03070f03180f0f080d0204030210020a020306060603100f08030c010e070806072d0e04 72
    0x1034918199200d103601030783c02414042c2c400d1040711020300e601030010711107502c280c0054401940307a00b010002c45c58204a40c0130302c0b00804400748001d5030f060380080c11900801f072405050103110035107002031403402015240148001000c4541e0803e076001124000c040844034210090900c0700e1210050b40103545c55548801c00364000e24034150f07952128101040c002c4e440d1901e00c201042111609103080c41e00709104c40989607441d649051030b4001070019112004004141401e00356480310303a0480b168a03001c1d01e034001001803a6602c0130720f400845480f03000002004104041200c0a0901c441d44c064002d481c0f0a60342050b0924034040c09a80d00c40b00b10800944c0f6500c000d0014903242001000f0310703040710000443c4216141c031280d03602c14420340c0d0740080820382d00c04580d0300345c006000d002d41c00d42e058540002d401600e003001c0740d0320f031034030303130042450b01803210899140c02c0c00c8100d10344076800174200303010004c10314050090040290318940c1120b440340b41071124900f107206c2c01000082 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 626117886 1250 626116636 626116661
    0x20d06021b0f0a0305030606160303050f070c080d0b031e06010e0f0c0913110706050a0501140d06090206040321020d09050a1206111605121e070c05030f1f 68
    0x3ca458116902240c0c40c1e40010080c3c0d03004141800040c84800d1581c42ea44500b5200e5100405d691914000840107588024900000c00840f50309600104146604903120703440e84110214411070100c0110740792881c08441130001c0840c1c240102482503012424034141e40036614210f102da2a011700701e44404e00309940c104040b0780d040000b18031500d8041041c1c0e4108240794404511000202da21107180d07000035400342c80d285c5d140c030f04101034800c40d4071826026012041a0440c45056003011650140140c0401004280d90320b03951002e640d01d500c241d40007158007580c08060f4001621092941300d15450411005d4458004004801402401104107441015105440003450b01320740038590384400324241c4555a40c1c2951400ca0800d50000f040c09100800c00303000350fa8043c0c07030100d140103001ca0a024180170207201d2450808c00b0702280101d03030109004916243c0ea11400e001c400c41c89241e1107143e142c07040b81089001c002020035a81c107040345c115180540c2029401d0528140d800d000c0c14407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 626119136 1250 626117886 626117893
    0x30c040e0702120a21110301060c0606050d0609052b23040e06010207080312060402030402040f142d0a050c040f0b04050f2205070c020d06021b0f 64
    0x28840e030080034a14075030101162048803070001070400703105203d50000001c2c0001540c824116840d035400780480964000040c04100f04005000c880c02d40b0f18081070003a4402c002c0004d1608040c02002e4102c2400303882c00912804035000a450300100424503042c0c201c03458020100480032040303e541d40086c008058481c440d0b50004181c101301d465485043c0f540500c9848600d9000300341619401030b0014090400140069040120000e45404d15a5220b0341c070582c000c04c0046602d01b0302124803504094142c1c0e000da102d480d10310004010308480341441d101c1070310301a01c05044080308940e01d8001c0181980c0102d4041c0034541d842c04628100e43c8842030207800201081d0b212034160f01081d0300c034817509803060a00d03403504451040d1a00a40c00000203000114040c0100d02e40042e407100f4003032049943d003140c0c10400e0354248070f004030320004030001c598800c0020b0059024040d5000075540c0204440d45110242c0390250080d000204194064841c0e60b4040c3d42012002403910822490031009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 626120386 1250 626119136 626119139
    0x150905091b04090602070f02030f0610060309030512040c050112021206120c120d031a031c020f0d090e070311030f0a06120302100b010318030c0f1e060c05030c04 71
    0x76601e10300500e07450250000d5440d1140004518244003404c0584d2181c01143c120103200d0040503d010a00205072030660000f4080c0803114000381c0d035800450b206400c0c045080b21080c10181d410b07020354504022501403d408100030400301d502044143c0e0b0f8242c81d0446200148a6400128001c914a1220542002000c6040c82c580f140c03081c0d0b404a10001240e00c00181000070400f06152103a14000641c004002d024400e0f0701400fa200c0192050b0308a400200041c0c000655a0751414003410b03001c18201130f02c134071031910a0220200740315204003220349481c0b01000091000a2610440c11488058808114201d104c6e02400d1100f214840c2514116281c0042180381c00c0e0000d405084010b948080016102d02c01c1c1525000c514002e4000c0c002c02c4001a5880c0c040c2d40b000f1506a042620303184510302c21032006035000f0341c50f54251900c3c2c17402403040e28240b6074100340d004000d411201c080400cad21101503400c4190020078031907103081c0659901c0300d4090f512408240c4800342c048106010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 626121636 1250 626120386 626120413
    0x2030a021908090a08030a120207110d0501060b04080f071703070b0c131d070915030c0207082e0606050d0b011b0501150b0403080307082815090509 65
    0x81d0200103018221603441c00c101080003c640900f0b690207580e03030b81c0002ca0440300e015001b8941c806003090403101545009100c0e0303140421102600d074050711071038904101406100007540850080c08944090560302e13525102c40a65648042203410f02c3c0344141784001c04c00001c07074a00d04810758200c1c80154102150396a070351000c190b000b4615940b0a00a100d03c01404540104be100101444505141d48807a066003c01031a0f00c024127030700a0092400b020802000701960030008040c0902e4001781d4049505c03801c034204503440e8091f007043d224820a480e107409400034100d40c44550050700500a444a1030f01d441907400903c15240880e1090200d014170f0f80b200c1d00001c540d1101454000d910303070807100048140403c500010380716a0741d11007100c070390b1034900076041c0c1c0540b1a44a50307a09003882d69484402512008008004000701600400d0811008500c9000041c13001c00c0d6200001d041e601c110f10041603d4086400c0300d80d800301000840039004d2084074003a000314005803006002169 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 626122886 1250 626121636 626121673
    0x40321020c041a31051f0303090320030604030e0102010e070f060917030d0b011e0801030c0b07020f0d020315070807080130171201090501240806060d1e05010602030a02 74
    0x1046c4586c6480b000740140452240901d4000182d4440d8460000007421420700100c107a40d8426905500c100d030609001c210f941c00100243e200d40d0500d003c00d01c0d110051300407070140400c0410110a441101c0c4041460069006a00252140d940e104600d440d612515540074421515000c11241c108001000329000c0607080402e2044c3d060410f50b000000041020240c4480e84c041c01001461000050041149641c40b00c00100305d90f84000741407011603000103914102d4281001c0c840d085050700401191801e11400245501082e1500c0d40d40c9800c14020b840d2000449a80000a8442001281030b030900c26907101d44202410050503903500482500c003851070f000c2ca09480841586103041c5050284500420803100250140d0140b540f401821030151030301a013041180445c04a010aa20040c03500811400c240341d00e0003981d29141ca8001c11000c0c810800f076030301c4080c01c10b910b400b810701d01c280c44500038040e071080c03c2226a90760300301240c60f40078040e41400180c02c00207201c2814120340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 626124136 1250 626122886 626122891
    0x8010303172d0403030c03050106020312040c0806070513060207030b0613141008060a090206030c0f040306020d0606170c040b0c16090e1002040321020c041a3105 71
    0x85000044881d00e1400301602d1011809036002941000000c01c0100b55042c0546d080030515801e044c0515410208003030740702d00400900070011303812000020180115284002d000344822400c0d58080e040404000300207500c140345100b8001c40c00e51001070001c2c800115042100d40140e21580c042e203079401009220b00034442c2e80c60040340c036889840400c0c4e15680113940203000010107109090f28020095003402c8000f4030107443c65181581f41c80168841c0d0701120742c4803500d80341711907844d80301840450503030240ba0005050984082200516501140c0c0090140c450302c2d100e400f0406110a41601c9401048440440d82c17802804104031a6084201501d10648110706460b8581e051010f20502603001368804020035441b103406051a2505108003141480c42ca50b040d0b18143c00c2d078840002c3c0301403549080d4410100343e41d11200311132092081800c0c55400600c24031068944600d040c4003901c410014500c01c01ea4858190290f076900c0b452103608031006055100684031210900c0c0007000c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 626125386 1250 626124136 626124151
    0x403080a050c0c0a0f090c080903030402150c06041505150310050a061703031602030403030f050f12040f11030114011a040e090102360d02040209060708190801030317 73
    0xc042c0143d42c0e43d03a60b0a82000a0101c0c44940c41441d80303841c42e5042038a0b20000c100041c020001d041c80f9003d64044112680a601a0b442601c607203e6081d0072286c921840401240310b006050a000800012494224414090302c83c24400d81d1544040e041a948401100350381c99401140c0c01d800141c8a90001e50340030501e140c0026409650b41400310380b469401e400440f80c0d13000041017051001e20484e40b011405050710007103050a04566010b40b01d0385c994200c450078450701182215002820400300c4061030908120308101e400d003850100290b03c1c403c00100c1c2d41c43e2610f00c003440c0c03600741489582101c6800c40b2116a80782d191441400c1c00c02580801c20700e403d10b0820bc080f40b00c0d80141441801a0065400180c1c0c0b00820621002c031004444400403010180f08801e440c80e01030414116074951040340c03440070b0b09055200241c02842441c100d03d420402c0890690140f142c00806400c0308940205502141c02c006001203030382c90424080240403810144900078584500e01d4100d80c01100e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 626126636 1250 626125386 626125393
    0x18100203031906170f1e0706080a0b060f072001120e070b0a0f0318030c1101020c15040503010b041503030c1e0f030f09210516030303060e0c0403080a050c 68
    0x2c8805010700f141035203506070905503200c81d4141449407030070030032074160031b4070034101c1c050310a540c13044140c954925104220421280d8400706201c92001c0d0700c1810400c5000f44800e0791085104031a48107034000010564503030030200398050015110344402680083c0c141d5403910441044031402000380001c100030f0b07002d441491004111b083c00b47d4024104161140c494401041500c0030050583d034850140c60203000440d0f181400080e04884507010040d0f01c11000300e85030b02c1e8840100d241002142205910019210041400d400068000c200b42d4006500030310100c0741d041d0601c810f4032020061401d02c9444405c04101092140301180c8045d4458540c8044000440000201052044000303880c1d02940010000030150089035040802000381880036059251a01c2a86141d44180325502c004a2000e00c5000700034060081a002c0c0e140b405154042681b2424000c000f0f0141e030081c1d070192204180840c40006211094404a0b0350012140380303001d400f01f80c1221150800c5411000510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 626127886 1250 626126636 626126639
    0x6061c0605100908060a1407080601020a0203101b080402060d090c030f0507050117071e0c0503040e0a1514040b01030914150703020a0206013818100203031906 70
    0x5552814480c201d585699440748000d04204d0480c1c14144060f2202104e24501400c3e441d40c107000d00042a44500941000902940d50000503400d00840b490001d516020b0140d6081c002600b0b40d00201c62041b1504100c200c030b10035a88260340e150026900030794055428072041204206903044030070380318458840040300540d40d41e82d540550100f08422521900301c2d960034407555900c0720700d40c4032b601030103065a0800e080258001d0f009004071401e00301c040700c1e1060000002400741100b404850b6000040365500c5654440541d400142500c6454104c0e05250041c0302c0c01150030124010340e8803040c480d07034046403c002040010301c05004002d0515464009401c041080641440e140c042000301400d070b020b03c045168507014038014551003d0510506c040070642e0340c00107880c0c0c10340f4042401e891551010b03901120700c441c041c821304454546c850108038a0451104007820140c09007402c4164602d96110801070404030300e60303140005a00900020300c40340502201010240d50160000a18a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 626129136 1250 626127886 626127889
    0x2030c060706180c05011202072f12030d0c090b0d0b010e040906020705010507091a0304020d0c060903030e15030a4b0504030c030c03030b0307031a070806061c0605 72
    0x300000702069404c080c5013001040156003240c00086003441e450411482d110300381e941e0a07030401501c61656454803500d01400c0210414080b6a08080c0c0c004100000e000100b030760712580c036880003900d030b0681030900c0c1190b443d6a0080c40818252400220310a041102100744d003402400315801c414100100c1e5806400103072520301c01c1c407241500071640582d40303d40c00d08225080d40c001826031020410030342c00402561030404203001000140702d110716500d13103c2d0300009805808c071610150140c81000000694160400b8403201103034400d4440b420300c05111801c018000000340d420410303c5404000040304a9129170011504105003001c0e0031039080d000a01c2043e043e6001c00c4201100d6030480450000d1109104444482d00c08803024001807400342d038002c19036410b081e8000c06000d40310044401f054000d8001103100300018044840f115a00c0c1800c4003c0300d5a0440500002c09080100f58454440e0202030b1280102800c0b90b45023903011001603002102c04a00e0621555480c01c000ca00f5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 626130386 1250 626129136 626129171
    0xc060c0a1e03020a0305060a0503030412030c060e060402030f06060303030112050a0f060b0411161b0e1005040e03070b01060f050c0102030c070c2102130209031c0f0c02030c060706 79
    0x4801c040e500141c0390b4109800140840714082c1020b8410058850100419640041101d003034500c0c40310500281c0340e9500e0142d070a460300d02d038020685030601404610201c1e001a20303622842c02182203a401c03510460400d5160603081d038640b43c05800400040c094460034903410009144504111144111310b5240d401c12040030500445e07140d030b2125107904c268036043c010811200505182a89032a506d080b207d00d030351103030010041540540e00c1070061080405034050008001d4a8441c80c1c5524202410380050240c9000c0c0502c9246000702170309460f10000300384c80c2d500b540410524000e90a094017640d07000b103140400020441c040110070b00c100001c1c00030314001c2500d00d4030170b503d42d640341c038054201c03401681203188038504060581088444202c00784080036011341d1142409001d0f801048040e01c00c02090580500c41c0011448130f1000809040c03d004a20b9915891501e111040444a84503980d102960603480103207604a9450201c00400307119100d8900018002131b8050001035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 626131636 1250 626130386 626130437
    0x402060702061201030b071b15060b070c090501060305041a04060b030a14060612100c1e020c01032009012105010b030702060702030406080a02090a180b04110c060c0a 73
    0x80326604600400800442d5a5015001076448c103220704086210883c5d207051080c0260302404518100b5030b041109801e40d40302c00090804034100c1a41e444550030309402444051140030216840d10703000040080c4a40b251b64055680b2078461440080d400403816004c0350040c0c01038512a9031041c00c60081d80e000c00000d81c1c444c1c4251041550042c289c3d50190400748000c2106006810581075600307100c0c000319228030002c0d055140000d880400140440c4c0314007c04040551148400d43e402c0f8030190001240880c46100342e9003072002903515800340030b0040103020050000b41e0240540e201070360160b078851103a10344c4080c081e0925a0300144603001c0d100c0a80c8000c5d0640c0c0c0001c24440802da050100136481501c6000a6192501d0903c00030001b00313004004501103680407034001c5040c1c1d1008120740082131329260000515a88800100042c80c2035100d0740d114030300d04007028050341d005500ba5941c1454400181185035944440054a40c1c4003040750010001c0081d041c040c0d0f6801824080d8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 626132886 1250 626131636 626131657
    0x2090f0f014b140418020916020c100314091204050105090411040303030207150504030801030b0c0705010e0c0117061e130509010213120c030311030c03040305010b0f180f040206070206 81
    0xa541c0f151000a01040345c1c0a81514400220071044990242c0c8400390201e41081540204080c3c164000d00308030f04106601c0d00e1a6031260b0034191845640e03030f0640102c0e030066510040d9150544070320b14899910000c0102148101000740301c20030441d0301440180240e90340107030010513000402140c640942d441a0411004039a003c941c88080c0051240030512418500300100b180d410641c030060101c070341c14803000303201c0b03010a000250610300b1b003015140d201742c0c803400902085020303500e126104e1041d03417002c0d80014500713012041410740c0c078107005024101c00760000080d4001c403150543d1a410000415421003140382c0f1031a082c2400b071007124451880b49000585440c07041c10014035060050741700d205c4a402c070b4a40b282c0131442c035440d400c044075491f0a0082c0302500869466066010780b00e840d0000b400080b03400028000190020507141c40708444082000c4010b10030010060462000c82c4007401ca0304000410389241108801e8006000031304039070420344030307500240c41c5500150490 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 626134136 1250 626132886 626132909
    0x80102070f060606090b0f0912031215010c031e0c0f0305130b04030209150a09180c0b0c0604201011100c0509010c060902090f0f014b 59
    0x900502c40c2901c03c0d880075001034a04260072138a80324407075219001d440107154082100041900382c555800142550582104043d2510344842100d0340760741c0d68040b54400c06c0c0c0d00b00c071a031203070096229414424800764581c079030254000042809401c000f4850341d4400610440e800030001217004006800c0d082403081e40c83d07640da40100a21882c609241d540f1070300c81d00009010600059403050021a030104289a4038070030580a10005018907c05500406855140807560010290f40e0101440c40341d000300a07122344d9543d640e44d08003051007903071919403c030b400020124002030001d544546968040e1181241c10002c00300000d04000483d00b0100c0225100901d1045044001d124070651040340c80010080360b10b022501400500c03034012298100814001101c040166a500000c000358028115420f140340000a000394000f00b81d030844080160302d400041c0044045103810740e03e20300f5138220711200e441e03803c10042000188123a04068001307464107009140300172098000820784017440c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 626135386 1250 626134136 626134163
    0x16151d030d2102270307030c0e0a0b060a2313180e0102310f0b09030a0b09060f1605073002160503060609060904030c0b070e010f2607030608010207 65
    0x84980c080c0d4403584c1c160103504000700800c045056440d11030119981c15042c80019610844008000c01c44014610340c010404559000c1890f801078407540765040d0a044490401842c10903901c00c2c1c007a0503001508040c2c020310034003a00300d83c040c03003950760b003c060b00209442802202040c00d90f008214188a6480341210f9100c24500706110b10300d910429110340c40060741048440c1d5841c1800303001c1c0c848034817000201146207440170081c001807150841891000360030700307102c1d09865042c155050305048118070046088a044001c10004810154481501d4448181d40c0c0700810103425004424140300d00c040c42d2a0f0884012002d1400c01c01603010f01031803030800107005890441d81d006140643d100404200303598645a5070300d074114200b00c030b010020ba0f50360324007201d4200a254006201145107800d002c03460390041400c0c2040c4e8008d885502c003503110544100c58050403d80984407224103591482030304c03028102000c7e04480c182c50040355854542101e5400d990118008940c6d00000303862 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 626136636 1250 626135386 626135437
    0xc05070330120b0f1225150c02131a09160e0d0501020913020310060c030c2d0803040506060102030c120c16151d030d2102 54
    0x403480c07490301424040e40741c4075466000410460860441a1007959198003c0780d880da940000400e0700140100007000702c003d00d501c1c2ca5200c03130030130600007a00c19280d40314245c0420b8035029007058601110b201b141d010b501443c101c030030280505040c1e8200c0d1090f58a54055034030ba0003034445159824059103401c84d10708007880b0440c2001441d490694510111204010f40e00c0051030b204200200c0e4000714001d128188113009101c0e4002d819400340c6643c0440030303107100d1038015500c2450741520180703081d40c0e0f0798020386217603c194a00a001038012140034000a01401000043c0c845606c1e100701e03c18542054101078801c850000c0e180c0b40340100401040060030441160f1060f402e20145081105800344240c1d01c01d031040c0e0703610701680f000c038a440f280c0a0030040b1250540c400070841d140e0940d00d0290903078203403025550400141400c414000c680c0000e08580c2500700740a0700802c054010312804455001442c61040404e0b03064441c81d1203021a540090400104c1290f20900071b009170a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 626137886 1250 626136636 626136683
    0x51009020c0c0f01050306030c011809060f0f050405010b0a0c050a06050c070506090f030403020120030a050a03051b19030605090703060503070e01050102072102030703240b030705040c0c050703 85
    0x42144c1003107001c10030003446403800324020142000a017840e0340c1e14100c1600c4c0c1d15415075107821070044103103040000505080d40d049003408862641c2191882d4540724000d0105803802402034540c1208108501103a140c841c10a0907452030240c420348141c050907035900c1d001d40300280e500040410010920b041480703001e0081da50410040b200802c000c0041c0d00403180c5034011844040c0c18020058091188422110301d100010025002a80d560308405140502503030040d8460900003450800000c1c11080b013500b509401c2211485013604120200c000d0243c9e07058034a8440e010140c4501d000a2035855401d15940500942e4801103451810072090501d400e001e80e0045075503984117070040001c5e0342c000c90042c00b91690b00192140b0440e16002c0700c404840768600081d018460300400000384000b603180c240c1010000c440d0f0101501c000c1084405880c01d0071401d0744d140c0c00070201000b2070700d8560300a0b450181c107403c00d0049260340b91146410701d10183e00a54075296038000d84141d444403003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 626139136 1250 626137886 626137909
    0x11a150d0e0c040612020307170f0601060c2109050418020901090e0c06030708040807020d0b040308100906050a1401090b0c0f0d111b01110d2f030d051009020c0c 71
    0x301d011170320100c0d05070006561445107114000007042c1070341907400403510a10500b02140451001c40340607580d02c150080455400100586100411011059500c0c016a80e05842000260b1f590380c041420042008002d001010703d10742d101d040c807850f0754010b0320399000180c024440e000002444025091600741004810b0340320921484041007040f210503080024103401607044028a900d8001e42d10104445a0a0703920140403540084100420550b1019807182300f54101e106552031030399102d810320190342c41d5009843c0d1001c69041c2c24000c007031140c8004a00c45105142c02c260302c40d616103c0c0121680903410b44802608080703014010b103c4104844210446070f481d25040503055003038981c0d2503d04c0800456000d4a030107124501c80d82c45101362a0b1041e8007d41901c90641a250303001c8c0c08080b1000e02451030032107000080450806011b1694610a6500051850805010003003002004001e0522030a00c802030b1000c5040d00041c0701a280c0c038072a280c002c0003244007580401c030504205 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 626140386 1250 626139136 626139149
    0x70f09050402031b0109121e0f0218010803070321090c0609050102030306181b1b070f03020a0e07180b0a021509030f07050a06052502011a150d0e0c0406 67
    0x2110304441c1142d0b4004e200c5c03022607800e040c1f0400f01054505c1c3c00207100c104004d0030b007200380403d5111001c2c01447c05820100758402c442e144002c400c40d01981102200c02d07c40c0601a130020f114480c0880d001c0c28404c608075003800714a810381403d000101088401c2400256580c1c1c41c016410320005402c00188805440c003400110b04626107880026214035903080300c03202a502c0b0b070b000b1405200b5914288100000c0c40c3c0308554540d8518549502d915200c1c88200280e44104000007070f030800d21810080591f600900500c031a64208050110110405400c52041060380b40e0b01c0c07905140f451148101401506145980d10001c2440003403038030310304a15500f41d00c0e030107101f440321904000049410079100c001034941c4584807420110304020401030094a054141400c100e43e080400602c0d050009050b40b03624458085080128200e4a1035006402c00550b000d14881c1c0c50f02e4003104108866061801e424504100c62400c0c400b5203c5141c040b88050b8000740f1038020500d01805480040d110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 626141636 1250 626140386 626140423
    0x50115080708280503090a0605091e090601180f030804030b060105190f090b0d230c1e040801020c0c040c0e060313020607020a1403010506060301061e02070f0905040203 74
    0x10160b020b40b911100081514500402251108007040380610684d40021b0340101803200480e6a0b0802400552100d2001885a26400661204500045144042d4510103070489040e51340746401500c0c01014028030040000f941400000c04d043c140d504500038502c220011500d9915500d802d160807170015180c2d5040c00001d00040020510380c0c080100a221240f408000c941b0b20b03002c040d03c04050540000c103c0b120700290ba03a5640203980c00c28103046e6010010724a010403520050504040d058681000283d02000303020308002c0300d0310b00c001401e15800c001350300e0f140c0d48480301401c991016083e003038690450070320b03074030703186800d2058074620240f600b40000035207542c4000a02521005003005490012444500b0554940e00c05582c481640603142e6146c403622080d40450b1420303501d00b114429130030a800140507003045c0050702c1c102c4010f515040c0c180032070b034558414075514050001c0c04600c40c0c1c100002c0d0300702c143c0c1345280040844071000103850515006041c2040744504c0000200c28 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 626142886 1250 626141636 626141653
    0x507030b010c06050408130605130b0a05040b0a050d14090d08070203040308031308070503030f0a09020913053c03040e0105060c01061d0a0e0d02100207060207050115080708 76
    0x26000b00812021540c04200002e05a60301e141046150198174940c20650100490108034650081c004004026800404d0304140f03a40d41c022481da0711401010b40300169090108104d003c0305000500301a10060411504009440d8144806c44504450030452104100144520750b0024000c40e05600c0d26454184064504000081d68900c21840300404d070000c0080010b824140c0310b8445803145034801c0c0d1040e0340c0c0381c20342002c43c0d89030010760340c8060004ca10303004a180440b25200d802c111a50141000e0045d903901007552100d06002c460556031030003401340090f002840e06910046da916541480c880b190f13034440044083d4424041e0060030703a44100814400d007a4400181070440da41210001e07078078402c000d44a8058483c2d644165058051501c004d03040202107a015841130150850400c01032403501c1c1d91603038407507480c90b607131016800c845075004800207a90001d21146002d21405031501c1100e42d46e09084a21814500ca4000000700b0180084c5206000c0c0000404442c801480c011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 626144136 1250 626142886 626142889
    0x170712090806220206040815150a030312090b0a051909050309091b0a03050f151302180a0b0304031418011206090c030504060b100509120a020307031202010507030b 72
    0xc2d08050410404400310480c0d0040d040b140c10f2000c2c1c8115401381c0300b00e842c1c0341c3c0c40d24115500d0744410880703060b221081000035039850440450301000000140b080c521203180d134030f080c0d413420b00059021300032540752034803400410092544070340a01c40080c1c000410f032400801c140c0c0c2841e0000540c040071130030070300c503c00172680000c25078034a10000c850080c5070f034540e5810381c441c1e800c404110408110001c07490007001c1e41c00d50301c0703d44070740c01c56443c000c910341d1402c400c43c0448161000f07203580b100074402211501030f2503078003130300080340c01c4008100b01401800014081110990080682040000c00c100c2055840a100a03908a41d007200e0b9040c040c0c600035106111080c1c2410034108003108903444025140b071303040302004041c544020414855017500003005020211001d8486a0500c400b80b01a4185019424481e0946569150604804004119000c01c101ca900140b43c132641540402691f000d1100100652040004d6454054984006400d450008200d04203240c5082600c0205 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 626145386 1250 626144136 626144143
    0x60105040c053a05040203011a030303190b041a1305010b030c0f120103050d09081b04020d020415080a0f0203070f030b0102010906051e0a0605031f091707120908 71
    0x42000c0509141c016880800b08208460511603640e01d200c0c60070740c50f4901502c60f0707a0245009900a4000707002030b8401c21000300b00303981c2d13102d4499015802000001d041001c050140d04d1550809c800105e0742031a0324002800f82c40340d0490181d040c01086010243d2440c0101e0303680c2580040c01c10500c0150b2504466050038000100f42d8038000100040d00500c6511410484c1e2200c880340101c050a940c44e410000d0303a034020be422010115130300d8079010901500018103401b0060303107040c405000703052801c103203c065040703022155004c1c1d800b4803002c1400341e914455038901c0f000b50754804d085850144444030540b00b110401000e8144100305122525074401c0d40503980c032005050100d000c0303d80c8030040b03004140500c0c020307005900c0c0c4824070840105000c031010842203241202d11a6032540420072040f00c5162150a505501c4075165075030141815822043c143d1a22400103007094054a442c52154070035031030f42c0140e0000007980f0080000c1c641e0900c4c030494203032810400050520410302d5a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 626146636 1250 626145386 626145397
    0x1020409060510202515030515010c1a040b060310090302030f250b01060f0206100311220f1b210e0a110406150c0305030709170f060105040c05 63
    0x4d00c030114031116884c80000f00320300000c24100f041c58080c180b100400313005002e01c031401600000503809001c2682a4824084d05d4004d02d00c1d480500701d4040c1100055a100c038102100f100c01d47c0c018407085842081d0500074030320907405103140c44c000703207041420035090969522802042610381551040402c1d07002003500c00c4445884000b0f503681800c41c0304030800081c0ea0289807444841c1d0301c503c0c1d08220b52428283c0c1210030340d13220f0030306c0c0e01c101e820166104c0034122540140044400810004280c40c0c10300c041c40e1000c00303000d5010450204203825000c01100f4088400c0988031081c0184215480c4101006003a46c201c0c00c04a020303021200a20340101c44540c42c020155594071034070150210350140c00f410254104a4002d1807443c42c2400d0403400f0a504640310301e29004000540740c2803121a24290120b44c4c0d55811014a203944c01d89807074001030121410082020008101c4488034001c4210b004115802066105800000f40b80b404905800142c003443c00c00003241a5035421206488 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 626147886 1250 626146636 626146667
    0x602160905070e030a0c15170a0b18070c020108060909060601080a0605060406090e1303021f180525051e0d05160311090106080a020a11030c01020409060510 69
    0x51940b40c404044605a50880711503034980540380f0301000300020740c2c5955007187c28082c054080300246120513a000121b8440e2070b4581d1001345c0000d000810070b544410900170009004030000d0101d620701c19a809012561007005c41c030a07900310030940d80c000100075444403044907090510f04d000d81069480340790213807c2c14144044040814003095803900840c2c05000090071150f11103554200040605041d441a0200c14401c1d0000c103c108000348480480c0b19096001001030340ca6904101c1c21000014140303002e1030361780d800e1807092901c0307501c0d040b82200c0c0980000e00c0c540014205409024413007201c08041d03145161010850380e10390060b079241801140c442925451500340200b03440f01400e1a0040087c0100d00590409103000c80d10401a02d000f14100c0360740a1000c6c080c8040c1135820f00690001ca801000003540d1750803e41c0043c181d405d00d80c0f802200030010b00001503d9a08062801d440c1650003060030f20000d0418400e5200034801140d4010001003c0c2e0f0016240100880860 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 626149136 1250 626147886 626147891
    0x801090209062b050a021308010902090610050f0403060203010503011b08010501050f07052d010603240906050103080306100c0209060103111c06030b1f090506040e12040f06021609 79
    0x500708107200c2c40011141c00f5078003c007402245041c40001000390b1010301c00081803902031001240400051060803000d81c1c0c09030040d9280d440b01000c10a142c03441a41c1101001800c03c06c0e810700e0309085000d0b0009501c111005030310b079410001090700b5540340c00002c0200c40310712141c0c0400c455100151a044810130b081099071a01d082400d840341d0711500700d001e4268421440c240c401c91140385d01c5070f50090324400c840b039040d002c0d4004047c00c0c1c0d01a48006080711000d070510400c0e008080d85070320300404586600041c10301c0140da400c070699030240d00a5420b0302c0040b04224150070040c0d52a203c1a026241076540c0c40510740c0054804000581500d04060f40d8208121001c5001c808603440040c9906e900219172401c142c010000d41702c0d6010031100c0b9075880002c66158400e0100498403002d400d0045450300d4204408640180302c000e20141e0b1180c0c407121100c1642e1014451460300305103080c2c0742a0740381d00700841915000100d610034021507014644801108003041030103810f640021001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 626150386 1250 626149136 626149177
    0x130b0d14061e0d02210d14030a05060a09090c0501080a0908160503090a0816140d031112130f06090803070308040c180f0f0e1011040e04080a080109020906 68
    0x70804a400c0701070020340240c00000e09a1140c980b40a0b240c005ca0240c20449034500c141e080704a07004609140c403084800d0042c008a10342a50700d40000c1d5004c000a051400c1856070b0f240e008080e43c46040043d184001104002d00141d40c3c81241158041c0c290001030042004503940d00f0640e228040e81d008028400040d800704014062046800d0248001d0010f4440c9840d008015241d0142d105d40ca8904008004001440c80000200b4100740000034031600c1c2c15401030710156410b000026250b20203025100210307404010308000380c0b42003d1541c00d40a142420a07a1040f00c40d10940c22890501000c400c08014504000040340d500d540d0501e000c2c1c0988d1280c2c68003500c406480e400030000003001c641c00c05001c0300d240e845400c0c40c00e00741070207018800003c0464011074051784600413490300020020405865940c1080c00701c850400d40c00c602e01592101c05194171001514116079800001602080b0303560300044080c00f410310a0700c111701d07150b01d0b440055850310564003d1071b03d40070600807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 626151636 1250 626150386 626150389
    0x40501081801020c06091005040f0209040f1e030e030f0d26040f050606010c05030d0e1018050607050301292811030c060714130b0d14061e 61
    0x29001841c0324400075915104003415858684800b140c0c5d800403485403103008007072000b103405440e00a03a0001220a03540c81d03141c00788015180000c1c0b0985d02c2403903c01182c000920700ea585c1d60864140c000340100a01890700d0001c00d907007850f49050744268031030384040454031004101d250308503003981880c804400b1002c0c503458041104400b00c0e014a035012080101703005854440c20701141c4039030290b80641c0d41c3e260055404c1ca00380e000c054019802406807aa0094059000c0c9802c0c034043c400300d503000c9203a603010600b5a407400c1003500c481a015680c01c01040420010f480e007100c054104141558108801010b00c07900ca04018028110101503050803100c006048036030440b60f400c3c0b0a00f1200c2c20725000f200d180c0388a8039440010351615a000207491001c030a403203d100403480505215295410b0882d0340030040c500f9003005000800c45000315144442c401c80007031030310b1821140c0342c95032850707841c00710b801043d0b07000c000c0d10488080100c9035480c0102450f044c042d120b0200d82c112070000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 626152886 1250 626151636 626151661
    0x910020c0c010f110f031e2106030a02040501030f030908071202040225060b13020405150d0608030304030c03120614041a0d050604021003020c0a030c0f080301090f060b0f04050108 79
    0x1400c0742e45a01900c014031426005c00b1000704844501c0200c4901203a06002103000207105d511042c0c60f00c03a1800ca0041c0626081540e2541c120000804840309001280c002400f25042a03008035403110801407840101900b0100c80d1000301450405424a1881c04021410345405140b0080c03185900080040404109103050702081e00424103030a40c14900b0f141000051065850561007159481c60036196141540200c90a0300c1000e0300d680d08407105900d0009035070b00100c92250800d40c0300d10300401e00007005c0000c0c603c1940650f54400f00c41e152801d016000070318035142080c0715400c10009114107604841c000194207020340e0002420ba000c0289070b0f070912107054126500450104044060100c00100107004074001c9904080c064010007065040b0720072507102d000c582d0061080900481d0080440c84c04660007032000c12403080043d610485030f54400d070041d508440c1d5489010351907150b030f403003134401400c5980d07041c6141461020f510f031828000c0384542810013444400085000b41d019 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 626154136 1250 626152886 626152907
    0x10801140409080406020d230f2817060306072c150a030b0a031703130b040c090b10120f060909030c120806060a0e0d0b0109050910020c0c010f 63
    0x100d0f400da1a541c48050003911410341d0004503001847d00640241905098400301ca1300a41c003200c250300d4100d4210401d07800da00100b481c5221070001c1216a00c101001d01c451048400c0300380c4d500b01d000c0036500000074840c5d50103031425010f5840307402086401a08001c03d1601a80041104880d101150040342c078030317040e651030320341d01710100524041c1200d6421001d8a52124542ca0070312940070070b1014030800020512014050482c1d40c100700e130307901d41404015908100048400100d020064440e03110300e09043c0c4084481e6803041000b04010401031080c038000340710840d80c1d4072030402c0d0308000905040020385803501440d9181c0900044410982c000001062038100030700480f011418094140002e644c001e4039007641600e004201140b040c682140f103508020007060400207000d0044a50b280401615600042e06003009400f1950240321540280040400400c251420b80070b8541045000072071880218014845030300c00010210701c20f80310100070300c0c05c0c0014a10b40b5030200c6d08160300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 626155386 1250 626154136 626154143
    0x603150906021b0d030c0528090e0421050702030a1e050a060c02060723071e150b031603020915090a0e1b0d020f01031b02010f051302010801140409 65
    0x92000c00d80c0e070f4200104070502103101c1e41d20100808480701c5070503074092003044814504142c807a034034040021843c683e40c410701e003280d203040e80500c1c2d1a41d03003c50f00389600b0b0300d00f51081c000c1601d00000340d00d2004100b00724048070380740c41c2d400c20350b966002c00d95070702100c80000d00d00da00c6c02541c1d52500b11903014058500760080100c400301150380c1482c000608000c0304406c0180542c4001418442c01a4040c03082071847d03400070710420729144e08481060b00400d4048500c107203003c40b182c000742e41d2114080051800769025200c42580c107030100040755003590095001340c000a4003d5114044080900704803901941c4002c5e4503030300c01204a200d80380c2c00b608640d00c14100e00502284a0040e80442c00615a074002c4803400c80290720501c0b40c180260b5500c0c0d030b100e81542c40c040b005041c155600703040b44506040c0424061482c2d00109290f030210f10100005079075403488150381a40038085d0a411504a40707140180c2d040c0b503000280400414050640102e0b6400303c003602076111603001c0002940c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 626156636 1250 626155386 626155417
    0xd031d0706180f0308040e040c090c051b010b060405090417031303020606090424110408031e04030c050d170301060f0206063001020f041202090901060315090602 71
    0x1c807040058449072255125000d41c112500c00031845001200c400c1d0140d036007050f0060308040c90200b40ca244a40001c1040354800355090000400c078103280a401c004e90030603120303c0c0d00c51002c00c450031f000c001707100440f580c9603043c45840c0c42d05441d850200c0e410f94005403450151655142024400300745500382800e0b007610000704010342d008030b07201a031414600c40d90a489468940904000740c0305000d07613001d00010360b1021040c25540144015140d5918400004117030760304c00c0c49c503004554109500220b01d41e08005a02542c040c0f1915004003810071030900745052030f0440d16100c005410354010b042c050920700b03034002e050080403014074400b000b003100b44035a0b0b50f0315044011721a00800b0035650151260001250071071070011000e0004606800e5041100500001d0340303007584007a52410440d0355402c0051160514404c0c00900290180b0104003580040d14414004120001004440144d1401c1010710001d02c0408905072179000c803030300108091045080000081c8a08000440c0501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 626157886 1250 626156636 626156639
    0x3061005010e0f04061a040806070806010e0f040b0a0f0f0812040303110307171305101224032d0305090f360711070329010b0c070f0302030d031d07 65
    0x1860000907c00eaa0454003600d0968461400c2941c401400792070740d030b011560f015606901030410a40191b81881c004101194200000707010481810b895088040e080b030f010741e02440024405a44880100841c2d80140400c62400a829903140102d00004041040064060040c0d1000300706440040d40c210440315000758000784e12041680c0506100e221000e100d902c001641e280c0300c5181500095a40c99200f2031200c08036130b075401031028245245034070112207901004801c00715074200145214040c41c41c40c80714100601040428252408820140700d804807400181e40442603c882c0141554034010000d14070300001c40040030050315000012a241211401d207101000e0802c0c20b007401c8070300404c141c4a040044a411200300c80f00c030721562003144200700198078480c400d07202c0c0c81c07101142411b00040c2884544031040c00c0c0e1100700b58200116080600704001d100400080c05820891807032107141d94040307078890490301d80030400d040d41d0304401c4070b00c21307400400c5000b0700ba003c03400d541149 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 626159136 1250 626157886 626157929
    0x1905120d060b040f180603031e021c03060305010b0d0206040306320709140a03030e0312030103050703140303010e0112020f100c030e0405060303120408041a04030203061005010e0f0406 81
    0x268081c0c485c080413080d543c9981c55060400d849070310103490b01583c802100c00103903071654290071051454031086104442400758400c2012404011441c620340d00401d4075441d40c2080da00352002210b01c94400c40c049050400141d5440341184c0440b5030150000c16900ea50117500801c0b50611448101140d01030342041e140103442c2466144101d11a40752081c0320b9440788074900d0325040d40281c03a90801c02e000028030100e4011a00000034900080c22148000f5805c05441425003080c3d00444c0c1660000c0e005004000600d9000040301000303000542c2150301d80000c0b40a0000103100d0560301c070854000f44819501c0b4040743c030584110107001c061800292035001404c040c03000d0019400201c041003100411301d40b50240c1800b5220050045090846603220b82c20303141c034060804c44429004001c0012414400c114440f841e05080c41c4e126152440c50041c0350400400804009411502100c2801030740e0304846a100c150009036291202c082450f40818000c02c0d060b00702c05d511030100050344001e0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 626160386 1250 626159136 626159159
    0x14030705211014040f0e0a0209070503040c0911090a0b030a06061106160c0b010909030f0320160b0906061807080a050c07081b1905120d060b04 63
    0x6240c8840d6554400c0d580248039a4040302050b0ba03421540741c1c40080c1008012100c0800d981c40d01402000051011200710300b40c0d04503281044035422a400c84180c90040d80350042803113511050a040551071b52a059542a111240c2030141a44407546c44007190040e40160040da086903202401c1d0f04107154882104282d640c04c00c82d03000580e00d00302400481c8140c8a94840d0b44880b14250007007105441c2d015680c0b2103c0c0c0c81240c40d504101c1b10500d45c43c046240d242c017841c000d0025140000f805406420700074444140801582d05050410503004050b16160444026000840088589503105030340c5c80d0040041c1c801014050550680a000c182e02000c20b105028000c12541c0050322001101c02801a0390111510780c0454100400502198000c1d0050b5501c071040b1403880745010025643c1907082e070043c0062203151241c54408000078041000280c0003401308007503003449041a5500d80e030f5100030142c0b8642d4043d20100300c150304008c0c15001a80a85000d210031a10350303881e075046400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 626161636 1250 626160386 626160397
    0x6130803130b13050c010c03171807030f02011403190e0f070e0f28020a03060f0612150807060e0f0301050c032406040902160c060302070204050a0b01051914030705 72
    0x9544c0201807400045c3c0d03001d80320a034151581a111202c584405500b07000300800c00800c40e07011500b10b102e811066a10074080d03000594403408502d00e49003103a0000600c54034006e45d900355858010400e00500000196a01000080c402d0020a84040c04d00c0091300385410801004840d12a000d00401c0041a80b02c40610405c0303050004d03c42c0b941c4002400c2d64034200292811860421607940b280c2c16540f5800402c141c080300d0a01180c02655030a82115454281c0d21450024204942a680c2d20b401801507c056240003001c0c00c1441d8107100c0130a4440400d449100240002c814060040e915058001c01c0340b0300c80100200010720b040b01d01102d03d640f044441e804590282101e0036420145d83e283c405800b50040e080500300360811000000941c815030445e0840701c178014100c40001c06501d6004050100c2e50303005611420b00d0310510080d0394003c0c05441050782030202c1040c07a66130000540f494030508003a5440500090707182500c040c0030040b03040f02015800401c01c6180c9070080010f0a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 626162886 1250 626161636 626161643
    0x30b100e090303040812070903080d060905091f0213050301020f031807060206040b04060e06070216050d0506070525050319020c1305071407050c03060906130803130b13 74
    0x140da9482564840d202d20045a0082449009110742074200d041c54080692115040c01d0001d10980c49455080042d080390403000019520340e0020f01c0550f48500070560130500420081070b420200c080100c1c51103011852211809902107420060780111002010040c90041e0086680d881c010307a104400d60b00440b19002c400c41403044038500d440c00003e668045400542c050000c50f1508c0d502d2681100c0050800c0e6013480e00c4080b403203140342c028041c070341c010110f51300180181600004001c0c0e01c61b100e03a01c0540320302c500041810100d80c000c103050354407201c1443e0865030f075083c1c0e110300580540c99029401e10300e0301d500c4040e001c229000000707002e4940d0300f0351040d2508020140885e6103000940e0440d400c10241c070704448020391560049a04440642448003c800c1213503040c0c1003603040709205407050381c4000c0081e003450034184019500400780e000030f041d80786000002e0810108242400a00080713002000611000601c01140314465001e856400503007082845240300c004100d4042d03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 626164136 1250 626162886 626162909
    0x10b010801170303040210210506190e061507080304080403060f2c01020903010c1e020120090f060d09050721111804140d08150402030a06030b10 64
    0x204182c05071015424800011000952075682c0e40d03400c1c030a09015041c0c00071b0500c80414040190100e0b00b0a40503101c0500c2d010018040c45c4c14400c010881c01429090284211207072014480172040c1001d05030b014005480189503240c0721641c640b01c901c00e60101030301280d80841070100b00220400184202d0b802600f0601c4612164049502101ca03060b0014050106400c5150900d60b076281c484070912040d4070006090490100129081d1051500e521340005d51480c24029100b890380755401d000012480200540143d0b4540440c208181c2c5540080c41c04010900c550300340e440400c48007a0b1040a84015210690341c280e8002801514008441070702400c03c01203603c00301c00c02e03122104001d0f03003c03001c0003003500d89a4071a400c0c081e031078182d04000400c140340c00c03408400d00b41c9400b03284100ca00320200300e0f08400e401c2c1040000d071400c40400c00c0b91418082804a01c0307607407040300c40e01203400613603e80b0f41844d4403000382081c1d8401403074108404100032030591103011800440c2c1307124001c0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 626165386 1250 626164136 626164139
    0x2191a0403180803090a0302010315090c0306080f0a0519170406050702212109040501080c010206100b040e0c13180e01020301030c03080901021905031e1e09031905010b010801 77
    0x10f280e20390090809240d000003403014204090342c8aa08500c01c0d55841001c0380c01500d460340e40140c00e9640c0140143d0100b80c481108112140c020444860078081e050050150501590b5407140c0300c0c600035080701d011003d01d00c070010030f000174004035002c1d00c1000340f0000c3d5201e94521000d0b0440d00261011783c4221040b030b0240411001d4071070b0103908006444050168552140342d242c0e48a100798000c0c040180e8213005040940c1c8840c42414041c040e11001403010340b048200092520030010200301030040c20764020022240702d2400d54007610411204800e1940d1142c52001c101c5c019a8199503e41c14404000280d42c14500c07140d40500507440320600030341c10416511800d0744020b1000415548981d0300810100c1d180c90090b140d2148140f0544001c54003540c6048400b03074800c41e00b82e60b2608001003012860b1035800d000b903248040345810380d0504503c0300d43d0300e100211400440c180203500050098003964207016041070a41041f0890944c0d400714202903000309030741e82200340441c8040c0e00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 626166636 1250 626165386 626165399
    0x30c091203081b09090f10270b1201150302010927020706020f030705120105010806060d0e0f0d090e060a0503071701020f07080702010806010305060102191a040318 72
    0x100d06020380688404486803105001d210701c0f280c410300c0801505905210014607982c0e4500303c540100c95003242e04104e03003403242c009008400300b540500d10503500000c000c41900800204902807020048000a0316928040802d081404010003803000394070303140d4000f0403184001c1800c0283c1c0d00030303a55000629211183d1031000030f51005408a5040441c4018114020680003000c1c4244030b60740c09401d0000f00802e40c00190001da075000d020071004102601c0c580c1401c14840d006210901e80382409042c2000820312a201d588000341d003041e19140c07512841542002a1104090514100d50401c0c14021008040724503e0103030a8450440a004c079070750b850449154001e07140000c024000a601e08445100041c40c0404500c0f010b5409100c001302d244054400740041c6030060b055107680384a903200050559100030911030505251a041c05482d0f6400a08524094182610414078180e642403203100c820140c650b02c109440c4087c10002010382c011603e844003140b10a21821003501c900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 626167886 1250 626166636 626166659
    0x81b0607030e030903070b0c0313060c052107020103020c010e03030c07030207050306060f09041b06090305060609010b0f0c0f01050702160b0301060f0503070c02032a040501120f170307030c09 84
    0x111302c96041e80402014403410888100412a04900e07100b01c031701d070001415014804041740d520850100f03404100c00707000d21034240048645a04400d0342c0b05207089114040c52101c3c081d1400283c1055800b08074940708034400d511600c004961101142e84074030f0605400c1c1a42d07482000d0850040c00340c482c0000b01c5042c00103c0302e005140003401c40e02504480d1003030065519004100346c4001036201c0c0da504401c482481110054142d69036004001d40c2541016460800003403c400d00911415004000d41c992800544075800300050100341d4a0360380c2d0144a142c00d48032400c61034654030300790502c100203400045425441c001521400103056803660604030303e0100340710f81804211003141450403280304200547d400400b50408156611145d00840c4c90504000301c5003440c82e107100b40982901c0d000414600259908607070922071036062250b405500e01465074001d082100c00d0f03081030108040c03510110380940d502e00107a502d81c03501c0788005018001040c07000c00415810b4901160340340c1e801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 626169136 1250 626167886 626167897
    0x10209041b170f0406111902060105010305090c010206040602090105220504050702030c120a03140a0507020115030201140c0a08030406050415180b100909031d01110613081b0607030e03 81
    0xd0b040780b855a03444e51a184041c24061003000c2400108000106499642c0c1c2c08524000e03074284e004010640c14a4009800c4450242030000303070783c0c008900d403421680c5c000b441f41c1d44241d01400160300d4820b40d10068400b800303a00c02c2010103034400600da91986190b12841c03021550201c3e000c0c0b01c0da40368404181d13100d02c640d840f540c0d070035000040c0081c90404540c0041c0740c20b000d40e2400180703051070a440700d40e92100a60b04102c50a46510a00132100d909005513660508244400800c0a1a560000e0302480781031010780f540d99030104086c11111001d000305503120b9002520190340703240c0792400d0801003804450850390904da0508a146445482c402e508800e520302c0310a01c207052440c0c4030b0203d4944000c1000d4000300d4000408620f05607640642303c0c2c403600c02d865001780385441c4060840700c000401c1da014100034004142911700d0600054454210807066828403002a040c100075a0350300c9105c42c2d44280c6007a021584c44250380010b1482c2c4039105941c3c0c1042200d5201a80390303180e1049 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 626170386 1250 626169136 626169151
    0x20a0620071b0504110304032d030905010e0a03050c060114010c020f040b120c0405010e09060118090c0b19080c03011703090409030c02011106040c06050903010209041b17 75
    0x140100c03070010b054010080610400300142020441c1c0d601c0c0000d050f5405103158400e41310b404024442010303000749110008210001c48003600c210190740000c9102c0340f100065081584800503032061008c29440300b41185404000c0c0c075071002c1c0e5420080c16680c000b80742c028251188400010344840520152052100140c0d40c0014542c95034082240c000030309119a039001e6030302c0c0c0100015648850040d01c2075000341700500401d00c0d07075504010072520140d1280900400003410895250000300b4001d0541d003600c07882c00661007003045400e004010340e4034010800c0100120209a2151080281c01c000b8280c0040c5c45a441c0c001c00d007205c884805554040f4040404c1c0018041048400c1d005420300842200712814800c000000509036000c0e918141c0c007150602400c807065592210b1540c40541b21500100194105543ca61924052a20414040120100c4d0180503590300390100d554140b401801400085112101859803c180007000400700340040d104102680078580411701c50680d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 626171636 1250 626170386 626170451
    0x109060e0a091b180b0d11040522030302070b0601050a020c010819020d0b0f1e0118080607021b010c030909090305090901092c0a0f061b020a06 63
    0x162041404054148a40112010722039030054050300c401c1c1981581c01002c40c41c45403a080100c0e003400508840d110351741c0a000d80040296203000c01c1540e9112010b2180c150b500050340d0f030325000092049400c0f4080b816220047e40400b03428543c1c15000761252034022081244207854020040d00c0358407031802c003100583c00020000d4025809884030039400080030700002c82030880040400c04a81c82400d40e00e4020381e4404400c003081c2004c0d0448030035854181d8140c22030b60703200700f00301c624801c12030704a904121215000340010910550000001c6c10580103d035200e003080c100203501e500c07c5007091141d44c4107010b079002296104282110105070103895200c64203007401645c070f0142880c190260117000b4100f0070001c581e150024070300c0c0240012000002c580c0c41c41010001c100c1346050101861000740d01403d2681240410740c2d000b150703840b2840c0140a031040c0317004000350001c4034800881c41c20085407517425540118541c20003d10448003000415036100c0c0501c41103061200d80d240110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 626172886 1250 626171636 626171641
    0xf0903060f090a030c0501020408160807050103140a090305091c030e0102210c010908041512020304081c110a020c0a05100930060c081005011e050c12040602060109060e 74
    0x5d0098401011450040c0009450b003900d4088451908484030398182c6046c44070101080000f40138845c0c403000d0102441d05014082290303100d22801c2e140074017101c04c29640c03041d400e41018043d000319022000c0250001c1e5921902c00100355400d5007141059001c1200786111810719840030502d00d81d010781807028170a11051600445403079800010406070f00b9945c91141101140e1104064001007442c02c09810705400300351401848450385541c6004414014424440000c0003241604c07410b034140000d40288a031921115030240107000c3c1e4a401842c00082d207903c40d240c0c00718020110402c252020b403044c2d50780350b05110342c090040c0c0480340001d60491061000721110100c88105130030b1042c000b4840c0500715000d0750090401c21084030190b542e107404c070341c0460300072981075031085032004500d080c54600340c00a0490b084101e012119000d1040522103a03034004c3c4155008107000108a4442441c90002c015032607005004942c00b6214480000809000502508040d54070308482c1c100310344c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 626174136 1250 626172886 626172893
    0x9050709090c030506061b0a05030f2505120a0e04060e06010306061d01030e03040b270102150a02030c0408030d090605130321060806090706090b0a0c020913080f0903060f090a 77
    0xa0030f01f000c1020007805035100e240007089042001c1d24155200e500d9041d034a60700140c4140c0400c940e2201c40b2001c1d4500111503002c200007081c0c40f40001c0c40c11142641d680300413801200c03844450000c86600514020780401c11020040742140b00301c80a0720100302003a12400107442c41c1e8a44034200c44105c507160020074040d40300e90452407454440c90201c1e030520383c403502c185410b50440b1143c040611000e0006064200000f000800b0380a020b002501c510195141c0e940002607000708684c195580000c04200b00d081400100c2d4010007412050342e48616504040001425642d0810303540182007070041040c0d0700e0040324400103517506845e5001180b16107841c2400758035003401c05a880c96079500000401107001c0c0704035480b48030f488000d004a6410280c0141c00041203401004d1526000e21a82101c140c001030001c9046d80c04646100c8260780d0b9443d802449403100c440241b034140702291301d04492000d4405003402c49030450507100075a99044048507550403c0710b80f42d805622520441010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 626175386 1250 626174136 626174167
    0xc041a061b0109120305070206012c0711010f0501090f020412110d020904050f161d0c0c031303031b02010504120203010603140a2a0501110709050709090c03050606 72
    0x144407001c0000c200c840442e1502c1400740041d04101d00030986900801084c0d541c10300030709000d405011000407801030a500889540c00030300001c00341da90300d414042810f0754060a40d203200340c01000028408085000030b00e4014003801e1042400060400c080106158014003e5405851524400e81c0d0706035030b141c8403c001d4007121442c40d81c001208509040c0580c4605a0f139a100d180250024659140c049880c03034908003101e000c0070450f80e42c065042c803000584000c8204601465010b403401500c0b003001c1504148503550401c0e00038400000c4051441441d290036100300c9000352218021061540d802e03034418812540000e000400400c02440ba40c02450ba040d20094005000041d44544903500d80840a0030340072186080d5000484090410107034080a801881e540140d55540094180c1c000b0203181107405118144144811101400300040050350010003140d4002e100600f0425000f400782041400380f1f0320030f1810a08001551390182c090b2a00411300030303103e94a42500c0c0304080c0310303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 626176636 1250 626175386 626175427
    0x60c0703210f050f09101a0d17042402070b040627181a0d02090601020a0804090603110d05152d0901051311040c0509040c020c041a06 59
    0x710b5620b0042140014540c8107031407040c00b0050892190341441440c541ca80102d00c030030801c01c24204807404d43e1403402008601c144c0c00054410039030101e4940f400d64031004420449508402c004a4006401c8126203c0541c01204010480484401d0713200c08036111021360186103000c1e90104070400c070841c0701e41c80e11004d80641c10a440540e0b601e181024140e07a1860b8862a0480c000000c1304622000520403030108100110002c00c00c08901c801007806020a10800307441030303040b800002d4650b4024059240b46039842914140c0d0323039847e000000001d00040c002a600b8461410320b101c000d0510b000c50b1100c07180c010000b0030041800e0f44212010810042001c0007116566006c019480450030745007681c08480c06080754039151203500903003103900040030140b00c000041d1000340032a0b4007018850800c071054030042010800c80a007030328039104081516411529000c841030016034003203880c02c3c41540803a001e000f1a20403d24200101d41d0f0915a194010030410416030820380c404020075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 626177886 1250 626176636 626176697
    0x6051009031704030206120a050c070506040213180b0714030106121a12012f270904080c100c1b1407270606050f09121e060c0703 57
    0xa02c3c103030300c030b40c0482c50903003105e44441201c000d12410320100da5803500403140e10030703540700c140c40c01c10825440390383c1d90b42400341020b409030148080100701da009582011195141480102406000a00d40009401c000b00d43d00c000183c070803104207013820a0582220b0485990341c2c3c5200071a5500100340005010116424004841da82403070740c966111076141c80b221168490000074002e0b0041d00140d506c0e061540070903c06424007a80d42c80c1010789009440903800c483c004107030031480c4000030380e041e1400c1101c0141e20000a08c108020064030100910700b0310000400e03900405450000c000a407010740c899640840c2d880c03d001d41d0710f950071a81d200e83c854000c21049046c2000701010a0600000e5000a0908102001044541c0c240c48000c0206a40c595a081103018075103580103203140030700071112403115400603250300a55509000301410140ca01d00b610100228034100b50240c5024103281035070f0740222070025040c410b0203401e413032059405860b40c1c00d5500c1098249a00b80f40001c1d00f01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 626179136 1250 626177886 626177933
    0x516021e030607120b06161e0c0f1403160b090307180203160c030503040609051606030b0109050a050303090118080d0e0a120c09020a09080102030408030a0605100903 73
    0x480d02079404201d5039006031941e450340403580031209801d600362403da400060040390104828280c000464242200041d0010a1440c00d01500c00034140903183d1004003410090407030381c000c208141004ea808040b40d110140c4020107244200605440b600761ba4501c0100b14541c9004004006070407005094a550007801c0d1800c0644800c1131003140c101c1c0c001140b405540c040100a2118070030360701034207956954188070b46220425a4004d141744001030000f48025210913040b401c12000300500960f6403580c520141203181c9603600140148540858580011003510000841d41801c2e141711050b15405000385184c1000a401510100d03014000171302c1da03400c0881700055540302480124845103442c0da40d03410000300b1a040010f000c00729003003040e040c0300f000100c03130005a10144140031144218000750b2142c43d081002d81c0c6030000c2d0380c80074038154000800c00c03040002400c0254490301d0035040401000c0c0d100d0040c000714244402c0042c000c520307503410030b0021886901f15031103000e500c182c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 626180386 1250 626179136 626179189
    0xc15091d2e0816080a0b310501090b0606040b030a05060d210f05040803031b09130518121b0705060f0c011d03121e040b1501051602 58
    0x341080665400714100e0f07000709850300030000c1142e11000061018030300410079a1129182c007510364002a14103444100820032250400f002d41b4040c03000d20b04881c83d050403864040c200a40078000000741152409a034034005001c038644031059a007507600c6480d220b400c566645128500910002d000b141e0f22064400702d8100154021150810024412081000901d50071201500c41641564250300b0301001784800c0c4071001002083d2035100200f841c3c076555024041503081c80d40d00c10300301c855400c1040d044000e800c400c0150030990046c00c8400712282e40000154283d910f4103800b0300440302d210340410403000918407591503600d140c5084420b50f41070580c0c44d00001c00d594040c81e100c10000030085940d080c512020700ca40d003c603540500d00180c516400c003604c00c1e103034400c0700d024a001412000c04035a00c0203d50400c00c50203103c106502a0030700b03150411102c0c6420883d4007107500c0314500796000d0702c0d5100340159a40c071071041c840b008140209034208a242001000600302c175142c481d50 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 626181636 1250 626180386 626180461
    0x122205040c0e0d08092e0305040201080408070c031506080f1504230a0b060f040c080c310512070501050f0c030903060c0301140f131104030c15091d 65
    0x1610143d46c11003404c00ca40d86042d8072107034038202c880020070810b00d0302d0130f410080583d0700301003115840760b40403c141d552000c940c50400032207020341c2c1004d4200d130040380406203030031000c5e809001a100340104461f00404840a6240ea82c0e04084900c02030850400100f000070b40d00129401c02818403000c4909280249a500c500c0c0055500c3d064032000800000e01c08503040040d00c3d2680c2c034030151800d1201e00c9642c031000c0e14030000a40700400b014000524008100b100340c00c500c50800307403d2058004c11a609400d03d0200075140a002c1c45015036849100741c010300011081d04941c01a1500ba0501503000712003403040d00681540221800304000d85511690148407603441002440856602d950405004400000c400740c50a4010400c052801000355203401c1c5600e02807030025400304030348607888042e540034095071388024003400c4401c5004c80d0400c0c00308901d0003e85800d9071480e005a648105080d0796a08810f8108126521000825144840071b5021010b11a4004051012120b15207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 626182886 1250 626181636 626181649
    0x807021002030f010501031109010c0b19060b04030303050c03010f0308070c03061e0c140d0203070c020d05010e0c0105032712040b1206060f0d0509122205040c0e0d0809 74
    0x2c403c000e03083c1c01400103010b50740c2c06120b0b03660901c2140035810300700386241c80040c154460725803010b801c410031070000840300c00828240748000144250203004140d0346410030311040e0890b0004801007410800060424107c21003600d0488030001c3d981c00c40035241d5100c20200e07511141055400500e2440080082902409403c690340f10140c90341900310f04503801a81156091a0207408200c0010224081118144d0585281040c80d00c030041c2d0701d44540740c0540c0c04011046c2d00a400c2440c590341f400500806502c03840c000e030015001e441111404400442d5644030455940e9120b0080740013442000aa41142d1380280000c081180c032902e00102450312184c000d98020084050000703034502c15800001141600a2025280e06007003140401c0b81c0b060f41c1c0031780380040d030348540d5030800200025810017110307100c1d18540c40d40e03e40d0399800003082ca5030f00701220b083c000031098042c00040d0504007482410b5050384241d40759850848000104000b21202c140d040e100820184170002c01c55480c076 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 626184136 1250 626182886 626182891
    0x803090309120d020a11030c10050d0501120210120b030f0709060902030c0910050d1a12060106021020120f0a0504050307030e0301020c0604030306080c090c0a080702100203 76
    0x800854031030809404000094100da109010316400c43d440c034028a58002450210382a4419604601e001400012900d42515a0821580324503d440c0c040d01c841e03000001800e00000c440f0302808aa038075100803a2404030005002508007162080000c0e000e4417035000c0305861180810041074004000d0002460800350303c0d070000440d040110100124405442502c0c01404012010b5046103410710801d10240640e000590003071154101c41c00b1554400e000310b40e10010681001c100564a020f41d802c411408114201e00135800408008912000010744038103c0e286940102001e100c4980800054044021402d441303643c480700101e00c10207608090000515402030718101031400032a140c4081501510500c00149003809010100b400403085600705034250810460001c62140401c1c020301c038009400b075039401418148003c040d41600110100e51000c07040741d026006540400c05010750564902d00c04034000c00c94000302c1e0b0b00615002d50b00c500980151810f40f000d5208130350a070b9008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 626185386 1250 626184136 626184151
    0x21005070807120e060112020a18091a04020d060f090c09050916150f14070516050f0901050d111e040f0924060b070c05090604181e0803 60
    0x146002c2100c2d482d0300003003001c032010000b681485504510207505496a8042c068820b000c001e1102480954581c848640002c0002c0f010500e040f441c0001c0e010010186440201c45111721040210f2440750760343c0d0b1365800350750001c24840705200141c2e01c01d001425080400782c0b04649503030400020501000340f4000070181080d01090600d0560b14007130130300ca0080e120311040c81003010300f03001020300100410b806600c541000030120150b9401514407031031848520040ca0800104003081050226144601d040e98401d4180400e0f00d4000b001807c8003022800ca03000104400104180c1c50a00c03c0b0300d131000d002c1c04084040c0010240805d9030081c1201d40b003a4480c10320032642d0154201881a500c80004010041142c240b040da1016004589030100328604014401421001121913100700c000300046941d09030346216910b003d801110071486507500c1030f00580c00040a80c00c1a000f0200030002040e91998000969520b080380c0d10500111804180c2c1d102140c5400502450011401481c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 626186636 1250 626185386 626185397
    0x2030106050604120c1e170c1201020711012a060b03060c041d012d15020a021c0f0f05030c100605120f0c01030908070b0408031f05010801031202100507 67
    0x740c1090564824150701c07840c1904214044468000b44400c461b900b0b4070b50b02c0410600c0d00d40c1c0d034040f2915005100000c580d0044644440c0507903a5015401802241e01c00d4160782d07918050b220054072201c240100a030350020038a0f0b0448030030341012281ca802e00d031050394009400d40000c0d011a281ca00c04a0350081d404c40005020700100348000b8660241d8079042d03055803440e41c14009225403080d8002044402d224000c94030005048005851401411803c04040000103061000035903651400800b84d014003402050b01c0c00f44034442c0546030015801030003010a4104650310040d041d40c4640099525000602280704001c0b001d0200002c0c4030340181d008286281400d0410841c0c10201c804c030702860703002e94082610000081050001c06d8000d0070b00151261300b0b410045070314805d50400034546017000c8200400c000100011314082c1d10001c8a9030025954145420005001c43c041c40f8080749030203004000048002200d5014480030344144c40c04443c0203521001550307000c0d6280c2c0d02154 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 626187886 1250 626186636 626186669
    0xb03040b010e0103050c01050a030917040611010e1b212d0c09060d06020f030708010506070b0f06150304060605030d0f140c03190e010219080d050402030106050604 72
    0x80e40248a40034114200303000800707503d1030340d8050340c030395002011605000c0041400046070303009070701286d000343c1c01c07202803100c1040e1000084e1541d1301034000c05011422303844612103506014421002d0843c1d04000406031142c03201244130300700c502c000c04950b114410f0030321111003080c030f01c100110003c2194000e150004111603e502080000654142a8004084003016040000401d030138148002e43c1c1104032500e4290200d20150079020014000c940001030602c0724010f2600210f208844a80c1c034075007541d0300d910410186204d1031001605004001000c80c0d40520794140240d08a44014902124403109900124032600120f4064900c0340d0349070420460f504040c40000d03c40e074194540a000c8021841015001c601844500e440104001ca1090b0300601e040003150182c030b0300380302c00d2151090100c400600710240325140c0341c0140521503030b00f51283d0160b80c0e0052150b501c000780a0030300c0d4010507110018200240107981c0b540d04ea60000645d0340b9034100a00250020912420166 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 626189136 1250 626187886 626187893
    0x414120c0a051b0d0b0a02040b0f0306090f040201020607030209031905010906150b0409020313050703050f12040f050f0f0603010902090f0306061c080909100510080903031303050f040b0304 83
    0x12241c1c00580801d8421125460360136600d21691100150340500d011626807692201c0340001d00030b035080152049000110900b960511070f0140d449114102d6001050760f0303950303213801e400c40415600280940c1c8064086000c0d14060b030041c1c400c03000c015088440742c900b1030646408500c0721000540312a552042e004040c40060b012301002c4640302400724041c90300c3c00005400f28441c9210b1204a80e50200100301a83c1002c003071080d4180d0001c007280c49031501da0802a489813402520749200348580c0d15004031603080d6406071411246a0780300b842d400785c508421302410784101b820855001400c1d01c01e2911540e82c000146000e840003420068461956000340411480710941c0688a648914100292a6503443c0030001100106401c40c40e10f41407890701d15280d001d061349155000318800c0401c850b5014500e106021a64101c6240090502c0c08100390742e03200007a240c2d0300b029001000000c10552035800c0c6104814482c0c544140381440c00410588190090340201458107000004d21027130 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 626190386 1250 626189136 626189143
    0x180601090e0c031605010c03090b0d0b0108011431060303020c0f0a0e0105041e060e070318120e01020708071401200a032f0109030206100803030414120c0a05 69
    0x80300b0940c01028881c0060404102409151049504110003241d9a030100351151744c0d107800903d400700095445404e01c40e070720009000300100b81400110b40030f00004134000c544511280345103020740980b034a5081108905012075440a15030070007200c14102a0700d54440d48140c40c0110b010340d003d403803410b44050422181c04454000240319903501c00d420321500424102c00e50450b0320840340055091b0b490017843c804003c1002002d4001b9107440d800054202070031100c10b02c200176958040000192501c81d132803041c2e00803c806481e01802d032a6042c41c07240508805480450140100d075403282c2e82d10200e91a146c2d03150003000341c1c8107900303100306505e5170810040c450100014810008811300700e030641781c1d42c00911901500304881200e407000189142c4680648945200400d80e400359401145280130307010380c0d0000c60042c4204000070b150f0305104005203040d102ca44011358915101c0e80c940040140c24a14050303200c3c045c140c940800300101000500100010901601c6d0300c0c88281085d508 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 626191636 1250 626190386 626190403
    0x506131d07090f05060d020c0a081207020c0901080a0212010b06072d03021b01030b040e03120108070f06032c2103010e0106050c0f01020a030e071a12180601090e 71
    0xd03c0d00780304040c031940e918002500c5040c40c002034016181c0c000b0301041441d01700000c42c0a04001000a100400c10b2100c0b44180d100d00c038a60215401c072410442807001e035407424480d9801d140c10141c80d480040c50003000c03440071008482d0000c520a0000f4001072040c0d0b2106204541411001d80c041c2200c4551034100b40040c646d65201d0107002040351006502d94240b0b1480140d107101c110304010302603002c0d034401e8010420107082040034110500142d42d0380c0d80003111824440250b200000b409000c0007800300291000701003e801050305e4088140d0162014101c4600341c0003d9441d44034000a104100024020030000181401510404e0039038241489403401101c04a00b0801809039048054100341105c8184c54559075941c5001c01140c1040c00c0070410b0351155000141c00c1c240d055160700016542100d04081d41c606585e6499030307001c1260810600c07078a03244240000302d08100040041f0340d1001511018404040e5514441810110240c00850405d6502c000c5220914400c218010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 626192886 1250 626191636 626191649
    0x711092d04020102030a08190203190b04090804050f011209030c0b0a0b10050a0c141b0a140103020c07080303040516081912121a0411040303090506131d0709 69
    0x1d04007900000e460f4890103c66505100b40e40c404540302d40b07140f200c00d4000e1031003940210b449050012100c10380c074841c803440b050b03030b80c0c2040c4000d503d6240c2440b501f82c0c0550310110760b030310340b44c0340c0024080d07034100301c0d03810b1814410304456802c1074120310b003e80340d102403095440703041da807080b0700c0d10108008015080c1c60445252081c0410305407600c03040381220302014180682c80e090b2a07041110400e0341c00034020408404441c281c01c06690011714410100000c21068551410030014480e10402034460302d05140d4540031402c07803e501a03402490002c000304280d92409481e101e10500c3c607481030b10f0807900740c4d0129000c0035107002561082d001804082c4080c001c7c0c1d10b4002d00c0801d18403142d68014060034105000d03184458020385e06a08001c1011905001d07080b90107148440c064079404030240542c0c201145a42140d042c4412601600e501d0b443c4c0c4112030f42410284a01d40c0c101c0103401c00d0165402d840428440c1e01d003011280030a02e401700046680c0f400c0c40c0001d2001e980d591015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 626194136 1250 626192886 626192971
    0x50115080601030633060206130b0109020706020c0a03050a0305180a060f0e0a1103070e070804060c05130902070c08060c0f0c01060512100b010c17071109 68
    0x500c441040403903034070b0442c0e0700100c0c04295001d1a4130980381801020700500e0102a0f2000b51400742c601000c141000c45000c4c0c0c081d100203170759041d184010810030380401000079080310b005122413407840d4060025a406a07000500f480c01008906141c045030301800d0b80070944c0480c00340009645070180641c0319041000004214041d0084a603445c09441c50080406072a002c80d00380b4680745600c4011407001c5401280d022948074200901141000c0c0c2c0e01d540a4003409030085407590301755054070b02079444c503550701003199101e4480a0003408565180d50070448100002d0702c0290070f810320600a02500c4400582d1600a4034100b1454807040d0310819a9410403002c024180320342c403060362882c0c1003080d40c0036a140c40400499004040a400a50b4041c42480601c2810302c5c0c00034844581c003205080410440c102200113541840303507a08e000300704000c1314410180c18481807019007174503031244a0b54082c0c040c881c800159034110842e44075044540b200c01e541800290308814000d5003983c203007803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 626195386 1250 626194136 626194139
    0x3090904141f0e0a110f041103240306071b03180e09100902010518060408011407120608030703030207080d06090c02120315090711060f01050a080c030d080702100216050115 76
    0x542c6a03000c12521114841c00b11380486c1e4044c0d03101d036005489021007601d0710994030315107110000049510100103041545c89460340300094100042c40d180141d100c4d864036030082c000c0d20341d949440e405a10086003000040c6c0c4a5071403103004286a00040c00654901c4107140c686070198500d0820070b00c2440c1031b81414800c00c480940d80220031900144c01d41c048000c030f400010b101041c018801c50340080035940c608010450701c900340a6480303024115030f94442c0c0307610710044402c905440160144107100e4004100100009000f64010a000384c8118100e031b0074005c41c140300e0405c03903a603544a01ca009845e102c017500b009070305015014103800075aa44a0540c01c0410ba41c103030f14889190514001d101750700c0860280760007181da4510003000e40085461520704401c000c000c9a00a02c14070740520364882e0301184001000c590800300381780140003000c1e0200c0240d022100082e0103407502055010308401001ca1500c240001c205c80300740003c440b800300c1d08a00e840703401c484203640700c0881c50b03038124070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 626196636 1250 626195386 626195393
    0x312090c0608060607050f031e072f040c0e03240103020f120316120309030f0c03030b060a03090c0504020f0706020c03040506120a140903090904141f0e0a 68
    0x1050007a50010714104209945840109106208801d0041d00c148142d280c00c50358540c0000c0200112841e0058001d0025440b50100c603040c050198000c118208441410242016001c10a101c40348004108055203c90b0b1011030200d82c90212440c0024100d04040b06541c1000c100031040f190004000c0340c00c031f01d00000c1c2c500582c030040c04001d01c120382c1480010740c6030380e50002c2036444064a0f420b403a9551500c4119641144016104a03074008103188610f5445010b07204007403601e60140c03500d120328620081d0817210300c0c003002c07001c605040d07980e40700109541703400d0080d044055881d10006400e44280c18880b104c0380b250340c00513104500400208101c14100c81c1600c0c080d9a108201580711100301d0008ad0540c0207940001b0382003500814810300700290000030303900442d03048008010301d944181c0d410340490012520700c94654010820482c860030881015588180a010000d000030701e031242640c00e09100720f0802845103580e0303ca17402d0341c0301c05100d42c014070500d14000304644207450f903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 626197886 1250 626196636 626196653
    0x30603071205070915080d0305130b0a2705060f130b180a030e01030f1518020408011b0206011221030e0d1214040b06040e0a0f0b04031209 61
    0x941003441c1201240c0c1d0204481008548081c180302e6030144440e071a0346002401c0b400350351081c0c10442c400d02e0014520b160080c491180512400f02510b048441e5548440840a10180c0b40c4203580d0755a03542ca0100c105000f0441d5840040c003a4044401e49450030000d16281002d48111403001c3c0c010b050103a13107524030040080460b13000b01d10101c103950711541510b0309408404405c50340c0c058140c00c401056440403000107185c000743c07000c228000210906800f11a01d412014242042c10786040c0002e56034801c40e03c44071604cc40d0090300d01a03c400301c503401d681c01d003803228400d003850300c0c5942042901840300030b0240c0002005c1c182c11055580310700c8480c1c00d0140e030034a0f0b00c00d03040c40c1c42d41c0e81901c25042140101140e00c11515820045c45009041d0b07102140304440152a09086190303d48003031881a01683e0400314102c0c0984030740d402c000007014000000b1004e8819202000002450803030508003490003204544030030b00d41070802170107020380034080841441c907001c41c90700002c4189 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 626199136 1250 626197886 626197889
    0x8060c070b10080d0c0210020c0109052202070b15090c0a050d1d0a230a0204110405090108010203010603061a03070c020102121b0705040b010203121003170702030c010503060307 78
    0x25032081071600d40c140b403031440c841a9000407600e030003501111098540c1100c44030346101d2081e80d5400007401960030407a114902400389600184615404124a15000003080780207101224503020302502140184103c0e0700000084900d00480400c02c840725020b10750022031408142d079992520b19100760340003031911031100c0b090705100c00851356004003851603000340c1e84101050a08080c0720280c03140366654000c0c0c2182254074840051000124441c104107800341041c0ca8401481492103642c200f0014200d402038071810147c0074000007403540c0d0341c40c001c107000300b240c03030001a0b495040100040980f2025040310f045070035001c2803118000e0701c6e40c040700d900190a10740103009000030310040741440c1e08c000340300f07960704c40c081140c00032400c01c1c01c00c00000e09426001c85518540d158103000c161161040b199015070002e1155090010614003243c2c0d02401da001c2450307070517803a5555050400e4585842210b0864040b6211046003403c1041902034003003420f180d4114a0891300080e620443ea = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 626200386 1250 626199136 626199143
    0xc080402031b060409050a1b03140603070b070f080c01051306050606040b12060d0212100b0a08030f13030c060507030e01091a07030513060c0213140703020901020c0d0605060a08060c07 81
    0x41b10009841c190495101c00c80507040c1c1c40300b4010101d2001c0008001e04850305c0410001c0084501041407480c0002e580c500300c0e000d076140a410100513840c5c900140c2d02104003505c6000c01040030306100341080c8035a5108604000080004890381e060120499000401841c004c10040200b4090401da81c0184d4a000340e100c103019501d035803141c0220f41500140c2030001d411140b40c064280590401050040003810144010400c01c0d100c0320030006d840503603201d24100ca070400c000d00706000c2140f400518034424052810200107550707603115140088503901c8500020380104802d0304141c6d00800b03a400440b03092038211442401c210b181d10504901441c1140140d2000a4101c20140104c05031000c1034100314502000542d140c001510000004d54200c1c0b080040c2c179981110103686125650b0b8110035901c1040c1e140d610035009400940c48203800741e06610540c40890303555926030301003a01e10740c42034002089a00301941404a4043c9903000101c40c3d800c2070080241c2d480c440300a955440f41c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 626201636 1250 626200386 626200391
    0x9010804230a20010206010b030a1805030f1b011b2a1b06180303030902010e0904140d030204080c09100b0432100f120c080402031b060409 61
    0x1201c450256200241c15852416028410002d401d005019103c4007250984020281074070049000490b15407809015820281ca0180b0110300494000d50055010a040c0c00110380d04100c01e440f40e51440d080300c6d02100e0044000a5011111446c060070941c02c0503060000f80541d0110006c0807844209034517a220420112040003080803002e0003040302030307420b60700d0301a00e21000ba003007a0241d0b04150030b40e81c0c00011402d0300041e80301c3c460100000c02c01c904c40150701e0700c0c1742941d4045028081503981070b41040094040724425a8a03403c20f07030700981c45189403c0c414814040c040d03040a80903aa05020705106100400505002281c04180c03000110303003201240c1e0314100d880c0d075010b51940140030a0080401c02040000161a0f80301201c050200c24000d40e00c80100424051706c4032481e85500800c000e81c0031515140a03545114102086007801c3c1100000ba034242002c0784e5800c1024400502c03403c003170000b581002c0c48500c208400c442010b601d00c01405d408070b51540700350720941c00a41ea = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 626202886 1250 626201636 626201663
    0x3130e012d0b0a171f0e0403030f0c0203121803071502070501060b0a02070b13050103020c0a08160219031e03030e12120f01032d02030d020d0207090209010804 70
    0x1045190703180060309941c0a096200c200b290070041c4192004a00410000206004103400c00118900c4408045940010040c544e0070101c070710400070b1010748124181030b1102d07103400070f1961a0042c2218902590700840c3c40300d01e00c080d102100c1001038800082101c4207414845503e2010044544030303a0040000d000c1c0341078200c0740e20006c0c030500001418a51800c100403400d101104020b207000c1100342e00321000141c6070b810054a6108100c01d50b0001c4036990800c01c200c1d4000d8003e000e48103101015680c0c29040c545440d41c031548000101e4541d01225020b01003145000040c045800c195114429031a038119a16002400260a00200d100c0700b040b40071001c040c840e40250081c40081c1040c1d80e004151100400041c0d0840241a00b8950381080018051380f540040e00d4120398008201e00c3d0961180c07030a5814116141204c003030840240d0002c000580c504110304828843c9036401020b40b880e4800000742005216040040317180d0040004040f141c1c0d016141031b4001d41c1015443d810b04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 626204136 1250 626202886 626202959
    0x220b100806091e060d020f0d1b0b1c050c22090606140306210703050304060e0303160b150405010b0d052401050a050403200f040903020601140a1703130e01 68
    0x1c1e187c10010a600496201d0b00030200402d0000800ea011356007861416801d4840722503604c28081c100d2841d01a03044210000280001d0303802142d000294011020719000600441e241e025070594011045070a03000d0040007008581e00c02c1c00000d08070f6141c14030319882004444182c0e440050300d4144242d08245803c1074034100322107801d01e0010681c0440d09a15907034680703141c894001e0b2040c3c402088040d1007120150501004072015003038101a2004031004a0355404c00f88900901060465564400110071a844510400380038100c600600d07622011034180754010350f400100520b9040030407240d5005141c0380c5001c00e220382c080c00d0a05946620001904a0311400395600c00341030400c0442c0001c2c2030620715a14600e8010040e44c4103a500140c000600050700c81c180802001a8001001000480c104500140075610000d100c000d0080da5030032035900001c4001920b0007140c000040b2485003191103d41d0300000d10744002c1c50600d5600d41541c01c44100d0101c03a10040a140308112101c4a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 626205386 1250 626204136 626204149
    0x10504150e030607230703050d0f0e150108100209031009020d02040204090903020609030a0f08060d2f04140106050d0e011a010908010b220b100806091e060d02 70
    0xe100010703040301e00e04d1420b140d0050207401e21242d0320b01d219030455994452040d84804582415415031201d130700d000e8145200c24000c1c859500c4000e00c0554980491050b00e00c1400b10041400640d034030040c1c0ea504200016060210764031801012502c1005a000c0c191408200d0340d030140c40009001948108600229103040001e500080d4824400600416084060303441046400e01075406c940c903942c2c441403450395034030a0f4103903100421070074540b0080ba140b0034140140e100c8005407050b41180201c0c1d071a04108a12085900800384050b1762030126884a650b180c207071103034100d8007440042e240c030940042501060160303104005000410f40d40030f621a030000300044840100812140341490004074022680035081800640070710300000b07800c48140200040048010b0003d400c00c0b611689194040d4080e100030200907445903100241030761a801400ca400c1560b4a4010845c5850310402c54100002001d04088400b51540350718150101250aa4041d40581c2c24041083c52400000d01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 626206636 1250 626205386 626205407
    0x51b07030c061d060718230306010605041a18010f0c150b03010c0905151b0d0509040c030c1403090f01091202010501062d090b070606050901080c01050415 68
    0xc69042003c0810343d216a40c9214102c0f201d4603059540d80d48480000302c6a511000100358800700040c03000b840614000c0c003038005003144400b00702114500300400f003400c03c0e009a2007080072510108041001c4803107180351408802c0200043c0d46002c1c11046210804440110402d04102c44035607000c84160080a4262885400c00d845007054807240707003444090f0241c01003440c0070754242120f21101318001c0e642c41080d9003005040c0d01040050601c2a081504043e0040921401c0107901002d0340c0400c0c094040c0d5070b03c09985199036540c1c1403050105640900c8680400c140c90f11207070188842c0e01c850344a100c4410489001d40e20307192198114a011080000400254600342e00e0800304940300f0410040c090080e0024000c176a80c031a07041ea8181c20900d001341c062155032190021408146a15841c40100380c00d01c40380f84c03500d48440b0b09160f045083c0454038150386c0d000070312140c60586001401010404c0043c01030a0030980002d03e14081c81c4180895408001c0d02140c0b544e0082c8500203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 626207886 1250 626206636 626206643
    0x1209030a0207270905070906141302030a021312020102160e06010c02030c1302070c09090f03030207081b0c010329060c0c0402030403081801062d08030d06030b0a051b07030c 76
    0x40001316500380386455a100d481282841454828001044410310344820b03490407004041500b00c100304a0380750042c0d48000c10080003640e08002e007a0410418503207040c00340110b22011444010707a4400a40f62000d246d12681d0455040e130004c00184244100301030b0301210a1a10003a41c058510219140840400d0400d50110400d00c0450b03010310f4035800341c04001e0162a6011000d0355654031310045450b1040041d02c042d1864160300082806900244282e43c40f501c056854440703075062107141c9654001a020050704510110110341d0307818041e0b8541d440380b401c0b20040749241640d0f07220008005c84513603401075901041500d603425052100c1e981218028000303560703078a0a850000d08050341110500c115424000c903094100710305202d06c0c8295240303d60340040c0d6060524102c040e010344090a240901541c03240800d0b80442400540320707a240d0340c2030200f165401c0d4074007900c07007100041110301001e20b42010841e0b01e16840c0701040c1000712441900c0e81e60655420f04859100c180403016 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 626209136 1250 626207886 626207891
    0x11b110c060d140105040216031b0503030f09100501050108060f2202030712140c070203010b0a030602130602060f01121b081b010302090a05090901201209030a020727 73
    0x100540d070301900440300183d107842c607914060307803140b04110403801200910801010741c4406400001c0c01104030103031480102145003603a007040d6451514540c400c40f4900914900c00341800500d41d0708101c4800a0084800144207035810440003d01910004003414420420f8a2074034009407161001ca180d4001080c00c0d011800000c80d807898065031043da50340002640340090085190058403400f103001c640f02d02040010b0322002e0703900340250080c1d1f9041e0383c595031350204501075a60345800c41004502c60400581c403244001005d44508805603c03007021754000404010742d60031030301e48050540d10100c0b4442d4040380c2e01d0400d1005504540303505d04080403540008079541c000000d0001181603403400c8070034911114401103086e4020010030503000201c00c0c034240a2460160285548100340c5000041c4048144500490344c46080c10800305001c00003030301e024031000560304640d005c00075000035840c081030040025a521715603c14080030046100880c400711620040d03050301100c801c3d406 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 626210386 1250 626209136 626209147
    0xc04200706090c051002030a05091f021b120304030803180d1701060e0108060d15020703080a1505030a0605100b0714010b010305070207062610060809011b110c06 71
    0x704001c020162042e07480c240c0364080050180303850100e1584803245c83c0e000c0e45c24290b0142c41075601d0340110400f5075020114080c060840301d410003000c1042041980141034042d422007003100e003240c1c2088218000c0c481c1101b40c20803210000200c60849074000429a940c0d40d4016088008101001405840e805015100d180982d0310020701d844400b0a81321151490b6600c000c02ea61021400d106203020400301c000207072851401300c103400e4034580140c90f04410f1010148820007280c0c465001100429a001d080c000c807025240304091403424002d0702c00300320504250010b0b6640000d910000c003507a480d840041c0d400c1c02001c00940c008c04410b1a856154561031070004100c80c00850240e02c2586010f403800c101358480e000e01c074000c0d1055000390510381c0c1032282c111002024094051604180116000318065002e000c84c0d114445102034404100c0c00c0032002040013070081c103444036682c10018281e11005010b1040c0441c2e11060810741011442c1207082400d003c003904513284e200c4408a031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 626211636 1250 626210386 626210393
    0x1b1b0c0e10181b050c0708010204170f060f060607050c0603070c031e0905061e18101d100c0b1015050c0604031404090c1701050d050c042007 62
    0x1118058520140500e103440a0201e4071108882c16000342e6061401011403810fa5a0701410080104081d5081510307407046e00c9a11140c2660b1281e40140b20580c0308030241c4d400303007205000f80e1138041014006006c50f4141028034484120004e84203500c5142c1c001401c000300502081410400c44014054585929291070040d0114500080c00da01146003031030212006400340c1494500c0446070348071001017a00706000c1c0310140d0464080d1101400d00308010030000080c220240410784451504015500d41e40000e10511010350350110040c00300d80c0300501052001c03112800b03054001614400071110a511040310f1562256601401e90013032030090050f09a003140d058015102c000c20040444050700d60f04a6680c45040c041c444075410413004100003910030081e844041d491846040c0c1416120314261381141c01c01040600850102182941c1c544010340d07a65006102c100c0d0741d00c0d0f8450a540b1050740f11a40030040d103100340e5030b801c0342c0b0340340451154165110f100b982000c0c688800f51482d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 626212886 1250 626211636 626211661
    0xb03270a030306090903020604030f0c020d050c270a0b0109030b18121c0905070308030a0c120203060d0b040503160503040503060a050618070c0f060f1b1b0c0e 70
    0x1002a000242000004500060980149520a42d0650042008d40d4603607d080b20040103034940c0b10100b150342042100581e441312803011b049030241018105548620041054500700c60000880030252400fa981400c10340307204603640000741680100314002e091004907880b00103030b00000c0c00114620280803803c62424140315044003100112810031a10300030355402405041c0d40c218030500804880b891702e9210340c01c0360190030700c0303402101d200c2d546075035503c41103030000c80e02040d0055540e001d034150241e00411400904800c03590840ca18100721012070070703014900e07602404104c00a0046020020100210381b59501844050041c001092800b140c030382e4490700c40c403807003072150a01003822207182c0c0c0702d146c0c002d2000403d50100c00900c0e0120300c41c1c00c0c00050440042c0522101da04010904c51104110f1aa200f1a0f0000d14505449a11411607000e80c0050300c1d80e038110a03400c1c0d50207801c8000302c110b205c02080f58400401062074039440307044007a00007504207462030f01884010301c1840d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 626214136 1250 626212886 626212903
    0x70314150a020315060408030405060906071e03020705180f19020a09052b021203070f030e011d0907201203040b13020303270415060e0108100b0327 65
    0xb03689410b5135018001c000641c0920b010715040740d0070070401000070b480e01d007005060844024000c070303007000302d15102d000c1c0d0b00400f01d4461031a20000303170f002d038100b550600001c03021f030500b120424000320b001441041c3c0d808000342000d0400e82040c0c08a030706510114242c1c0c00c2658a010203558030700c0210780040c99002d09104490160003414014203540f9401c20b0410150010202c24007850f02c60b503000c004210352841142403c40c0010040d060218404071044140d40d0b0007030f11b84008165007000010f02070f12461b40340c404180d0405c4c000d20100e0780c841c4002908500e41d80303000c03c0b010003004850082c8039211036480d1003521030742c0794050309040a0303030166101301d0140318048600c0c0c0c1c400c0c0d00301c100c400d84098000d505030020810884031048000c20510300d8100741e441c011902e000c3e50041001c503000d10b80840709440e801b060030040c43c3d510046001f0824401e103000003c0d41040e681844150103d030249118181003c00051327051f503200b014844088019200ea100b0f840507803500e1503128102c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 626215386 1250 626214136 626214151
    0xa05070209090c010f020f0a02010302090117010f05090708131118040501200406120f0f090609140a020d0609032102030916060206071404050a030c080d08010602070314150a0203 78
    0x1408170045402e400450f01001852140018200c0d44005a00460096000001c618140241042000c4000c1a05805a406050ac03c1c1c690540c043c1404100194a80c00a21000070443c1403010440c1c00b455000940300c0c040e0780065010100301e0300e640050707040e070440598140251000310401060102c1500194130500083d0700006e040758084044072958440c0d4080c52000c41d040c0c03414000241195800b03030f145590b18600005a10fa040407418090b5603000205584a60326007544205205023111039001c01c020700390041041002c258003042c01c2260340000036207160303611007024040c03600030b914288512004450482490406d800450000e4105807560f008501c10710400e0304141d40390111010640d50160010001c1360b44512040301d1641d800c40190324101000e0100042680760b400c3c0c1400a507204180c0212101c1c2000520361400c20f90182d18402c000f41c2d200100700d410740126917001683d800412400e0701d40c480c01010707854401204080389001100404100102580381e0195004115 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 626216636 1250 626215386 626215397
    0x240705060610030b0102150907050d03050a0207061b0602030a091a010e0f0c030a0e10020d0609050a02120103020d03050f1812010e0606011812060207150e0706050a05070209090c01 79
    0x2401c5000f1011280030307040007405a80f04260000c2e00d00d0001340c005501070000e40441d1003042d255000b00d1011144c0440031008035501160381c030303422030f014800f003000b40801e40703004100c003c802c00c03002c9542c8a00210250085074000040380810081c0c3c0c01a00e891a040750a071140403120f803019004140003449003402103c049000715030550324480e02e890245000c80c0c20b26080d0f0712075101010040031582d103440c0702c500c100a40781c2480411800a04503000c00c000c070000340d981c6040c40c58002d4450042c41013007420300c104607005850781d040034254152901911129140510b52500350b46501c03407c18051959400420b2402c03099a49035801007086006130303441e850350385444480900303807914801d0456881d008040010f00c0355200d1102040207411920244100540d2108228200391407030314161807607500080d202040c08200d1403412043d406a510401140402c3c4602980b0340350b09008070010048001b90b2103001c3c0f44030310b0503100350640040040140303040c45112165074140120380140460b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 626217886 1250 626216636 626216659
    0x306030f0f0606091f08010501080709060f0306050910050c0301050a0501080f07030c1b0803220f020103090201030e1b040e0d1439100603020303092407050606 70
    0x48082544003980504200030450b5449202c10440d500100400b0745150700317440035540c4410559415608000c02c04400001000c3d41403880403030500c0b095421401e4141c0c10b00d0001c01107a00ca81d01d41d04112a0072010000d801c3d00c030418424105071020365500c410904181c140704000300424002d5040b504212400f5101c155603074010f40d8020030885460520070702c4040003c030240d000b90852030020300240b81001344140f000f211114103600079241a0f44007980441000300c0c0401d00c607134400c045884611b800300b14103011b0f501c1d29001060b401c03000f810552164465801c69010350014030040030400141c07010180031040b180707441242081c0e0248201e05201e0f04070291200814050380c00200d60791000f41080c080e40219a06a000c202502440101c0c4c9500c000141c09441c00100c1c3da903c41d0144021000405608501e0410b64008100300603142500400050350000100d0b074202d881603a440761405003804010004540c03080343c0890113000050407004000010079164401c20003100e13211400d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 626219136 1250 626217886 626217913
    0x5030912150a1413030e1003090b0c1e130f09091b0b0d0209030316031706090106080106080601020a05010e01020a1e140d09050d050c0607030e07050103020f070c0308030603 76
    0xe4540303900300c10000c3d0480e00410901500d0131388484815019085c6181003001c0ca0b40483d0003a400708040400082d0b80306602410880c001482540101500c40c109007801485c4900800d01000150a85c00b100d03c0081e00c80710b4200c0c1c10700070030300a04082550b5490070369030380300c00e83c0508000710044540c7d000c000c9100c0e00608200e0401401e851042c1001403c0c01c072680e80c403400a600c0014200d80c50700c418042000d411507004a4002c0c00d611030303595408102243c0489100d4000c0103062107114415400c018000030b40c0c003000180c1100c02d1880c040f030b00b81e103e0600503401c06d0045803001e40917500380440303080340f10340540040030300c00d410b699040c4c0c440040302e80c14030282400c0400003001a0600003800d0300f40481c0301c00b0b46404501c1e03840c0011300d000a40d40d10307494404c40c9688030003c150085204d51484100b403208650001d528101402090903074580036486840c00d001e4079050603800f0901100141d80b0344103071605281e001c009a0002c0c0e4690a04c001d8030f40088461038428070800042c500384 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 626220386 1250 626219136 626219141
    0x1021806131203080f07031e09020a030c08031308010902240c07061e02010e100b1201090c03110f0307031b0305030318070803040f0302040f020c100504020103051503061305030912150a 81
    0x2300644610141e4071146403003000000e014504400e0b1fa01c20410a404008a422a90528014501c04000310340e80d5503203040c5a00000c3d9183e0203843d450745802400000b50302c2d500064615810010105295455581d002c80701a00403c0c0305040c02d8440c100b40840d815800c01d80f504060002e0100400b01410749582c12400d07141900b4079000140c00001c21400c140e502030b0440902624020001c0880d0f07000100c1c03250031180341a40c00e17103000c82c035500100140721107400d000c00789010130398840d44100301040200341c0e582e12900c4000c18440b940b181d00c1c40e46919040c08900990740c01000d0342c0d9a4240501c00c80c08080d404038818006005407180020100300002c2200e04564180e0181d104041c40c6d41c0030080105500801d00c29003a40070040e0201a81c0c00380035032407451414507000149030805000040c200c940040c1744003058045100c5441081d6000684654070405801d0840c0e010142880d2590650050310201030f0080366050000c80c2d403500100c0c00381d8144500c4410090b4581d24074068005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 626221636 1250 626220386 626220401
    0x20706110718110c0d030203060414010503030a23070317010b0c060106111c0543110a06020f0615060706090f020604140a0801021806131203080f0703 66
    0x4400700b40d800d02d400b0103030b900f0103e200030098000604200c0300f1640282019940c0250400003076001040000c0ca14140c461400101d520802500c890360400d00070966074443c43c0c0b181c005110030800303407030412505800031080300c00c0800c0005480751030030300d0094000d005002004000c01246e40020855030907103026540d03004034250081c80710740d203051000c0c0c84d01011a40c4c507952038050200c518091a502c844202018030041d542c050340d483d40c0300416103442402044401c801125030640300010f554080b40c1242d0103500e0804001d08020301e03c0c0c054251904160496007125415500140701d980101c3c141494034424001e481c601c3e9200e111510040322110300e420b81c868424071031800440e110340d20401c0c49030b100301202c00b0b00c4d52194000807219001503009555804400c07a280010341040c100c460010300c1545e000750300b88560019405c03448074689284038051140410070032501441c074140c80008180154aa403241c41007402d0040c5441c40403100b95086069602c04a02e03514403038400d481 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 626222886 1250 626221636 626221649
    0x30c060f09120c0a0e0c04030602030106090923070509043e07031d01180b040503100e0307030e1c0305031e040f0803090f160602011b141b030a0207061107 68
    0x90311103017000c6070f6078000da40103006504080030601010000038024801140030b44074036161011114500809882600c000c5008410704488454441c9042c80204203120f40294040c100f581e158048200031500a2001c6142e0340e110350072401482c10020440000442300c0d185800156107550ba640054a889100300c030401000112801c607060180da0f010441044400d40502d0204c101840c00b24442c07112490076001506551400101003119141c200001041d4400741501400591107030005d494036030141c048003a080c88410540d00010345d554000c0c2d0100307010b200b0808440055503050040181d08102c83d401d45c0c0e02585400d045401c940c1c620a1403180754015690391102003e40e640355941d070000342004203a40708540119401000c10300811086c852031011048240e4a02940242902e54611081c80c1a00c030390718122255035403040981880800ca1052241e4400760035001000000382c0300707141c0350540004101c00039000e5000ca4164110740d40c0b0340d03408540c61501c01a040c0c48418a10998 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 626224136 1250 626222886 626222899
    0x142a012111070c080d111f0e0a0516060903051b0402070f0308151f03110405030d08060901170303150604180203040204290d0c051002061e0c0405010e030c060f09120c 73
    0x2803060780204403503191301c47c00481c01040d0341e4569414585001440c0c00e0403134072030704281c13130301340e908062548024000c141030700d86004403502d191101629158800c15012004103588104040d90710f4580440350107075442120f41c000c030703155818006c20030352040d95011070917181c041540a40f480e110030b00940740c2c640c01443e410300c401ca0320400d03001454580d03540d105642c000d000006082c0e80500060403444c03d0343e00c030b400003450440c041240450050700b12490148808072090701d01c0c100001500d512902000d002c8981c480e881e80000d03110701036944105100304c0300055483d44500f40307802442c0964800d0f02e0610945010104280c507004034200840109404400700b1003407450201307000103566003e0201005d1684c3c940300031074081440019840701581c44079041c40b00910b020101602420200314001185051030000240c141c8101c4c82420b04110003d0780c00325007540c1c20b200d0f150344204006c20095503604405600342d220340003d2501d9108040300403010031400c0000c40ca07641385850003841ca = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 626225386 1250 626224136 626224153
    0x12090112020318070f051c170a02070f0b04080c03060c0307120902061206030d0f050f0c01020d150f0801141b0403142a012111070c080d11 61
    0x401000b0740004101d480e0b00000102542d00d000c4041c4072800141c0f440e074203200030903800c10050101c1601c02407205100e03100c0b9082d20710045a84904140c100e961071030a101d035607802c045030403450402e458012040c074002c0c0381c2c0c002850710b1442c4010b00480e140300e02a03e2012051404042d100e00044402c00c0940d0410170001e004540300d0b01409600580c02d1b50001a002040d0300400d991740c000b1049000c0d503041d860140200352a0400c006018414249044181c40386c03075400042060144000000340440b010800c00700034032080d010707200030200b0b55000f0000807001e04600c4e04541154401c4400701e01c01007901040090041c0244034100c02803089040481d169944030308880f00ca001040c0040c0c1909210200000d84031007054048009220010040b1205000f82c18084082c0000020703540c110b0440d10030700c40c3c1d80041c0703011300240e02501c40c04018000640c1e2040500100a445500d0120020b120780401480b900c10005880e0424111030f0030b107500301415150003030350390302000e51580320b003c0703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 626226636 1250 626225386 626225417
    0x114010216170709050f010e060a081b040b030a150e0705060301151115060301110909040303091e0803010906060201020a1227060b0f06340503031008120901 69
    0x320a1540300c0044119051140c2da510130108480c000d0303582001c81058200100a0b2100030304000c0d4205400300c445000c41d61914920b00d070388544e05620021062810080c102e400e6485a0010b103485101500340d6121503201d203012405501c910100e60541450710b130b2250241ca0f000204002503910290400e841c42c1d090a413841050369890a0490800c8101c03548503410003001d0010070042455021548602c0c01c020b0308160030340b400119102030390041441613494960b02d01011540040d05400c0011700c00c1107a040480e0411000c41d032202d401c2541a06030b10411140c000154101c51140f1800c0044c0c51b01d0306422402c1c3e101d2000a9000641410000b8042010681c08482c240e070004009080e21031103203234402c0181d003041500baa120759550808580074107020b160780ba0044d01c02ca60180c03a01a507504810030511003c2002240c0c00641d10803195840e0021801222450b085000c880e02c0740741c00c506002d4182c200340a00a014010b5485c060a0130340440e0030341d01e090030141c440440041e020352 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 626227886 1250 626226636 626226659
    0xc050307091214010e1c3902032d01090c152c0f0102070506250206071b08030c0618031b010f140405070603020a0507060609050114010216 61
    0x12402d96460402e050300500d109030901c5070303180d0f42c2030010183c07400042005c498113980190600050a21042d40540c4c0004d2075001c01c6090080c1d0034030301c228810b9041803030b410001f00d0704510007501481202108605002c45512941c80d809110b0210401075406220560aa071000710b4010f00c000c4403400103118402851450341d00c51482441c100c1c1c3c444180ca035141c141804000500e04600103c0a80389180b41040c003200c01c00c2c201d00b800108203051038500400c880d8410405603107540c07109a00e0b46800d540c100d4484000203600142803d4640050b400c007000d6225128982c0f00c0102c0002c9000102c00300003105440c40c05440314060803450f5038a8850300c44028041d2080c91090204012012444450041c1d440e10807110100008017155092504012161180700852100300c0c010100000140e00003080010780f149454056100c25070504180d401d40a6507900416450400e60b000c907814016520403030407181d0765824488490306a10059880314294900d506c44075848580c284206078820 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 626229136 1250 626227886 626227919
    0x100b1e0f03150f101e030602160c0b03061009030f1112190611180607020d170c0606011b0303050c0c01091a010f230406090513060c05030709 62
    0x140c2503030000900e4550750440240100d80d0703100d0200c0403109000c20103001d4000207014200c415004507111710460480b204e1001d0910000b081c9640004070303500a20350081000390036030740c40100269015150b4070250001e4008890b0785014011140340d07641228130a15003002266003003400310250707074515201e05d10081e9800381c0081d08403221810100300100100408071401001600d00001c00301d02d441c00e00b041d6034018945064100c401d02042d4030080c000500015800011120280d5850007440450000004144080e01010340e4a040c2034400e1402402025145114800d660b117560707800c0010b4800403501c118004100c0445841c0c000064000d6000e50b4010500c01c8007141081400e03040607007540c0800c3c0c0101c541c07214115840d440c0340c0800c070030b4a01601d000209404030908103070003038400c843c440307403a01c0c0310118005c41c280d616101e6074440b274003824143c58284801e10301480c031880d14441041d02265080c0c42c0402e011400c41c4128161784c0102865624120760a1411405002c0070070310303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 626230386 1250 626229136 626229139
    0x30a18021c02040b060f070c270e0c0904050706080127050604141303081501050f0f0c0a0b0708070e090a0b03030904020a0905120607120509030d060305100b1e0f 71
    0x6440d405651070340c5d070340042c1c59074103d5400340c117964201d1403030905180445507216807580c09100407210f040d04608a111000302c240f05400040c51801000b00c0d5190107480800650495011410720050140206240c0305a070b0007600c0e4481180d0340c0c1e068400f2a100200c1460720804411a07003d0182d0425070046c0350407034070042000c00d0380c42005200ca405101c1c03d45c0e0240860081c800911308241c1c00c85407031035100c422400c41d101c00da018203002900d681314004401c07100107030016021115500820035038400030380500c2281c03101070f400e00e0500c071052025200e9601040340400061440f5100c0d10f00900900c10103009030255171614054840900b091103684c1c0d51500040c0039800d880c0c0c4540c40542002c02140d13941000c0c40c0d15210030b01240d4940300c101c200701e61300070100300003000d600107a07c52000c0e130111100155651300d41c1680c0b0f0450150300d80c006580c40c1010800818400d00151f01444910300079810071403120350408104000711201c40c010281c0804c000e50841c07507d00081d144618100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 626231636 1250 626230386 626230391
    0xd080105011b021302090316080d0302030423010c170601020d0e03071d0f061002070e040309050415170c010e06030a0212010e040b0a020c06043302030a18021c0204 72
    0x15640099510f03134400006109041e070124844903503140400142e064a0600c0754406a0241841005030f12482244840310a0640000105040180c10031040d5000112400c02c44c526000d0341038168041c11440d00070f075000a110b190101160311980d80740303601030340c5c0580080c4008520100141e940200014240c1e6050003400c0001842d03481180343c0c4003050901c0c1d2140c0c00a0714080b000355140da400a07125501605401c0c9161340e9064001803000152801c580f498030099a583c601242e2100031794000981150810920703e03076101c03400000340150b84c3c42c644050303001030740d0302d44c80c03a9101c1803146964000307120100c4a1005090440045402006055001d031a01d0700004080b081d10600f80d001211260400c2e082206015003a41c9491300007050600c15072400305c00c61801962148054800340034201c0303030241880c21410805c806020340441030400140c000d00da410510094108454900f040d900f40a0041412450f00c05210031060b80140703d4120781c03007848068044100007101c204d030010b5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 626232886 1250 626231636 626231687
    0x1140d0c030605030a030c200d06052a030604061e0b09130e1b010503040c1512050901140603060103050d1b0c090c3c0c061401050a080d08010501 64
    0xb2005d00c5040c4419000ea194005001264505454207400c1007442c10a9a01d00340d014200c0d90b80c800c109440011f4100d840440c80344c840c0221610340010904004040844c0344020b1525480010091442040f04031010020f04d0303070380c030f0b841c0c4210800130f29117200d00031004005124141818014050f1080007400c4042e5440c0e4407200782c003c032200c141040005502c1024465140d000c05004003444050078a0030724114149a5100c180c20019030103180d28920300c0c0b54400402600c41c01010308030702080d0405000a04000c418070703008120252801e0a0104c29000195840c03c0005800d4100d1381d0100c000c1803035040300c440841d00c40015000d107008141d003940c58480800c03400e01d03043c0050443c07000d001585c17520021019010724031140300e20202900f1428444451046581c4030342c403112940c1c0381440301ea412410111100d41d50300f000202268078229244030713826021603030b480c10707a0016106d110b1345503112500c05544160078071403000041c00050040c4899480781d1181c07000d84106050750f88051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 626234136 1250 626232886 626232889
    0x21c020708030d0618060b090d050a0c1712030402060405100c05010f0506041a030d140c030f07120503010f030f0206120a1a040b01080615040e042001140d0c030605 72
    0x560210700e400e00301681302c1200f48a2880d001c09110a02015003900b0042145449000e4219000b80c03901d4901c11030703590b40d150041c02010b101525801c1d5224242d13100d2240c451212810500c2c42c0040342c196446802c16070706032119030b90100d1f405030750020099402d0510b02400c00074840c0341041c000c0204004000d0401c00074600f4004c81c00205e403410b401180324503085083c0404c0320034100b032005004000500c00041510701003100020724106182c10390001d00780e1040d442c902d11494401ca0f81170301c000500703a40100c1382c41d8081c0a221b4483c9003000d40c4411801001c5585020a0188404d0001c00e034108100068480003520440381c4054500350522814800d42d41c10004100e1f12002030070f07240d4502111102c4140c81003c03c4210480b420040e003c2e005000900c40c0c04000c001034002e905620120b10644240c41c00d0f80e005101001a00d60145864a0000b01d11511841074503003299400b16070342d00c41e40c010304050b01d8801c50500403905082204900300080c0103001043e006060303481c400850903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 626235386 1250 626234136 626234143
    0x1109060f0c0d0807081029090d0606031112070b0307140403060e1c050f030a060305030418050901091106030403090305160609080c03060711030c06010f03050d020706021c020708 78
    0xd500d6864031005844c000c000907040d54801400000f604598000521803581002441c411420040260b501c2091504225282c5d0740b2411452981c45109000464100b0203642c103c04140e07481026044c1c0140b00c0c41d42403003024010862143e80da50010107041c8a00d03038140001d50303030107900c0d4074180303503505444490700d03003541e110b5001541c80766200c9001c2d440d00d003410020410a001408824902ca110f0040001c22034003810754010711450000010815201e29604400003660304034090740e130786da656800c1116031040c2c20315080030658108000030f41c0005040c07142003582c980019001e80c6242c14a0b08206040c0c1c40184201e0a004180c40040041801045110501000752881030f135201c0c03c06001819080095120200c40d80c890300d08070b1420385010922a8100382c85061842c0551040000c0c00d0941c0646400d446403032041000010300460714807005804c403401030054031015042d240c400ca0325071b00580a0340025a009400304ad550403407070821b06008215900c1691081d0340c40d020340505 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 626236636 1250 626235386 626235403
    0x5030d020d020702030c100516020f040c020c19030218070c0b04030206090f0102031308070c031202011e0c0903030e1206010305031206031f23180c03011109060f0c 72
    0x590104840c011410100185ca07825003040f110101e1041020a0043c0944031760409d5080f1000c07da04844c00315218034010280c40c68004000340311078442c11600035908c499020382d55101d95520352a4650030000c00a22038241c07900608120040740000d04240e1a111001e8007113420841182109004140a049424050f502c25030107050786003050030289290004035084448207901c10010f111440342c0c01e031100440650302c03c0c12035880c0e110f141007240b024120342c1d0014024406500d000c40f440399041d072102c00c007950381000c0d6071101e20390f0140e41011298445a6032020402c89142400400d000d800e2030080488002c0108002c2e49440d4101d45c28000280d004640c181d0000c80c5c110306400c80702c0c181e980e0045003500203101c112036120a070100040e02d81012140d247c1e86241622072072030b803040c00d10300d47e0000b510424000c0c104440d650392425120300c1009800d0040c80c0c441f1210349010701842004440c071a02460504203200c08101455000d2128600c240b4000c005400301c0b070f041032142c2103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 626237886 1250 626236636 626236657
    0x7050f060712110304020d1e0b0f1006020c0f040609061805090606030a0b04050703121709071211030f07031505010510051c3c0c1b05030d02 62
    0x1504001402800d44851824480700c040d060240300209040d0710404e69a0150301102c04110711095400c022442e0100003110410488180d00301a042c800090a0300d8010410303214202c0c21541e0f501d00040c0b4505c440d010310320040c0c204000c454414600201404132411005000081d09956416080100e81d074550208400d4449180c0d0044c460b5414454a5885500200a48518544040002d84a034140740d00246440300301408201444001c2003078102460788515491114200a00090300408458414014407862000056144000418014225682c50142c0f00001601d541d0300070f01c100e50484466090f10401e800100300c3d03242004058011401000000c440c05c501425200580d08141c1003039004011a0321290081036002d02100d5558640c0b540028032101600ca60a02500012104034042c140c0c4400701c12200742c4103511414810302003400b942180064a251006030303402424800045900c1100c0005003401c041b081c420414414070a0b82e01d004189500601240c11110160 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 626239136 1250 626237886 626237893
    0x61509060a240908160b0f040f06030e1902150f070605180d05090303040b03040609021527060301030b07200d0306060201141f09050405490507050f 65
    0x407100c46401500010181c001314010788040d908040204513034041ca88114070446034009101a034585c3d1760b9050714090003100200e4603600f80c6d10000180984207800c0f010070faa01500905d483c810484003203041d8050b5000e4440c01c140c9240010703030901c5400c18891f07548006410000480024080e11980303214441c021890000000703540e0b900f915001006a50b001484404c121810342a82d002043e01d048401e101501580d039034891400744003904940b9402904000f80c118503110810345040034010040c46191104036140d112904144004005110f07150020001c000610101c0c00b012020b5500c0030590814845070216802460b007107080d070320000d00307040d0003500380004055494010000189030904c02804013481e44580e410340c920003c1e2186400c0c0145001c00e000340d0651504403030050184141c1080707945440d04000c3c1e21191201c811110b01450480079280c952421640ca04500600c034450f1501c0da50a0049940446014140c0c10300780901840108002001080790010041001c80074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 626240386 1250 626239136 626239199
    0x2c040b012c011b290f0c0f0c191103010b0a0911130b04080d050408100e010f0204030c09060801140f070c121806090810090c1d070f02061509060a 64
    0x710901c001c070700380b058113103892101400116000070440d2900305e40d0b0480d8195507526643c001030741f20705c10510b0b010002d000750303020420440038003000f82c07299600455613082445d000c1c60400d8200e40c44088081d51103124a602440100d40703e03071140b50306001005a8074500409001d41461f04003c0d0303400002100c40c001f40a00a0810a01c82500c0751000d0381881c0f41858180700040c0d460b603020441401d200796a03482c1d00550a502500401e00301c10544800f195155281e003002d00490310b05001d0f81c1403003801c100c07001408800504c1107078072184250300c0c580c0d41c0c1e455048a801c01c0c8000541144100b200b06106940881c2c9000e44d0301c2e080891071b4841c1c50343e09080c103891041644041e8040d40c240030303586504004003013011441c070015800c1802e000038908a54501802da81c1099004040302000e0301c01b481c0170f60580d90900602852a03511650940303d90403004a80d201c03c01caa00002c445c00c0e4949007000b0f03061245160340c02c83c2c402410321140071746482d503420311950b12000701520449414507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 626241636 1250 626240386 626240423
    0x2071e1211121b094c0603060f03050d05030912030a050a05090a080f0c01020408010c020a0c08010203061804081219060803070c06050a2c040b012c011b 67
    0x1490f40d0400c0f044e62110003a14110014100282d1404800903106450701c507804d040d981003031311044100e024090700300d004030109221801c41100600400d40031078540003001c40e500248000100460f5800300050011058061003203416400c05006040641b0820010701001c41c10345014501c1400004000119460316003d0082581c001400340301081e0405819400842d00820854422200d07041140390745d80000c030307003c2d0b0081c0b040da40407407403c0d4a40704480c40d02590201307150800c640500e1041036102c0d1140441801c03807005640d0340342e0011240e0f500300016200700d03c842d80d1080c00354a501d400d042030010b150b1032110b4200c0e00100005035244000411450600c00c0c035000e082c42000860070000503a950510340c4d00680208400d100007c22000c021603c5254810300311b1003221100e0f860310510001550074020f2526040f48250309000f04001e1a5100d6840d844942d0043d10490320350f12189045d42c5000159400550704002c01c2e8445903061120716149140128070034040100c42c510540c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 626242886 1250 626241636 626241673
    0xa0e1c15110c07060503310b0702030f030601140c16080601060c08070f060b03160807140f09102606010b0703050a180f03110102071e121112 62
    0x1910303034503811051100500c84840003e42c6415522642011652921810b07000c106074101034070340c01c80c06040506040d00c0f8000c0e08110031149480303600344960300d0b110000182d8490049540c0c40c000d0050520008141d9032180160720003100a5031161407401122601190a000d084a0f42e0140803000300020480707260f0822000c2d004200910b400c0b0805082c9694100c51440b503900040c1080556080c01028442c4590000300d081030010110351b400200d481c4010505009803003481d203e806003400000d01022011040110424000d001c440002c141f10108803202d0000b402c0c042d0120029840840c42a50000300806034408030031024a000004c60401c81ca0b00038144c01075071a11009100002c00250004262074030010346080100864418031444592b0403403039808442c0c0e075240e00c2400414040c1606a0402d40d680070790940d082c040e111b050340d0000340c1d5494114040d01d03045c1041040840741070103048988a110700902c65814a00c10005145480b1940500101c0d03040b02c2c03480440141d220 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 626244136 1250 626242886 626242901
    0x3120e0d12020d090816090f0209060403050f0601080d051903140c07020a0f03030c2621060d0b0a0209010201020f0c03030f01090516050a022415030708030a0e1c15 72
    0x64001c01307402064031034005019046107e0f41030700340e48403090015105000d80580340000c01c09082542c50b1580c90404503a03518206261001328050b102c004500a44040f8071114440c1894980e90f2801b80c502110180214400c0c40c0f400801d66107440c400b010182c0c040005000303019812149072203400720700400c014075001d50302c5505030700c10381c7c1d108000194014001706400e0380c1044d8800c84104241845074240494914a8080c0100001d03a0703600c3d0440759500c0d0710012081500d40e1190345e42e0b01c030a100000e00c8100001d0032400320340000032544580d58004160141040c8000350800303a0600700032800e5045000d07080c01d580c0000c01084501c81440d0241801070032440410310190030429410390695030f0035003804e010050f000a8662440d4002c002c4056822115980409400b800c01d0020049690640c0c9a0001c00d401e00044583c51500161000554801d0f1020354a880d90300760080c8d401170000b5901c2c035080f4504500b0716170398080740a01d903001c25000782250001c075076104011800301c0d01e10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 626245386 1250 626244136 626244149
    0x9030706020601080627010204090504201f2a1a0415090f08160201120b01090528090f0f060b18040b040c030915020403120e0d12020d09 60
    0x2d00700400c9100b0000a0031a0854400c0149a0084000a645036010711641c95400000d43c00040c1c00210304030b05a1040b4480d070300802402004d0000040b45294160400000660000c00e540985804180c00714811203103140e541041c01d22020369101441d0300300c1c41180d8424148840c11042d909100e460807510105030302e03d02103d069131411307598103210321120300640c80b00315070748bc6014000c114030560180200794102c00d25581311050005e10101c0303000703903900c100e00041201804104801d0140503000300700f14161604140642480103001320091161000346200300d05413454a40c008840e00000c010b0301d0148402b14110502c440c1c800c0541b250a803220f40e2452a0100c02c108140d5164280da040307035903110554400520003c0000c003c2c0040d03000c1294040d01d058400c00170650198481640184501902d54412101081d0042280114480901090030058040d8080344c440c041011301000000c0c4041407001d000d4039004c0c0b8031807034480303d05c0c090b83c090010741070b03402c1d00b000022006066 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 626246636 1250 626245386 626245393
    0xe0f0f010b0a0c1b090c0f020303010f03060905030d0c050406030b22020a020109080d0b0f0d050c090c0d290901080309040b01090b070c0f0e090d050702030a0c03080903070602 77
    0x1d05488041c03148070300c0c501001000014070b0710504221140e00e100038900243c0070728400c0c0740e07192501980203020301c40701388011941e00503042c10040e0020083e03904940d000180c002100b490768641002a208070b50081b14280400c010005807001e41d4815840e40d0b15070303641da4a8070780d81000c40c042c00701d0740003030b440302d11030030708424070140069008640c010b0002c001c18000da100c40d03841c54207901405207200c000b00790900114034140e0400040d171004004442c11641d048007a0381c10f906204005207040c02c050003580209108400d076040003100070781c001190200207458120000280c40855043c0500142d110540440d0102e00722808044002c0d61901181c40c014154542038049540e48190f08030a40201d89035002801035078000e900420040072007400d4507a0301c50b11880d2100381500e003400f56001310981c000001c10002c1c400140c46106950100007002d1444049905032a19003080b44120392501c06c4104060020320f020032150f00a51180460549403038444c001c1505124894201900319407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 626247886 1250 626246636 626246639
    0xc070605032809021002032109190519110f03031201030219030219050910030f06051b070b0405010c05070b01030206300603100b0d03120f060e0f0f01 66
    0x280060b0603502c1940b241030880140c54410440140c101450040e5200304049144030b06542c01000804255451220701800c501c0c0c0000100c00e180d0041e59080100c0d03001e000301c1c540002d00301480e24401ea003d10115010105458015413a098409108a8032010040200c00183c24580c810312003c55085010b1420441014101e00d15000e052001078403c02c1202c060302c02e080c0d04200300001958000e481e03050b00c10180d4180800075542845903a000d046a800021983c8003200c500b841501c0d441440704481140c1c039100c002c054a0040c0c66103107288101014103160041c440028140e2a1140d00a0f98241c0780508107142115a19404101070210400c1420700007001a00c62a041d6513040f50056100c2100c003c00c840b0200030130700e04607945d800c142d68107100c59034480c070344a118403012009c458031207103a50344400a551403405000e030070408800000001078014441000405499000040c1c2250390012040a60b42c2070f0b4405001180d9a40a00c80c200034400849540240c3c0102c0810095 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 626249136 1250 626247886 626247901
    0x20909130b24030f0307140a0b040b0703061523040510030f110318060703021801030c03290a05060a050304030c06061d01170c130e12030c0c07060503 66
    0x3100145030700348116035992500c0780c50203210840e9080b0318001d0201d4004001d58a2200d5480e4480034066481440c012280481c10000041000c42c42758806181e84858030b5a40c2e521110b50405041d810a054880c80301007010424488200d5450b01a540d0341c4038a00f001ca04c0309854040307d0388400881e0a0200800c0c4900c2d02d0f00500c42901200510b00041c1904400410307000130014102c0c409003600c5c00000f0301000816242c0c0c0500c204200805903a0f107501c2c0c81c8401d40482c0700b996418184107100c1e00610340b40398040c0d031003aa40316a060070301103103070901041181c40840c0e003080341c480503d00f11200ca020a00f090310400010b010152401c1d4034010345000c0141c010300004000a04125204160700204641038000000804008901043c50100902081b003518024014085002c80f40c01009610000c0003440220840c40580364402880c4026914006032a4201500b5900c1c460112504024140000214451322520a580d80c607141c040701064200340c80380e4450310400c003050041c030040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 626250386 1250 626249136 626249153
    0x70b0f0c160602040504060306090201020f0633040e07140607020d080f070b04050a0201080c2107021f0e1e150402040603080d0b0406090606080c0304030e0901060302090913 76
    0x1a0821028040e40e41c582450810701a204a802c544d0b0018106100001081200c2c0c100550040c402d800381e40e20110030030252690b17800e00720740d004282c2c10401d13034008212880d5903103c0911040c03d500c1c034103481d1241d4045401d0f609880816a49940000401c101d0440350648211108200300c400c1c80ca0310703030990000f0342c0302c0e4801403002d03000b4a00021040d826100f0901291603082d0f01024520341483e182c14004c1d10b07250b00c180e040c0c1c04100c1000000700140042003c03254400c138610808031240320141c01a1031948402040d40d400d600c81e2000d20900e0101003900185014460680400c140c003c1450036410086056522a115200d032480079002e940042014844500003400706030403665280001006482e01e5840506025000222003e455180382c1040800c0202a07505000f115652418482110494420721002078020000f007202141070800841c0c00500a25100001030480300008403900401ea100c0c0011170341c0003401c88018146241d841d41e01400302e1000d1500303680790b61500c281 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 626251636 1250 626250386 626250397
    0x6050c07031e1a09061015030b040e07080109120f05190c0b010905040c081b0f04020409150306060b0f0f0a020715090311090105030d110c090408070b0f0c 68
    0x21010800c03a0400b074140104000c00d031220b40200d520490501e0102040b2690300d41a103000005024800006240600901c100c2c03040b940700320703450480140000c200b14010070f803940f2441d43c003030744500424058a80410101c40644030820000820714000e1804000340702c003800310340045c00346402d0780e03841c01900f000c1031310b120800346e980420a4000c0351100b1039240040440c0141040c07151800458a882c16a0100b4415842a84650140760315100301681d911480482c286007212821031038106420200200c184412010700003605140e11a041c070b8090f2040640051031709030410008005020490159500800742d1140c404d00d004010b0002403040d1003500784134501a1000208107148901c00c1151800074041c0303464510081019020040200c640c0340300036a42020002d0040c101480c1c200c00d41d904070340e0001c00410380c07140d0103103080c1c2d41d64003c0c441054060140104614407529080d8400b88907a00ca900b03500c0d540c2106181180c1010701c0034294781100140401086021500b0740700300c42 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 626252886 1250 626251636 626251643
    0x41505010807050408010207030f0201180b070e0f0d080913360b0a1d01061d09100501030308071b03020c0120010f090308070c0b040611091012050106050c0703 70
    0x22582e855050070b071281c1c4074a43c0207848541c80007424100345503000d0300c1e10000343c10990081c4071004e101d11400c40d001a05480140c0051682004184110300640e1420610700014000550f0710b481000010b60118040d202079401c1c10000440040301e1400c2034406481045034a420425406480e0902484200f0051064034000d0322141070b0075120100c43c540c0c00000c0c0c0c41104041180340c41c90450000d000c00d940707092048030070318042d030740d00c541c040c010b00f03040c0e03100000312070322604020a1800c9540e1000c1c000310554040e1805010b20040309024460186000b915901864202621700410307000c620303141e103a100312144550340002603000c109104000701c00d10300205241d45010029081d18101c483c0160158645040c03006240f60b0740d00044102c40c02622803000d6a990728034142e0300605441c40c02401304600d0f07000240010314540c014241411199042414000782d007020480100041000f81c0c08102c8070030300044550603034028070740504071a207040c6040542482201e40c0c3d550701400000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 626254136 1250 626252886 626252897
    0x314041211010e100e13020a0e100306031407050109090501060e0409030e331617040b04030b0a05101d2d15030a080a03020c070b0f1804150501 63
    0x10705a20901082c00c82c164001d086007051640803c0240501c0f1070310303429a0050400b10b5408403d04014130030742c1c0c11040390b03850b210f91a0781c4030030400188483c00c141c400c0900d5a901030100220f08140d1110b44203c940b60001e0101a00705030024003200159030200c280c003030074800140007a581c4400e031081d2110040c1e60100c3c0e900071520382519a403060207442c3d07421005985280028030140c0c6c005065503414200722800840ea840e90214580c42020380303880250380440340e4400042c41c45046c15012240d40301441c0e0400d0345800e80008030b544a40d00c25280482410144811860301d03110301504205203030f034140310441c504052401c924048000c45103008602c60001104200c8581c0c04804095007a819082d8840c1510b0603101c0d0b4200540e01c4400103241c00d541c4041c130b07080008015142c1a00300c8012030800200c008101d01a600c10924201c6078040c111000628401e11406411610244400d0035141d013120840003090303903408a211403050341032800711442d056200382c80e0ba064031000c0c80c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 626255386 1250 626254136 626254163
    0x22060209041b0f081303020c1504180b030c0415050622081f05070c0b0c0c0d0917030f04090c170408030f090a150c0315090903140412 59
    0x203802004000581021410340100c004400c0380e020403c2c0403100e030180c83d6040d0039107803540c2e03001c46000111001409079020106406040c03502c0c1211582ca000f01c0107010b4a499160004001e2001544402400c82c40e00c1d1050001c0d1860288980361260030b09039800c104103052044043c0748a8180d12a0030f000d01800103400402c00e0714090814803103104034030540c40d1103503250043d56507049614a1043c0420700010102411403150050b1406400c071a520490000c149466028081c80f001d88011803250040161004e0100d080c0555594900e1548460211500c0c00c000000da11604c0c1e04225090780040011400d645401810341c4d082d120802d10019501141501c180d80004505a0440316596007500300b00422189100440c0301c2d00c0120820403442e100c240d8155952038000b5001498450700c800c1c0302c410a44035070b001c0c00d0403c085103804101040c2280500c42c1210807070b0419003690380c035000c1407801d254200c6001c1d10100c85240032180f5151400e0355006204c62803100050107440003852 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 626256636 1250 626255386 626255389
    0x1507110705040b0f03160329071d09151e1c0302010608030706050907060c11132706060f051c050c15030402090a0b030c0427081222060209 61
    0x6a1210794040d089a031480440940301e00707a070015100c120f07042400800da41c10b42d40003041c5e23040b4040321000c850107095103d99406130f4440c05103090440800707c0599003c05c59641307184543d400360401c01800483c60410400703000c2d107151a641010f2002d100d08507581c0b11a2140c0079000c512210300005561081001d2500700c1c0503144582c0070030214800801c49409000041d40118090035650342100c1c1c2056488000b07441c0b04080d004090a10700d110908401181400c1d01aa0401949400002801010845401003500b84e02c1c1c0e801d4045d41101e40f805042290511659010700000d0414202051600d0001800c10800d03241850f580090031042d8401c01c071041101d00d000060042c00c0542d0b0a072540780f00010740c0c01c1220183c0c4211403040208100303da861240c041c84c0e000140c0a000c4007040c000034000a4409078104074403010302030569400394684010035004091181046a07035400201081c0c1c64511000740034100b0422918490320810402044005d41301d0360300250140e2118441130 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 626257886 1250 626256636 626256649
    0x609091203100e0f1807060c06020304050a05010606030b03010f0506150c01020c07120201020c450705040503120a080a0b19060905041d06010501081f081507110705040b 74
    0x80c440030b40548600e09004101c5641868141705804a2105c40c42c191020229990350352024410280803454004907a004181d0316002554094080c100300c807945181507440a0840381c2c40c0d446580020f648411314411881d003802280d001c0907038040140480d05214002501c0b00314030010000c000f210004004e010504290145c0e02040d1000090307660290b030f6a044140d001c041c0403800c0f4014010300020b20314618059038801d402c80841424140c04000d4000318144c103481043c98801d0038000081d0007500112280c100c5440b542240d5501034507140707024149131500142e0301c04405490000d000303d024596004003180e0f4450506040030400c0388080006c56040245841d40b0744aa80a8200115403546c1000006040b0b48007038404000b41c0103a0b640791000180391042d450290b07008200108895846100c8842e005190b68035034984291801c3c4c005400c00900358001100c58200c10f00704030701340c2000007c541d4092500c0c1003240c0c0040000542c179407200c20314043e442c800d40c0d0300e003d84012a11040d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 626258992 1106 626257886 626257889
    0x603020a091e031509061d0309010f0905090f04031404030203030702040b03011806090b01060807020307060903090503150603120a1d0f04020d0b0108060909120310 72
    0x42c854207481c040001e4a0140021403880400412140714040400b0340100c00c001408807850714040055602d941c40058100f0841c20140020041c04002c45940c82c2c02440d01180703c10440c48241d94491541d00701d542c0140c1c000c410490b129064031090350055000f40c440a01c02c5840c1703402c2e240c403072059000083d01504184009801400d0541200080c0328000300040b03031038500d084100c9103400c4001e006458040d12100200d062282a0b0f100c44c0c0500240d05e003051032849d01c150080c0d6a44101000180007036910501390080c90300c00c00122016010050030b540c000688594242410a81a0342c102d11a000307110030f00001d070400c00e04542d142c1009448102c103422400b1010081c7c0c4000140480d000340028084040f15035851009054100c0517420008e05290228001025104024080c6000e10360100500034069400106524156004c01c0081c0d500d1755440000f02125032217 = true := by decide +kernel

theorem cover : BRFrame.Cov 626079136 626258992 := by
  have h0 := BRFrame.cov_init 626079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 626079136 ≤ n) (h2 : n < 626258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
