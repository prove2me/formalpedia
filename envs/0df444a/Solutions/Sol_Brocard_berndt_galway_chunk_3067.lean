-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3067
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:34:01.371125+00:00
-- url     : https://prove2.me/submissions/bbf6551c-e342-4124-8a9d-812a74425b87

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 551438848 ≤ n < 551618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 551440098 1250 551438848 551438873
    0x3050c0405060c07050f1002070e070203040302031f050a0903080424111801090302180406141f050a14040e0a02180708060d02010804020103020d0e070f0e01090b06030105060a050403 80
    0x3d400b800103c1c0c0b0b840c0c00c0188130100201e001e40100c00840580d054a5404109001550b1100c8075000c282e0729031010482c83c41c0990341000b505845130448240d000101d40e10106400200780c04140700c40d0759401e130750000341c801c01034006000c15001c0001c00c3c00200071844e050340340118410007281c1040703441400410788109110b2081a00e0b00014001003041201d00741c1c400c401428248808070500c1c503804940c2404102e0004111a160b40000c034040004580001000c000d42c0710020142d410718040d404101400100d00c84900f9030111400516420402012011070b403100d81d10107134110790b003018000904010444c0d9402d502850b125400185e840005802480092040c00381345850064405400c0d4079002e04880e202c0d00d0b018001c280140c1c1e003d44600d511681c20b103400758840701002014000390014a02c2c1009a0080b0100443d100c821507030424120f92000b200b20341d9030b90341d440421040301c032100c0c000381c0c200000b0001070040e42481d100a00000046c0c1c0b0340f03545000c0ea01e4960400d08450f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 551441348 1250 551440098 551440117
    0xc100c050903060c090a0e04060b031005010e060a0e160c021807090e0415180609050c041401051e15070605101d04020112060807030c0627050103050c040506 69
    0x140462609242c1c1020445a0350100303500860601c3c0c00c1d03880001035803500d01445607802c0072040800140800c0500c0d00041400c0c400036040f9810440160401e501905090182c0003d003549a400101c203840d000f52104112811240140596200c41012143c03034160a0315120074403135000085401038941e03501c2d12110302982c5100403054104500020410481e9900c44005885840248804141035000c0407038030f5401ea002c00140c420314401d54400703908600d00050b0882e481e041c0e962003441700114102d44154001c0702c04201e4030780c00b00440c000e041820301549030440c0015680c046240ca07404041101000000c000e0380d41380c2860f5209582d07551104030100c074010344640030b000145013002d0402002e400503002c40d901440030300014030781d12a4002e00290400c55045074080c10502c659109602030115801a80e01e50b5880e414003030f072030020f50311a07600010800031550144580c28400700d0f02c001102040305070210302d00740046003c1c0a0240440301b640c01c04000026042d95283d000301403100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 551442598 1250 551441348 551441357
    0x17040b0c011406031b0f010c05100501090f180b060a08030c071e03050c01080606040b0408300d0903051603110f0115030f06091e060606050a140c100c 66
    0x2001240c980044000a00700f0380c06944a107510340c50824441c011701d9160b20098400e51341145058004039420410040040d01600138900c3d594920440c9d900440c0c1030f10b846a00501400400b100705078121121005403441355000004180d0005122904460f0824001030680007619224414103065130f2003c41c000304142c0c4080020095000c440d203000400030b6041004064180c9140c4034162a800e04a04260420283c040080c80f40e0f554401918060801c41c03501d01c1d02e81d5190300c54155207002e43c1401c08081c400350341c2d07030000310310069403003103102c6c4924000e042c1044007201754003014151144048050100034040840811034a0000359090b0340241d840c1141d5144641ca6581171240d80c0c0716103181a410304200c4140d1200948003601140e40c040c015115424041c141070f8000d0900100c02000e28100c42c042c240300d250101d80800b541d60042d902000305941c0c038807007a1a5032144003448008243c07448018051034440c14050300c0070300c1304242611030400b4003a9810044600095119000c41c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 551443848 1250 551442598 551442611
    0x3070b09190e071205010b0a0318080a0c1a0105010c1b03050d120c090510110c100503061002031e070f02030703030906020d080c0405090417031009141317040b0c01 72
    0x240c0c031a0090308104c4c1c511408025650500c5210040c5108000503030050503168110388000322060340c1c00b0604280c100e14038546803851000c004102021621041c0c2e00030110051260103c9140c0e40da0ba412202d0584030051b944e0070340ea4850902030400b030174805144c031080703000001103036051119121521107696904561032820300342c4001c4449424140c000c10400700420301058960540da60b01c8082c2600b0156001e51201010030303d0300407600b040d242c210340780d0f2549006164010b8041c5028103411681041d04100c4084226900e0081107000030320194919000c2d078a1803469801005040d0044000f0220005141c0100b03207841c0455004600241000c40300700025503050001c101040b5251801840324200b541c0400414010f070300034507104014100c003040400102045c01141000d4040c20130f030703e0713281c1040d5001e100c4200c2e1241c1c40f0010b040024085a031080445400d20403000303191044c031043c0c45a211810448415480411104410080401d0089007803024200c55920701d070021500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 551445098 1250 551443848 551443861
    0xe0f031018061e05160c11040e10050601090501080708040f0f0503160501050603010c0c080c161401030b04020304030c120509120c042708030a151403160503070b09190e 74
    0x1c0720300080c6980c1400c1c0e0180f017030341e02c1d1a9015003012a8190070041d441d05a10585001400801c000d02015540d40300d0002250010721030303500310074403031002600c1d00d010b200d507510015503d2013011501c00001502c11400a0001105d018808014501a0445400d001003556507546107030322200044c0c900344000105030342004402d0140c1644100f06034000d00074400944409082840d420030000d010a0300810b07180c0591808200200b162500b00300c0c1c100c482983c8503102400700790b9400000340068203000c48048242801e00890380101d500d030b40c0302150307414a51a4256440502d0310307600b04000040bc1455455038170ac408420201d801c26001d41440d5540c441084115200047c4000b4a00490300a4950300519440d81e201d28941000e0107d03035035641d17070361114002c0c0ba44848206900740618004160340c1d41281a01e96a8a400d90441c1e2128018203480703101d001092255036491350201000340b1607641088054a00050007400c7d004281c0c0381902c0e00d01c40c00c1c21940091340551540000c0016 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 551446348 1250 551445098 551445101
    0x307031409030d060b09030d0509060c01091211030a140c010906150e13053012090c150901050913050c07020a09020a08070806031c0806010e0f031018061e 68
    0x10459000180c0c41c1100800102c0d4035030b8252030001c23040c4800400c40780708944034481250840c64007030300208004960341c80c003020300682c0300c4000b0b030000d01a1410703500302c1c02d400012901c0c265041e850b0500d110307411200442032540006070444095490f01c1e80382c0e0001d5001e000d00340243c17040450036482d441c2001140000b0020003080803040c1c0011480c0c60340491404107060308035030f2541c2201041000e0007180241e010522041d0000e41010004890780545400d1141502036680f1209640481b42c80c04200b0100003102c414003071711042c0802c18410558011401000c9021015148405041107004400216202151180400c0310000307030100440c0f41003c0c0c01030240034140c0d01103080120001c002001c0c0600244080144041d40c000300b1607a50f400c01c81000820201110781015014511004221b03c8050301e8890110700094034540c8a8600924030903960030700034004254240b1a85540c5028010701d4003000907540070480c0104c04100140240c5803004a650494113640f03010710440d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 551447598 1250 551446348 551446361
    0x10e0f061609120609201c0b070311040308031e070f08010608190204080709050c03010303090b03070e03030a0e040606020a1718131b09030f0b0a020919050a050409030f050307031409030d 82
    0x2a8101f90700007801c0010001220142c00068910340015203451031050041c8901c542e4201505010000c03040000c90112800365003100a0001c0c00c01c82581c8503080251403c07242218070702d001c24074000040c40328600c6110f2256008a410060307c0d6000300c905c4c0c05108aa1103030700000340c650042241409107002034001c0c0c540000c0c0b1041030700c0c42c56255407002404130003280a04042d4075000001300721403c1c4103000515414500030142c0e1f6a8100d6110003612144180c252180a181031a10015a181c004a40903170052b400c24401120200424680321301a40081d1603c1c40d001c030501c075117601c180c9a00111005800700780c1400074007804240f01c032441c8207100d2500801000800c540038400280b6510001030002d501510340c180c941c48100901c4003034020841d0701c07500409104011220301e030070300c81144101d8806440c4128a15100d4040c04181d0b00c00d0240940810064440180d6503480f5100440d40661780786000110f48805680c10383d500d241c15112034180f0381c40800c0300c2007503a480d0700c101c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 551448848 1250 551447598 551447629
    0xe03010c0212041e030c141813060b1c140c030604120c0201031d01020706060801151a0d09080307030b03150c09060705010e0f06160912060920 63
    0x91202100c00041e80b0014419070090040750342c64a900c140c4960019400720002d540e02c5501354440c82c1c2c03035422040e0704000c2507100301e104080302d03190031524240c003204083c050440301c9510708141950361101e9020b440c059150a80100200e00c0042a6081c0c080070040781c0780c49100c0307541d1a4505407200f140b80504510700700e44243c110746d091000042c104502e1081504044c1400b0b21020050300040c2e00a00d43c40c2420140340225100c8101c002c40198010308035144a0f04040109949071810385013201d41d118944c068440b42d5440500c5180700305002c4126041021261501c1c0002c198040c10544807143c0c0115071865021042c4100c080d014052805100800c0d4028a09450f001a10020070140940880812240050702070010b44a010413039840d40d8000d0024092403040302e29540e80d40000c8041c246160190001003945401040101c140f200b140d66a1140002c1c02c107d451425002c60200444245a0751911000000c0d90300b60b02028520204403156018407000043c0a456042d05461 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 551450098 1250 551448848 551448853
    0x1e0a05090702060402010f0f0504120501390203030408030406021c02070803060a0e090703080c0c04021b1e06011505120403090303080109020f0f0306030a02130204240206040f061b0e03010c02 84
    0xb23160416405820755084941440750007801000c142404c60051450010078926921124a508100b610707401100e41c4007140e601d04403044140101d800ca8981c0020b4500a007003c60030000315020403004e40203842d2400d4907200c41c4002195884400040f64010b0004035000d00010041010914041003003000030640c80d01510b1841c502509041c2d180c4015000042c502c40f00842c108141e1141008980c0c844080540704540d41c0f90007500d20758191401c141c4080d0300748100000c04405120b20682c906603002050b00822043e42012103100c003880410f1085020004140801c0c80800c804000f00f500031400303038480e00c2c145820742c100100043c1058101c00d4015004010709140d513207005080b502c0c030f03000145245441e9214440000e0406440c1e810280d8090751141940619131482c0e40140129284d243e440f10a035041105540380b280c022030b40e080c0141e00700000040105d0030350621ba244152081340e0025030304c06076414841602448074030903400282941e04880842c1024410700794442443d000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 551451348 1250 551450098 551450117
    0x2a0a170114061815060c03070606050406060c060e190b0613180b1302220501050f1c02040b060f040503060c07050717011112061305061e0a05090702060402010f 70
    0x4204540f03c11a0010740151024002070b01c5100b14060640e10390000400050fa110400e044156581d00009415100e03e0720301000001c1510b01840b52504440c02e82d241c4007508401034039090002d00b0208009001c4e8000c4041c540400f02a060845e02605e12480a200b080c3c145001402254002c03c1180301107a807402a40601c0300211054600006034400c4049441782d44217400c800501440002c000d400500c0106000d00c0383e400c0c01c0305800318481c80182008540e0303840c000c0092480c11000d4098020740504c0c4081c1d00c482e0810180d040190000c1d00c04984140180046a21a80001b410544034540400c00340440c2c541405030a0f08003075458a01403e1241c075448441d200e010601c1140c6950700d03050340340e009101c001e40110003503402a160654691404a20b03906006004032440e0b4400c00311100c081c15401e08034030880380510070107440c2d454105580c020064082d500d00324030f55480f2030007680000f269950640c84521800b002c0e03014050701d081c18400544240d00004042c414040c8514 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 551452598 1250 551451348 551451361
    0x109080715150b070212030c21090d15200d0c090302030712051906150b0a08070806040f0504050a02041118040c0903201003020a022a0a170114 63
    0x802d14141c500c4269955a600468400036014031005851483c5d58000030440d03070100580403408607102d00b0036034844072102914941c0710b0094480c11360039660200408403400301044464446a52511151100041c0550410380d00082d20302100c5003e0320700304001940140c00c2029000740c40c070340140ca0070700c1443d15085138001b03522010507020350030b8400401c04c00c0700b080c40420000010048020500b4420b105440d04012020340a0f003ca00c0e800c3e95265000080d08406c0c06c1e0032250042c10954400d0000d46a00c00100d801003c0078011542c0a5110141c002020b4050b124141c000ca110300010f0040c2505403040c00195808115010390501e01030020102000307000c8050927280f07500f118006114106410140d8021225400c082d2803180840007085500000c110900108030003204e80201c154141c0c00c040301a03100b01114580182c1081c178007640400da0052228180b0203040c0c94030a03041100d80c000c540c9a032502d41c001d95200d10980600e5003251001c2c4202043c64900035851902d615144 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 551453848 1250 551452598 551452631
    0x4030f1b0618020a14180603060708190c020304050406050a03080f030c04090204030803180303101403070b0f0a0e0303070f2010030b09011d0103031d030109080715 72
    0x450301912031621400441c07a4a0701c801c04000101d54003c00000c94203850b444201103480c0b980d4809400b842d1068420205074058941c0d013481a01c00400605540e603843da01151001405040020300029080101e000038119004005454105900554449140400300000d55409a011501034840d8401c1440400d91800407a0415540c9660b00d80c2d4070f48078645940c00621880d44200c0e9403030f101013401b20030045220000c0d0300400c16038400c0350b012040c8021032a120f00c02070352102031600310364004000300061402401110391004098803078907940e40c5504006648070100c2d07400c02d0407000607548940d5400034041038000a040e00210308000c510782c0d0740034010310001d60140c1400b0061001d46440c3c0110b5000c541c00141c06030404845d0078442e6400344c0a010501030303c3e44512210300c0045114900781070500452604032158980d030764a10b0b141a100c40c140c1501c5180f100d0b401e520388103269182402042480c500c60003030f169842e0341d2800e0602400841e4005400b50900300b030300a4060140740e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 551455098 1250 551453848 551453897
    0xc03064b0d0323220914010b040909060f06090903080a0c020d050c010f060915050409080a080601020312010308031e150f0a33020f030a1b02120604030f 67
    0x11404000c8603c203505000600540d40c0c1e2202c1d1042c001901c000b02c00e482c0c941e50044400e544400d1112000c2610003c000702c00c240100c005012090108100e182004d4001d03820003070040c0400a805c01442090509540842e0000c0300416103400142c070030940e01c00c0100340d2100c0310541c20171104080c468001c3d00d070624030702000200300011a95001c000001e500114845407a079108024080da10b035210f001030554029506213842000c000042c890400303000340000170f81e0103005189460b840803000e803800c500203042e050442c4030a100082c44d402140301d82c0b902950088808a8a030314103d500410799082d01d014100c00e00c1c503a4400d0107241c082010201001c40c1c000c41b26603110300b4415012603021101c03a84400702e814140030014180500080040405082c20401c1c140030b2062444203a986200a41c6945005e0303000304401d00c5214400c00034650138811001040c034000115400003540c02d45089850b0b84150010303004e10007059000014001e01900d00e0410b082410302c09040c1c101501d10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 551456348 1250 551455098 551455127
    0xc03020409020105091e010f0201060b120a0213090f0b1e211b1e0109060305150409060b0901051009050915090106050a020606090c03064b0d03 63
    0x11504108070841e8054000d480c20310f00d0180405400302c80070041c1c036409002800d40700d8080703038200d04120305c00351040c05041d058982c0500031904e020451040300d515400000d05504406a0038401446444100740d00070005080340c5c1000301e20b0740100b111040417540d035200707503034858528044036000c400142600c050124504807201050100390100c1d82152030b0252182040901443e10001104040140f801001d5002070312814400380c480000c4691001e40004905d010a1181c1c108105492281d08095405000700500380305180610b00030805032030074003504555240e10380e240c1302c4a50400400140c01088100c5900c540ca940d4040d020389100c040340641c5010b107601100083c010b02e000c112000e02c0306006094a080b075a0341d000300416980210100030014060140802c2c020b14251700c50f81d00882c0c14858203031a507241c00d0100480c030120203a488002000c401c1d085001004080f00c0408000d070940480360307070700d40d04032030320880310011020440c0b02d1804101c03490007090340150000b21440c0f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 551457598 1250 551456348 551456351
    0x4080711040e012a02151308040609090b030706080a0c09030c0312080a02040602120a030917130515030c210c0d05090d0e011d090a050402010f020303040c030204 71
    0x1041800c01480181144911a4026091040800c1444415440807001c1d40d0b600010b00d20040314440c498070b072460038007203403801a0711000d00600c0a40100000f15001500d142048101280590341c4000700d400682c45140800d030f1019080041c002c050040c0078480310101d000e4640c8506050025202420240800190130354513240030303019038014980d2001660300245c00581081d5a031804400c2c441e41c41ca00103001800c88008114038268500aa9050b40d0142e0041e280308492048410501e800050385401099101c040c03800120320041d8515100900c3c04070210b94440e0601d040115181d0300f940142d002c3c0800544c000e5860f0364500c00c1c0c07504100c419407416500d4000e440601150b243c00c0c41511000555101804030150b0100d00400e130481c82c82c00e05111651b20b40204585903001480400c0201d158800d05450540c46448000c0f115180c42010039000e8041c50013003a040401200c0142c02c140c0c4d100203020642d80c00031907404981c25075200951031403829554071a4207801a1100034040c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 551458848 1250 551457598 551457607
    0x3030218180f1504140411090708150105071a01090e1911030c1c060f0c1709070f14030c03010c0c06050a0605180a060e01060c08031503010e161d0408 66
    0x610088001200f1400140f050001c4a8860003010982909450072150291040c40300000ca0801e020f006200702e140d515000700603079816000c545600c0c0c01711515030400c2020840c1600213024044420540c0096180040030307036050005402c00c503680126005801d61100b0006610040d2000c40c0c403034031607440801494030f039102501007460b141e1300c1e5450030b500401680c40c2c4440b48142001c03c2c8240f90040c0380c10301c0b02c000034100e58030480d41250480c1001a03120b24400700c071004110304103908031481000f102d02c0259103041d0144040d03040d4020400000a1400e2610700d460204010b4107802c0045000704042040303d40058500812504010601d540302c00005d01001c0c22548400300419014004845c40079440522018048c0112040b000c1c00b403800c800440e40303640e820105810380f00591105505540d0548541c0e8064100602071520b13a400d403800c1c040c80d61428005c104106208000500d040304441000d28443c1c50182c2140320041891403090072010001e140700c03904207804c0f54006a44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 551460098 1250 551458848 551458861
    0x10c080705031c06140901050d0507080123090606011b0602090306010f031e030e040905210c0f030a1d011b0b060406060c150c1b03030218180f 63
    0x180100d0102a00c180004a0840f0710440c0c05420b02e9044990300e90100001ca407917030400030014800280daa0b030003042030801400142403503203100c0d0242e4010012108015520500c450943d5512583d41d520072042110b07103d01c09903010204c0703070003038a14005041d0f589400c5000030801482c0038802c0d50100780c0444440c0501240d81d0448101541c0a026035041d9038442c0303641c1e07c016560303100c1203c003102601108800c844448850300030300c6a05070341d0400b61052810402015000b968810354260198054807003102211024080112250344c4849444000d84003c1600f011100f00e000401360700100308881507241c0c0120001d030321010171507294484072100401214608200d072681031094080441a9007440190000944034840840d41407002c3c640369070044511060502c00101807074804940407030903504030341100d80b40440030314207504c04420b441007001010340510800e40100760b00140200040750303200410f20300654142e420946402440c84001c0e181c000c0103101c11140c080300c801142c407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 551461348 1250 551460098 551460113
    0x180105071208100807150f0c03170a0e0304080627060105190e10090c09051f0203090316030b010f030201020604150b1306090501090506060301140402070804080f15010f05010c 77
    0x10304018402c0b0741901346c40d14094596204070201c1170020805e0300c0603410a141c41007044071030345039040d95407015507908040b0784000d90b48098102051a51281302da010b500782c0c00c0016200901c1003000070f2080d820070000404002c41e0004241d41c1d487c01060003201044000030310b0b0350440300b0030798860007001c80d83c000c0503145503450b40040645035070200900c060f4500c46860203007074802d441d0341000344008a46c0242d41500c0e440c0b240c0d85d0403c802d074010f441c1b4007841d01406000c0300380b140152481c060b5aa000641000724480081c446481104018818400785542c002c1c05003007451f4001c85402d0440e00081e540e454010720042100348a035003041c0143c0107a8000c8010300001400c2c050380b80d901d945540015245501500d80124608800014810703228040c40b401450080c16682c5940d09055412401200e418685500240c0030481003001910340d100600c018800d0300007400c401d0f40c400403201e082401c002d140d18051b01c1d002d00140548180d00d0420000c9030401d003492a1154a546820030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 551462598 1250 551461348 551461381
    0x9060702040e0c0103060b0a230904060f1806030f120918090501050a051314010207080708030a0525032004080c12070f050402031515180105071208 65
    0x7500a81854202d9400d2500003030358500d14107098900b407241c0b50315014030180da800341d043d903c000600803040303528500c10600320806500c0c8058050030320744000c140214003a60300f1070f4003480e1040140003040022004003101d60b83d22111a03074043c45520b01d140c0729444500c3d18054064140100d00390a58043c5005a00c144010020084418003032040d0b15140d0008050000b4241d03031550030302001035030b0146103100d681d1190602c03c00700708529985440d4061500040900c2806d150341c20416a404500c250f0043c02480c0d201d850116a00d00c0c00d2401d107810b0b500094026803400c04d25008a103111180e0b03845008400303113646000142010504084401e0103440c1c10031080d04c08000a010548020119988040d90340c26160040c0442014441c0362b580c078081c0c0f04801d04050a07007070620052500da0001e5410610710840400140700b035400040341c5000b542c0c1c0f280c0002c1d10005042c0c0b052052254103110000e001d084c0f1a04058440d190888c6c40440e9920318400c001c025000551940201c1c2e0800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 551463848 1250 551462598 551462603
    0xb03010209030709050a06080111160507091a01110115210b1f05090106080432011401140916050c06040609021309080a20010f06051804030212090607 66
    0x84620340d58030084c1200030316007503400e4401039050041c0400c41c444140502106240d002d07045910b481c800b90010340c2e051068400c00c0790f06000364640015940ea00e0300a25083e54207018600e0003e2806200150074511300c191444050307410041e64444250b01406400100c490098501078251010b460101400c1c08400d401000304441c1e0040c02039050084045c201100c20005041d080301d6107600c104155501c0c2441000c0001d007411001600140711405c415028034000f0501c60480b02c14862000c40070050102161026075480d944003692983c0040b406004000062580d0094030518012526803030000345004000d2034020100da408a101e0002c8800c1110b03944180e90440c200b51403c2005000502c0302a032007000507484000c0b00305c401d4402c0401e110790002c0c14520741801480c3c20b07074500f00741c48441c5105443c040c9115440220078007170341030142102000003544c43e0038402006010300707640c265007008429400c10400040c1d00083c09a088502c00030032079841c0d07056080020300c24403030290300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 551465098 1250 551463848 551463853
    0x2040b0f130209040507050405100e01090b0a1707050f3108030304060e0d1e11010f0204060306080312010e2203050903010c020c010e01050c0709022d0c0309040b0301020903 76
    0x9081420260b9400360050003000c80c2c06100c180c4a6200c101c03150301550103042e50009400650148045c002c190103407102c0d1041c1000d0800c82d549483c0030a42d2303002402d20b40046056405460501411812201d61016160505c0f40c1401c0c00000481920300036940c1e44140403544041d8048101c108a840018000c0e108103100405034990086584a410945044890a04050000e51901d2020900355005109036644140541e080c0500100036203c11098005010500400f030070120070a004005000c8a10040503990b5032601c03000404940c0346500c0802281c0083c800c6000038100e08110742c1c11500c002200b402d040c3c503064102d5001c8e0714410390040443c220f01c202002010340080243c6a80e076011002009031944081060340c44410025500c1c4c00206415881d40266008a0141030b08941900441d00d00a4692560000302d0748009940812100040201a0901005400d02d00c9801c90300700039a040001c50000c869580c040c0c11400b0307100c3d075150852451591401d5050714800038000b000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 551466348 1250 551465098 551465119
    0x20d0504050109020307080c01120209180709061403040c090c1416060506060c0a02040c0e120a110105041a030618040b0118090203030d02130e04140607091202040b0f 73
    0x30664020311803200d01300d010b405050800140284003180d86800990706844034043c152a00c01c0b14402940700024440c0d0101100307210000065019003040d1151415456400c9000d04003480034140340460584d102103031008208010005640d005558211641c0110115221034400f85c1a42c804140c20814091208089044441100d256040404a0740660803c000300e446003402d100c258441c1d81407401007603205034401c0c03005041503400343c55161000c2c60403440c0c19550ba000100003042c8135101144950200c41c0134010305c09030401d55074407490242081d44ca0545003020380e0a82c0142031150041c051004400500c468840302d08003400030000301e10401440c030b06850618080d40e000c2c0220341108003191a0200461102d1140c3c0f40d80075001402541000360401d24000a03521259001407040c001c5600003c8401d0424000b6010354401c511030305d035540310b0343c41651400301c00070031480c1084900c400400007540f4211500c4140b580542c0c010030440c1d242c0021032002180440072a40040c0c8204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 551467598 1250 551466348 551466353
    0x60a1d030a210f0c020f2206170d0f0818030d020316090b0c1f0e06040311010c36031e050c0d030509120a17031906060e1201020d0504 59
    0x841d40c0c4080c241e1916444941c01607034200700c41c01800030340000d41245d42c8440c4406c0e40e16005c8054103112414420800001080750031103010341b4000d50180a003c1c55074041346400b10020f01440d003036240c951902100c02d0000040080c40d02c4d001a00d40800416481d5074400262018001c89204d049103420940d6641484043e1403854060300d8013880000c2d0b102030f8007054010340c00301200c0c0b807012214014581518840c1f400302c3c000d9010a04402c0d4541e641303402c5034128030140209485180641c0714a9030f800e9410700280d0940c0c294145c08020130903034911007101c1c0006001040c040001003502d900c400174240800b11108070840c1c10140c03800840002d008040a200720700840118450000e82c2c0c100743d0032006102541720a1f00d0000c020520500566181c0c1c1407481880b03420204801c00c880d106d02542d110780100070751030064142c2c2c01c41d002042041140740e03c19001840c40c03110804015813072a01340c00400e02c11040001034441e620035110740e90f07148401d4040d1030382c400030b049080009003002e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 551468848 1250 551467598 551467643
    0x702030f03040317070207030305270d08041802031b0d0f091103101103060603060d08030c070c080c0315180118051e0d1808060403080402040506060a1d030a 69
    0x103290304d105100c400540450b00c0803a041e0102d80e81522420700f8180b00c2e07854030300f1024125281d0622042444a500d01550340c107a0a07840e002e002d001c419607242c1c01c08090b1601907000042940090f4010402c0c08810b08040004410283d080b9100c651610110390b02400a080707412036502650f400c1803a14014001009044010240101c0455849045410540087d10196401502c0703040090001400e1401c0c4100115403240004101500e542010b81c1c0c0c0a855400964100b1011100842c80c4c1013089000032245010340348c0d44008082d50031010001903034031002d00e8241001c0c44045c0307010030b180181050501c0448600c0100038010715401e0007100c2211007440707400317a0703040c0b090034480e00c0b05492004c845181000c4102c050100720342c5581301900c68130340603601343c449030300d540d9000584588107000c420700440c4280d0781da00305403c080c0104030907243c020b41401e00c0795504208038114580c00070460b4083d5221601051000000701e0002420300c10140005050030b01070711400300200099 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 551470098 1250 551468848 551468867
    0x9091d010b0d02030304151e180f180902010e030327040501050109360c09050103020a0c0605040503040f0605031801050411061c06081506270702030f030403 69
    0xa0000030040140c080c0d04102403841d0307a61020750143c104200900c600894401916084503445c241004841c0e003809041d42400f6000d000ba1000842418618038160002c0182e88018440c910880e40710034101018001e049120441c01044ca039603414102e42103902a24400c6d00d2104010203607030301c80c0013000b844555003203501c00298400300f5015121595251500c0352034141e50060350340030b0030142070414100f0080a600203e40300300780360507103000c17150b920007029402d400703203041d8040b0304001307070341406801c4240980010341810f0041c003403020381e1644100810f000a410601c04101c40d01e4905103a411803040360802c19a0140c02c580200342140c0210081d0300801c3c1140c130f035241c031a040c0c540c1c4508a40302a10000d04000300c21140d866031380342027005402c030b0318545070040030220000c2000108030f45a0b5440b9090f00d070461542020b00039160410a9403099050320004003428203400c0604041321450f01c01240c0700217190105650300d208000307642001140718020f035500e05003810040d19500d00f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 551471348 1250 551470098 551470151
    0x909020d09061107171216020307020901141305010e07140903070f0608011a03040f02030f010e0c01021b0d0f05210403020a05060a0f05160203031201092406050a0909 73
    0x10300c00b102c5e89001c0d6410440d0007100e000340b10103801b504c640245c082e0106807444500d0842c130061110001503503030302e0b828900810008022094a0000005000c11900c0041c402c4075000e250000401030700f03010b030503041c0e0303c2500e900e00812800e03501c0980d0701c01c600400c0c1106405100740240440c1c50044004c10300292901519291100d81c1e907080c908900d04030038203500c044200144049800104012907202040344020309991009a5000c01c0e02e0846544240c1c011440e88601422456540c060206024100400780049021003000020920040107600000c0503091000680310501800340078440310070b44070041c1c4900e00206031920842c07a40041c081648034604028000407145010b80c202e2b0302e00002a200d504003043d210200752520b801400040c4600d2500040040050b07038240010f100f400c1400b00781c0e19665041080481c201d44100f0201c0c01e00c07241c0c04035200032800b901940b40c0e0440d2a01d240043e680d60b803901c0c0840d180202030b03201603065410500c0403074001228810207866901d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 551472598 1250 551471348 551471363
    0xb031501150318030f050d0f1404020f030c09060603040812090703051905060703150b04030819020c150304051c1d06040f0b07081b0d02070e04030909020d09061107 72
    0x210301060f94112011100301c01004035105d010702d40e180c0c40c010300241241140303071213000411070f03e04d07003120341035850508240c096100c000c010402189403260307140c6503000040c0c0003400e1600e105004100304080107000d0901c6088044000b1b02000f8003841290225100d000d031981440c2000c9158070b0f0b442006000444041c01527120404000c0580d0452991003a0404000d2611391110007050700208800141c0110a075084a408034172031500a00601c000c61103107400b681d80b00306002c6141440d5006d07141613002c640051280c041305030350b402c00c2da100000301504078550380d0300c56103049890940c48400180f12050006100340001703411808000ba01c01c0e4550110815a604000f04030391841607000d8255410350050301404024845005844610f10072414103142041e03408807080904003441380c0da0141e902a0045030540b6030b041c40014000c1400d005001c1c0582415540503290001a016001040d0741c007203040f82e0029030540000c801590132802c10840250449060949913101f00d0081c0d511b407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 551473848 1250 551472598 551472611
    0xc0303041707080d050d020304030e09010f0302040e010203101e0914010e1e2703040b0714010513020d0201030b0a08010203070f050705071a0409052401020a03080a0b0315011503 78
    0x3c1c180440c1c11082c44249070380f42842c00504949042c000c0d0000703041a010072281102c81210f40d10303526142d9000e00b9003250300004951a600c1004113880a8000708a01a4010700c2400386030151107512006448180740d03c00c07448038120080c0d000d030f0350465101070007050901e8000c00c4011076900905041e10b10702d0003c8c10059640004c00510004c4e220041d0f282082c403440001c449102d0108031307215500403400c0203da4000c403a403a05146401c02c3e04803021629000550404000c0051980b00310421024005e0099203007911407440564911040030303000d80c1c14804810110ba10a900c241a010b0005001d900c00795244c0038001c1c002e42003150904081007881d07583c41c2c180c80c00b070019a006254408014900a07003041400001c041c8000c1082c80c1c50302050001081040c0a40a11072080007840c20300c1d010303440380c1c070100b207202c0c54980341240c1503401250701000440d40c030a501c203034800107145010590010030700129140c440b400e076840c030814038850004198000d40c01d40c48581c400d455601413084 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 551475098 1250 551473848 551473859
    0x60b01030b040b010918060b1812060903030402010c1437110613050a15031103070512040203030409020d0e0d081e070c0c030f020102010518030a0503090c0303041707 73
    0x212600f1145003800b10b290b1090806c1039098040740d0022000b40c0d03840108005684072a04640764201d0206801d071141070500c03c442030305241c440c001490040d1001040b0506280c0c48860f228071024001a0400c442100302c9024000d030100d02521401240007141c40d9035a01c0358010013941807800d031001010340503a140000801c084e00e4588940d42d00b1100000c00c0305158400c100041c1e1000c2e8040403000c2500000258640d1048900001402d4241310541d00e03801d800c500408030b903528040c519030000d0910901000551001c103540002128209000a944032030000900d54052a48020b0308140002107140885c0119000050b07017100d4441240c0c00c1a450004c26a065079040391001c0c00040003182c1d0300b940c401000d64094011105061803601103c176921504c100f105560004d0320201c81100303602045580c248505a441444408151000c1e02545491a12441091042c004201020020492690080c445294074075002412250360310707070301e003d0640b58541d140b00521046c0034040c0c00050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 551476348 1250 551475098 551475101
    0x4050a140f0f130f0b0a030f1b0f1403010f021b0601050409050303071d034911010f02040f06120b010806010804050c03010c0e040c030e060f22060b01030b04 69
    0x8801c0b00091400200e84051040c0b8002007030005416440c1d25190006110326407030f501c1c490b001840c0102e69902e03044001d800c03c030344c1216646401d055401d1803076004009000342c2640210580702084030400980b0040c5c00004e02528418071505c03091480040c0d80d051840c0001001640c6442c900c0136507107241c1e40c4004000c110307040c500c00030f050394004100217092184101e00d601034a458003442c4084000b40328000c40c2c64898010b100040c1038030400320365581e51151104a41988804a402c6001d00c113180d22415a00807801c5c0803070080c02002502c004a07003030207402c078100701e03c48100c0c2151a1942e940003548a45090702c64040804c091100043d5101c040340500e50143c1410b843d0070001e900d03500011a0001c0004005854034068210345100580d401e02410501f00b00030b0f5503d480d1040d4100c10401102e0495102109041c50b03c100e1584501d00465656441480c640301c942203039a40380640600080105848800c944107160704408000141d4850b14184d40d082e82c1c2081170122000c00d020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 551477598 1250 551476348 551476369
    0x406090b03130816051902010822060c050c06100f060206101206060503010c0801080d0905130b011b14010f0612120e120601080c0d1e02030304050a140f 67
    0x5096000c0c220b01c0003082581d802001d80040000015a1050450f1600c2e801d01180070607010b40d4040d42c0c0a40819076078004003043d00030204541000d0b111100481315440010780a000500054491250640c40741c051002c4d1003001c80303003105035002842c0c0b02045036500a4070780100048030b4a14100070031168030008045100348852600721b00000d040c5004c40760034044084007201c04586401010400391000c0c0509420000d69441d50303801c0d5410480800e0924562204840420408034820003488d42e4425808808920b19000000c4074006030004a541c80d84500714100020f50208140041003605400c04003102d10181c001c01032003110740d032100255503103803280f11000b4042c6140d40000c50104510510720780c0c81403d100403680c00050120b001300108001081690300700c00010000d10b10144164585080c045603014001a142c1e43d94943c2008081624030010300030b40c1c4084c045450400890740a00f1008100c00001941d500c0b145450740d5002a496000e003084a500d10b449003040c00211 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 551478848 1250 551477598 551477611
    0x20715080f0921280806040b010e010e04051b0c0703050f01061d060f04060f0f05090705220e0a06080c010314070c031b1202060c040f03080703030e0607050406090b03 73
    0x103c2c1941400c07100c25095030004480055140522038800748841c200300342c04100c0c901c8a894041341d91800c2d908200031600d00c28603040c1484410001d4044581c0d003c40042460082105e000401d5102c0303605150b4861541e1290f103620744000520003903510000030310282100e104004654480100e03000301c0b400d94074603224510030010900712100907840583c00480c0e109074041d0104122400210006003a100c646d44481018a8000c030184595200d8611500c041e1405481d2020142485603004103244a1280030720380074040480c2903251001005903807401403654204a10050411002d0080200f096110b045164414100c9038403c2e94040d015401c0b000010007811242035454180c00d40d80c840d0311010480800808010304101020001400c400440c0180741c6083d48a8207100c01900d800b101900344890340d242800704220210034080b100c41900c1d8080801c940740d103a640740c164013610300c801090340036021310001c000c8441d6111014008440031036440f9482030782d440c03c11084502c800d0f03400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 551480098 1250 551478848 551478883
    0x3080901030c0509030a1103191104090206041208190e0d23031308280204020706110d15090c020c150c0a0c05130c020c010f020715080f09 61
    0x4204960081d07106080031581401c18a290132011000a0b00304184040111603811100f05140303d07600341000102c0c0c4181d80b070078042c5540b0303100f919401d0f1401c00c0d001e8082c2c45251140924011503e070581030300d0080080e61070403821580c05103841002500b2012005044a29017035414070000c0c468040d01384140d2002e40008054516500d5920041c280e0006108004409541000300c5850400081541032664012100e0140c1480d410b1030520f40d20b0319140352440b40041241e6090400c02020400c22a41140e0041e0780344010318000c0050107900c104c102c00c2800c041500e021800007a08a00c40040784100700700c960603120180d1400700d90f00340c61080d005038001d800f1751105040030f06182100c80030795402d8078203284000b00c4040c0380104841e403c075919141c0120810072401d103124003104169000c4828080340c0e44080e40299508032041c038250401c002c40f40d4080d289070090000f40045c1815981c010118011305101074407100c010f540c2d6100e56003040b000501d00341e60204080312240e40d01e200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 551481348 1250 551480098 551480107
    0x301050a0506090630030c0f030405060d470418020904080d0203270a031719050a1a060a02060103080c150a0b1c0c09090c0f030b040b07090308 63
    0x103005c80d18102ca41c452850745114501c90304450344007880d0396850010032005503a60001d5001c07590800451004001c059441808280455551042611244036400600040610810368001d10120141007a0310012031f0341c1d40003622610243c00380c54900c0c101592200b6140030540c0500c81190b1001c000d12111007030319800c0703400500c2d0251b1141c0d0010b000f40a0349003030050305810340d800c913441641c0c400b40c1c90380002c29050320540792900246038905507c0181403501a10340380504a14112400e100a8002100000390000c41c40c901100001c549460f04024520345000040010609950300050038040c1c0c05546001d80740c8801210601c82441c1e001e000c07240d00c4e681d15031426401c104812039450081030260b21100241140d101c6c4100d00c2108046400107644080c00b41e00e15116402645042480181d50301140385040554100c444881c0005034800e941d003040c45a80e22241c00c4004040b80306040001807042400034280118014096082c0719122000182d48420071480001d00201c410300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 551482598 1250 551481348 551481361
    0x11404031d0307180507020d080c1927050f09010b0a050c12030906161707110f010509010204030c05030714010309030e03160906081914010605130207020301050a050609 74
    0xc454065404080c00711100c050b01d1350780081c1203201e01d4000750041c582d640100641c583e41000900c000b00c0c002c0c1810f0820f0308107007045c2c1d11030b441202119410103005c0d805620072244902540c41c075007000050824070081c1c05120955007030900e4402e842c0309090031740008101e4505280c00e103040b104081c6a040c40c0100c4104d0076200c540140320030b1401d500030780e1b58040704090410011886070f03410300050000ca10f4544801030303800481d02b14401c1048050742da000380030641822050303004221424a15448454210400e00d801d0104035050032079400c00c030621604080540103001036038070070904091210307101c100707055544980b0304c9113031040c58102514942550080e40469521070007454002200f42514001c40d20b031490300303044140c3c00724604c0010044c409491180c4c40140c50181c02600d52418660b4485420340702141c805000100110151107941500754003050041c07001402031604000101454002500615006d1b4040d50070440040c0000c0e2040c4106841441c00502040141d296403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 551483848 1250 551482598 551482637
    0x9051506120601020309130f0f050408070b0c0c010c02060612010b0d0308100302060406051207050a02150604020d0606020307031101090215070606030231142802040605090301140403 80
    0xa4080b605500041141c00b01607203500c104a03000307120446c3c0105d0060b003811303010b104540c0d121302c0b49003e440c649018040002d8a030011500000d0700100300324125120540300b43c02c0d502c54030390070f114a50306e0201190704c09038010035203e01c540d004454101040420003100d5080e6000c90313032255400421000c444001030b0040c0c0e005504045400c1c030301038555480b070340031030701581c0560001c5021410101d0503440b0030701e00720b140640c041603906e07000c2c3c1054200380000e5031311800302d44d6001107464100c00180b00c07911190b06580360024040018041d642c3d0b140b0000e9201d84c851071054001404000714846c60700c405001d01c0080300e40c05410f81184640104030b50f1000d030802942100e078070b0346070303000003004d03035a000e0b42c0c0e411400e075041c03100054801c0203403681c030701100050f2030301c41160600c0050080030f08403118051b03014090040d103120f615040000bc85060507150441031603544089400f08019600101030140541c0c00d0340200300801d00082002d02442c403c9900071700050143d803142c01c084900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 551485098 1250 551483848 551483851
    0x9040201021c023d06050307061214040f020108010e0108070e130b070917010506030304060f020304090c0e01090b18040f11040e0a11070314071e0c0905150612 70
    0x1d00c155a08031001c0420749420b40c00210400c0340e1400e184d0052510300c01d11a0050315a400b045400f0480c0c94038005c0400d44400342032080609000b400549000b55845039044098441940300b07081c1c1c20351401d45031000302801d01080590008942070300200ea420000c071401410782c0d03000002400003900c3d06c0300920075204020800103149058000c0c1c00002406c01d1000c0e4007680541d1159102103007440490480301c01000801c545903030601e0144a0315883c0070040301c05558003842c1c040d07089441d21505903d54800d0f984103001207440c12500c007195691165214071500d8090307071070758015030350391303884080c68081d56400311011100176803c202180347c140d1090110300e960540202d561001941c00d100c06030000c0d80443c04507543c440400031400345038400d1640303101b890b000d8141041240e4600420074554072158150181c40002d00d0801d110048a02c000d000d402d8601d4403c00c0d4a882c40c062103c003070a03100b4200002e04001c08a020301080d0303220703110401c1015205a0070443c800a61200c1d00340b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 551486348 1250 551485098 551485153
    0x3090c0d0804052709190b0a1508010507020c040c020627010f0203010311010f021218090727060e061e0f0a0e060a0c020f0127140904020102 62
    0x40800c0001602e80300c80c4041344240715014040f80c09041840400e0a4200d0010129045a04864042020130204062481c1c116401c1a0f16110f00d64549000740b0040500700c5d0349130080082e00da000640d0480540100c3c0c8034020700e5080d115100607030410300c0b064480c004551005038201000252141c9640c580c2186940048820420182c0c1c110810b035007150081030340ba03c0c0c07640e000001481800a4070003c0301d90304d071080c6400707215a00c042400940f0340e0f90300c40c410100e400700000c01d4481d2224a00604c001d825009010210318104400042d140d44403040c0262075407034500300c03042041d00317031121050210303039194841007108180401044a2076200c8a2000c2c052102d030340b0303403102001c080d60103841e40301070803030400d82c0e501600c41c0081c0003010009140362144208001191203240d10140c04402d06a040d11009002c440e000c005990320300d040070340f40740044403031030901070003600300d02d4010225004611034072500d0300755005211695004581c0a40940d103d029100d2498000b41d81c2600c1104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 551487598 1250 551486348 551486363
    0x230a0e0606090103150f0e091203070804062702120a05030406031d010e030a1e02030a12020712030b1005090918070803040608040b070c03020c06091909060305060c03090c0d 76
    0x726103105d4a1501155041814031922180e800c3c4802c107001c042e1103030440e610354001c01000d401c000340c1c1740c0e4604c8024915020440104c01003820800150890f00c041c10000030550300e4554650710b18850011240e400303030311510210010801c81880807540080541d0007401031440c6c5410034509034082c2c040c00103400e228075598202c2c001000004c0c440c01070f2600902014581d180b0206100404c200244d0b0490742c0c0511034a41d0f004140303900007046030145007103400d1138480d0941042c6680001c0c09031000141c91046000ca905c01e4060341035101504040e01151540c040d11074042c1d04503558000d50f2203184e0800ca0280c0480d00500102c440a00754850b10310440f50b0080e01c4112040c1103400ca43d00180100f081c91040c8000c015038110025800800c6260461260441d42c40c002c0d960341501540074080c803c001001840340e140c42d861401c040c142042c0c07621102d81d440b8400c2d4002c21161101355224006c242c0402d14030303086d1404585c0100c0d822801400c00031440420401004810b8404031280d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 551488848 1250 551487598 551487611
    0xc0a020709020a052206080601181202060403080a030c0306170c0d061b020c040501060e03030703140c0a2105030c0403060203060d0b1303081f0b1b07230a0e0606090103 74
    0x203100c0420030442c103060344507070551486c078101e0003801030400600700300c2c18460f0001100850601d030354041412a0500c0303010340305002d5035001003500b03441641c0024064100008402000700d806402540e000c03041ca0754200111035076a0b480a0f1200c84088038040c45420840302c20829240c0701d0141428103015940002d810600700d1101840c006041c00c00c2405600002d00680c26440c0c0351051900500300e0b414110840f100081c00039449110765040102440b049801610041c1808029543c000c10200103e442c00c035a141405020031061512005070f041c00b80301e070a00c5440c440c000f900c1c02401d0444400f4100f5007940d95140103908010301c4070341c02c904420881c001040601c210705020b40c03100d00303245240100f1401c0007480710100a15240076108818490008040740b07000c0e50080303408220302e481d12002c11400c2c1c91300c00440080d00c07802c00d2003500c101103000000314400300002100d01c09401c43d00404542409140001446120380040c0740d000042d00508052004021040c814940041c86 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 551490098 1250 551488848 551488867
    0x6021011090a03030819090305030a05090a020406260705060307050c0a0213090203100e0319091d07020d0e130f090b1501021b1f0203040305120306090c0a020709020a05 74
    0x42c803415401940018149001e0259460007500d40e211181c043d40c0003807200d0307800d90320b0183c6180f202428001c5441d0750b44000a01c0000c0c107004a042d0241d00800500005a03500000d03440c02da0b101d034100e0000d0a90a440e000071035800113440003141c02c080c0041d41190f50f140000c0c0d0301e0341c01043c82c0304064054581d030200142e8444080540703511140c4000620481c240c0141443820100101c0008043c5c0303041600e1524407800410780700f001d009848071443d1400300250803128032000d0b0340203620011106200503981d1100d50341e202d03c00c144541c00ca8a0841804a0071208490140d080310740200a66001c1000e03001c40f900124101e50016401007000c441c150384100440c02c048840211403030900c02d800c22551381c1802511042890b40c0d0030320444c0c600c2c0c140040c41c8800320f0810300b244111002c40c0076148038000d00584004503040b10542d402040501c0c0c46400961017103400c540300307003210000659144070120a90300213140550091010f903050514003802984441485414000c0c2440240c45 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 551491348 1250 551490098 551490109
    0x21070902030a061706060102070e0903070b0c09010e0a0315050a1d0a15060308090d1a090a02031623040609020f0c012703051c1a0907090602101109 65
    0x240c041e0080014110740390002e40c011500c068844c2c020590000803e0241d142c3e800200b04064a860891900080e01d8000c040fa10b5031180304e0340200100e0010301041081808400940008103083e00c54403980c100d4a402c0080300c003a280801020810401803a440e0034032164811a800700090b0f07800030b8401004048240c1c241c480c1115910941c0c0300c04001e4003000200c041c21601c11580000900c05142165102d40c0c55000759000035004003803c400e01741c20300200540345a1113030080d00b2050b0003401d0450b041c03038139241d500e401a07020b84a2042000c01e21003c040340c0004030b501c4011003803400e101d82440e80000e11075144480c0c2d072058032200c010414032850f00c01021145c01c05102c3c00c0d610544020403030300351890007c040d005d00300b082501122283c540d1415422050b410320304070f44d039004241d02c40b009004186507c03c0700189800c44c01c031580800301c8102484002c04031603188803551403c1c0304860b501314501131540180c22240304100001c00a0300f26240c40700b501c100803030070700e07031480042030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 551492598 1250 551491348 551491351
    0x70f0507030204061e0801020c0307060f0b180a1a0d1214190809010614100201140109021206040c1b032105062d0906010302070c091a040b2107090203 66
    0x8481c42e9600e07802104c056405c40d044020499440254104200230699549a00030804007038180f50b1100084600c0048561007503a0000d80104500c545100001640d5041c3c9000c568000ca1149400049109610f15002404850b00d00800d280140d45160340e44c1d0482e0607c80c2c00f070038117002800c49607824808031180581012315402801302c000403901e500092055501405019180e40b40c10418043c48000b050348800c00302c0d040c0d400070340c031010101c0220700401e00005040f5032142d20500110340d014954004018100b805102200310361640e4040008450509083ca00400d02c41d40100c000301900c2c401d60341d0300c94002c1c140801400030310350028280c071034001001080741d60354100300415481e0005c00031134152800891610800c10b80c401d000c404022901046108a142400149041c0e20035011101443d50001950101c0303656035500c02c0103404101106400069422800c2c4e410781401e225541d20b550000f00480d80c0c40a0f80301810703604420f110400c840034011440049040e0f81180000c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 551493848 1250 551492598 551492609
    0xe061306020f0c01080910050c12010602011a010810050405330a0b0c070b161a07030605040212130303020c0a1416141011011505120a08070f050703020406 68
    0x101642d1007103180d000c0c1081c00c0248014103110145090003a103a00002c0c00325002c0c000c034400082e07030343c0301d19503e91000e000708040941081002c6d0000f180d807940c1900002c181c0c81c503e0f003110100160102c0103681d4030b441241c04038002e4103505c40030480e600d8680c11890f00240b8181030350440c1420702ca46446014101210842c40c0d403000042c1400500380089060300509070129401d00700741e1000d043d81c0d01c0e6001c1c1c2c41450400741780481c03822000f00380c00208005443d400888021121800c190782100c48a0450b10711010078508070001030b05007464001c4407000c681e480c41449281d43e545d8a6041c005030068015000c040d801c0c001d00e100303202c0c10402490070b0f9010300c2c2c501900050b442455490041081600450000c03248800c0000c02059401070140303590840b030424401150020456007820100b0045440e582080780070f04145281d805004191902611180810141403652907038400c480d42c3e00a181700d00404c64200812103c0101103076003440340058900c840d40e2600003600b0350f40c203504032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 551495098 1250 551493848 551493853
    0x40e0a0606030c0614070803041a0702150609130201030e030d1e0b10080a090f080d020408011b0e01050f070b07030501080607080106020718090602040e040213060e0105010e06130602 80
    0x1d00030b1103c542000030040c00c039440c2c081801c4103000c8694000780240c01d0b00610140c03010011804010703900003408803d07401d00c058101c15103440b000003507540c0014001700300c40e5001440030500a01707101103842d10407a4110b5030143d11004681c01140280103101d4802480d000034480340350600c840d405000ca441c00c0d4410420b080380403d00d1240300301d86180f03003003511841070881e110b090345820a602503800b02042c0350008410310503041600ca0380f1448000113003400030004003044000c070740c0d83c054401d940c00740340200501609140886500b1095004500204001d41200d8403190300c101c0042100300145460207007055400c0d65004e003000c4042c2d4541e4041b0361113500501c2000f004100b6294850a21f1808040b1342d4908440691a000140140d01c1c21082c0300680c0c032240c0055030410499181d20100455543d13a54600950b102d11040c9c42c220b100c0c1180b40e031681280489030284605440c11044102010307440c00006651041000e09451f0308504180700e03600c02000c00c3c210f2840113142c075402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 551496348 1250 551495098 551495111
    0x130f083721091406011512020313170d1104180c050f043b0a0c0e0d0f110604030809061308030c070303080108031318180c061e0806010e040e0a06 64
    0x1845040a205800c5880e074410300c06e8148006913403240401c0840e07104a000140c1d01e440f501c951450034001204094500c49105103220703034480600c0000c09004401d208204030303c03920306001542c0c611076445820701d442480031032440c002c520faa0240d0100710907410028a0207810700c101d0001900726500103840c0595081d54481c441c505c038046000003922026000100100c044035460107200040c180c0e03801c03503036501c98480d011400fa100c908a030400041500b8220507070381c40c1002c205d90314088102d80e0381400140b41c10b10380c145182541c090300d52104010781001c001e90240100c6811100751010040558200018401802c0c0f00038850b83d0001405003003190700398200500f14403010381c40301c001540700300401c03091091a52544005d603500001c45d806d0b80121808030b1405020441070050051200c242c01404100c0d4040059049902c99202d241e508100a4100d0541d0203030951aa0f003c03030b241c04000742496101c0d404030f2080c0c107801000003402a40460b9214581034007850100c13141662004d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 551497598 1250 551496348 551496383
    0x305060106090f061707230c150403091a040b0a0203090f150706020f07020a0b12091504022e110f0607050f03130f08372109 55
    0x2c0e001d0300501084003003085075514210300100501040c00c1c0c5030580c00c640310042030005108406901e50480401c1e090702051010b560046a65031102c80303510380703030b1083ca40c80080b1070485071b099510a1750161101c1e1203080c5048004085148522007660500c14204408580052008040e01d4903880035401151649031f840c09000c242c04030340340614804c142e00c0300c003803107141c10910485800381e50200b0096143d104400d00902d0502480702c0c02540003116900100c0c40000c010007400035085200c0050416840e00d1130361581b541d10303100c691501042e0200015000d42810180c80101a500c11251142842c2d81141e482c120200ca4194100040203210544a41c00041202d881c0c00300001d0042c0249041404d005000d9101d11448120316002c00700028590454103000c0d21016900140a030390584540c0c5051501c13544025a802190600c0343c400c80b60340003610100c01c2505210381d05240c4c03112290001510344000a040c55020001129000c0100284500524180301e118011800c03e203200316 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 551498848 1250 551497598 551497607
    0x1a07050604060506040b012d03090206190f09080a03030e0309040603200a0f150c060c0c0b090a020a050f040f060e04031115040809010e0d0c03050607020a17220305060106 75
    0x1b0401070f410003a0802480014950741000324403118402103600c40e02180d00d1205030041c2c440d6400c040c2d070007580800c00080c5442c200f042200c901204e50b507131000d10441c0d482d00782c9018005010307034403a42c1d01803800080040e00075408515200082011607040c4507400000806960480e04211000b09a66031314550500410101440d031200407900c03590224101900c0d8100c4000c40d2007140f81b243c98407254941003074043c000001c2070700d030000c0c0240040203101c88042c0082901e844115112083c0383c00245c46c0306008201d92005c1a0700400c8182d4a03032030305040004400c20260000c3e801583e070903102c40f111000b80700348002044802081846403403d8100549580002024602140c0095140c03550708a52101455803184d4040071302d9843c3c40c241401240c01c5103004050701d07000604540c040c0e091001c4040c03200102c0340319608444041c5d881030000c984074210200018070740076400c0c2203016405035101c00303408030042d5051180900104100304d080e40745203951054802e41c02620040c4440c5900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 551500098 1250 551498848 551498861
    0x60d15090e060604240803090907050901021c030b131b02030a09060f0513061d03010b0102070311060f1b060601031802090403020c0907031a191a0705060406050604 72
    0x48080400107030304080112502c03158010441c91195a40f6070900300c5004060803403070b80c8030300400c24041005890f10f400700e640b90300801d1300700d114500f0440007a40c1144100102c5901d17000690242183c20410401d140e40349100e5035942d41450340b900c40307004003516442e031107080029526002084200b00c01c2c80020701c0210b40c049650031500104169581d194000c0d00041c211f030010328004030a41100c2d0b8044845010b010764901420301441130029940c2c2d448040005200c082d41c2c11039801507100020542240c209201e458050303005171104002080c95020004285000982079524003e09509040705c19400321155651424501700d0320748151008000d003a5101c54203003003c024840546e00380c0c451407550301d040240300b00c060200040405200784050048940301034003483c1d26040212028000d0302071444010380d10022001700c0800d514182002d000340701a1248030a1000d400e0400360407642d0810f44607000032000800ca0540000c03020801184154000e05000560341004420001503880307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 551501348 1250 551500098 551500109
    0xf0921170301031226160807030903120b0613081e0109110d030c060c05030604141306091b0308031b0702030c10020f10020c010501050d031418060d15 66
    0x201800103000203040f4012201406840c0e0170100580c40008140c141406041c010b03162146101c84103102c3c1c00c0d150415140c0f002c0340a9140c03c1c8040d590402c0440440d00c00810240001d002d04c100000c110003245d10403142100042c080c540790815000d80801c0b2020701c2e50060006074441d40c1041c0d45503a4200c140b40f11554501d00a003c2091a5140d4003211882c0240c01407250f504900b841d81014052681d12424603407006050007040a00c140281c016001269440d0042d420f26255041d5042000e810510860f400d02c0d24072003280d01c1d5201c0070014414050210b400380c155680486951710002054401117110b240781503660b00d007024111242ca19905602104020184083d1006039804180c3d80304002d4152034542c0340100d010001c030314046d201160700409016203d004400400396400401031500050001e005170390340d66047c00441e064844018001480340000c0c03006102c03009004001c0e41000e42c0550420150085c00519035501c2485102242551030491300c2b4032144c00c5e01800018034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 551502598 1250 551501348 551501393
    0xf0c06061002060a0b211c181701091e050d030c1d04020d0f0e01180302100509010b120307050f0714040216061503111504060f0921 58
    0x280e0140103942d460001d0300c0d045a007501c550b000403082d20341401c842c016440708510468190b5006d402076071180400101244034001c64401c280207940203105101c007581c80e1034410000c2a1070300072941490700a014201d00c6c0c55403175840ca0000701d080c09100460711b03c042c021042e407500061810901e0404c541d00641c050509106000e40700503008141207040182d801c1c058403003403001c500020000d114142480c003030146050300301041e140181c1c0c41400803000340c200821200704e0103182c451840c2d0a0710001801030b031000c210410024071640002d80c006210f4400892003003054000121180c4022607525562b80c4041224414031004010350101e004440b030107002428285000074500f28480c51a0034015500007409001c407003040c8181207001600714004000c40075480c4002c43c3d0000852000b950760000d4800d080b0702ea480c0030910b404800d0740488155187c40d01e48041520707000444041d000501c8541d0030b0004481120044000591600054040300c0c0701c8103107410464008030040c1404404c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 551503848 1250 551502598 551502619
    0x20301170706090b042c0c0a090b03011a0f04030c06051908010501050a18030503030a1d12030a0e01090c09050a0c020f03250f0501060303030e060603071707050301020f0c0606 77
    0x913070f010310481c3c09954038903d243e5101c0003100211011a0036409440d2602262502013100144881001e1f01140301c056031600f07080c1d07603140342100c480e0200303002c2c40f995040d55103240d900d02c0c00030000600750004140700250800d43d40340ca8a6208441a0303100070045400081c000e0125059020034110040003410a540340e0f504080008103a8040c414550041c8107035242260602c80c0c10390490300040d42e211003225501c0c9080ca40b4040642090013400083c810000446100194046481800b820000908605550380c0c0b9103098040d0124003100001e42d5a03c034241d0003c13400f0f080c4824054500144003140f641008040c2008441118007543c04540020b90103841e0b1040100444403822174888034143c100b146800129080d2740d84000c018800a00c160050b0100305040d0044001c60b1b002c0d807000c00210640b0941c0513203c0a04441d210390542160109000000c007880f1840002030440007240e94050f100e1000c2800ca80c800c42421915103000b003051040d078801008410341c03116050f11903d541 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 551505098 1250 551503848 551503859
    0x5010c21020705040c0c200a1707050f0102030a21140703050403080105014407020a0b0a0911040c02070b21010515040b0904090609030816050c0307032102030117070609 74
    0x503440c4101400d41c0c07100c044003401109541c8c0b00c26180180900a050300a071714141890f075a510101d6200c1c1a0081207103400d2818250b00200940350307540859100e2424400b510510488085058100c5443c2135980b0f6082d81071a000b00203442d4400d8013551800143e6040c0340c1000340c40b004050f8403481c100031020f005140380c80c0c03600c007441401004001101c000c5510b1900c002000b052144204901d0800400405c101640c2c005100c0e00080d00802d258111920b0341000041a200b4241c030185c4a035051026801d01e43c00c003907001c1510103c1d02c0c030648188688410103802c451384030400c0340c1007292042d02200c1400104551080c010709088610a81462148040900901461140c0c5180c40404900c0000c00e8442380c0181c04c0507517028000304130920061401800380380080d2009000034040c1c04541107000e0017581100d800e203040400950a00c00d00d9601114054101d000403c0e945034443d030307203c480442c00d00145000e449410b0403e00c000516200e42d0f4500101507000004100340d96a0811a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 551506348 1250 551505098 551505113
    0x103231f020319050c0f1c0c0c14030313081e0301180e0105060d0b04030e030706030504031107050f13140c04061e0f11150c040602071208030105010c21020705040c0c 73
    0x980c0703100d224264903440034058105040100e21140400d0f2414405c8c2410a140d00040400407240f20f40490119820813001459403030000b207501e030180032924003289020541c410080d22040c480c6100c2c06880f01c1d1440d851076503540003a4040444040e410124640e0b042c52070282d0380380c81244030000c03c41c03480c2220004402c405d003503202415090070303d0089014941308803484096108060211000c050381c41c000280109004c907829400507075851500010100042980001c4500c0100444104012282003000b040b45160300c00114690343d09010403000b080a1040c0e206c0c0c0c4403404410f8039580f820760046d019103080f0300110807203035481140700f5400d50090b400b40b010202c030349804101040410040e500d0300c0e028100d4000b60542c2c2c02c080002c512500390003002034641139400e072140075588076034038040d070120000000c2030b5080900051006521074011801524050070620781042003100c61104002c00c1d400c00c22005802c0745000b4085400c280c040c54807070805a1401c2c0241030130585448a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 551507598 1250 551506348 551506357
    0x70221010b030f01051329090307030e031b061b0a0609021503190c030b0402070c151106180325030315150f0e0a060305090c0102060103231f020319050c 67
    0x40c2960144c5580d042000c0c060b0101f03032021860400d1028550234500f101d0382e030300d400c603060480002d198040c1d640c1c080c2c1004540c80c10011440e14020902e10401400c00c0116007108100c1d613540e03900440f11100c000400c01424a4690081d0400140309000d40140088000152a014142d0b1810410702c0302c0c083c0312000307020b00c029212800081521401c0300c00c50143c10b81ca40749075070003400800c5400500190491000840365518114084200034020582e0760885a0b581000070741c01440000b9004030314518582c0c0c1440301c0070207403803422a8288017078554010800c01c001840c550714829100b01a0940724402d542144c5402e0f03414a01e2804041d456a0f55012038800108a41410841c100303a0117000244440080200380d4441192100d2004005020880f005121449250f42200c0380d940089940c60503a600071a070301041c01c0c4465884a05404410030f60125446001011031111050300841045101c0903900565a420303e00510080010201c0e1516030461800c070500a98070030040446 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 551508848 1250 551507598 551507603
    0x51308071802070203070f0303080907170a03180e0405030406081f0306020705070f14010201110712211409060a0e07050f0a03020405010801060e0a02040503060c070221010b030f010513 81
    0xb580e10350300303407010a06104486d07100c40d2a51140c3d100100816030000b40310340c41102e0300800c9422641c0d840014003c3d01440514035145901302951440200f0301c5507035051031445503a883c91105559800900641800480c0c0c20baa90307804c041814415160b03c6098aa005801c00d82e070344c0e060710500000c0100c401d440d8400102500c0e400030302c881c1004002e001c0000100880405001403c3d0b4460001011102e4141c4860040d4a0054200c008031001d034280c0e1400c1750442083c1120105104c8161814558040d0100c1038200c0e03000d1400504072607004044c9203c1b4450101d10303140c20b140844e689006000b909040c05a030a000039041c801c031001500208a410840303000b6101c101020208510303041c1504040c1d000380c140800414a4901500544100d0f24981c2c0d0342519603803401840e808034007490041c540e15401150215104102d440058040c09000501c0440901c210820002001c101e402080f05c0a03515428101d115250501150f100500030710000c1c4258900a00c3e51105606c0c0d080c0b00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 551510098 1250 551508848 551508851
    0x203040b0114030726010903031a0603150f06040306020c07090b090610030c050f0403051b06180105031509070309050c0a060203040b030a11040b030a051012150f06060513080718 78
    0x1200c12442110174001e0200b1000710003001406c0c07442c20000c020300440101c40d0310307194a03003c980c0402d0a10b070707040720b1284142c005400c0c04e488400302044032003d10810010303030050080c000072000ca5110700c01040e114207001c008000c814030304040c82c01950285034002d441040304104100c0309482d0010302120030740d032501d0000b4900007420340c00d44580c0580080d031284e20001003000302c104080041c400b0324a41451110700000050002002803901c100341c040f8020b1405107841e03400c0c65000f80050b540068440c1d6114450320314000204405d540b04442c6107000036103d07060340080c84410300c0b200b60300d40c0b025103400003000d003400b5001c0d40e00d12903440340010400e000800035020200036400010780c0003542070820ba54981e10241c2d960241c000750f40c1001c03180d2500000c0ba0300c0c5282142144122041c801d40034440c403442d40c9800004442c84110040901d8480f04100480f0b0100c0c4200c1c170107403045480b0740c0c0d11150200350711156241d080c0c0048510342e1061200303000c5090394003c0c10512103c000350 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 551511348 1250 551510098 551510129
    0xc1d060604060507021917010e0708010225150513032a02091b0f18010507020f0d111017090106030203150a0225060c0201060e0c0c01020c070602010203040b01140307 73
    0x4031034101c901b0691200c584400c41203841c1209032410741080a1302c290200491781829150142c01d0300700d2145946601c400b04004400d0b00810718141d441d0415203000d001c4c1140d44124030303c0307180300b030700c0d42154141e2440c156000c002081540009405000e20031224031103104031045c040c130509049d1704e900702921903803084c0300098080c0c4000881c5c0920050302c0800a4a81d98481c02d05040c80c1c101403141d041580041401d00a40d5100300c045e42c4503941c004089100c6030600130305110a0b826294000d0320781031000d03040c4c1007041c1c481c50400610740d01750350369001408100401c0100e8044000d440102d0503410800708001503540007a030303030380381108000c00c854064807802003e000a00ca0303402180c0b51112903420385400b508400c0c2d174500c07541d405118240f01c2c41002074012401c031100d40c0603803001c01415001241c1c992502e00040c05071040c1e60300c001484d0524189042c0d140644961010b13006079000801c010410021102c05401804d25001c0701d08034010400c0081e8440100e801010b0b203001c103d10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 551512598 1250 551511348 551511379
    0x31e020705240d0222080307080d0b0303130b040602011404053a02150a050415050a090209040b040212030406020319050712110f0c01120c0c0c1d06060406050702 71
    0x411200d0b61180c081c000c56807810201c0300b0128241c090410001c2180e405c000004004001004803000207a20440007807070444c007240c2c1d00c0c6c0105801c01030f05070144024441e0440f40d8031155100d10107000e00340c00e541d490b203203410780080c252803000c07460294445694044c800010130000741000d08000c40560303c0b801c4106211002c24004008900010401c005080e078046c4a4000c00d110b4044503040c141c02c0000d44e101c00301c0d50161401a1070040c0310034489101300c00c40d6100caa02c0329400c0400d48102013016003082c0c00040ca4000700b502c0944184040f0b00503c4110315000248201d5400008061810700f403801e000a901c82c083c201d0401c50480c0350039a84010340d0310807000c850301141c1c0015003000c40f0201034401030800d010000c905281d882264500c508504000401815019059550303c1800d0070b03522800000d0007025083c1030a0080340b04c0420006000002510080c10700c807c00702c2c0d401c00340482c0303041d07200c0030242c070490003580c00b080305000d019445003c460016806940383c107642c80c54039 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 551513848 1250 551512598 551512669
    0x1401030c0c0609030c0b0a02031b0702030604061d0f1605180f060f090414010c091505070203120c0d0f0c020d060513080f0a12050105031e1207031e020705 68
    0x2d401c0200044506c504014541080d036000d58051007841c1c000700e0300007880513203070104c501c10b151340030b581a40704800140002e0107035000000d050400c408a15403e08030342c9801403800400320310b0085150400e03045c811b1025906104803008100c00c0b580d0700240124032501203a060006051003d021030301c0c50005080e91910071900000d0003018041860616050a0190450982c1d5018460725401c0020640440e445403d082082c0e681c0c80701d1a904c1c42910b4101551907502c003410490f0580034140d50301c0c0d00b0200f40f201801a00b08084058038486403400300c02040ca80d4940385907024443d0741d0349460b001d40c84134050b00e1940c50703100d440000c0340e80b688032000c03c4030148501e0040641c0c45c0002c0d8207501030342042c0601b03e0002903880389099542c081c0e800034140c440900800c0e805901c1854021f00b800001078a8032815002413059400c0c0141813445031183e0750041c10306401240c1d148680840146a00305071000b02005c2c1e1000c3c00b42d00c0d09203c0003564150360f03020464200c4035007420f164803a00a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 551515098 1250 551513848 551513867
    0x71a2107080714071b03150e07090911060a0315091104170c040e0c01090509010e0609040f120c031e1e02070801091505060303070812070314040c1401030c0c060903 72
    0x10038840205c4610110981c5100700240c00121550384803038a00380003440381c6004000a0200f40300250403103c0c106a1880300405900d601525040000510304844d525188010510314031569004200b801d009011141e170000d441d444818880d10389910000750740340b42c60654054855003e9420700b80324171110050302c1e01070508000c0da401032038840445199040001d048001503c280c890500142d84c4d10100141008244507107618084440e0028619161407040e445d40700380300d00b000200d900c40c262251b48601313400c1c1030803002054007024100103264000103a19081040c0c11100003034610024001401c03900c3d108108084a101030542c80d034042e00912560b0090100480204400340560814100085519031040000340c601008150641804401c8031101c542000d0300f80c0c81d2080400a104948000801c02e004141d03581b840440102d00e40b42e0200d0040780555502041035080001c00c010032102c980341141031500d42812448902e4025220440c11074000700f0004040010b0308080c0c568200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 551516348 1250 551515098 551515103
    0xf0c020a0e070306080706110a0807030c150606031413150f0e0307060b0307061b0507030c06050a171003030809010212040c0806010503150109020903071a210708071407 74
    0x2070704040052040e07140e440182254410000ca50003070741c1c0d601007901e00d4140c8803224040394000480c18808503e44100918581c1d100b490031010403981502c900e181964664a60b490750b6458082c1001496450700404520b550140402052401c0c8019051254001040010004608400d241450312440d900c01d00720300840c40c0c001d12010300580c0c030554a13544141c1c1c044134141d28080382840c16041c0098114191407444e103520070045103d03107000880d0b0503004012109442a4000440020311045558000340700540b62142c40352030006c80030301004844581211070302030310340800c0300e070601180300101182d1b05820446501d890301c3c4001400780c41101081d01e9000c10120520040040a40c914021a40540143c80c840d988510415496550f0701c00d00c80c10204004005115448040e8000c1c205c910004088a04441d6180c40d04104540c007800707000092440441c03011114a0700854800c000da100101e0322040b031600c1c82018120b80d00c00344c8240c08000705001e00d0214a200c00e07080b01d82198 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 551517598 1250 551516348 551516369
    0x809010902090916092c0106080d0503012c060d08041502060f010603060b0301030809192d120b1e1006090522050615030f04020f03030a0f0c020a 64
    0x14204581e9607940d82d0380c203c10324041c4c1200d100091120560321903044245a03501d010f03507a0b54110200c0c0c3c8510009007900030b0076075694000009400e0030801040e400c160301c0b5102c450302c0758500401e01400c0c81041100f0546a440c1d1410081d40e824041c0185034002402c843c201c90541a5040084940c0a66081105005614060b40e2540c0c0c2e00010101c3c4948072100b5100c03260707a00c94000f181607841034816180e51042c01d02c0140009600d40015101d80e02c805080742d003800070009842401c04c106503005101e920030940005032100c45051304080440514803000c0c41591400c0c00741c1d48403490081001e0801201000031540e6001c0d06030b0401090b0b50402e1070744105040906450b480c000d00e81c0304040200b1190b000025050502c1e103400502040c0c958120401000003003610320241c5001810b007903100014101c0e081c1e20030700c40780140d4002d40000202001c5403400b8818080c1c92009040a01e1003a40140a1282450742c02400c580d5a6002c918000c0110001c07840071036a00644d5801154000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 551518848 1250 551517598 551517601
    0x303030c18030819230a03020708030a0f0605120a1506051e01022107030c110604081006120c0b0d140403020c041d030a051803010606020706021219080901090209 71
    0xc10f1141c050924000840000704410f815801c00381d5009a20208040c81110400c840031072200a48014101000745810090315141d51030360340da1510b900849058222544d1528100f00501e07031071086101801003641d1920204111003078259851004d42d4005003143d21000b240401c2060580110000f0900070700161484803500f42c1c0701c84113002e078440890051041d0106c07402219501c00030308130303001c020fa802140390000984046070274060b0020203440a5001c40c1000d08581c4540005200a281000143c43c9452210b5202c0c1c081d02c0440d40900008410b0100100108103100d8251040350185d18016913189402d6100300701406620600c81a00300e08375003080f060503001300b60142906012207082001c000c001800761060611107401004603482401000304841c056001440890054200f101c51030350420700090039940680c01000040c0c01c6000204401501040440c0083e44028801c41c01e1010084d11141c00100b140c3c0100300b00300b01c1e040071802302182984001022034000e070814415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 551520098 1250 551518848 551518853
    0x6070509090c0c03130303080f0705070f05010e1b0316062c041d0c09010303270302031e070e070e06030c1303081c05190522060f0b03010b09010303030c1803 69
    0x4603191b21082d030218800070f0024001403084800e0030720404058503010304003600c90300c0d07940d85410000005c40702590380390f01c540c800c807408000e81015803034004e003181030343c0c00307180141810701591815039050742d51482c1c410301026401c4490302128004809001e2000380e030140b0fa20b0280301c80508002d0b0424036080c2504001c50740210781c000c04156003c01c4641c00e0010320107125005e40c09200280c0001c1c0165102610100c134110245024490030b50325415081e00c0c0d0300020300708509611900c1c0c41500201505030140d800b0300c1654020b00c9041003104d0685041c10b0b01070039a6010000d039a01c1070744001300240e601c44002c1c007a501c0007030070811202ca9054891400c6030072540864824481c0303400710011a42e203407034940030b13252007416001401001c42c9d03480d8462502500c03015041280e040228402c88a61054450070503034410700601c0082070083c81f05440c00126039803011014002e0741070040310840e03620741480c260b046079494500006d90003107a040840e04c4000f180b486034540d54400d0800010f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 551521348 1250 551520098 551520127
    0x6030907170a0c0e1311040f14060a1205070b1327060b090a09090f0f0c0f050d1a0601021006030302071802040510111903021e06070509090c0c03 64
    0x1403040c0304a82c240798480e04d4804420040c00c048905080c000c2e00081c1c4100024040746884010010242c00450000c030184801c0c0190740c001c01170401100707440d0040015a145c11101c00c40202801e0030303608040030541d15041c0e04d40c103140c000c0c490380210000d149800c025203490500c0060000c000002c440784140105400c43c5200040c010b071f903060420f02c1c0807030200140401c03175549510040582c00c0d841d181c0704c100b0002e8800c051050701c078415044c1824011a05051100280c248507544003400681410b0380d10803080b6868008600900c0b4401040300003404003151490180041e9601c000c5a540d1100100d141070445c1951540807401e1a10020400d5000207170710003600d0200d40410340d5000d420800204038001d84c0300340c03503100200c0d20810600324041d11134001c400721400250b803880406441303c0a11003904d4081180180d0010780f440041c114030785014040000640040c140509141400801c14003c1841c40c1d48240424008111a090204100c541c81034010041e80e0300e90700303203206521 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 551522598 1250 551521348 551521363
    0x5011502010c020705010507030e030703060203040b0f0717040308130210050414040c0c120c4706010e010e18180f1b04090501090602030a0e0c0a050603090717 70
    0x4050741c24040c0b90040d075800401c00c001504c4c010382d545401c0200c0c80c0c0b0f003100e07059a2000310301d4050044440c0800400e105000170f5118034094017001c403c504200385582c546401c0149040f04020349052001c65004003074a05d82d0b0410381510f0000c030582c55449072004035084064000f90310021024a92400c0c0e600301c00a08121001031b680c2c600c80b90b840c1010300c01a58800f174982c00004015103542000074201a031280d907068080c2c03500d1202d4402c5aa504481001201c161078850340080b5103071800c1820000408485480307401c0c00122049550480745102e2401602641c180300ea507022901361070340705000030200700300b0040481a015645103e210403004066984822159020031150001580000c00c5290304800400070076084104441c012850903619050b107921549866620000c80c0d024007440d0035560051030010303520b003005004013088071400d4003101c03d550440f40040301c2c142d071503884001c119082964aa80d40c0d58032040003506040c011b42080300107101104100b69021000150700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 551523848 1250 551522598 551522639
    0xf09010e07200303010b21190b0301020703121a06220501020303041709042c1006030b011a07080c010c08070302030f07030c0207050a06030902091806040605060d060501 74
    0x44010549a10480d408a82e81041a40d0541d2081004100049501c002003c01102c95103124141801e20b03c0d00300859641610307117100e882e95840b2405450b40e031034881c1c4e01ca2518120001c51a03c541650007030307d91060040130404484e030354982d10344124030000c021200090000c05940d503c1141850580310020081c0380e0039144610f0300408a0315500000882c2d00644c0c020f0030b1003050300a501000c140d03a42c014000c141d0006d0300c64403400000021021045000501807020400c4000940021440c04004004180c1e541f8100402040404c0744400320505480c0003610080c5a0f00070f04d001040244104107000f0300c20200002c032495242c5c0190301448070722040e03a440724883d46444000710203038001038422403401c010500200709082d00a030310a00a00032140140d884d125950f0b00002c0440480b40e0280c1c000c240c40c4c1102108600c1c002c0300080d402041c200846d00000d55150502c3c0d41c902c5e004100510082d0345201150043d5582450619820392012042c0155a100c0040980306546003112 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 551525098 1250 551523848 551523857
    0x1c03020f1b0f01020f030a0203041b0b1909060c020d0804030c12060b0d1e1b0f060305010f03050c13021c061706041e03050c011b0f02010501080a110f09010e07 70
    0x3044030750b11042c000c444030440f014a1050564a9004996000b90300140040300d40c001d4491614211018400450700144005140c03170384c03200a4860201c40c4500c10b01455820400d545405028903900803082d8802650156564034085800e4500708150b03100ba600702420788214110009485886e4990117042984203003001c0c05454106070501c40d00c1c0c1882c04d030080080b0004014240c2c01203000c8645580c0030f0040343d505400b1003003c1c035500e400b41c0c020341003800100c080304c07010302559070180030301d600600610b03c514102074a103844182e10b54101039110342c4141c00c142900c01d501c101036019134280b000080203124603034268a01400040c4032a1150300050030f030140c945400d442d0042289071080360400d0b10740c01c1018010905000f55501182c0c101c041c00418443c410701442d0901c6203018803a91170392a01030859140b00040e1800c95101c821100b1a814034005200b0030201260541001e588115500b14403900c00000802d00f4000505c6550400d5458000284808203900c0150040320356403039 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 551526348 1250 551525098 551525113
    0x9080d0f02190f0507020f03010f09030513170d0e011206080105270a060e010905070806041703011a13030803041119050109050f1c0311060c04081c03020f1b 69
    0xd0f11000c4000c86070740701044060101c44054180610754031103400005000040350991124100c1c2158403040d400e800180021400420196030f41411001a0070315140b0010b0480204102e1a61032400305000810082c40c21001407441c2d01580d0716a4000307003016414808261210403960080004844c01c000040d0342414103410303020913404070360305600103602808440703009441d0f541c041c2c5003540421819661343e06041c404120180113100140c0070301e501500c11400e060512801c4902060607404450200700010131a000880080036603918400209503141c450150240c2d445d10b0f0a5440540090070010800041001b0341424141c0d19100b220310444051a01c9850340ca1000c150140310702203145038800f8400d52904d102805100706004003503450390700c2013502e15582c1c2c1040c118220085100080c025240d8101071003080e50007140c001d00703641040d02c4c0c051020b584180c091039103010050185e030f2110304235100303804541c514041c070f42c03000d0758469104602d195248404804036826000d07004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 551527598 1250 551526348 551526397
    0x30f03120b040b011e05040b160c0b0c0303040b040213020409020d1b0203040e06060f12070f02031206061b070b212e031a061801060f0309080d0f02 65
    0x203d4041d5440c41a0b4540003250003589444003650750101182c0b003400024040003445007460001449104640e8044002d100e040e444d012030444e0030f1b504540e0001005010304001000b00006403548650030000e0844a070300c80740040361506960381c4a034584e0324000100414100c0c540e030010618070400010404c0000820150380072042d95541000e80140c01c03c100c1006072142d41e402c09500014000c040902c2c0c09408148800b06038030103600211800715960400c0041500800c0c101d040340c01500146203440724448581010003c02000d451140b84081080c0c40005c09102440100c10b819004503a0000d480359614805508004c07800003541043d01d9000e449541303c1284540522400035500c000c0f000c4101600c0c0f2058800da4600c001440742c43c8000000c290120040c080b0700a040896022a080880c00e002140041e00c00c10001c0b5040003004025031f41e880340304180203100303a01e4000341c4104245461011480380b050100800c90400e240040a107456074020000307007000d0034810b00d0a00051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 551528848 1250 551527598 551527601
    0xb0712080f06010206011505160f052e021c050414070b0408030a230d0911060a02071503020c0f030409060e19091a18120403050c0d020406030f03120b04 67
    0x100c50b5280107821903001044900300a11400b100c2c010142406820540c03a4050004807881d0741c00d069603454118070039082403040501c080b04001c000c5842e100c6204c400804031541d45d21030722074088111540007640c1c282e00070f0009240419088102c4d4140401d04080c00c250305080b144030200700481c055aa0b00080081c401c0044400711800c0f18007031410408505001c0d0307240d40360625040400701060148403c01c45d01da03070003002d6540355100c00140c5d6818034140042c1440d540c01074203000d11010070840b0700c40da8000580720122039100300000c0916210f600b00f00c01902039680c52034000c0c860758041a400800200140090b100d19038010070a684d541c0101d4030344807100707458904130100b24107000e11107000c0982280c072880d401041d1140f480c90015200c84c00142040394034045900250b010030541e04018002c09854a68604c5807605160840d21150344658420007800d00c599140f460402c1107440380e030055002540c120021030025181801c000e00240c1c1d018402100003403a2400641051826 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 551530098 1250 551528848 551528851
    0xe0f010b040e1506010504050d03350a05060406050a0803031f030b0c0d1d06090706020c0604091a0301020a08100608010b04030b040c260f060f06090a060b0712080f 72
    0x504000f0720820b0b0710b052120040741c0d40038004074100002080f01142c07c0d20b950118800380341c481c0c1ea410108444102c041074948000c4a015101c3d01c41030a07110003454101d000840d004003a106000903541c6070031001800900f00c0383e1003e0b404c802e412500050a4001202452107214060419642040040b0b11000d56000030f00000300310010313281c0400c9125000300050000c400c12200e0005000715107080f240c0b860805c400b150051903101c0700400250400501c10800140f665000411f400240345d00024100e0080703000c1c8080b030300e031381d01408000d001001400c1941c0c140081e00071540c8440c00800105060303c121000c1d07088000380c101c0000c54078800c041040c102d80004d1400c504160079541c440d4241e18015000340d4010403011404036500b44a1001500045424601c401514000e40412802d0001e402a0f0b15015081f81003000074116485a641c0d074003a038100d0341c006480e03851107080300c000c0c005c940081c0c3c0302400c00b04400042004060318100d40e4400e54941810700d940d01c04426240c00310 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 551531348 1250 551530098 551530121
    0xe0a050103020a170f03181801060f030f09150b120d080c030405010b090c09100206090706050c03040f062616110c060310061407030507030503040201120e0f010b04 72
    0x3024010013000302c10b03c6a01d8090150002900c6403008011842840e50f0082540703640454070090800b4010314001840b42d010700031076016071080c0d6150003c00b0744004e80b01c00154040c035442d1070383e5805511280d40300f01c203c84c0d072020382c0414164840820074000d00402d5503881c040d001a01c0145140400050201c407110305581d9149c501d55a0030760a8081030300080d0040741d40c0d6403281c166090558070011818810002c14160300d44030107001c010090236029901c40c007000d6408c0742c414002048008941c02080e501c0c241081c07999a105062810302d1841643e028140c2500085400316616910042c03028401c8104000c1000070584490320004030380082c1d4200c542c43d42c050141100903800740e6000d80340134400c24203403003400100c180400c82da5882102d8820030381c03446203400e0100c5908891071000400d194010303c0c1c00d24a90fa6005030852040a101609204010000404580c802d0081504030525000d06219a0b810103207080d9503060328034440103055003001000c1d00030f81003911444400d0780 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 551532598 1250 551531348 551531359
    0x1515030506070e120a0302060a0f0c0c0206130b0408031309020a050d1a0607031e031103070c060f0f0c0f031109040f090b1e090601030b07080921040e0a05010302 71
    0x49548905071000300f02d82046682080400c26032100d041c000344102c91015009801070503541c502460304504440040d244000280c1c030301413005030056070050319071440c154140c1e5880d83c1c0720700d0b80a41102d40c1c800c0307500148401800040100c0c61000104c060b11100f400b201c03409100b1a11444030205078011140c1900015005001c2880c60042c15045022040800e4804503030710003034540464140d9114400650210300c0c4031401c0b0119016220b0300240e0700c0c43c0c40c50104042c0c000c58200c3c40c007601c805040c9000f0844000401414030540d82d020b00d40441028030100658560300c007117000030307080c10003440000c920580e0f0745506050003405030590108004a103e4600743d6198200401001031b00160034015640380300c801d00007110490114001d005c1c0d43c100e15030900846030002401c00008006405076001180104001006042802c1e000541d80c10561459030312003140901d048144210b4170440d0011103051801c2c8040d80c030052080e201044c078012555503030102030314191007080c8030083d00203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 551533848 1250 551532598 551532601
    0xa030210021c020901090b04120309170303060607080c070311041a0a050607050a0609030503040b070905012a050723010315050d030c17090406050d0c061116031515030506 75
    0x72410ba0041940c4c40c014149102280e80b107440f800c0d45504550403083c0c005034400c580009260304410030900070512102c0703018108a51060058480c00043d045500880c070108000080114800a40d40d004071a0f40444810302d80d2070501c02443c40074414028059440d0002e0f0034600300c42852940d940701005001804420301e0b1a060040960108605a58601446010800040d068008c85071500e000c0e41e5602d840c0c0c2001d003801c400102d000340c011401d00681c01010032a40c0d0700a0504c1200c1028805000c00220b0030010448004400480082c41c601401001140100203954020140d070106000440141104030040d811640e00404400003165144c01c01c03c558a030440307800d56900d1003031800840d40746103030765240301503e90389030079140e0300d071000c00c0b008081d04040c800e1b18000c0c00211408a512070f41c54450000310002030080c10100040c2c15501d8500741d0f820080017100410074800d904c001da41d01d0070071060b1103049400d100060b505020388001c0902040002405803a0040302900c0310f03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 551535098 1250 551533848 551533897
    0x10b03060f1914100503031908040609081c05090708071205031c06050405060f1c0507150809010c02030c030f03060307091802092203120902040203090a03021002 71
    0x8a42004040b084a0912045502d00104543c002c0e034408040c503d0721030300c45040c4520042c0c00c2e00800d4200a00a42c030502c018090310402201d039010908690410302c61640715030030801c0180c180d1310005440c41a000410803a500c2098000034480c0c601c0d11b90420040e160641307015100c4100e407095a0156100700018843d11125460a40c20b8903c6a0103d030301e0800a0702c0031403c2080520601c51410b60f5401d0100464107140c01125840b40d01154a0b807509154040002c08510703504440c56510020000c038803040180400020010304005c040c841100a88070400800303800e4201c4600c806c9500f0945c8000300140000305035840c600c014005542003244503801d805240d040181140d03814030643e079000440382058411003508240705081c0710000d20340c0b40140a031804014200850845104803000100c0490801400340c05506160245c0440343c1503c0c0351005e03103100706002c1d520520000501c40001782c0060003d03201886034083e40c5803821a682070100f240240f41c1c1411141c0c19110007000f1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 551536348 1250 551535098 551535121
    0x51b0c1318200306011d01081606050901030e0303150a09050f13032d0e030c01021c091a07021206040803060f01020f010e0606010e030106210807080f071103010b0306 73
    0x112501c26000103140340142d500041e141c45000ea0090104d0482c9a54142e07600c2c803418900790140c154400140182c1d44485d0220130b10740400d00c00c0408000c00400c80d41405c0e88250006121072012004403922802c103004951411140300382480d1060b002030038000380002041c0902c0e031152014030031400c1d250341c4460f18040010098001141005484c1002c840d4418012140c0e104450750000d4030304159200910103864180d10702903c40c80390340810039154442c1e81c0081d4208404a001e144020600c515680c1503c0300ca406030014140503251020f6840306040840242991030700880e0054a088011410745071650000d480103400200f0800009001d0f040601c0406025107062040780c2c00070041440f03283c00c42d9000b9082681d1030304400c0074401c05603440444890200405c900810072140b030217054070305084920a0b03442c0e503900254551828403125200343c41d65550011140c40d945c1101c19000e81e034581c804e00d81128440d10b1600c101c011402c051054055854024005188903128101e0a11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 551537598 1250 551536348 551536373
    0xe060906240319152d0b09040212010e01020708090406050109030c0504020901121d061e041b0312030501091d06040201080604022502030607140f030601051b0c1318 72
    0x440e0144181ca01107480c1d4003d100b151400c2140e0360130f80400002c0c1300e01d07040f194981c00341524100307401c0446c0310364503603140120f694100c0c2e81200d44040460445038141d025117081031114120354404240841448521070040120003400ca4003001226110401502d40649a000150429040e11000d00c41da04081e401003124200c14104000e803252682058016a000c04a5030403012500b900c00760700c0303554200502130700280c50320a00303410135065041c1d5100501004201611007108400080314400c0e1606500e0091a000040030240014081018001d01400e201c9d9060841c545000c0c0d1030281d1f442c042100110810b80080c10490f16140c00460f81c045000e02803a40c41542002083c1c0c1006040130756220640e50f41015200c641c44900403d030a06034000c0401d814802c1905c0d10f00160a21003044455900d805000c4030340740e4075400c004031100c0c080c40d585041c40084000000b40d290710000740380201d041c42101d2210950a1a1510344203640850f007181015842d200c56800c00608029500d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 551538848 1250 551537598 551537603
    0x271a0f090a080d11030106170a060b0a0305040609120c120c080d051005130903030b060c03160f02060304060e0d020c0a051c0206120403020d030203280e060906240319 73
    0x422228040d8580c40c4d0309074400e0340040040341c8038100e43c503c03940c016421710741e1140362070004001c814070f0490404c5d07440c03103004400d10406640310006000c001455000b82e072025004280d13501c42042064018042840e9081c040e20720401a103402d026507840782e011444101c8c0c4c4005220305003403d85424601521010b1712240c1d15400000002c03420342c489200b24200c6100c1d170100880c3c1c8040c2800c025045aa0a00005004803420042c0700c489600010403207545189172025800b03c04041e05000b614a07501a900940c00040001070105120543d04a01c07403c4925500740d4090b4000d0300000c0c3c3e600c41c00380250707030f411904200041165250480c1c0c01c0ca1081c1c544401d03441000071503400501e4a61002103c0c0b220319090703034140428541e0400403800110301e50704085195041140c0c041c0841c000940c1c6000b002c10b10400c40c0640d4020315041000003000c54003c4550904141081ca0f4072120300b229191080e4030348980f84026043c480350792038103c51000c0c01030900b041c40e05560440311605040117 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 551540098 1250 551538848 551538851
    0x70507080c10050d1b02010b040c05090a0b09031f02090a12030212090420030708010b180f04090203031b1006031502030c09090103030e090105040b03060604271a0f090a080d 76
    0x40c174038003009000302207406000741d03400042c2c071040c0d8034208411203584040c0102008800d01c02c0032169124906503034181ca882038170381d985514401c00068a400f1a496041e6610b03031a0b900d02d2542c5c00d0741500507005091040707a80101880c1c407410340030040031200c0006001640032424604034000518010b040410340a40b000c03c55840c0c2c40c0c11201c08400d18402e50402c40e05c00010842401d5020322010301518030500160701d00001080040441c0d060070080c1c511441c1c031000390140e159101e030703ca00c08082d0702405403900c440040004041c0690700440d4080c030b500900001c0000244c1170710400301500d1b07100351740c01020f821022005009400042c28029945010090b50909544280b5194000d51282e551001c1d15412101408210401a0b1210b40035604040b0002c205a50105074158404815a4002407010440d141e9244d000c040310380d0021010901c030030728414030602c1c2080c0c03110b05400c10064034440d115241d40b607a51744811550103101d0340110f00018001440b04004014040038a00c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 551541348 1250 551540098 551540111
    0x1020309010f032304060b012f15130212060c12180a0b0907050406030f08071a0c070209100602070b0309030d1b11070e190e010203010803070507080c10050d 69
    0x110203d0030a810041030a134000303200304000401c1114014015091001c0c641031150300d40984000900225541c200904442e101041418068007082440389015000d05087c59034103000e5002100040d000b44281d02800040035070741503c00c130011341e41c0d02904107000001d2800850320842c02d101c000141c095017004880b09045100b031203080204440c01c0340600c01c4441281030030152240382c203020390700c842c0c0141e041400c01c102041001400140841d0040e401036581c85892401a80006256080c000f100a260050000b01543c07000906004c9100741e40c800d45c1e503200c0d81c180840b00c4c002031040b800107034003145081c46940e04120240d034201c40f442d0212410030a031203130300d03d080c4e46400c0414100440c0c4464442d0640f07901c010594840340c1c0c0607001c1c0019509186040801c0e0038000c100780e80c1450441e40c01d807084c07189a0710013080c482c1114021901e83d6101c41c0010388a40c044441034406c0d10030014049418070012450300b911030402058400e01d5039251005680c41e070000003c0d144007694400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 551542598 1250 551541348 551541371
    0x21f0507060516110a020603043002060108101503030e1f03051b0705151e100e0c0307080109091103060907092003011703070206040303080411060901020309010f03 72
    0x70716030080020003d49100d0b602c2c0800003c04040400e021039500d03501140c4151701603143c802c00c4071340081e001034020901e0703000400c240000b10341d05001d0980d600f030441e0400d480198046400b074103954074002a2139040d16015410b00c20740e02d606641040d4841010002c100280c010721380d104102501400c1041d040d41905c2c52510400c088481d1400031940b564108058000000c20340ba41c50034618100a040c002e0f60307122507a0340d1480c007120b02501400040810301c0c2c88a00101e00d416180c071245540c9840c0742112070042c0303607582c81c860382c000340b05021302141c07032460090f05582c070884541e6500e20150b03113440710706409048005420794140721143e0025149803818000da600c0382800f88010900c4a142c050010101c400d00070300030440c51a680100c0700c84411a9003120b04644c042064000e601c00d890300f040e0300f18840c6544c0258403000020b0000100340d04a40081d02c19401519125525000380007030007440d21032042c0300b5006030010442d00c0307600d43c000d0314800c510201c40d2800296805015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 551543848 1250 551542598 551542601
    0xf11030a02040302032b0804030e210607051c0f060902040e06120601050307030318080601060f020c090c03060d1407060201020714070806070507080f040611060f04021f050706 77
    0x603151800d00d03580008061003541002c01043c0c4001d000c4411213400860049100c0c01080030166080701081103034000300301454482e0a00085041c2d006240c8011103900b200c51011803080300007032580c5e501820000809641c0640295018104c0c084004002110100b910b0303030046c00c6200103801c8207a9141c0c00032032403820910144c0043d00001ea048005800c00e942080181e0400310445016540200014081a00d02149007422682d240c1001d04100345900c00c0440799261035040301919204400001485d0360344100080809000d2360243e0b45102c0b100028031041a508541035000e40400708042501c034100000c031070729144c1c0030f09422000d03078580d021a02d09215184c0d000034010707900441c01c4000d10080240c0201e400481400601c01c9030303e801070300707501e500000705800144000032801c4c00610850b00f0031038090550b0700088995560702c5180141a020701d103003013140c4910848000944010f02c801c15540550380080407442c900c6201200207030400e11030036110080103014044400041c441c0e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 551545098 1250 551543848 551543851
    0x5100f050c03250203010f060311060f0906131d01060206060607050102070605011e0f0f090c0203160503030708090d0c14190c05030c010c03080a05041a0a1407090609090f1103 77
    0x180303e650070510030107004260070740321545662a0035034039101017007000a8440300e198070001e909581183d01c455084031241c0c107d00070510f1107a0800000501c19601e40114101d0505440103119809070303020380c102400725410424011400580c2c132020119910b4a4154041c2803160312900003d8030380181540e4440941d0801c1c1c5c0000d59280511904003482100380d440d140184c919400c00202e203e24014180c0b03203661085c800c401682d6510071940300700a1090040302d08171000d00180b03400b05038051520581e2688111180800203841502250800e00d0100d81c1d02c02c0403509a0720600d40e100a40c5a0344540141880c0c09a141c0c450f202180986800d001084842103004411200080d460001413500b03107010800828100030101c100e00b400690000d090030742016102c0305c0040c2c5640c4900c0c01520980350034522140021031102004840313541c5400480f0b19484c1180e11510a4031101416900d10360280500404640b281100f0700c4280e0496010f000c415051440208d41c2c00c0d80100e130044d00c1d520 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 551546348 1250 551545098 551545147
    0x141e0417151b070209060f030312060414060f0121060806010819020307030605280516020c0f040222030f030f1403010e0601020a02030d030606030605100f050c03 71
    0x6100e01410aa0082100e5200810344007030038882d9210895102d540c4500c0000a00c180f206401050554942c90303034020b4004000b40440742da50900840c507100c0d40c0b0084036083e10075802d051442140303100c1401d900d8016003003d411440c500319504015140f8840007030314050000b0200b00c45e0181e840203402000020059400540400d504049400d41000c04d0410401d0300a25400425401600c0000e215001ca0f9000000000c0fa516800145600d10b003541c00401d085d8400c44107030380da05080e5940020f0150081c0e000390280080580020303038880c18419040f03540115907040b0400181060b0b0000c06803039010680a8030003402a030f01e0303851020f026800076142100165a10780415812041c2c11465000d0390a241440c02401c0d514604144014000e000c40c165414021407000d0740200214058103600605403880e0307190507400100140864803a8100003400e100b03001035582060b5011622180b1696107624085260200640303403640840308000e4070384010049084e200d0100014101e0011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 551547598 1250 551546348 551546353
    0x1b11010b13140108031206010819141e040b060111010e161a0c0601030f050109020a0902091302090607120903050607030f0e011a040506221b141e0417 66
    0xd094a0b2107942803405800c818100d0b0f0041001505400b04d90b4021603001809281c0740c0019a100113014045599090900c0c401d01d040071130001c80701010841031403080729020b1041c0d94007100c2680380c600d440c40c1900d01030070070303007200021403055403094072440e164111131400461607959420381507242c403018840c8220000302001c81409081000b424461041520031511400d1400350044d00b900c9810621000f4240321411065004203c3d081d0010072546400800d100d8640740e0f030300403c5002e0751048140071711540300c2091070f1001002c14400e54132089000780107141454206d68803520b0a019103e241400c0c0a06c03504000006076041040c1841002690782c0400c202c2d280000e6441996008148a020769041a107920401c3c1102c03011803941c0d8100721000300e41c544a250100341c0c2104440d5070203100040864507455601120f400907c0ca40c103510320003096003095004101c2d44031041045600268101700800800410350300001410006203d4080b4509542c84c1c6100d940303074445113240f4003181c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 551548848 1250 551547598 551547611
    0x20090a030c091b02060f191b0c0201030c0302160605270102070209011d13170706090c0803030c04031101030612030f020616022517030d0c031b11010b13 67
    0x201c00d41d41070703c101540e01d07000910450404198410400d03000500c809420254001d513038103003090300d81040301d071541d90b00c00c205011141c4007401002c14100c0301003a0301184c1480c80c480e1307560707102e8821948041200107a0f00342480e03103a0b4030304000e0480a00103c50010307407100038410940565101580c440e0113200016a00c11080c814880c2180c1c05a20520494003921203081024014603c220740c030000744506e600410520b07244c04400301410030711090710424085030003010482c45a1140310501d01034030608000ea90354160003640c80c4011902040d086109010800018401d481c040c070280f1300504000c1002a02e41180500c03070803045109800003410b2145200150b41c06122242d08090341c14000c1d81c0d40307114200065660060b8146844807040920540041a065401e00350b0242c0f40c29a075042c450325001008039503c2c1c01c00500150f4081c0340085080c5901d009200706a00902d806c90bc00d02542085101558196201a400b080135520341c001c8a00c2e0703039608820010306142441000541 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 551550098 1250 551548848 551548871
    0x141204020a050a0f0f080a1101051b061003021e010c021e0310020424020d11070302060d1e0b030d0f0323100e1e06190f050906030120090a030c09 64
    0x1012086d0784030849a070003c0e40f52801080ca8015001c46105080c00c080e035542d240140607410003540d0903c0d541641c0102420301c50407658400610007200d0088588502410031441e082866a40d800340113404951003000e03110040c20502a0701ca6880c8100c43d01031a070007040700120381803c1e140002d14903101d60000301446125a5400b03503402407200300415490f510b400c0c50010390f44640d00c4080c28103200e442c060791074080c0b030704001c00c802450b8090140358440d403051482d03201800c20103595010107020340d500108804940e2107a890400c5005000740b000c12411340c030548506250315072880c105501c43e04108a000d030108030790320f404000040c3c605506d14111001c0c11804040d5041206115410b1080c070500c1400c02e801469070b10414078029020351680e00004214001a800104c900c88419500080000c1240c000b41c08491082e64000300c0c6a640798101800c9588562081c00600700c800c4102c4840c001d5003020344582e1030080c00d0b9041c960b46a8031a41950038466020200e4140ca883c0f05152 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 551551348 1250 551550098 551550119
    0x21f091701090b06010e060d0608011406010f170a1d0a0210030c050304020927060412110607030c0203041e080d11061602150103050a0201020c01141204020a050a0f 72
    0x100340c05003030003089054a660303907403c40d00202900c00c038100501c045801c20182c0d1800c00b110201c46c000e40e01080307403a0707451504a0207401d5070b440705e00b0f00319035400010340c15500408045400f1003455a5a0140001c40d5403001c003da0800361035030400e15900e41c85601c18040c100c031001c03007400d5140010415901c0510400000103040005d04041508200c070f03026000750000e0a413904517504696154460355400080515a45100034031109070f40d1854a5000441c000314000e406280a52a0011150070f100c8040d22541000c3c0c11141c030300d900032030001e0350b40c40c401d901c180d2441c4d4242c8142d0317140554071541803403030b00c1040305d141441c60300e20f040030880f289082000712180304240c24112044003000405588800d070003010075a002d404220b500d031b503d501c24060700d050301c07051139a11070076035071030341002551012040401ca001d48525503581401d0343c0940a009002a4203e1449240038401c2c10b4021030101c0103031003280c205243c1d420210305a90b0380c0c0b00b441d000d0b0000082c0035400d00e00c0c25007a0380 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 551552598 1250 551551348 551551379
    0x1e0807060e0f03042922050301180201030b01020c0a09020406030e0604050d0f05090a0306020a08090c130e12030408130b0a051222111005190804021f09 67
    0x10050b440b841188248420102c1075408481c0a45885035065090302c880c1c2554107122445100114000510040d441c020000d001d801d40a0703245118034400d88900605088a9460800c0f507010b000c6060304800541c401d4018500308001841a25014200107006c2507403d001d076000240041e0b008174007440300980c50312a40100c80c0041000f000c0d6410070351100c68440350300400f54002c01101d012030003040e03401103049032481078010b80040e245c01d0381c070b0070041e0003900114658000540302c000441d6044100207040040d4080013882c280300080d400e000071004195010681c1458003981d40e50203540c030903260140d4443c82c041c1200030342d00c1c00c003c01040101c50f0140c01803501e19006012200400e6030282c1581d181c09003a403002e8580da140c07034040d400201900c0c0c88001c9891031003d500010002d00321420912240300f40c4905540340039405054a850092a005141c2065100410407040788903078a12500540081d050701e000a41514000c00300d0003507034140602050500d0410000702c05000e50742c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 551553848 1250 551552598 551552621
    0x10f0f05150406030b0c031e0108010f3c090b10080c03150415060b0d141b0904020703050c0607020604030801062c1f0201051b03040c0e041e080706 65
    0x2c0080300c1c21540c408454170000340000c15110004030000d401c0700c41c0d40c200c041d41050700c030980c899150b0b521781d40180078203210985442d24500b4180d44190102c4207202c010682c640f403842000d04c162080300c0b0004000c040040b00340046803074000005c04149664500303401a01c00f2000340280700e080c00b400320301c0c129520124a000758041c0011941481100c40d041d40c08c194000c4c6003007190360034004000702400c043d810158130043c00103002d551400c4c40341d110398000348050000401580e43e0041c243e003000c0216807403218040c3c081000410610b459801000001e22038286a07007015400443c40f49488021501e800240e84840240300c01d05800014042c010142ca281200301c40b0042c030301c05201d14a0070394245130842010203401c0c0d0701e69610aa566141c954603014081002c0d00404001e02902d019101d03c141d00294855080d1300c2035490003203031f11568000240701101413a00b2032451118130000c1c0140d07400e60801107950500c4960703010040c0d0742806040072584a5881b0f040100c102e61010494 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 551555098 1250 551553848 551553851
    0xd060204080c0315070c1b08011d0303011401030e03070f05030705010e120706150312021b0409050a0206070318060302030402032517070e0a290102031b010f0f051504 73
    0x100d84503500144c000ba5070003a0185003004e43d9075031505e03104017041d0586568280341e90343e90202090342a0154010300d0001800740a40c208182a0301e0150b44900c000e0184500001102084851a5003c0e40105d000002d16030104c901e03101d4280c48695500401c10801c8409800019013002405024001e81690094036006481010011000c3c000309200da8140106019126a04155001e0342e04003800d0046410110308800f117040003a00a40b41e00070300c00b8081e08c1c2751850000d0002c505080c440d42e0811503100008042d0b1a080350204440e982200d84214200603040131400380344100090a0001000c054402580381d0a05104142c1801185040704402d50f85441d094950303440003101d030504854100500d20711080b01d89400d00d00300019074000a075420b490406101030760303807a98040c407210f810301d0319084c610303c0000400100701e002030740000c0c1c01a803041c495802090f11150800d45d111071100c0c00002d0800b11260f2040903500c042a0b084082ca80c0c0d1010031004001400e250346401008450 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 551556348 1250 551555098 551555113
    0x2209020703181a0d090201022a01020f0312041b0305030d1407050c0d030b01121406210d03150518040c08030703140c1501030506040219050d03030b030c0d060204080c03 74
    0x24a05a2401030040b540d842503280c0b41c005e019a4028045422810f907465203d186601001c0002011075a80100c00c60051184d00c07000114650003006844400000300420281d5032125112020a4100710b04041c00030b0011400000000d1410002491000c00c4045c01040d41880005c184c1c1084500038001d10921104008960442c00041040d0a10030340c24103000980324000c0c00125032010503004030440075803600210012400703400c4481c0340314400464698141182018282d04c3c1d020210700c05440c140e024086541800c0d0281e0003504203003071080c1d04031027181d0380c03800018139040c1d103008942030040000b03040c0028482010300c0d40000d400e055004529020155030014030540c3c4080100c1003508001c0390b200b00040c0180619080c3d0500d40c440c0d0015540c490410a4840c80107403000c0b8171401075100303203450390760000c03141000315040100800107803540c2e5141a00a440c495050a90501515210b140640e030350070001c10300b00b809500c0040c1c4039030900c0411031074a9400c0e01002e103c0d501640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 551557598 1250 551556348 551556389
    0x504050f0108191404060c050a020316030c020d11040b01030e121c05071205070905010804110102010e01020c210304111e030102040e0f0615220902070318 68
    0x6400318891500307280201e415914100d54605200351007a900f540c860a0121002d003955084800034001e43c0104810804126030550a840e40c2c8100135031f490258009000102c0804103803810901e05074000e082010342c00500b540040c95042d46501c0485e40d59030307640342c40c1a16003414454524400401e0030300b0858a45030941d0740d41d60f0074000d00c881080745800940000006030780d9200c130101c0c40d0000300c03e205034104a0f0b801f0300000021500003110b113117020005074402d44140c682c00c08a0340c0c103844090080d1120f4440b1101038480c41003d905642d02c84402e41c0128400344010000c4100d030001500c14078182205a0403a011030b5101221004c00c01c0c000c0c440480d00018102042220455030b4000c840244100100040804600c03154075520220740043c00f442200750440c81004031841030040c50391060108602c00c485600b64400c00c44050100300d03e055500000c04d5100d41d9619004582c00303030344401d05010307640b00000480c0080c0b0f501042031540344444102102800da404820070350038003e031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 551558848 1250 551557598 551557609
    0x625210903030314062407020d030503041208040803040221060f06010f080c09040b03121303110d0c0b0310090501031110022a0103022203020f010306060203030a020304061113080d050405 82
    0x300001103001c1b980c40101c00d1203540c80c4c000c480949034054002850032900c0d040291554100316070a0b80c50610400c1000749c02031140305000e04c5603900803032042c110f4590381c0900441000d1641c0d1342030308416010340b402e83c0741030800c101c074440c2d00c070700b03583c8851351400100040242c00000d5002040c0b02440e41800401034038076080d80c030440c400f5200050b4a20584001919091400f40458804040000c0405c000c00300b2003811410380f405080f1383c4031202455410b2010510242401900410740d10806001c0e86840500035034211503100e1040c400e080d04c541a2104459081e40110380d9040406030010403420000d40b404114001400a001203d03c0301242e2a802645a141c1002000c10344103054250b071f001c0c3c0d050b5506640305601d01001c60001070f00584c10700c00300d0f000591068100003a0420700e50702ca4002c0f00c00341c51241d0f0107035046468020009019406c081c20403680d20b510307030f002c0c035071100b01c000d0151800164103203003c162289411160707400c0c144c0100310f00080041c00c2009001c1602d55 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 551560098 1250 551558848 551558869
    0x60b1318090305071b0b0d05010503160810050613060909050f010b09010e07051207020606040f02130509040c03050a2307050a26070b0702040506062521090303031406 73
    0x3085c020922428421003541911103e6048040e4050011544102d03e0b00c0b50352225060311000e5007290200064030280c0300e181001441041179981c0070f8007198000440303540105400c540c005c4d1507804100d011241070015984031b42c1107a015075543da003030f9070305200007000200ba403611420001c00440240401042441c0014016a9842a100400b040003e40f1507412500d9040b2080c0c4400440d05091400035101d450540e0f0b0544180c1c240786100d2891006417003103030000e030f00c000d004c03100c035515180c184000158001d0055030015281e00001021800034001019954840d640c0120f14410903600401c2100b000b00c03466469500c82c58051009803a400900320580d055841e03111b6210904d10101d201d0580303c0c0864604901564500044103203000c40a007141510031103051210761b81e40c2d4244902809182c801c0303010b814000340c815201c00c1c410701c55808003500a1259400d02d0789098103400341c03c00b400e50590005015800c0800a041c1d242c4034500c40b040f07004030001014180840029030700c844 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 551561348 1250 551560098 551560103
    0x7051605090402090403110a030e130c0e010c0c09050c1b0d09030b040615030302100606031b050f0706090b15030d0c110f0a0905010905100312030f060b131809030507 73
    0x100701000c00c0c00d250180a28010308800d0347e003140d000e81858174000703120b19442040ca60040c80401c0a50380b104905000340c8200c0c00560340d6010400100d40011241016000003c2d0350641181c50007246082c00d5001d001d101c1c403c55003443c3d07511103c4501801030340020000f4105103030881940c002c00142e2005022003126089142c2c013016807910708018005060784128210700c02c1010300e00100b015004603262111020700d107030800116a0b1440140c06954100c00c00002408007040d4000d203060160002c0d0900e8002e01d0101804c00b5038a45d07400c401c40d04c101d0f0003503c81014810030410300c1e8182c14498426000d058015001049803100060322200607450002c2a41c3d0140f4419030850b01d449031405802c0b2001403580303080a6a40c0e0b407a000600c0c2c00c2c002c100116007010300203004070100540300421a980126560750040c04144120001e14616250544142e196080011034030003040282c40001041d040790710503145004034070a401840041201c401b1400d081f4414041707070704002902e001a8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 551562598 1250 551561348 551561359
    0x4080a02010c060e0318040f061202090406060312030b131404030e030c030a06020c160510030e030f2a120409050903040305010c0f0e0901050915032107051605090402 73
    0x480b1443c10301d000c0c0411079218800c5200116104100d0320201d128044021800d403000c1103414054462802660100d010742c4d0700300c10060f11600014185060050ba00c01c0c0902d00003d000d03a1240d641c2580c14114514910000c1e80311a100d82480c90140b49910040607a184204010140c00700c030b01c180c12200500103000e10241b1440403500351800d12640c42d02142c0201500c2c0d00b02d5403032421400039084101107454a12504803008031211040c07400c0010344d48002d1005011403080070084018003241440c0c0307407c6020030f0000032012864280030300380b07064140401c0751843c1040c1404c0319404500c11a49105648401d0b0543c9035442c4c031078102c8060f2841010003003a0350390f0301c400191440c401c1c0c4e40000c0440d0302c2c0241d03013680d55034452080d005940143d994109031000319003c20907440020b000701d03075021040e1004a1030b503690748003100880c400081d058506190030305d0007021602c9043c220000034081c00203002d004020007441031800e0109100c2c0101d644504260100f151a01c00400090160 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 551563848 1250 551562598 551562617
    0x6010e1909120c0f0804080307030806040911100e1005030601080a1a010f1b060902030d09150e2e0e0111100c210c080105010203090d020424090c08010b04080a0201 72
    0x1413001582c002a0015000f80e920340e1350380c0846a5903400b981c0240c1c0020800004680b00f031a080c020302842c9074025040c0030340c2500c040d04201040300a08000801c2c410030700380502c0c030740e250f91030914501c01180c0c440301c0d05c91034000005800c5280c02072408108601e8071000c0040b210000c41c4c001c00320b010a2034030405007034020400392800e0103500c11030840c0446440740c1b030080204503081100c05500c00e40a940c408059510159203a00050040d004055401424906282d01c610000c58280500038441e03400582c00c012032002110501101880ee901e40c640040f221a4102145c0c500e1038000b840c2002d515042c3d071100e26201c10308440e421030300a48814080584501c1601c0503480310340030704454910003900e2402c0700002c06c102602c0c1d40c0030a04100c000101980088140c07140010080e24001c0204d895908200040028040001c2034900e44400d208041244100700d02c09001c02d9900061040303030000c0c0103041c40105901084950348100030a20401c03d020580155641e030a003000311a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 551565098 1250 551563848 551563853
    0x91609060503130506090708120c0a060902130906050f01150801030b07090806160215071d130212010914090d1110020c0313090b100804080c06010e1909120c 69
    0x41d803500000140252140c0020300c202040f010401c541101e000740112070903809c0c0310003001894011840824003e0f0000000b580c08200d158000740c4015100030406290120740c100e041c801c68107440703402d0302c41550b10010007445964108440e80034015200c0858070410410000034a0754805000c0100302c4c41b800b030007054415000e054124040c00000c42980c00524240615021170240104540c0040c41165154046501d10003d02409500f0700e648482038941071071240d0303103000080e568003a00000d4414840500d000e5038800b03020f82c0141c03044100030a5161002c48001d441424404034940905c1c84184811310000250180e04e00d00b242c00d285010350003424405003007511034002030209900014940c003607200c0202c010f1000811080031074110b1600c403491001140c02207404503400040388019290043d0007540d4040d031041c0b040403c01d281c02c0192035420700301031082c1e104000202e14001070062441c03d412226100790318800f402c00c43c0301c88035250a17aa0403402a0140140010403103070801703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 551566348 1250 551565098 551565121
    0x6051c0c1a1e0a08281826090118030f0f1208071d0a05210f030705070303030e0307020904081b0c06070206090d05120306091609060503 60
    0xc00526120aa1054480040d40c10790b0b408807003481111040c19215048090542c0152605440355581e210300039a645000c00c41501042005900300a4031404c454041c858240606498040c00d00b020b014510b07918035112070f080300c0c0f0601e0781401c0043c0404042c02e05c1d02100030365080400901e080c8507641580b8064414012054001812a0429030106000d20156244207407101d8407811381204000c9219608442c203c1c01910744d20005203d020810907090a10102d800200748028200d0b40443e943e00001054500b41002c03074852501e80c9030f000c00f0030741c00a00058420301c41d401c02031031421032203030f490341d888003100c0c000241410b49d41d08240144010400c240c0e00d00e01d0707029100c01a030341040d0808800341e800c0f11000c40554110f00901c4105a180030688449501e1b0180c0f015040015540c00c00ca12a0012044960031504022000f03020503400c00003540c00d0b545c6d68001c0c5a0300d051120034044d0703943c0b00a140b0000000d1040d075220350302d944504580100d800d9860041e4803038403449480d41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 551567598 1250 551566348 551566373
    0x50d0b06190e0411011106061003020c010f051305060105091315020712121d030315011b060f0b1f081807090501050a050414011208040b030705030f010906051c 70
    0x81d1101c4030b50208810004002030b0b501407648242c8030036840d0700034000180c0ea00e2008441e000e070010003400d64180d4960007900070f000c1c00990800042194001c1d480d65204a41003100ca840310009010b064106004041c040d0034054002690b58050a20b0038490340d01c0d01500d60303c401840401210514078030780c40c1c02c4e070648200d642d0007207015030303510031141e0001c040d6003483d90190a02c52500030380400c0d1510201c42c0310100c41c09040914159501e45154801052207001c0c2d0505204816400c0d000c041542d051800500d4841c2c0b80000b41d20b40c0b41541c100c1111800780c84a802748031070720403608041d0403118640407210850301d0300034116555116964800c0002d500b01e20700c0c0348200c001c0890245420b8000c58141c400542e00060401e40e18410042541d81800d040b03240049404018007142d01040745070440c15000d504078031704d091341d5070803007407904d62084441c0710010f68084284504400000324582c010210844103010441c02d007000a694000343c0e4140940504920321910700b004803490006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 551568848 1250 551567598 551567609
    0x2010f021b10060602280f0305030a050114130b010c0606090204170a0201050304140c09270c0102120a14030109050412090602070b0c16150207050d0b0619 68
    0xd548500c080c150040a825600240c0e40079402040c4200003a04654410842190300680c02400000b80004031041c0b81c0c98290b014a11030210000031001061a00b0011035055109940d03203603884c07409030110301c11075a06802440c8901c000c0c0f51601d400703548105400c08404c80702e103000280c516204004ae01c00d01d06115005003502d091107400603107100c1590142041317505007207080409030140480181c540c0c00b1003000a01245080c00030a0104d2000030300b6041d039a02c51401c54000c003034180000f03180080d08950000c07541c0741106402e0814251010400840d01c1b910000b001c0b08099140042d464040d40512802455804180c101c0924812502c84000c07a0f43c00c19042c0e038a50b102c40205010b0a8121010746840b44039203810710103c0e10842d9518115484c03a40a804041d05001c4825a19030003d43e03010700521402e40350340c41001d01180b480006040e02460f61441d8140d0b5034004e820301103d0780c0322500c58807803543c4030300101b0780d20b8039515400002151851060344140d10b08a5400030682c100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 551570098 1250 551568848 551568851
    0x50c0114040c21020a0e0606040e04050a0210020604051507020307080705030a020114150609040f021909051207170f0a12031506051e04090903020a14070806150102010f 74
    0x744010b002c80b040b80c480640e0188003070350a100100701d101d040b02c848a81c4000350043d118003030801425034045400354000200900c2c9071325182e5181414800c0e0310055038152034a81080320041c0852401106c00150700849001500061915440316510b401c0000d242e00c0940800c0400244460700c02e204540c56682c0c04450740f45c071181c050611720755940107903098070090f41c07914041d60131004216058034812000800801e05c03500c8554144100c5401007901107030480d440d1450120801d609001901170400d126032001e29907071615200501000b155071140c3d0244980078803c0d103480c0008103510007656501384480032200c000c800d56078035095508200066038010800700d901007107421240c4801c9215156000c0c804035641202904c0114010b205150210704108001c48811652018819000114404040c1040c2c0d86002c1c807015940040405c50040c0c000d03256000401c00300f4201c001c2707490300600c020301c0c01504090b240da903141005805400310340c02d4018070111036031003500160300b15110b0480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 551571348 1250 551570098 551570101
    0x1b030e030f030304110409020312181c060f0203060a06030b0607050d05031506040509130f0b15031015061103040305070b2a1009050c0607050a02010909050412050c0114 74
    0x1c440e501c83e0804c0d141200d02607a0006051041c1c50175000b12801107070010f015055000790034820615a5000d501941080d40c40c106024050fa510810440c520400f038240000c02c2d507040b894200110703507900c001259600c1c0b06105201c80d0b0f80b1880800ad00340e55941c14001801602c9000003241c034040c0d0030f002005441102c031030700011940071015601880c407441c10480503d11120400149000d14050b403a084941c103000079840780021440347c20142d00450403600000b40c0b40c0c40d4195011030072110400640068540312407142410400d5004803c0800020005c01c0541c5004600e0703c0620300c21074007040054110720012100c01e1081743c1c01036a020040718420f65031034682600c13907001824004424940d00e01c0c102c4000c0b003030324280200c18003108082c0805210b442100320080000b60011b40c1c20f40b05000b10b0580e940c031a0401024850300030303401455401c01c0382c400108040c5070747d005100c0a5007000140300c00240d4000c5152540015420044e484691a07040d071030040a64001c400c212207907820 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 551572598 1250 551571348 551571373
    0x2070809060307030e06010f0b07081b01060305030405190e0115051204051b0105070c0501140c030409050a11040f0b0304030c0b040b091e03250b0a020d0606030504031b030e03 77
    0x620281c00d805c202c0c019110143c1e070343c81c44280d540780644250814104200070503800036040310300508441042080b03800700140034801d0741e421182d89401c100c2e003d40c0b0009042c4110b00d451038031200380e510592a030940c00e505160620010304418812841c0003080030141c64a40b078050420b4030210fa400b0b91000e40d507450182030107991442e240c0c425030140c0c0040e102c410065446081150611a0412214000c071483c00004485542c1044cc00c898182c1e07081c001c3d50f910785414030050005007100100404c03641000c0c160741e411204010700340e60611008001c1003001c4000f00800c40115030006800c1a101d5695007800c2d5110001818000c0c410102c200400040081141803075006848003001c6038901030303244a110021440242c01348007950700c2800000a1031820b80c0001d0704c00c00745880440035130700c09035840400c0c0f0401507801c0c04006070082a0114030036000d01c9400014041454103202906154601401d0035a0352500805850315241c0560b080c0360007109050301400c00030382142c83c04001c02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 551573848 1250 551572598 551572601
    0x905130f0507150804080a0c14160f08030405031f060e01060302031503241b130303140a09050904140718060510080c0c10060f14010c11040207080906030703 69
    0x203020700144455201c3c49400e100d80315444041c0303d00d0380024414a4a203c500d03040d0b8040d80c446900310384510542403c400e01e4042406003122a20700c00f0782c0ba9507440d040c44040d138440c01c91608581e40d10f070700a200c104501e83c1c0010746001d00305c005012503048158081e050002270b00c80780d044a1010341019000050b007035499402184120011940b04611555004c1099212008258820203141c502070004d0705080c225003250785c0102200d51b01802022082030920303c20703041072142d0704884501150400c180364010268001d0b42c0103201259140c160404009031032400c49004590151555200103030400c01d450b400c814449410004403442c0e01d03070f01c40400c08484242000d2081c034a08103034001400317092070b00c0303000001d00160f25020b035940c0d21018915490317004102292410700c02d00b002140b40d24502d01c1408080c00e207000c0c0c4080000d0820283d401000001400303541000007200114012881810200740c0d0260216000360795100e103070030000014026401a568420b00c000b0a008116405 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 551575098 1250 551573848 551573863
    0x30b181204031e080406030e0307060e1f06030312090f050703050303071812061e0507020304030b011d07031107080f0c240619170f061503070905130f05 67
    0x150070843c00d640035240c400c422440c03541100501070201403009014190080d00f0a2425904181c120703810708005460f0503003690024000e140c000d0300700c0c17107040d80300c400c000901c201613210300c80c1c1c28002c0e9803a59400a080381064103400080503170702c003000c82c00c00c00320081205105801c14205c42005481c2c1c201581c607580b0640341d100104001040c408246042c154041003181c2e00000c7c1242a403d042c1c0324040500100032a44104030000e60030341801108610403503016003850360055442e5411131902d01c0d2006010b0b04001c190417882c4194050500038541c11590280b5035250214124138044d622100b28050164000c203581d1001c2480411189814050288420004101e40105500701050460101c4c07020004d08851300d80c0340007440908001e004c140c0040803e0841e01c920300d43d543c0040040c0042c6101c46862034000300700c103184d00182001070750381203007841419449044078070000a40c0e0f071103181b2410300b600b6103440000d840303c031031404129100c82e08004010003039001407070f1858a8a05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 551576348 1250 551575098 551575103
    0x9010501051c02060306062b0603200d11060d11030412080108100b060702041415100e0118122906012f011a0306150a030b18120403 58
    0x1c0b10481054034281402c40e101034540c01420992031a2035680505c5100e500c0104030284014030b0010040700e002800c403a58041d28000c11000a6090a61400c1e03001c16140b101140b04600c01150300088654540ea00000f9150f07004410004810181b40814824003c0701e030300903082441c0510b114140c18002004502c90f0780b1070184440c0c203654090701030b5400c00c0207014025540e1b0006907243c2c0c0745800313640f003201c128000070501403c0007425070009040e207104480440394483d0fa2000c1c801614201e8504d000e400c20100d40c652040001580010003100a00780d6650400c02e40c4240d10040a500708210000b038401074000400003015400c00500380105104504001d032400d9080c80103003068070790134900800059540c0c450b42100400501d4001e107940c800c1e55215040301009a590031402d1203502c0340c042e01c02500c50460b8a918007090b04210009010710704c1d12219047d190b5444daa0a5000002e07240d10280703240140e1030354070000c841c03410140c8600c103d500c94920a14504c0e03101002600440b0b1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 551577598 1250 551576348 551576359
    0x6020a050f03040608070503040c030c03151b05031603091709090f010503031911010914120903060a0207050f030d060906080309010e04111c02030603010e0f03040603051e0901050105 80
    0x1c40a68840340e03240324900c19440010000004143c4a0388100002c0d50050301804030030940f10707100d403500100310560798001c80340036202e0000d508000c089030007202813242100c00507070440c10310a00d0180503848020302c0f19103010904000b0003c2240039510450f010780d0800c440703c0c45900d14283c001001d40c001d1484030b21a01c2c06000041e03d0107208809507041e944041d01560810701c05202c901c046817000c05040003404600b06d801e1f59001000d204080c40b9500030346400c0c0751010f20300203a070700740110050000c500000400c40c00c0d40720f4400003402034003c040d00e100113079504042d0601c00c4c00c10400715007040b000d0200060701952181c1d1a0007250aa803600c01c420030806136a4070780d29680f0311a0a0300c0038041545002c16049524095205a407070741c0000400318948482c0d000030740d0b0008840030722080d00703907808020306c0a28102481b800100d00283e03070091510031000101c1b66681c1c042c41c032070a0301705900c0d02c0005001c5030b034090500c4030641107504068028105155a103000c1c0901740220b80c040c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 551578848 1250 551577598 551577613
    0x402040b0a0305150703020403081c0e070506040e090102040510021006050103050411120325060b010f08010308130b0c0f0616090e15060a0807081b030708040f0c06020a05 75
    0x203141c19000c000840b0351280c01021450040c844807950035500801000134140d0900c030000c08249580001c0250034040118500c20702401407102080718491451201588d12081003071049444a200700d4081d01c0b052403a003d0345940e5202854060306c41c5410080d003182c40c070900101c80c1a00020f2513003064104000900c11240c0f144011402c95004441c0900044126036140030b190800c00085a203855048080c0d900d0208a00c1048001004020344600400c00c0d455800050151500c02c1032b54044091820400202c04c0040c0204a140e040c040030307000103800100058208401070b0741d2001441481003943d2501482d821807a11000c0e54400d40c0b1450040c800003e6490b881902d11100c03400058407903c4883c0c1c1030042403014648004c04e902c000b0702c1c510700322450580c0c0d1480500303440c0c050b0b9551034410b4607000c6001000c001010340640740c01701564102d070051100000039a03034045030b640b4000d05695214188010404040f500c00740c1142040007011400c90703404102000514010811594013 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 551580098 1250 551578848 551578871
    0xa080322030504060c0309080106260105090a140a0b180c011e0e0102010e070b03100603090c050103051e2508090606010c02030a08040b040e010902070b01060e04150e040204 76
    0x1100c2020400400140701000280328540c014545001d01030b00078138044082c80c0c1c0300d00740305003114070380e03001115a540003c04000741450b0300749054000e001b00700024441402c028001e10750740c622903e0b00402c0030455802882140c50100f000300c40680c1c00200c3c501050815040c1580501003480030100940600d08048800354015208a4844520301c14800c1c1c9000d011441201c181041c000414115501c2d00200c0c00d44550070403811000c1e001c5081c21950300e08203140100c10320740c403941c006810b05080280d02000702c1c80e500b4640d1708440b406e003004502545e4009081c00180d6003500ca4000c0080f0300c900303101d00c859082a81004100c00031070480543c0d2f4442034262401c2c4002c4400384450360040c1d00041d17495120b24040204031f071020701114100d19055940208980241c1c00041c80f255001c201009105802c032038007030042440290031803500170103071685c04206005008020a03c140d420308105261210350001800158205c080c01d600ea48940c0041388031002503070103134410340c1071810309000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 551581348 1250 551580098 551580151
    0xb040f081e071109090d1206080a050d030c1407170c0a0f03260406020702010e060d021215010f080705090a0b04050f0105091003181415090106180b0307080a0803 71
    0x142080e00041c03c00c0706c952101107900c0c0d001c0352881000c05840d00400900b01c0820055082d0707a500c61000f400c0400c910a00c010206d0301c98140719010403404140303040c5140c0700002280d0501d50410481c4800b228041d02c001d245200e040d031070100e03a201f107040d07180500040004625500f40300799640084220702c1190099050180000810360303082c4180401c0c0040e0841e80108601441030401e080c003114558001880c40d00920f1500e04501d40008000394035902040c4500c1d0300080c012003c210b00845640024222941c10001c0414002c1c41404124014012403d4450940c0004c044407410703911262421380b61b801c10710429005514902141c8000c2d0700903015520082800340c075800000c900200124050403414134480c0c43e9085940c85100403408640001c081c428240c001080c11610b0140355589546008050320740710391403c0014001c0030010a0402f0001c03501e6800400d01d0520100041e041075501e52200000380308201500c000c0156140c05140705a003032001104030f08811804000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 551582598 1250 551581348 551581351
    0x8030a0305070915180b040e1f060c02130603020901090c030e1209191a0c150603030a030b2e1101020a0f0f0509130e0d0c0b040f081e071109 62
    0xc2074006002422442c6500c541030b1798006014002c0b0014000d66603542c0e01120b607020b50080c0003640f6041040010070800900c801190304040c0c034125461501c0c01d603000b050610b5a447c020300c5040381c02c45011003450150002c45c007641e0014801c84c169659104800010418101c800b00400d04190070141580070220741c0c1c0160f00384d4007e80d00d141100100810807491f01a0044010120940d40b000c42c00144094100c146501c0c0116425920108804180c0c98031102d14004a08071800c0002c20400307403400300681e0310f900313001d003030200b0b000f01058001245d03e005407400c0d00ea040c0e40c0f100b1401885103d0020034007014019110a10607040100d0081c3c00e0b40b082c10b048801107905072030382e040303143e1060f03504131421003151409506240341440040c01d211a4100200f8005449024100030146c09000d416118001070402c08000511039075042c07002000200003902440482d040d0310107000026044450701d5034040304c1030011080d410491600343e00552001d403840808924852154104903000e0f5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 551583848 1250 551582598 551582609
    0x50408030f07050c011b270e0c0d0515010f14030f0606071a19200f070b1303020d030624050d0e0a0b16140a05040e0108030a03050709 59
    0x5a10359900d104440740440c2000d40740c0c404200042001502d100002e00c0740e6120040054045400f0030078040f4010b005490451400700b6105844840440d580e000044560880e403500c820b03100144d40766a1440703010b000c6c8070070042809040c4000c0200501110381003060790761090b00c0340100d10080c1d54040300c90003001070003a81046030410109051420155200c0e6002d41d004081902c1c0c5144d0f99504410414400c000000880642040c4100c40800c2110040c5004100100b0081c524a00310038803240140400b03094282e0000103a81d0302c0c030002c00011203186075002007600640d410410800c2c0f4850401c50000d800501800910302d140901c6401440b08442d8544060a0725102c0401100c1e402000040b40744103200e000c00214903191110301600c40070580000140100b02e11508200200050041c00d102441030704000010000e500603030b407103030108980604682c03254800201a00e80380710319003240a8107901072000055403140000101036000340b41d90300f40481d8840c594103507800c01940c09034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 551585098 1250 551583848 551583863
    0x5060a02030f041407210302010e030306060f1c0e2407080f060102250501120c020703170c01050a091112070506070501020d060e01061b030206061c060e010507030e010504 75
    0x4100800c0082d9001c4144d101188140c0d03c00c4c1d66550a10078041c50310030b0700c4000c480c100e03100b240145074081c03060b02d4010981d603024620358900600003402510441d80400c2d0203444c00316143c0b142905d0030003d070360244241c0004000003d000c03103515580e1003203413801011500144409801001080c05464013030195601c0380200383e03d03042455a844d00f00100318504512a030040c01403050440d10280c4560040e05403a49007050505000408a03441030340c0842c8040d00707201c0c0400312142e0004039a01240c1d088402d18940001d681c2c1d6058540c07194850307048c055800e01e4180840c0c01040c0d07001d041618072070500400c42000000034400441070644000c2c51540005030108070908080c001031a00d244102d0006203070008880140741107444981040489001440042c0032203a04012960240c0302c01c0c3c0a00c41c0120300c0340d5802581c402d03004020340d029205803001079030210785075040095240e42c0b016003800140707071006525008002c00c558400009007004421940c00c0818480c1d0307070089400c29007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 551586348 1250 551585098 551585101
    0xa020a0f0e0a05040809040f02130b0c032a03070501140f100306050a0b03190201110f06070f1202030702250b090d230319170412030f110705060a02030f 67
    0x140c00208002081a05d01607000c0118807403a0b6607034411203282c03000f031000c0107031034044440b2800c548482c00e421000c850b50040000450b0301e00e001041c0c400c0ea03541c00440f20228159040034030b20514455001d1b111070702c4042240003c00c08190080c3d40306142030110049a03640d0009412400402036403206584000d044090020a00c150041c90307002100e0ba0010030011120b901080c43c21079104e41d01100c0003818080c060071907910107204051a11030400804500880d821074070340300e050140500080c0300320740c0d0180d15007500a2010030307203804150100b19124908034102075120600050003010b000b05c2004c58014056a001021003524041545d00d400d207010f20b0300340004081d0408080e122807540d440030f44d1110445028054110504a000e1501c0d032602120403840b8401c07034141507007480b150a04140058050700b0750b45034000d400401038000d40302d4149080e4020035a004195103000d040c407906040081404005046032482002104c030039a0b101e07425101280800d81354548440b03440d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 551587598 1250 551586348 551586361
    0x103120e1e0f030316081201090b0901060806030c0402040801020a080604060602072117180105040e07120908130f0f030f0314040806041416050a05040f06170a020a0f0e 74
    0x10501d02803010068200c918018440708000217013030344020b04492290001820701d4140d210700e02c1450040c1310f0701000b40800f0343c9020015007100d0050003100c0411444000203501c6960400c02820b42e920003410031559142c030fa15032a03010b5441511044041100d0350301042917800c05205203400c0b5895030307001c0d14520b03003420700a803010b20b2107041d0003152906103440b06000c20405211455001130050006036180d0300901d00c0c1804458030a5451305004d01404204644040c10031400d0303000e15103103005240c00500564407001410b41110150400102107002c00c0505003960724141030b00e22454904001d15560b900645c00c0c00703070500000b0940c200c04140a40013a004a10f5031440420303d1a6480c00c3c00d03100d00c049031800c1e404590279510380d0400c0d0800602c0e05014054080030f54644041c0490b402e0604010803418038580c4a110300a954400c5546064000b035408800030b003403100d0450030102c02042c6400d07540c50b0f07040c505a1140d4206880099650080c45190303049421100b0610840e03514034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 551588848 1250 551587598 551587609
    0x3110312030114040204090c0f02120705100c02030c100e070e04081801110d030902090f100303120b1f0f080f010909080708030708010801051602191103060103120e1e 73
    0x21100300d40103170f024000802c07840d04c80d0140314070500c0706a44200105031103d000910f005410024956648410059240414030101e40030035950341600e401b01d00e24519440407899071052603940c10050107541b00301450302c400c50704000440788021003192403158980840c01c0050100740c03002810860204485106001440d0740c815027007070141040e00309620341040e01424801806e00c0580003e0740c2700750f510114a0f03c001d5294100d02002d503402010310b8804d107194000802c5010150900c071103041c2080e8502416002000c0e0404054100f502d810030504985a01034269035a00012400784100402442d00c02c01a9510560404d6601800c50340381c207100c08024092040300b40c5a0300e200700b0240010a0b400e50042d4011403069955540c0c541c07501c241903003140c0d005414812011081c01e0018071040c4c0c0090000481c8080300c80c0e4510541540c501030301c41881d00d070340080e090300420340000140803802a2402c2d000c22a51501c50000b60030360104104020402c014118080800084c070b200c07418607 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 551590098 1250 551588848 551588879
    0x1d0105090702010e071712030f010801060f05060901081f030c05120c030601060804030c060516030e0c010c0602030a0f05040819030506060307080714030c0a03060b041d0a061d01031103120301 84
    0x58509903403e00c42e203140100101d07403084a00a5109d1000c40040285140901c03c0800070440c6211f4030002c1800c2500060045c4521200300d81081400e1380811801420810081a102140b16411004694a1500d4441035034144075580c4141c1400340c88401040004c2500c42001e40000c01600d0660708081094801c584050300a408201c074000c010000100c0901c0b039140603070031041e40c0e0342c3d56481c08400102941c00c040c1e14840150000700000e90700380d800c0900040600e6210501503160f03982c51100a006218003c070360360140e4201b405201c00d101c80000103006440b0f040c034035201b485083e00000c1e410f46000381e48d80380e008901080022200c52080e04016004449482c048008500e03080c0c280079941c02c00c2d269595070ba24000340c0100e1143d014070134a402885041c0d1000d04040c0703000300d11540d214008003c045080c0c003400001d120301c0d1030b9a02480103170007c03440140d6000044001c40003504401d01080b254003540c006032040d40d14000903420b41a8200e010301d1440d41c1e00300142c00d07160385034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 551591348 1250 551590098 551590139
    0x10b07020a06050717070c0302030d2c060705011104030b0a05010308090d080702181e0c070602070305070b010303120509010e0a0201050903013909060212090a1d0105090702010e07 79
    0x142440458031602c0090020580e46c0d004006510109085004050820f114500800b00740021040100900e12450321024100c940141c0200e00c000d601d400414160b201c2e010000b020b6500e040e10076040103500501a0080c0c031301030016aa000d6030b9900017203045035000e0101601d080e074103000c51216403800c8085640e180d03203d5a445410030300580d020822400080440060300c00c1240c04101c001445a10060425000708206000c28140942900045e208014020303000c02d80004045062600842c1214034a80e4810891504c07036a403805e0080207002841f840c0042c95040001044a000e414001c0c2030190070700714007902039010700d580156a554400005e41c0d0700f554965007480880045a01034203071242208100c0d145128044002d1480300c0c64002c642c00501603001404c0c010070740e001403115a00803402c2c00d000d50b0b80c0050400a012800982e0004241010410810b071a03038581301201412074006079040082074513501c0b400d90036220030070703080360499022510421040ca080303c500d10f010203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 551592598 1250 551591348 551591363
    0x100b19181a030615071a10030201080c1308030d09050c2b020a0b0c030909070c080d150b0703030b1005041a090d05190524010e090c1017010b07020a060507 68
    0x406429032000f604254400e0f6851a0350a40c158220100b1b900195840140240c000b41500c0c2160300180c0011005403021381500c0c40400c0000140106100718409070582a0803030b030701c4e00720100c0844080c1100781000c80f4640105040c00390903042600e00310460f84540624284005010b024500046203040003c0c0d9104002c20f0300042c0035101007004003000780003c0003440d40c8411900c1030006003a4058520020410700d4208070020070308520070742d112803180c28404500b90079a5004400065683e810000c2e1880c000074980c420150198081d0a010000703a40d01410203a040030242e945005900c562904041c00c14004000309504030010483e102c001045481212035a88a40345171403000c01004941c0c9a95a00800c14040f041100072400c00c155048403071201520b039070000d6412010702c00c82c2c0d9180081030100300100801d00006c2250040941620049102c480b0020503110080c80d00c50718245220001049034215101101e40b01d5401600c526985480c4c0300d400c071515400b8034020f0f07443c01c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 551593848 1250 551592598 551592619
    0x31f020a0207090e15090a0b07050c1c0825080c1e0301062c010e01050c19061b05040803220906030506150105030708010e100b19181a0306 61
    0x41002d4840d40304c0c981d4071040101040c0c5041560312071a5407020f44400b150f6481001c02000255003044000c0d8410320f81d1824644502400c400c1c0751a189241d90300c243c0b5440c0720003942c181950b00842c017507c105081c00c02507101d0003d1807000c0302d800d0754004201000994240c0064907200111006101ca055011070403000780c119421284d405030420381241d80010f072401d100d1003042e070481d01d01c0c2d000021a11450b0b00b03001c51404c00a4810060542d4060510074041580080351205019a8441d00c402e408404900840340c07400c9002890444c1103040510402e80070030307507894071070300550701aa04601c1c0214a48001060886c0060095100030b400c118041c030350100c8c0300b03080c0c1c0c0201001140700748018a43d038100200084580b131045017840f4100314050041000096000e03119904542c12488102d81c0c0352290082d43c1032003005604003c0079010006980b602e16071000001e0307a04820b180d030707405152a0b1403040030300181d4000c0c801e08500c0d14610007058442034100c4000c5401010003424036031074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 551595098 1250 551593848 551593859
    0x15030603030d11070309170a02010e060c3a0903060e01021909050117060d06151e0f0503190b130c060807180b0f0705010f05090604050c031f020a0207 66
    0x5a4004483c41c2c805080c010a0362000c140c2c0003030303040005d07107a1003100ba0300e81403212640d1603a404150a001c3e04202084d425015103482c0c1c001211101d403038810584642203200c114102e8900c0c02440a10501c10080c145030502c06418401078a403400c01d43c1e500c00401d46161204130180034900030120080d503003080005440c01d4005484030000c500754a40f480074918007000035103090134481c0d51440c004c10322010450036655154100d111250b1003d0300054241c101c030b10230521070b92107810411008010b100161500c000030191002260224417481d03080701c0e00d55040c10344400412041440c00c1e230426850100060760040c0560780710fd08910711218982e4592206140032503aa80f11001151138402404074280e0720071403111a0180c10f010b0746884a2030107003c0c6a0b544611008020150400f1030000b0802c034082d04130180001d0420380601041c141401001c2e01c805069a007181c042c032076074101c0d89442c1800f0841034440f0300c4840d680c19030b500396540418084d5000a10040c1180220345e8003282 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 551596348 1250 551595098 551595101
    0x30c2107081c030629180a09060f0b070206070201230409090519020604050d0201020a060e030a1b050c1021020d0c09050607030c020d05300915030603030d 68
    0x3031030040900d22a2108035907003000f80403241190021403503e1044409500e032074280300c0341c04403000c0304c84186030390301d44240f54040005e80c0417211441c0c0c0000c41e40c034000b400c841c45d60000d405507000c509200c0c040c6c0b542c441e0402c0251040c488004d40000c0d003840300c1800756020344c0b03141e1024003941e40444031169102010b001c880d842074003c100c0d15130f6104051010300c00100f14140400c1da2031940105d80c40740175000103140d07000368400c443c40f80c000e116034201164400d002c5c5181c400d5021105000000100c48160741f6604041c003000001049641d07603c542c61a00c40d100da00e41a004009840b011000c00140020f04944000070000c3c480c454081c01d1601700c10200250701800d11050050f151031604c840f81c4261401220b4070000c102c1603a02c00d01041d515101103d00a0754141003014501d003261020070201055144094500c2c0201c45040e42503c1503410030b00c00e044520001128029204a00d0641034050608559081600301254101c0200c541e0000c40d0001c0d00207003100e04111100c0210300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 551597598 1250 551596348 551596363
    0xd020301060c0b180709022511010f090b0708070f050607020a200108010b0307030e0a0b060301050a1116140106091407022808091c020a05030c210708 66
    0x181c0d0310914005000c40e101c1401d42006002c2101c4c91582250241256503140034000c04548a5001480046c0d036008100d520380f941048500b9420800100d04082060f40c40c503524103800b2032411004914201d1080d04000c054031000e112f0241084200d84417040b6070b4206403002c8401c03882e4800e103c000300c0e504200b401d110310f102d90b00502c501106441e0078a40e031201c0c4d05010922420083c0b075094182e80140ca110b0550707048140040e240d90790880b044010b00750f5400c040042c1e000740e40448080c008a000802d10914040d130082c00b468903024000003c48101c200c094040031014000d08564444081c0d07807180050180107501d24240c0102d400e0742c00c603052907000b101403c0d034030600d0400c08518403241e02c3d072090040c00a080a0401c0c0c1100000317410a8080681000d80040c040c81c0c200135420041d01e1005501404c506201c080d003e442e114240c04540c801d9200d5122950006100d25000812a1142001a2001c40d1101c4444028001c09548070015401741c0148400858600e00400040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 551598848 1250 551597598 551597609
    0x6090c05250c031b050306061c1106070812070207051503070311040803090a150c0b0c0f071101030506100927020c0109140607020d0e0315010e0105030f161a0d020301 73
    0x602c0c07003484084c501c000c542500c2d03020b14082d0708500308204d00b42e5188131401d03194800114030002209051700e422102400c1c4912420341c0800f0102e1740900740405500900300e1a49525000d04158807400426030361032983c0d00c21581c1c02050190000e88013010103000d140c0001240c1008921307401c1c852403c00842d001a0403080b000d51000c5001603261422056000040c83d001072400c0b03a2054428009180104159000d4081ca425001280d02010310704210b60402e4032094106031100001d2501c608504036400d04035000030f0600011580c249803004294114550548800304141d20304060311280c49810003e4104810714030302c41f40058080340c0004c040c3d4203121400006c00c481c0c58980003603181001c078030816155008038100300380d0320b0700000c3e0140022050706041d0035036440c9200107481c00e032814210400781c10000000080c0f82d035840c0c440710306862048084e030f4040d194001d01e5643d00e40d030034080c42c4a2581984020002811083c460111403114003180d54680300c00e5146500a07a80300b139110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 551600098 1250 551598848 551598863
    0xe0118020d0c1806030b3006040305030f070e010c12050409090b07080c040e190e0118110105120a051b03090610120503032e03030504080106090c05250c03 68
    0xf10098018101484805444a414100081300700480420340c1d1000c84c2220307442e00c50781d2070a00c00b001c0c3c2c0a036080c20900c001f8042200c4551501c1c1c40c0c01845d642099a510704004209004586258020085000544010f81d16002d159945444140000d103040c24040140f110801c00800c482969002e00c8000360f0050080d200d0b03a0501030001002e40310020103010240009100c1400000c0803c0c10f015085102c02e2081420201805415802000c840444e10368940ca090560942010b4401d4516580c5004824405603d0090030064500d4030880f1881003410b101d03000001c0850381c09600068002c4611904d80103907102c4000c4120495000b0766102109601001c2001506490791403240c01400d240c9960307480032501d5560b299520b01019120841826100c0d02205030a82c60300100c01d000ca20041d804985650390317040250155010b800349810759400c2100100c0c90804900441102d50f41540d0342602d002c0145034200391130715109000641d03d0803078400400210700010140000345009512 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 551601348 1250 551600098 551600117
    0x6020303163f0b0102070b07061107060c021b010e120a050a0b090f0a02010c150b0a14040f05040201080f070504150504090e0706020d051b010507050306090a060e0118020d0c 76
    0x310700c0300c2c800c24509008281810f10142920690f4042190700c00c8480a044150b226044c07841d00001030500d00441c50400c1c8008154081030001c43c0e00001c0300c0c1c642036020b031030403810b000075000090f0001c0e19909002c6400340544031000c1c201040c41e5102851040c05450b00801a40e48d140c2c14541d000b1026544001004244445604180040c80c0c180e00580010204000d01341e0010780340d140ca44401a10410010b0041540002540c0080e021805d005103010501ea845090103490300180d055154003452401070084491141031141c02c0c00703150161917030b0310a0355070840c1c44900c0b800010100c000f000002e210000d401030a41c20400f0010450ba11844d07200e07810514007800300c980f122031108090340090000c0122680100e400010000c0c0c5150065590340c8660500d800e5085066072900032350719040c10881200c3c2d00c500518010742048580c3c0c0359a03241e84081000303492090086d4004005010300402800e08110144401003072284009403c10140c1c0c040f1304100c0302c42a00c1403000c1070380c020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 551602598 1250 551601348 551601437
    0x1205210702030d05120f0c0705100f06090b03120a0203120a090b1f05090702030418020310121203020307260901050c0406080c1b191109010602030316 66
    0x818004000d0003440e106003800c1707403034a1507958548007401019203030b05424040382102e050340c41250001da80000c110381144804034041c900500303801103455a20341c644800418101c031380c0e004000c0c410740001d00610300b100002005040c0c179800358001c2000e501c420810340d1410390b440445c6911603801080005050701d10380c20b151000038030003030800044400741180c9040e001200d201c4101a250250743e402e400d95100301d0143e1a621441c1c11060407070203001e01c1c910b102111500114410300304018000710041c1e40c4c01d00b040c8840d4011000611000c030440c45034141c140b00c0c1c0d01079a8420810310301100e80c46d4411418211a20040301781c8000441d8100c10170090003070034080d868000e11201d803540c2c907051070208002e00c00320002d030209c081c6c210000754106c0441c1c80518212600c5141c802a20000c801c0c5e510000340301401c80808551119003020303020303028903040c0e500038121003041c0c000c0d610316a58001900750f160401d04100042c0648002d81c1d00c0505104544200c120842583d015091321085 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 551603848 1250 551602598 551602603
    0x14011404180f060c090b0c060108010b03030703120504060b100f1d0114030a09052d0c01090324021605100501060f12110d06060e0a0f120521070203 65
    0x9200803806100000c0074000050301000031103107243d80126002a25210205044801103099403050310030304008141528000004144907040310081c0c802004070f010914140343e1070340075161010b0301280900364212010103654215590051060354002407200d0300c0c00020b0304022102d50000002090009107480f0150041111060035030940c80100c651541c44000034800e901c0f0b42c40c0d40c2040c2c3c2011010844200c9244c1000d800a0f6000c0140d48440d070305003060104100d10b00100c010032080da0f20064010900200d00310801d56410795600d0401411521011080750101c1c0000101d021a03000c0d0102040840c806851012003406641002d030455081562070500d4070f040da00d01d20740c84d2000400c0f845d0b030440d68171001c14141c0c2c01c01118801c021910103009124404503107411002c00508450402529802001619810748459541a854001780000714009004000740c0c1c041c3c040c0d0903c604910502d418401500ca4801c0b160311a0500841b80603081041211512000000c1100411880d05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 551605098 1250 551603848 551603861
    0xe1804021809030405150d0507020f0d080c09091f0308040f1d06010f090e04030c1419080c0c030a06060906050603090a06020904140f070f0c03020703080d14011404 72
    0x6106641d003281801502640c41c1c1c0f04501c42d5601c078490350000341c4a50110071041d1060300311a403000300b00c1c3e40782c0028060345600f900c4010b000d00c0e005034164484100c0c0520701c107078011100d0300420b5003400707070210a00c10f10480c05000071621031000300c614122020550100c4028502c603c2079140c60341d1501e8910b04100180d0b130400d020500e54041030450003045412410b80c007103001d18060300e034409041004d9903603a82c1c42d00070300c0b03034248240100018180c0105030946050701c10702018001c02840c001c81c6454140c2c02c4108a031500082e82640081080342c00a0700e1040041026200f40150000c0082c0c500012100308540c03860300c8140c100001b421038800e850061030140c52062540c03070002511501c0b40b40c90200208241d078082076103440f540f80c65000f80c000c00100d102c20381e01070a020681200210701140c512001074643c0c2145003c0380d100d44d4115101640c141c004089581c20759846404682025082c1072489507241c207201410314520070914020030218076900380300c3c244035041c00265a072 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 551606348 1250 551605098 551605129
    0x70f0206060f060d09061107030509031e19060213080703050106060201050910110f1b16060905010c171b0606060a0903061a040e100b030c0117070e180402 68
    0x5091444030050f8842c241200e02c8a05145000074483c503051070b00400400c451004591011008182002051341102c001c09803140124101d90301d401451510420f20075001b03400303a1054010a100f00c04c0d44051035490004a48540360150903e07a52402c0c00303002d0f1b030741c0e6809081c05500058082003403180a105640c043c0c1101d00c024030581c035040155039a00c0c488003481e022110f6580e01140b5161007030308107884e900f801c3c3e50145951010088881d600101e041e01c04690140210785020485c0422100b101c0700701c1d10151155a001440c0c5001920010003c0000303442a0591400c0c4800c1043c9140061507540c104094052540707007141545441c004000b40400c2c0904810411600040e030401148d900b102d910134808207110340401e0046c0f081810340c004040e0054140321080422500200799600d00700b007100b40030040025441c0415599800c1c1c08031050104552aa03000c80c4c5c03402d0452950352003074060400e003020014010200384181000c00e805420341c1605401c2c0011850111042c614007107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 551607598 1250 551606348 551606359
    0x6080109020403170a020c0a0b070b06040519020919030f031d0102100905210903010e06130b070c0b01090f0608010c090512010b06030a05010e0705070812060d060203070f020606 78
    0xc0c190384e200e000700c1c900c030100d82081e00f101048882d2900d108211000c04520041d01e01046c03a40c1d104201c0c0100d0b0051a0200c0b480c5002c80001219410f0a10600d4860315014000288200c03041b803094009500c00690241c00044e40c80c1c1d84240c00c40b4000ccd006000b503201c1c181d004401122410000c22a19410700c4071025848691111041aa80010806c0724101070b240c000903561030301e1030128904400003038000d048455000d00c010065a008000d8560710030242d00902004c03100004c460b0701d440040340c00000d01202e0030381c400046400d4144196000b0800c3c1000e0140140c41d413640071100200340d00034042191900b00814003280b0b6401207100070260500240103525010a0190403600c190081034085d030b224040000d040b42003500302c08824803016020310fa403420055002d0014040900a01042d05100e10110701c425204204640300580c0102c030b903500313141c0440ba601048683c0a0b250550261130042c0000201d203440c40118010f9800340c03a07121294540303c8000c1e081080051060744a035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 551608848 1250 551607598 551607607
    0x5130203100b0d0614011a0717030a0603060e34210b0f15010f0219150603030509030f030708030118200306010908060c0a03180606320a0902070609060509070608010902 74
    0x9d445282c150b0004184000c0d60380c41340d403a4009c0c80b0040c03e56500241000b41440c191103c000004150400502001d81ea1052011040480400045e05a83c20104141488403003002031804559460f80d8064030602e07400c3e010700d41507e600701c6680090b41e030341c20901014424084140e000c0c0c142483c81070003c0c20b141400400043d4082d440300c11000c2240e941340d90301c0d040b80303041103843c6003201042c40b00b1400800c1030383c5d220b0074000c0c01c40d00001c003140c0c001d2140c40c0c00111420000001d031984142d0023a192881c1d42c0c20180660700040d00d05106002950304c1d581c9014140900c0c0b544020000d25002c030700c9482e0b24141000400c00c9445a219036126000b25080c04030701ea81000031588004e032913090204407008a00411046130042c0e20000e044140b9050011468981400c0e00d00d400e088001c584060301080300000c41c030800d6206407140c0c0d02c0f8041402c10040c06032242c01501006c1c0c003804001980e040c0781d440f403c003aa2005c5581844036085a4000d0100c241c000c51058090030381c480046041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 551610098 1250 551608848 551608853
    0x801090b0d0f020f030715020705040f0e071806050919050f0c030711120c0f1506010c1424060102070e092d0f01050a05130203100b0d0614011a07 64
    0x210b120289000c1e01414048000c4400c40d101040b8502c020174507030103000c0c40c000c0030340e50082d294080707030007058491418220414201c5026004e07588100d50100301406040307240c4002221034000d40504900e001780c681c02d0008150383c42401952060a00d211541c1d0080f91091400c0111540104001140c1c01c03064284800e0f032555005582e804046410b0104545040c49119443c4c1102e2a0340361041000004e10b00c1081e241c049043c060380440c41c001c03100d01040900000f00d00b83e0084442c140020814100d4001042c8803c0f204083c03155110306840a2283c0584418008422032494000040c82c0c5410712082e964104030040092040000213103203410701c4aa0642c03920303036a40c8184c10144002501d400070207198000810f8082c151004c603415202048429400f90800b222825403861611340040d1176650b012a41da400707280d004002d000300142001c81714000742540200d4a400944d0304401c0000911180301d10203407443c01c00c8102e0000d41c07404103003042d002c142e011080070046060114900 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 551611348 1250 551610098 551610113
    0x1f2a0c0605060f03010e1624180504020703020a0b0a09020a0509061c060516050c03031902210901230c0d020f27090c0f13150801090b0d 60
    0x4140e500c500c0208a50715040009100e4407201404990325519154940078891000581d15240611848001b404e55544014401e0003041c6440005640d1000c2424034449520480914118400c0d1840340080c060b119000701d81282c000300001c402591040072030003b0f100214200301c0d07025404080500040b41c83d94040b486011151242600541d0902d003c00c4071a5500103000e440134500000d0241d4082c02070404102400c02500e031800000008003485a0181c404d00445050746c0210005624540313a08109100c1d0b081044d0f0f4901c2940d50900ca10340c20300901d40001506a0101d641030903203420041c05480c01c41d6062000324000d5140050f2103a03071100c0d0340360965030106080c1911500c43c0c0032a00c05801074810110407542d601400130340280300c401410364041c148101c0d440c0c0040d0800d011024800200303402e84940b23000d01c41c10b100b0203002c2045180244188208649800c00659903205060f0320039400c003400d0307804103030b0800c014442c40d641c0b0301c141800844100c84807450101240c40d1510b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 551612598 1250 551611348 551611367
    0x20a02061c050708010f050301020415080402030f0d0210111612050405090c0c010b033f0f0406020d0309080702060a0302130f082415031f2a 62
    0xa000300004140d2000e1040c00c29489488555409014045441c1c00380d401800c40809001c0c0111240d4a064045040c3c101403007590290340d0394210b00e200b032108214096030b881034000c00407030703040c030503409108d052071004d00100c190304106800806440700e501c011401038a40c0140701c00c000140c180070034002e0504005282e64007541052415012000c215001c494a01c296081180c20460324418404004000320081070000799000082208214581c101515558640750349034024402d150a10041c12201311109414000401068580c0d01503841c04a890740114200c6661a40007142c1088000e4040c000d1181c0b0023494501084200745a40c0c070b0840f00d0041c502d002e4060500824210030282c001c0d411940147c580d1403640200720781e20320303903400c00419600602e601d600406c5a030a0200ba0000c42400780e40b0059124014280d445c00002458641200e030155071501c215210130840000b05146407240e040c41c1c040c0814402c030509248020840340c170084040402c0419401000030390300140e9030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 551613848 1250 551612598 551612603
    0x501110310060e100f120501150f02010c0c060b011101050a09030905010503100e06010309051605040b063609071d0d080901080a0e070b0904050a06180905030412081216020a 76
    0x42214088010846d041d640d0095107050080c900000840c900002009859a08820359a80001c941080d50200d00780d4001c4030b90b40000c1032690a080700010081d0300030802c162410724000380d22030042c18485080d118291512140203603602d07904003c0c0766000c0b81c0f05014020a0a09506c1c42c10488500801c05150703120305450354004401240036a8402e070481c1c1281034006007100c856418115001c14800c04511034148914584901004903041c0581603d84880c010801d802c20041c0074210448409402c000c4c0310040c481c0240440c1c400e54401c0001400341c909035403448408082c030400700c60f444100f49440f03489001d9007410500010340034000c03600c40700005e00e02204540c940584400240000741c590705e880c0d010f01180030a1f0302c0140c00150106560403182404035444400a09045440382d02a04000003070701201c2000200480d040f03061440d00c20000c45c0c3c60300b6501c04841c060211700307078001c40750f01c90700040e10307400704942d080c0300b5030080840b04120901d008031000196030b0741e4118400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 551615098 1250 551613848 551613857
    0x4030b0907180b0a03080a03020c1509150a020904090c06030f0207080435150112020904020613091104140f1c030203120f04020102070905011508060d0501110310060e10 74
    0xc6071500e07100c80c13800500441d40300012644445065401502030740107110300309507902c1200d0780e40c5240819504014087c100301405020741203448a01e0b07400f98a0010800c040d255000c11480000d900e96206612111b0b01405000b01200c1c01c08000030f0640300c52809480c1c187c0d0040c0300700d4010880c0c000845044a51403d4001c2d0500300e2010b030070000e0208480c0341143d8034612040c480600c14042903880c011610750080110603a01c0e0042c501d020001c1e00c0010350440d0032040090010f050560040c44035142198405c980141c1d2904d0b0b810035240941041d486180000c00c0400010342d00e07039180c5140340c1c41201d035540c00c0a50140030414012040e00c0000c00389801002000601d40280100d880a03090000046018a4822110680310341c0a0354202d0046c8502480062400802c1c0304041c16a00181d282c20041c111044040f1052900a410305070321012119400c0e00180f030910a8011141e01c01582d42c0e200c0c58150140d8010000310b40c422418461092420300495071914030703a02942c3d501e403c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 551616348 1250 551615098 551615111
    0xf12020702180921030f0a240b070215070b040611071a09070b18010e0616110103050a0b0901050402071a010e100902040e07030c14070804030b090718 66
    0x421540c084003950040340000024006240c0020655010384d01c000c088604410b140c01c0b03c040341d64841100d06000600750100881c40705e4043da0031412103400e40021800c0d41d1000c2420b0300302a42640d0340f00000f0100d000a8840860400c2800c01c440c2a0000381d540e0308085042e214900301d0180100010041555078004c3e281c0c0c40f42040c00c0e11483e42e0450320410082408040300c1303400c0e400a8581c1c020a1241070300000b44226035108488030300300321b18012085a004030005403044640c40590750761108050220080c1c60180071700d02e041182c0160b070681505407005001404580d0060010300d050f0b1f0900000306c03034a40316981301d0b60444d80c0603240160388604a0070401d01c08a88050000b5002c0c2c207203400064190f01d40d68059010300040000000100da854078001c0c100d10652281422407220900004c015a00030342c0711006084660074454a400d40b18841029a0303440b80c2c0341250000c40105042c02488009642c4540c007081a00041c06414142858507540c4141c50030401500c039120711 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 551617598 1250 551616348 551616353
    0xb0c040f0902041d040f12170712110c0a02130b030a08030906070314041506091b1e051b1606030c0201180308070c0302011b0e09070f120207 62
    0x104860080c03929600c1014a0341d12052000040d41c010311a502e61140e0140064422000f8403040a02981e8001c144d9200d401041c0d03145018000c6440242092003030941c20701103442c2e030742d58205224044030340c2e0312402281305982150486e072000442c840380d40303001e000c079071842140040c11043c0d480d0109c0e800b11043d6004000c1708050440f814201c0e0700741c041c402c140010029954061401455044e050325000d07603804004404680e0880e078140800d000074000b0070080303010718141c0c46610392545404942c4a45600b581d03025112a0903148120305500e668010300c03154442c2484000c2118004c40500ca0032200100520301d0140c82542d8103207a001c60641e188840040160100031b040c02d4400400541e55600301400030309801c2c02e840055400c205100346450305c000e0014541344e0341038035520b07104d4589110490b800b04004104606640d66500b480c0319070315401c00106030400103a80c80c8003407401f0300d0781401051040600402d0038803500c0d010013404150407075802501c8403210b00d401612184c003030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 551618705 1107 551617598 551617621
    0x20a0905060306072006180c0d0503040501050903070306111215150d090209010e100b0310140a0e04030c110f01170a0e06090a060c080105030a0b 64
    0x42000112034500441e100340c4107002da51700f2600b03d83e0072a01d4070b41c500841601c2040d40f9012620074401581d10402c0807003c00001a43d846614100d43c0c0e981c2a80ca0003a030040324144072010442c2020f540b0308010000041d40c20a40512180c520480703580303020b40c81104029400c118050000d41b24041c2e00c04101183e48018101c6105c030050728411038690382240c03a0360840140c9440c44503002d80d4620820501806905d640b440080c1881145800129a0f5502c103c06e001d000340708000c0b0069070580d0650444041005640c11303000b00000050098000c1e4124521440e014010700050503840b90045155074400c030503405106000004200b60034440860060020756801000b0410410303464455030014284035000c034901503840341c543e041a208442e201c1080e03001c40d1035a03040c0002030085550024990a20390403550414000c40e4035940c0c1b00001a048483c03c001041c50500f88 = true := by decide +kernel

theorem cover : BRFrame.Cov 551438848 551618705 := by
  have h0 := BRFrame.cov_init 551438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 551438848 ≤ n) (h2 : n < 551618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
